//! WASM Component entry point for Nightboy.
//!
//! This crate is the `cdylib` that gets compiled to `wasm32-wasip2` and wrapped
//! into a WASM Component. It wires together the CPU, PPU, APU, timer, joypad,
//! and memory bus into a frame-driven emulation loop, and bridges to the host
//! via WIT interfaces for graphics (wasi-gfx / WebGPU), audio
//! (nightstream:audio), filesystem (wasi:filesystem), and input (wasi:surface).
//!
//! ## Layout
//!
//! Four panels:
//! ```text
//! +----------+----------+----------+
//! |   Game   |   ROM    |          |
//! | 160x144  |  Browser |  Trace   |
//! |          | 160x144  |  Viewer  |
//! +----------+----------+ 160x240  |
//! |   RAM Viewer 320x96 |          |
//! +---------------------+----------+
//! ```
//!
//! The bottom panel renders at 640x192 (80x24 chars at 8x8) then gets
//! GPU-downscaled to 320x96 via a linear-filtering sampler. The right trace
//! panel renders at 320x480 (40x60 chars at 8x8) then gets GPU-downscaled to
//! 160x240. Both give ~half-size text for maximum data density.

#![allow(unsafe_code)]

mod app_state;
mod bus;
mod debug_panel;
mod font;
mod joypad;
mod memory_panel;
mod ram_viewer;
mod rom_browser;
mod timer;
mod trace_log;
mod trace_panel;
mod trace_viewer;

wit_bindgen::generate!({
    path: "../../wit",
    world: "nightstream:nightboy/app",
    generate_all,
});

struct Nightboy;

impl exports::wasi::cli::run::Guest for Nightboy {
    fn run() -> Result<(), ()> {
        run_emulator();
        Ok(())
    }
}

export!(Nightboy);

use nightstream::audio::audio as ns_audio;
use wasi::{graphics_context::graphics_context, surface::surface, webgpu::webgpu};

use app_state::{AppFocus, AppState, EmulatorState};
use font::{ROWS as CHAR_ROWS, WIDE_COLS as MEM_CHAR_COLS, WIDE_ROWS as MEM_CHAR_ROWS};
use bus::GameBoyBus;
use debug_panel::render_no_rom_placeholder;
use joypad::Button;
use ram_viewer::ViewerAction;
use rom_browser::BrowserAction;
use trace_viewer::{TALL_COLS as TRACE_CHAR_COLS, TALL_ROWS as TRACE_CHAR_ROWS};

// ---------------------------------------------------------------------------
// Layout constants — four-panel layout
// ---------------------------------------------------------------------------

/// Game Boy panel size (also top-right debug panel size).
const GB_W: u32 = 160;
const GB_H: u32 = 144;

/// Memory panel: displayed at 320x96 but rendered into a 640x192 texture.
const MEM_W: u32 = 320;
const MEM_H: u32 = 96;
const MEM_TEX_W: u32 = 640;
const MEM_TEX_H: u32 = 192;

/// Trace panel: displayed at 160x240 but rendered into a 320x480 texture.
const TRACE_W: u32 = 160;
const TRACE_H: u32 = 240;
const TRACE_TEX_W: u32 = 320;
const TRACE_TEX_H: u32 = 480;

/// Logical canvas dimensions.
const CANVAS_W: u32 = MEM_W + TRACE_W;     // 480
const CANVAS_H: u32 = GB_H + MEM_H;        // 240
const CANVAS_ASPECT: f32 = CANVAS_W as f32 / CANVAS_H as f32; // 2:1

const SHADER_CODE: &str = r#"
struct Uniforms {
    // xy = UV scale, zw = UV offset
    transform: vec4<f32>,
}

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    @location(0) tex_coord: vec2<f32>,
}

@group(0) @binding(0) var gb_texture: texture_2d<f32>;
@group(0) @binding(1) var gb_sampler: sampler;
@group(0) @binding(2) var<uniform> uniforms: Uniforms;

@vertex
fn vs_main(@builtin(vertex_index) vi: u32) -> VertexOutput {
    // Oversized triangle covering the entire clip space:
    // vi=0: (-1, -1), vi=1: (3, -1), vi=2: (-1, 3)
    let x = f32(i32(vi & 1u) * 4 - 1);
    let y = f32(i32(vi >> 1u) * 4 - 1);

    var out: VertexOutput;
    out.position = vec4<f32>(x, y, 0.0, 1.0);

    // Map clip-space [-1,1] to UV [0,1], then apply transform
    let base_uv = vec2<f32>((x + 1.0) * 0.5, (1.0 - y) * 0.5);
    out.tex_coord = base_uv * uniforms.transform.xy + uniforms.transform.zw;
    return out;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    // Black letterbox outside the [0,1] UV range
    if (in.tex_coord.x < 0.0 || in.tex_coord.x > 1.0 ||
        in.tex_coord.y < 0.0 || in.tex_coord.y > 1.0) {
        return vec4<f32>(0.0, 0.0, 0.0, 1.0);
    }
    return textureSample(gb_texture, gb_sampler, in.tex_coord);
}
"#;

// ---------------------------------------------------------------------------
// Viewport computation (aspect-ratio preserving triple panels)
// ---------------------------------------------------------------------------

/// A viewport rectangle in pixel coordinates.
struct Viewport {
    x: f32,
    y: f32,
    width: f32,
    height: f32,
}

/// Four viewports for the quad-panel layout.
struct QuadViewports {
    game: Viewport,        // top-left: 160x144 logical
    rom_browser: Viewport, // top-right: 160x144 logical
    ram_viewer: Viewport,  // bottom-left: 320x96 logical
    trace: Viewport,       // right: 160x240 logical (full height)
}

/// Compute four viewports that fit a 480x240 logical canvas into the window
/// while preserving 2:1 aspect ratio.
fn compute_viewports(win_w: u32, win_h: u32) -> QuadViewports {
    let win_w = win_w.max(1) as f32;
    let win_h = win_h.max(1) as f32;
    let win_aspect = win_w / win_h;

    let (canvas_px_w, canvas_px_h) = if win_aspect >= CANVAS_ASPECT {
        // Window wider than canvas: fit to height, pillarbox
        (win_h * CANVAS_ASPECT, win_h)
    } else {
        // Window taller than canvas: fit to width, letterbox
        (win_w, win_w / CANVAS_ASPECT)
    };

    let scale = canvas_px_w / CANVAS_W as f32;
    let offset_x = (win_w - canvas_px_w) / 2.0;
    let offset_y = (win_h - canvas_px_h) / 2.0;

    let top_panel_w = GB_W as f32 * scale;
    let top_panel_h = GB_H as f32 * scale;
    let bot_panel_w = MEM_W as f32 * scale;
    let bot_panel_h = MEM_H as f32 * scale;
    let trace_panel_w = TRACE_W as f32 * scale;
    let trace_panel_h = TRACE_H as f32 * scale;

    QuadViewports {
        game: Viewport {
            x: offset_x,
            y: offset_y,
            width: top_panel_w,
            height: top_panel_h,
        },
        rom_browser: Viewport {
            x: offset_x + top_panel_w,
            y: offset_y,
            width: top_panel_w,
            height: top_panel_h,
        },
        ram_viewer: Viewport {
            x: offset_x,
            y: offset_y + top_panel_h,
            width: bot_panel_w,
            height: bot_panel_h,
        },
        trace: Viewport {
            x: offset_x + bot_panel_w,
            y: offset_y,
            width: trace_panel_w,
            height: trace_panel_h,
        },
    }
}

// ---------------------------------------------------------------------------
// Panel hit testing
// ---------------------------------------------------------------------------

/// Which panel was clicked.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PanelHit {
    GameScreen,
    RomBrowser,
    RamViewer,
    TraceViewer,
}

/// Test which panel a pointer event landed in.
fn hit_test_panel(
    x: f64,
    y: f64,
    viewports: &QuadViewports,
) -> Option<(PanelHit, f64, f64)> {
    // Check panels in order
    let panels = [
        (&viewports.game, PanelHit::GameScreen),
        (&viewports.rom_browser, PanelHit::RomBrowser),
        (&viewports.ram_viewer, PanelHit::RamViewer),
        (&viewports.trace, PanelHit::TraceViewer),
    ];

    for (vp, hit) in &panels {
        let lx = x as f32 - vp.x;
        let ly = y as f32 - vp.y;
        if lx >= 0.0 && lx < vp.width && ly >= 0.0 && ly < vp.height {
            return Some((
                *hit,
                lx as f64 / vp.width as f64,
                ly as f64 / vp.height as f64,
            ));
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Framebuffer dimming
// ---------------------------------------------------------------------------

/// Dim an RGBA8 framebuffer by multiplying each R, G, B by 3/4.
fn dim_framebuffer(fb: &mut [u8]) {
    for pixel in fb.chunks_exact_mut(4) {
        pixel[0] = (pixel[0] as u16 * 3 / 4) as u8;
        pixel[1] = (pixel[1] as u16 * 3 / 4) as u8;
        pixel[2] = (pixel[2] as u16 * 3 / 4) as u8;
        // alpha unchanged
    }
}

// ---------------------------------------------------------------------------
// Emulation helpers
// ---------------------------------------------------------------------------

/// Run the emulator until the PPU signals a frame is complete.
fn run_frame(cpu: &mut cpu::GbCpu<GameBoyBus>) {
    loop {
        // Trace: capture state before step
        let pc_before = cpu.regs.pc;
        let cycle_before = cpu.total_cycles;
        cpu.bus.trace_log.begin_step();

        let m_cycles = cpu.step();

        // Trace: commit step
        cpu.bus.trace_log.commit_step(cycle_before, pc_before, m_cycles);

        // Update timer
        let timer_overflow = cpu.bus.timer.update(m_cycles);
        if timer_overflow {
            cpu.bus.if_reg |= 0x04; // Timer interrupt flag
        }

        // Update PPU
        let (ppu_event, ppu_interrupts) = cpu.bus.ppu.update(m_cycles);

        // Apply PPU interrupt requests
        if ppu_interrupts.vblank {
            cpu.bus.if_reg |= 0x01; // VBlank interrupt flag
        }
        if ppu_interrupts.stat {
            cpu.bus.if_reg |= 0x02; // STAT interrupt flag
        }

        // Update APU
        cpu.bus.apu.update(m_cycles);

        // Frame complete?
        if ppu_event == ppu::PpuEvent::FrameComplete {
            break;
        }
    }
}

/// Map WASI surface key events to Game Boy joypad buttons.
fn handle_key(joypad: &mut joypad::Joypad, key: surface::Key, pressed: bool) {
    let button = match key {
        surface::Key::KeyX | surface::Key::KeyJ => Some(Button::A),
        surface::Key::KeyZ | surface::Key::KeyK => Some(Button::B),
        surface::Key::Enter => Some(Button::Start),
        surface::Key::ShiftRight => Some(Button::Select),
        surface::Key::ArrowUp => Some(Button::Up),
        surface::Key::ArrowDown => Some(Button::Down),
        surface::Key::ArrowLeft => Some(Button::Left),
        surface::Key::ArrowRight => Some(Button::Right),
        _ => None,
    };
    if let Some(b) = button {
        joypad.set_button(b, pressed);
    }
}

// ---------------------------------------------------------------------------
// GPU helpers
// ---------------------------------------------------------------------------

fn upload_framebuffer(
    queue: &webgpu::GpuQueue,
    texture: &webgpu::GpuTexture,
    pixels: &[u8],
    width: u32,
    height: u32,
) {
    debug_assert_eq!(pixels.len(), (width * height * 4) as usize);

    queue.write_texture_with_copy(
        &webgpu::GpuTexelCopyTextureInfo {
            texture,
            mip_level: Some(0),
            origin: Some(webgpu::GpuOrigin3D {
                x: Some(0),
                y: Some(0),
                z: Some(0),
            }),
            aspect: None,
        },
        pixels,
        webgpu::GpuTexelCopyBufferLayout {
            offset: Some(0),
            bytes_per_row: Some(width * 4),
            rows_per_image: Some(height),
        },
        webgpu::GpuExtent3D {
            width,
            height: Some(height),
            depth_or_array_layers: Some(1),
        },
    );
}

/// Create an RGBA8 texture with given dimensions.
fn create_panel_texture(
    device: &webgpu::GpuDevice,
    label: &str,
    width: u32,
    height: u32,
) -> webgpu::GpuTexture {
    device.create_texture(&webgpu::GpuTextureDescriptor {
        size: webgpu::GpuExtent3D {
            width,
            height: Some(height),
            depth_or_array_layers: Some(1),
        },
        mip_level_count: Some(1),
        sample_count: Some(1),
        dimension: Some(webgpu::GpuTextureDimension::D2),
        format: webgpu::GpuTextureFormat::Rgba8unormSrgb,
        usage: webgpu::GpuTextureUsage::texture_binding() | webgpu::GpuTextureUsage::copy_dst(),
        view_formats: None,
        label: Some(label.to_string()),
    })
}

/// Create a 16-byte uniform buffer with identity transform.
fn create_identity_uniform(device: &webgpu::GpuDevice, label: &str) -> webgpu::GpuBuffer {
    let buf = device.create_buffer(&webgpu::GpuBufferDescriptor {
        size: 16,
        usage: webgpu::GpuBufferUsage::uniform() | webgpu::GpuBufferUsage::copy_dst(),
        mapped_at_creation: None,
        label: Some(label.to_string()),
    });
    // Identity: scale=(1,1), offset=(0,0)
    let identity: [f32; 4] = [1.0, 1.0, 0.0, 0.0];
    let bytes: Vec<u8> = identity.iter().flat_map(|f| f.to_le_bytes()).collect();
    device
        .queue()
        .write_buffer_with_copy(&buf, 0, &bytes, None, None)
        .unwrap();
    buf
}

/// Create a bind group for a panel (texture + sampler + uniform).
fn create_panel_bind_group(
    device: &webgpu::GpuDevice,
    layout: &webgpu::GpuBindGroupLayout,
    texture_view: &webgpu::GpuTextureView,
    sampler: &webgpu::GpuSampler,
    uniform_buffer: &webgpu::GpuBuffer,
    label: &str,
) -> webgpu::GpuBindGroup {
    device.create_bind_group(&webgpu::GpuBindGroupDescriptor {
        layout,
        entries: vec![
            webgpu::GpuBindGroupEntry {
                binding: 0,
                resource: webgpu::GpuBindingResource::GpuTextureView(texture_view),
            },
            webgpu::GpuBindGroupEntry {
                binding: 1,
                resource: webgpu::GpuBindingResource::GpuSampler(sampler),
            },
            webgpu::GpuBindGroupEntry {
                binding: 2,
                resource: webgpu::GpuBindingResource::GpuBufferBinding(
                    webgpu::GpuBufferBinding {
                        buffer: uniform_buffer,
                        offset: None,
                        size: None,
                    },
                ),
            },
        ],
        label: Some(label.to_string()),
    })
}

/// Render four panels in a single render pass with four viewport+draw calls.
fn render_frame_quad(
    device: &webgpu::GpuDevice,
    graphics_context: &graphics_context::Context,
    render_pipeline: &webgpu::GpuRenderPipeline,
    gb_bind_group: &webgpu::GpuBindGroup,
    debug_bind_group: &webgpu::GpuBindGroup,
    mem_bind_group: &webgpu::GpuBindGroup,
    trace_bind_group: &webgpu::GpuBindGroup,
    viewports: &QuadViewports,
) {
    let graphics_buffer = graphics_context.get_current_buffer();
    let surface_texture = webgpu::GpuTexture::from_graphics_buffer(graphics_buffer);
    let surface_view = surface_texture.create_view(None);
    let encoder = device.create_command_encoder(None);

    {
        let render_pass = encoder.begin_render_pass(&webgpu::GpuRenderPassDescriptor {
            label: Some("quad_render_pass".to_string()),
            color_attachments: vec![Some(webgpu::GpuRenderPassColorAttachment {
                view: &surface_view,
                depth_slice: None,
                resolve_target: None,
                clear_value: Some(webgpu::GpuColor {
                    r: 0.0,
                    g: 0.0,
                    b: 0.0,
                    a: 1.0,
                }),
                load_op: webgpu::GpuLoadOp::Clear,
                store_op: webgpu::GpuStoreOp::Store,
            })],
            depth_stencil_attachment: None,
            occlusion_query_set: None,
            timestamp_writes: None,
            max_draw_count: None,
        });

        render_pass.set_pipeline(render_pipeline);

        // Top-left: Game Boy screen
        let vp = &viewports.game;
        render_pass.set_viewport(vp.x, vp.y, vp.width, vp.height, 0.0, 1.0);
        render_pass
            .set_bind_group(0, Some(gb_bind_group), None, None, None)
            .unwrap();
        render_pass.draw(3, None, None, None);

        // Top-right: ROM browser
        let vp = &viewports.rom_browser;
        render_pass.set_viewport(vp.x, vp.y, vp.width, vp.height, 0.0, 1.0);
        render_pass
            .set_bind_group(0, Some(debug_bind_group), None, None, None)
            .unwrap();
        render_pass.draw(3, None, None, None);

        // Bottom-left: RAM viewer
        let vp = &viewports.ram_viewer;
        render_pass.set_viewport(vp.x, vp.y, vp.width, vp.height, 0.0, 1.0);
        render_pass
            .set_bind_group(0, Some(mem_bind_group), None, None, None)
            .unwrap();
        render_pass.draw(3, None, None, None);

        // Right: Trace viewer
        let vp = &viewports.trace;
        render_pass.set_viewport(vp.x, vp.y, vp.width, vp.height, 0.0, 1.0);
        render_pass
            .set_bind_group(0, Some(trace_bind_group), None, None, None)
            .unwrap();
        render_pass.draw(3, None, None, None);

        render_pass.end();
    }

    device.queue().submit(&[&encoder.finish(None)]);
    graphics_context.present();
}

// ---------------------------------------------------------------------------
// Main emulator entry point
// ---------------------------------------------------------------------------

fn run_emulator() {
    // --- GPU + surface init ---
    let gpu = webgpu::get_gpu();
    let adapter = gpu.request_adapter(None).unwrap();
    let device = adapter.request_device(None).unwrap();

    let canvas = surface::Surface::new(surface::CreateDesc {
        height: None,
        width: None,
    });
    let graphics_context = graphics_context::Context::new();
    canvas.connect_graphics_context(&graphics_context);
    device.connect_graphics_context(&graphics_context);

    // --- Create persistent GPU resources (ONCE) ---

    // Sampler: nearest-neighbor for top panels (crisp pixel art)
    let nearest_sampler = device.create_sampler(Some(&webgpu::GpuSamplerDescriptor {
        address_mode_u: Some(webgpu::GpuAddressMode::ClampToEdge),
        address_mode_v: Some(webgpu::GpuAddressMode::ClampToEdge),
        address_mode_w: Some(webgpu::GpuAddressMode::ClampToEdge),
        mag_filter: Some(webgpu::GpuFilterMode::Nearest),
        min_filter: Some(webgpu::GpuFilterMode::Nearest),
        mipmap_filter: Some(webgpu::GpuMipmapFilterMode::Nearest),
        lod_min_clamp: None,
        lod_max_clamp: None,
        compare: None,
        max_anisotropy: None,
        label: Some("nearest_sampler".to_string()),
    }));

    // Sampler: linear-filtering for bottom panel (smooth text downscale)
    let linear_sampler = device.create_sampler(Some(&webgpu::GpuSamplerDescriptor {
        address_mode_u: Some(webgpu::GpuAddressMode::ClampToEdge),
        address_mode_v: Some(webgpu::GpuAddressMode::ClampToEdge),
        address_mode_w: Some(webgpu::GpuAddressMode::ClampToEdge),
        mag_filter: Some(webgpu::GpuFilterMode::Linear),
        min_filter: Some(webgpu::GpuFilterMode::Linear),
        mipmap_filter: Some(webgpu::GpuMipmapFilterMode::Linear),
        lod_min_clamp: None,
        lod_max_clamp: None,
        compare: None,
        max_anisotropy: None,
        label: Some("linear_sampler".to_string()),
    }));

    // Bind group layout — use Filtering sampler type for all panels.
    // A nearest sampler (non-filtering) is valid with a Filtering binding,
    // so we share a single layout. The bottom panel uses a linear sampler
    // for smooth 2x downscale, while top panels keep nearest for crisp pixels.
    let bind_group_layout =
        device.create_bind_group_layout(&webgpu::GpuBindGroupLayoutDescriptor {
            entries: vec![
                webgpu::GpuBindGroupLayoutEntry {
                    binding: 0,
                    visibility: webgpu::GpuShaderStage::fragment(),
                    buffer: None,
                    sampler: None,
                    texture: Some(webgpu::GpuTextureBindingLayout {
                        sample_type: Some(webgpu::GpuTextureSampleType::Float),
                        view_dimension: Some(webgpu::GpuTextureViewDimension::D2),
                        multisampled: Some(false),
                    }),
                    storage_texture: None,
                },
                webgpu::GpuBindGroupLayoutEntry {
                    binding: 1,
                    visibility: webgpu::GpuShaderStage::fragment(),
                    buffer: None,
                    sampler: Some(webgpu::GpuSamplerBindingLayout {
                        type_: Some(webgpu::GpuSamplerBindingType::Filtering),
                    }),
                    texture: None,
                    storage_texture: None,
                },
                webgpu::GpuBindGroupLayoutEntry {
                    binding: 2,
                    visibility: webgpu::GpuShaderStage::vertex()
                        | webgpu::GpuShaderStage::fragment(),
                    buffer: Some(webgpu::GpuBufferBindingLayout {
                        type_: Some(webgpu::GpuBufferBindingType::Uniform),
                        has_dynamic_offset: Some(false),
                        min_binding_size: Some(16),
                    }),
                    sampler: None,
                    texture: None,
                    storage_texture: None,
                },
            ],
            label: Some("bind_group_layout".to_string()),
        });

    // --- Game Boy panel resources (top-left, 160x144) ---
    let gb_texture = create_panel_texture(&device, "gb_framebuffer", GB_W, GB_H);
    let gb_texture_view = gb_texture.create_view(None);
    let gb_uniform = create_identity_uniform(&device, "gb_uniform");

    // --- Debug panel resources (top-right, 160x144) ---
    let debug_texture = create_panel_texture(&device, "debug_framebuffer", GB_W, GB_H);
    let debug_texture_view = debug_texture.create_view(None);
    let debug_uniform = create_identity_uniform(&device, "debug_uniform");

    // --- Memory panel resources (bottom, 640x192 texture → 320x96 viewport) ---
    let mem_texture = create_panel_texture(&device, "mem_framebuffer", MEM_TEX_W, MEM_TEX_H);
    let mem_texture_view = mem_texture.create_view(None);
    let mem_uniform = create_identity_uniform(&device, "mem_uniform");
    let mem_bind_group = create_panel_bind_group(
        &device,
        &bind_group_layout,
        &mem_texture_view,
        &linear_sampler,
        &mem_uniform,
        "mem_bind_group",
    );

    // --- Trace panel resources (right, 320x480 texture → 160x240 viewport) ---
    let trace_texture = create_panel_texture(&device, "trace_framebuffer", TRACE_TEX_W, TRACE_TEX_H);
    let trace_texture_view = trace_texture.create_view(None);
    let trace_uniform = create_identity_uniform(&device, "trace_uniform");

    // Shader + pipeline
    let shader_module = device.create_shader_module(&webgpu::GpuShaderModuleDescriptor {
        code: SHADER_CODE.to_string(),
        label: Some("gb_shader".to_string()),
        compilation_hints: None,
    });

    let pipeline_layout =
        device.create_pipeline_layout(&webgpu::GpuPipelineLayoutDescriptor {
            label: Some("gb_pipeline_layout".to_string()),
            bind_group_layouts: vec![Some(&bind_group_layout)],
        });

    // Bind groups — all use the same layout (Filtering type accepts nearest samplers)
    let gb_bind_group = create_panel_bind_group(
        &device,
        &bind_group_layout,
        &gb_texture_view,
        &nearest_sampler,
        &gb_uniform,
        "gb_bind_group",
    );
    let debug_bind_group = create_panel_bind_group(
        &device,
        &bind_group_layout,
        &debug_texture_view,
        &nearest_sampler,
        &debug_uniform,
        "debug_bind_group",
    );
    let trace_bind_group = create_panel_bind_group(
        &device,
        &bind_group_layout,
        &trace_texture_view,
        &linear_sampler,
        &trace_uniform,
        "trace_bind_group",
    );

    let surface_format = gpu.get_preferred_canvas_format();

    let render_pipeline =
        device.create_render_pipeline(webgpu::GpuRenderPipelineDescriptor {
            label: Some("gb_render_pipeline".to_string()),
            vertex: webgpu::GpuVertexState {
                module: &shader_module,
                entry_point: Some("vs_main".to_string()),
                buffers: None,
                constants: None,
            },
            fragment: Some(webgpu::GpuFragmentState {
                module: &shader_module,
                entry_point: Some("fs_main".to_string()),
                targets: vec![Some(webgpu::GpuColorTargetState {
                    format: surface_format,
                    blend: None,
                    write_mask: None,
                })],
                constants: None,
            }),
            primitive: Some(webgpu::GpuPrimitiveState {
                topology: Some(webgpu::GpuPrimitiveTopology::TriangleList),
                strip_index_format: None,
                front_face: None,
                cull_mode: None,
                unclipped_depth: None,
            }),
            depth_stencil: None,
            multisample: None,
            layout: webgpu::GpuLayoutMode::Specific(&pipeline_layout),
        });

    // --- Audio output ---
    let audio_output = ns_audio::AudioOutput::new(ns_audio::AudioConfig {
        sample_rate: 48000,
        channels: 2,
    });

    // --- Application state ---
    let mut app = AppState::new();
    let no_rom_fb = render_no_rom_placeholder();
    wasi_println("nightboy: initialized (press ESC to toggle focus)");

    // Viewport state
    let mut viewports = compute_viewports(800, 600);

    // Double-click detection state
    let mut frame_count: u32 = 0;
    let mut last_click_frame: u32 = 0;
    let mut last_click_entry: Option<usize> = None;

    // --- Subscribe to events ---
    let frame_pollable = canvas.subscribe_frame();
    let resize_pollable = canvas.subscribe_resize();
    let key_down_pollable = canvas.subscribe_key_down();
    let key_up_pollable = canvas.subscribe_key_up();
    let pointer_up_pollable = canvas.subscribe_pointer_up();
    let pointer_down_pollable = canvas.subscribe_pointer_down();
    let pointer_move_pollable = canvas.subscribe_pointer_move();

    let pollables = vec![
        &frame_pollable,        // 0
        &resize_pollable,       // 1
        &key_down_pollable,     // 2
        &key_up_pollable,       // 3
        &pointer_up_pollable,   // 4
        &pointer_down_pollable, // 5
        &pointer_move_pollable, // 6
    ];

    // --- Event loop ---
    loop {
        let events = wasi::io::poll::poll(&pollables);

        // Resize
        if events.contains(&1) {
            if let Some(e) = canvas.get_resize() {
                viewports = compute_viewports(e.width, e.height);
            }
        }

        // Key down
        if events.contains(&2) {
            if let Some(e) = canvas.get_key_down() {
                if let Some(key) = e.key {
                    handle_key_down(&mut app, key);
                }
            }
        }

        // Key up
        if events.contains(&3) {
            if let Some(e) = canvas.get_key_up() {
                if let Some(key) = e.key {
                    handle_key_up(&mut app, key);
                }
            }
        }

        // Pointer events
        if events.contains(&4) {
            let _ = canvas.get_pointer_up();
        }
        if events.contains(&5) {
            if let Some(e) = canvas.get_pointer_down() {
                if let Some((hit, rel_x, rel_y)) =
                    hit_test_panel(e.x, e.y, &viewports)
                {
                    let new_focus = match hit {
                        PanelHit::GameScreen => AppFocus::Emulator,
                        PanelHit::RomBrowser => AppFocus::RomBrowser,
                        PanelHit::RamViewer => AppFocus::RamViewer,
                        PanelHit::TraceViewer => AppFocus::TraceViewer,
                    };

                    if app.focus != new_focus {
                        app.focus = new_focus;
                        if matches!(
                            new_focus,
                            AppFocus::RomBrowser | AppFocus::RamViewer | AppFocus::TraceViewer
                        ) {
                            app.last_debug_focus = new_focus;
                        }
                        app.debug_panel.mark_dirty();
                        app.memory_panel.mark_dirty();
                        app.trace_panel.mark_dirty();
                    }

                    // Trace viewer tab click handling
                    if hit == PanelHit::TraceViewer {
                        let char_col = (rel_x * TRACE_CHAR_COLS as f64) as usize;
                        let char_row = (rel_y * TRACE_CHAR_ROWS as f64) as usize;
                        if char_row == 0 {
                            if let Some(mode) = app.trace_panel.viewer.hit_test_tab(char_col) {
                                app.trace_panel.viewer.set_filter(mode);
                                app.trace_panel.mark_dirty();
                            }
                        }
                    }

                    // RAM viewer tab click handling
                    if hit == PanelHit::RamViewer {
                        let char_col = (rel_x * MEM_CHAR_COLS as f64) as usize;
                        let char_row = (rel_y * MEM_CHAR_ROWS as f64) as usize;
                        if char_row == 0 {
                            if let Some(idx) = app.memory_panel.viewer.hit_test_tab(char_col) {
                                let bus = match &app.emulator {
                                    EmulatorState::Running { cpu } => Some(&cpu.bus),
                                    EmulatorState::NoRom => None,
                                };
                                app.memory_panel.viewer.handle_input(
                                    ViewerAction::SelectRegion(idx),
                                    bus,
                                );
                                app.memory_panel.mark_dirty();
                            }
                        }
                    }

                    // ROM browser click handling
                    if hit == PanelHit::RomBrowser {
                        let char_row = (rel_y * CHAR_ROWS as f64) as usize;
                        // Rows 2..=16 are entry rows
                        if char_row >= 2 && char_row < 2 + 15 {
                            let entry_idx =
                                app.rom_browser.scroll_offset() + (char_row - 2);
                            if entry_idx < app.rom_browser.entry_count() {
                                // Double-click detection
                                let is_double_click = last_click_entry
                                    == Some(entry_idx)
                                    && frame_count.wrapping_sub(last_click_frame) < 30;

                                if is_double_click {
                                    app.rom_browser
                                        .handle_input(BrowserAction::Open);
                                    last_click_entry = None;
                                } else {
                                    app.rom_browser.handle_input(
                                        BrowserAction::Select(entry_idx),
                                    );
                                    last_click_entry = Some(entry_idx);
                                }
                                last_click_frame = frame_count;
                                app.debug_panel.mark_dirty();
                            }
                        }
                    }
                }
            }
        }
        if events.contains(&6) {
            let _ = canvas.get_pointer_move();
        }

        // Check if a ROM was selected
        if let Some(rom_data) = app.rom_browser.selected_rom.take() {
            wasi_println(&format!(
                "nightboy: ROM loaded ({} bytes)",
                rom_data.len()
            ));
            let bus = GameBoyBus::new(rom_data);
            let cpu = cpu::GbCpu::new(bus);
            app.emulator = EmulatorState::Running { cpu };
            app.focus = AppFocus::Emulator;
            app.debug_panel.mark_dirty();
            app.memory_panel.mark_dirty();
            app.trace_panel.mark_dirty();
        }

        // Frame
        if events.contains(&0) {
            canvas.get_frame();
            frame_count = frame_count.wrapping_add(1);

            // Run emulator / get framebuffer
            let mut gb_fb = match &mut app.emulator {
                EmulatorState::Running { cpu } => {
                    run_frame(cpu);

                    // Print serial output (Blargg test ROMs)
                    if !cpu.bus.serial_output.is_empty() {
                        let msg: String =
                            cpu.bus.serial_output.drain(..).map(|b| b as char).collect();
                        wasi_print(&msg);
                    }

                    // Push audio samples to host
                    let samples = cpu.bus.apu.drain_samples();
                    if !samples.is_empty() {
                        audio_output.write(&samples);
                    }

                    cpu.bus.ppu.framebuffer_rgba8()
                }
                EmulatorState::NoRom => no_rom_fb.clone(),
            };

            // Auto-dirty: memory + trace panels refresh every frame while running
            if matches!(app.emulator, EmulatorState::Running { .. }) {
                app.memory_panel.mark_dirty();
                app.trace_panel.mark_dirty();
            }

            // Dim game screen when not focused
            if app.focus != AppFocus::Emulator {
                dim_framebuffer(&mut gb_fb);
            }

            // Get bus/trace references for panels
            let empty_log = trace_log::TraceLog::new();
            let (bus_ref, trace_ref, total_cycles) = match &app.emulator {
                EmulatorState::Running { cpu } => {
                    (Some(&cpu.bus), &cpu.bus.trace_log, cpu.total_cycles)
                }
                EmulatorState::NoRom => {
                    (None, &empty_log, 0)
                }
            };

            // Render debug panel (ROM browser)
            let debug_fb = app.debug_panel.render(app.focus, &app.rom_browser);
            let debug_fb = if app.focus != AppFocus::RomBrowser {
                let mut dimmed = debug_fb.to_vec();
                dim_framebuffer(&mut dimmed);
                dimmed
            } else {
                debug_fb.to_vec()
            };

            // Render memory panel
            let mem_fb = app.memory_panel.render(app.focus, bus_ref);
            let mem_fb = if app.focus != AppFocus::RamViewer {
                let mut dimmed = mem_fb.to_vec();
                dim_framebuffer(&mut dimmed);
                dimmed
            } else {
                mem_fb.to_vec()
            };

            // Render trace panel
            let trace_fb = app.trace_panel.render(app.focus, trace_ref, total_cycles);
            let trace_fb = if app.focus != AppFocus::TraceViewer {
                let mut dimmed = trace_fb.to_vec();
                dim_framebuffer(&mut dimmed);
                dimmed
            } else {
                trace_fb.to_vec()
            };

            // Upload and render all four panels
            upload_framebuffer(&device.queue(), &gb_texture, &gb_fb, GB_W, GB_H);
            upload_framebuffer(&device.queue(), &debug_texture, &debug_fb, GB_W, GB_H);
            upload_framebuffer(&device.queue(), &mem_texture, &mem_fb, MEM_TEX_W, MEM_TEX_H);
            upload_framebuffer(&device.queue(), &trace_texture, &trace_fb, TRACE_TEX_W, TRACE_TEX_H);

            render_frame_quad(
                &device,
                &graphics_context,
                &render_pipeline,
                &gb_bind_group,
                &debug_bind_group,
                &mem_bind_group,
                &trace_bind_group,
                &viewports,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Input routing
// ---------------------------------------------------------------------------

fn handle_key_down(app: &mut AppState, key: surface::Key) {
    // Escape toggles Emulator <-> last debug focus
    if key == surface::Key::Escape {
        app.focus = match app.focus {
            AppFocus::Emulator => app.last_debug_focus,
            _ => AppFocus::Emulator,
        };
        app.debug_panel.mark_dirty();
        app.memory_panel.mark_dirty();
        app.trace_panel.mark_dirty();
        return;
    }

    // Tab cycles between debug panels (only when focused on a debug panel)
    if key == surface::Key::Tab {
        match app.focus {
            AppFocus::RomBrowser => {
                app.focus = AppFocus::RamViewer;
                app.last_debug_focus = AppFocus::RamViewer;
            }
            AppFocus::RamViewer => {
                app.focus = AppFocus::TraceViewer;
                app.last_debug_focus = AppFocus::TraceViewer;
            }
            AppFocus::TraceViewer => {
                app.focus = AppFocus::RomBrowser;
                app.last_debug_focus = AppFocus::RomBrowser;
            }
            AppFocus::Emulator => {} // Tab does nothing while gaming
        }
        app.debug_panel.mark_dirty();
        app.memory_panel.mark_dirty();
        app.trace_panel.mark_dirty();
        return;
    }

    match app.focus {
        AppFocus::Emulator => {
            if let EmulatorState::Running { cpu } = &mut app.emulator {
                handle_key(&mut cpu.bus.joypad, key, true);
            }
        }
        AppFocus::RomBrowser => {
            let action = match key {
                surface::Key::ArrowUp => Some(BrowserAction::Up),
                surface::Key::ArrowDown => Some(BrowserAction::Down),
                surface::Key::Enter => Some(BrowserAction::Open),
                surface::Key::Backspace => Some(BrowserAction::Back),
                _ => None,
            };
            if let Some(action) = action {
                app.rom_browser.handle_input(action);
                app.debug_panel.mark_dirty();
            }
        }
        AppFocus::RamViewer => {
            let bus = match &app.emulator {
                EmulatorState::Running { cpu } => Some(&cpu.bus),
                EmulatorState::NoRom => None,
            };
            let action = match key {
                surface::Key::ArrowUp => Some(ViewerAction::ScrollUp),
                surface::Key::ArrowDown => Some(ViewerAction::ScrollDown),
                surface::Key::ArrowLeft => Some(ViewerAction::PrevRegion),
                surface::Key::ArrowRight => Some(ViewerAction::NextRegion),
                surface::Key::PageUp => Some(ViewerAction::PageUp),
                surface::Key::PageDown => Some(ViewerAction::PageDown),
                _ => None,
            };
            if let Some(action) = action {
                app.memory_panel.viewer.handle_input(action, bus);
                app.memory_panel.mark_dirty();
            }
        }
        AppFocus::TraceViewer => {
            use trace_viewer::ViewerAction as TraceAction;
            let action = match key {
                surface::Key::ArrowUp => Some(TraceAction::ScrollUp),
                surface::Key::ArrowDown => Some(TraceAction::ScrollDown),
                surface::Key::ArrowLeft => Some(TraceAction::PrevFilter),
                surface::Key::ArrowRight => Some(TraceAction::NextFilter),
                surface::Key::PageUp => Some(TraceAction::PageUp),
                surface::Key::PageDown => Some(TraceAction::PageDown),
                _ => None,
            };
            if let Some(action) = action {
                app.trace_panel.viewer.handle_input(action);
                app.trace_panel.mark_dirty();
            }
        }
    }
}

fn handle_key_up(app: &mut AppState, key: surface::Key) {
    if key == surface::Key::Escape || key == surface::Key::Tab {
        return;
    }
    if let AppFocus::Emulator = app.focus {
        if let EmulatorState::Running { cpu } = &mut app.emulator {
            handle_key(&mut cpu.bus.joypad, key, false);
        }
    }
}

// ---------------------------------------------------------------------------
// WASI I/O helpers
// ---------------------------------------------------------------------------

fn wasi_println(msg: &str) {
    let out = wasi::cli::stdout::get_stdout();
    out.blocking_write_and_flush(format!("{msg}\n").as_bytes())
        .unwrap();
}

fn wasi_print(msg: &str) {
    let out = wasi::cli::stdout::get_stdout();
    out.blocking_write_and_flush(msg.as_bytes()).unwrap();
}
