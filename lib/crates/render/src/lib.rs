#![allow(unsafe_code)]

mod app_state;
mod bus;
mod debug_panel;
mod font;
mod joypad;
mod rom_browser;
mod timer;

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

use wasi::{graphics_context::graphics_context, surface::surface, webgpu::webgpu};

use app_state::{AppFocus, AppState, DebugTab, EmulatorState};
use bus::GameBoyBus;
use debug_panel::render_no_rom_placeholder;
use joypad::Button;
use rom_browser::BrowserAction;

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const GB_W: u32 = 160;
const GB_H: u32 = 144;

/// Logical canvas: two 160x144 panels side by side.
const CANVAS_W: u32 = GB_W * 2; // 320
const CANVAS_H: u32 = GB_H; // 144
const CANVAS_ASPECT: f32 = CANVAS_W as f32 / CANVAS_H as f32; // 20:9

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
// Viewport computation (aspect-ratio preserving dual panels)
// ---------------------------------------------------------------------------

/// A viewport rectangle in pixel coordinates.
struct Viewport {
    x: f32,
    y: f32,
    width: f32,
    height: f32,
}

/// Compute two side-by-side viewports that fit a 320x144 logical canvas
/// into the window while preserving aspect ratio.
fn compute_dual_viewports(win_w: u32, win_h: u32) -> (Viewport, Viewport) {
    let win_w = win_w.max(1) as f32;
    let win_h = win_h.max(1) as f32;
    let win_aspect = win_w / win_h;

    let (canvas_px_w, canvas_px_h) = if win_aspect >= CANVAS_ASPECT {
        // Window is wider than canvas: fit to height, pillarbox
        (win_h * CANVAS_ASPECT, win_h)
    } else {
        // Window is taller than canvas: fit to width, letterbox
        (win_w, win_w / CANVAS_ASPECT)
    };

    let panel_w = canvas_px_w / 2.0;
    let panel_h = canvas_px_h;
    let offset_x = (win_w - canvas_px_w) / 2.0;
    let offset_y = (win_h - canvas_px_h) / 2.0;

    let left = Viewport {
        x: offset_x,
        y: offset_y,
        width: panel_w,
        height: panel_h,
    };
    let right = Viewport {
        x: offset_x + panel_w,
        y: offset_y,
        width: panel_w,
        height: panel_h,
    };

    (left, right)
}

// ---------------------------------------------------------------------------
// Emulation helpers
// ---------------------------------------------------------------------------

/// Run the emulator until the PPU signals a frame is complete.
fn run_frame(cpu: &mut cpu::GbCpu<GameBoyBus>) {
    loop {
        let m_cycles = cpu.step();

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

fn upload_framebuffer(queue: &webgpu::GpuQueue, texture: &webgpu::GpuTexture, pixels: &[u8]) {
    debug_assert_eq!(pixels.len(), (GB_W * GB_H * 4) as usize);

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
            bytes_per_row: Some(GB_W * 4),
            rows_per_image: Some(GB_H),
        },
        webgpu::GpuExtent3D {
            width: GB_W,
            height: Some(GB_H),
            depth_or_array_layers: Some(1),
        },
    );
}

/// Create a 160x144 RGBA8 texture.
fn create_panel_texture(device: &webgpu::GpuDevice, label: &str) -> webgpu::GpuTexture {
    device.create_texture(&webgpu::GpuTextureDescriptor {
        size: webgpu::GpuExtent3D {
            width: GB_W,
            height: Some(GB_H),
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

/// Render both panels with dual viewports in a single render pass.
fn render_frame_dual(
    device: &webgpu::GpuDevice,
    graphics_context: &graphics_context::Context,
    render_pipeline: &webgpu::GpuRenderPipeline,
    gb_bind_group: &webgpu::GpuBindGroup,
    debug_bind_group: &webgpu::GpuBindGroup,
    left_vp: &Viewport,
    right_vp: &Viewport,
) {
    let graphics_buffer = graphics_context.get_current_buffer();
    let surface_texture = webgpu::GpuTexture::from_graphics_buffer(graphics_buffer);
    let surface_view = surface_texture.create_view(None);
    let encoder = device.create_command_encoder(None);

    {
        let render_pass = encoder.begin_render_pass(&webgpu::GpuRenderPassDescriptor {
            label: Some("dual_render_pass".to_string()),
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

        // Left panel: Game Boy screen
        render_pass.set_viewport(
            left_vp.x, left_vp.y, left_vp.width, left_vp.height, 0.0, 1.0,
        );
        render_pass
            .set_bind_group(0, Some(gb_bind_group), None, None, None)
            .unwrap();
        render_pass.draw(3, None, None, None);

        // Right panel: Debug panel
        render_pass.set_viewport(
            right_vp.x, right_vp.y, right_vp.width, right_vp.height, 0.0, 1.0,
        );
        render_pass
            .set_bind_group(0, Some(debug_bind_group), None, None, None)
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

    // Sampler: nearest-neighbor, clamp-to-edge (shared by both panels)
    let sampler = device.create_sampler(Some(&webgpu::GpuSamplerDescriptor {
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
        label: Some("gb_sampler".to_string()),
    }));

    // Bind group layout (shared)
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
                        type_: Some(webgpu::GpuSamplerBindingType::NonFiltering),
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
            label: Some("panel_bind_group_layout".to_string()),
        });

    // --- Game Boy panel resources ---
    let gb_texture = create_panel_texture(&device, "gb_framebuffer");
    let gb_texture_view = gb_texture.create_view(None);
    let gb_uniform = create_identity_uniform(&device, "gb_uniform");
    let gb_bind_group = create_panel_bind_group(
        &device,
        &bind_group_layout,
        &gb_texture_view,
        &sampler,
        &gb_uniform,
        "gb_bind_group",
    );

    // --- Debug panel resources ---
    let debug_texture = create_panel_texture(&device, "debug_framebuffer");
    let debug_texture_view = debug_texture.create_view(None);
    let debug_uniform = create_identity_uniform(&device, "debug_uniform");
    let debug_bind_group = create_panel_bind_group(
        &device,
        &bind_group_layout,
        &debug_texture_view,
        &sampler,
        &debug_uniform,
        "debug_bind_group",
    );

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

    // --- Application state ---
    let mut app = AppState::new();
    let no_rom_fb = render_no_rom_placeholder();
    wasi_println("nightboy: initialized (press ESC to toggle focus)");

    // Viewport state
    let mut viewports = compute_dual_viewports(800, 600);

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
                viewports = compute_dual_viewports(e.width, e.height);
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

        // Pointer events (consume, no-op for now)
        if events.contains(&4) {
            let _ = canvas.get_pointer_up();
        }
        if events.contains(&5) {
            let _ = canvas.get_pointer_down();
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
        }

        // Frame
        if events.contains(&0) {
            canvas.get_frame();

            // Run emulator / get framebuffer
            let gb_fb = match &mut app.emulator {
                EmulatorState::Running { cpu } => {
                    run_frame(cpu);

                    // Print serial output (Blargg test ROMs)
                    if !cpu.bus.serial_output.is_empty() {
                        let msg: String =
                            cpu.bus.serial_output.drain(..).map(|b| b as char).collect();
                        wasi_print(&msg);
                    }

                    cpu.bus.ppu.framebuffer_rgba8()
                }
                EmulatorState::NoRom => no_rom_fb.clone(),
            };

            // Render debug panel
            let debug_fb =
                app.debug_panel
                    .render(app.focus, app.active_tab, &app.rom_browser);

            // Upload and render both panels
            upload_framebuffer(&device.queue(), &gb_texture, &gb_fb);
            upload_framebuffer(&device.queue(), &debug_texture, debug_fb);

            render_frame_dual(
                &device,
                &graphics_context,
                &render_pipeline,
                &gb_bind_group,
                &debug_bind_group,
                &viewports.0,
                &viewports.1,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Input routing
// ---------------------------------------------------------------------------

fn handle_key_down(app: &mut AppState, key: surface::Key) {
    // Escape toggles focus
    if key == surface::Key::Escape {
        app.focus = match app.focus {
            AppFocus::Emulator => AppFocus::DebugPanel,
            AppFocus::DebugPanel => AppFocus::Emulator,
        };
        app.debug_panel.mark_dirty();
        return;
    }

    // Tab cycles debug tabs (only one for now)
    if key == surface::Key::Tab {
        app.active_tab = match app.active_tab {
            DebugTab::RomBrowser => DebugTab::RomBrowser, // only one tab
        };
        app.debug_panel.mark_dirty();
        return;
    }

    match app.focus {
        AppFocus::Emulator => {
            if let EmulatorState::Running { cpu } = &mut app.emulator {
                handle_key(&mut cpu.bus.joypad, key, true);
            }
        }
        AppFocus::DebugPanel => {
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
