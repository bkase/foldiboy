#![allow(unsafe_code)]

mod bus;
mod joypad;
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

use bus::GameBoyBus;
use joypad::Button;

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const GB_W: u32 = 160;
const GB_H: u32 = 144;

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
// Transform computation (aspect-ratio preserving scale + offset)
// ---------------------------------------------------------------------------

fn compute_transform(win_w: u32, win_h: u32) -> [f32; 4] {
    const GB_ASPECT: f32 = GB_W as f32 / GB_H as f32;

    let win_aspect = win_w as f32 / win_h as f32;

    if win_aspect >= GB_ASPECT {
        // Window wider than GB: pillarbox (black bars on sides)
        let scale_x = win_aspect / GB_ASPECT;
        let offset_x = -(scale_x - 1.0) / 2.0;
        [scale_x, 1.0, offset_x, 0.0]
    } else {
        // Window taller than GB: letterbox (black bars top/bottom)
        let scale_y = GB_ASPECT / win_aspect;
        let offset_y = -(scale_y - 1.0) / 2.0;
        [1.0, scale_y, 0.0, offset_y]
    }
}

// ---------------------------------------------------------------------------
// ROM loading
// ---------------------------------------------------------------------------

fn load_rom() -> Vec<u8> {
    use wasi::filesystem::preopens;

    let dirs = preopens::get_directories();
    for (descriptor, path) in &dirs {
        wasi_println(&format!("nightboy: preopen '{}' available", path));
        if let Some(rom) = find_rom_in(descriptor) {
            return rom;
        }
    }
    panic!("nightboy: no .gb ROM found in any preopened directory");
}

/// Recursively search a directory descriptor for the first `.gb` file.
fn find_rom_in(dir: &wasi::filesystem::types::Descriptor) -> Option<Vec<u8>> {
    use wasi::filesystem::types as fs;

    let entries = dir.read_directory().ok()?;
    let mut subdirs = Vec::new();

    loop {
        match entries.read_directory_entry() {
            Ok(Some(entry)) => {
                let name = &entry.name;
                match entry.type_ {
                    fs::DescriptorType::RegularFile
                        if name.ends_with(".gb") || name.ends_with(".gbc") =>
                    {
                        wasi_println(&format!("nightboy: loading ROM '{}'", name));
                        let child = dir
                            .open_at(
                                fs::PathFlags::SYMLINK_FOLLOW,
                                name,
                                fs::OpenFlags::empty(),
                                fs::DescriptorFlags::READ,
                            )
                            .ok()?;
                        let stat = child.stat().ok()?;
                        let (data, _eof) = child.read(stat.size, 0).ok()?;
                        return Some(data);
                    }
                    fs::DescriptorType::Directory => {
                        subdirs.push(name.clone());
                    }
                    _ => {}
                }
            }
            Ok(None) => break,
            Err(_) => break,
        }
    }

    // Recurse into subdirectories
    for subdir_name in subdirs {
        let child_dir = dir
            .open_at(
                fs::PathFlags::SYMLINK_FOLLOW,
                &subdir_name,
                fs::OpenFlags::DIRECTORY,
                fs::DescriptorFlags::READ,
            )
            .ok();
        if let Some(ref child) = child_dir {
            if let Some(rom) = find_rom_in(child) {
                return Some(rom);
            }
        }
    }

    None
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

fn render_frame(
    device: &webgpu::GpuDevice,
    graphics_context: &graphics_context::Context,
    render_pipeline: &webgpu::GpuRenderPipeline,
    bind_group: &webgpu::GpuBindGroup,
) {
    let graphics_buffer = graphics_context.get_current_buffer();
    let surface_texture = webgpu::GpuTexture::from_graphics_buffer(graphics_buffer);
    let surface_view = surface_texture.create_view(None);
    let encoder = device.create_command_encoder(None);

    {
        let render_pass = encoder.begin_render_pass(&webgpu::GpuRenderPassDescriptor {
            label: Some("gb_render_pass".to_string()),
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
        render_pass
            .set_bind_group(0, Some(bind_group), None, None, None)
            .unwrap();
        render_pass.draw(3, None, None, None);
        render_pass.end();
    }

    device.queue().submit(&[&encoder.finish(None)]);
    graphics_context.present();
}

fn handle_resize(
    queue: &webgpu::GpuQueue,
    uniform_buffer: &webgpu::GpuBuffer,
    win_w: u32,
    win_h: u32,
) {
    let transform = compute_transform(win_w, win_h);
    let bytes: Vec<u8> = transform.iter().flat_map(|f| f.to_le_bytes()).collect();
    queue
        .write_buffer_with_copy(uniform_buffer, 0, &bytes, None, None)
        .unwrap();
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

    // Framebuffer texture: 160x144 RGBA8
    let fb_texture = device.create_texture(&webgpu::GpuTextureDescriptor {
        size: webgpu::GpuExtent3D {
            width: GB_W,
            height: Some(GB_H),
            depth_or_array_layers: Some(1),
        },
        mip_level_count: Some(1),
        sample_count: Some(1),
        dimension: Some(webgpu::GpuTextureDimension::D2),
        format: webgpu::GpuTextureFormat::Rgba8unormSrgb,
        usage: webgpu::GpuTextureUsage::texture_binding()
            | webgpu::GpuTextureUsage::copy_dst(),
        view_formats: None,
        label: Some("gb_framebuffer".to_string()),
    });
    let fb_texture_view = fb_texture.create_view(None);

    // Sampler: nearest-neighbor, clamp-to-edge
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

    // Uniform buffer: 16 bytes for transform vec4<f32>
    let uniform_buffer = device.create_buffer(&webgpu::GpuBufferDescriptor {
        size: 16,
        usage: webgpu::GpuBufferUsage::uniform() | webgpu::GpuBufferUsage::copy_dst(),
        mapped_at_creation: None,
        label: Some("gb_uniform".to_string()),
    });

    // Write initial transform (assume 800x600 default)
    handle_resize(&device.queue(), &uniform_buffer, 800, 600);

    // Bind group layout: texture@0, sampler@1, uniform@2
    let bind_group_layout =
        device.create_bind_group_layout(&webgpu::GpuBindGroupLayoutDescriptor {
            entries: vec![
                // @binding(0): texture (fragment only)
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
                // @binding(1): sampler (fragment only)
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
                // @binding(2): uniform buffer (vertex + fragment)
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
            label: Some("gb_bind_group_layout".to_string()),
        });

    // Bind group
    let bind_group = device.create_bind_group(&webgpu::GpuBindGroupDescriptor {
        layout: &bind_group_layout,
        entries: vec![
            webgpu::GpuBindGroupEntry {
                binding: 0,
                resource: webgpu::GpuBindingResource::GpuTextureView(&fb_texture_view),
            },
            webgpu::GpuBindGroupEntry {
                binding: 1,
                resource: webgpu::GpuBindingResource::GpuSampler(&sampler),
            },
            webgpu::GpuBindGroupEntry {
                binding: 2,
                resource: webgpu::GpuBindingResource::GpuBufferBinding(
                    webgpu::GpuBufferBinding {
                        buffer: &uniform_buffer,
                        offset: None,
                        size: None,
                    },
                ),
            },
        ],
        label: Some("gb_bind_group".to_string()),
    });

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

    // --- Emulator init ---
    let rom = load_rom();
    let bus = GameBoyBus::new(rom);
    let mut cpu = cpu::GbCpu::new(bus);
    wasi_println("nightboy: emulator initialized");

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
            let event = canvas.get_resize();
            if let Some(e) = event {
                handle_resize(&device.queue(), &uniform_buffer, e.width, e.height);
            }
        }

        // Key events → joypad
        if events.contains(&2) {
            if let Some(e) = canvas.get_key_down() {
                if let Some(key) = e.key {
                    handle_key(&mut cpu.bus.joypad, key, true);
                }
            }
        }
        if events.contains(&3) {
            if let Some(e) = canvas.get_key_up() {
                if let Some(key) = e.key {
                    handle_key(&mut cpu.bus.joypad, key, false);
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

        // Frame
        if events.contains(&0) {
            canvas.get_frame();

            // Run emulator until frame complete
            run_frame(&mut cpu);

            // Print any serial output (Blargg test ROMs)
            if !cpu.bus.serial_output.is_empty() {
                let msg: String = cpu.bus.serial_output.drain(..).map(|b| b as char).collect();
                wasi_print(&msg);
            }

            // Upload PPU framebuffer and render
            let fb = cpu.bus.ppu.framebuffer_rgba8();
            upload_framebuffer(&device.queue(), &fb_texture, &fb);
            render_frame(&device, &graphics_context, &render_pipeline, &bind_group);
        }
    }
}

fn wasi_println(msg: &str) {
    let out = wasi::cli::stdout::get_stdout();
    out.blocking_write_and_flush(format!("{msg}\n").as_bytes())
        .unwrap();
}

fn wasi_print(msg: &str) {
    let out = wasi::cli::stdout::get_stdout();
    out.blocking_write_and_flush(msg.as_bytes()).unwrap();
}
