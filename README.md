# Nightboy

A Game Boy (DMG) emulator built as a [WASM Component](https://component-model.bytecodealliance.org/), designed for the [Nightstream](../nightstream/) zkVM. The emulator runs as a guest module inside a wasmtime host, communicating through WIT interfaces for graphics, audio, input, and filesystem access.

## Architecture

```
Guest (WASM Component)                    Host (native, wasmtime)
┌──────────────────────────────────────┐  ┌───────────────────────────┐
│  CPU (SM83, all 512 opcodes)         │  │  WebGPU surface + window  │
│  PPU (scanline renderer, 4 modes)    │  │  cpal audio backend       │
│  APU (4 channels, 48kHz stereo)      │  │  Input event polling      │
│  Timer (falling-edge model)          │  │  WASI filesystem (ROMs)   │
│  Bus (MBC1/2/3/5, OAM DMA, I/O)     │  │                           │
│  Joypad (active-low, 8 buttons)      │  │                           │
├──────────────────────────────────────┤  ├───────────────────────────┤
│  WIT interfaces:                     │  │  Implements:              │
│    import wasi:webgpu                │◄─┤    wasi-gfx (WebGPU)     │
│    import wasi:surface               │  │    nightstream:audio      │
│    import nightstream:audio          │  │    wasi:filesystem        │
│    import wasi:filesystem            │  │    wasi:cli               │
│    export wasi:cli/run               │  │                           │
└──────────────────────────────────────┘  └───────────────────────────┘
```

The guest produces a 160x144 RGBA8 framebuffer and interleaved i16 stereo audio samples each frame. The host consumes these via WebGPU texture uploads and a lock-free ring buffer audio pipeline.

## Repository Layout

```
nightboy/
├── lib/                        Guest WASM component (Rust workspace)
│   ├── crates/
│   │   ├── cpu/                SM83 CPU: decode, execute, ALU, registers
│   │   │   ├── src/
│   │   │   │   ├── cpu.rs          GbCpu struct, step(), interrupt dispatch
│   │   │   │   ├── execute.rs      Instruction execution (all 512 opcodes)
│   │   │   │   ├── alu.rs          Pure ALU: alu_binary, alu_shift, alu_daa, ...
│   │   │   │   ├── registers.rs    Register file (AF, BC, DE, HL, SP, PC)
│   │   │   │   └── instruction/    GbInstruction enum, block-based decoder
│   │   │   └── tests/
│   │   │       ├── blargg.rs       11 Blargg cpu_instrs ROM tests
│   │   │       ├── dmg_sound.rs    9 Blargg dmg_sound ROM tests
│   │   │       ├── dmg_sound_diag.rs  3 APU diagnostic tests
│   │   │       └── samesuite.rs    SameSuite ei_delay_halt test
│   │   ├── memory/             Bus trait + test harnesses
│   │   │   └── src/
│   │   │       ├── bus.rs          Bus trait (read/write u8/u16)
│   │   │       └── test_bus.rs     GameBoyTestBus (64KB flat + PPU + APU stubs)
│   │   ├── ppu/                Pixel Processing Unit
│   │   │   └── src/
│   │   │       ├── lib.rs          Ppu struct, 4-mode state machine, register I/O
│   │   │       ├── registers.rs    Lcdc, Stat, Palette, Colour types
│   │   │       ├── vram.rs         VideoRam: tile data + tile maps
│   │   │       ├── oam.rs          SpriteAttributeTable, Sprite decode
│   │   │       └── scanline.rs     BG, window, sprite scanline renderers
│   │   ├── apu/                Audio Processing Unit
│   │   │   └── src/
│   │   │       ├── lib.rs          Apu struct, frame sequencer, register I/O
│   │   │       ├── pulse.rs        Pulse channels (CH1, CH2) — duty + frequency timer
│   │   │       ├── wave.rs         Wave channel (CH3) — 32-sample wavetable
│   │   │       ├── noise.rs        Noise channel (CH4) — LFSR 15/7-bit
│   │   │       ├── sweep.rs        Frequency sweep (CH1 only)
│   │   │       ├── envelope.rs     Volume envelope (CH1, CH2, CH4)
│   │   │       ├── length.rs       Length counter (all channels)
│   │   │       ├── mixer.rs        NR50/NR51 routing + Bresenham downsampler + HPF
│   │   │       └── registers.rs    Register addresses, read masks
│   │   └── render/             WASM Component entry point + integration
│   │       └── src/
│   │           ├── lib.rs          run_emulator(), frame loop, WebGPU pipeline
│   │           ├── bus.rs          GameBoyBus (full memory map, MBC, OAM DMA, I/O)
│   │           ├── timer.rs        Timer (falling-edge, shared internal counter)
│   │           ├── joypad.rs       Joypad (active-low, button mapping)
│   │           ├── app_state.rs    AppFocus, DebugTab, EmulatorState, AppState
│   │           ├── debug_panel.rs  Debug panel renderer (dirty-flag caching)
│   │           ├── rom_browser.rs  WASI filesystem ROM browser (TUI)
│   │           └── font.rs         8x8 bitmap font (96 ASCII glyphs)
│   ├── wit/                    WIT interface definitions
│   │   ├── gameboy.wit             nightstream:nightboy/app world
│   │   └── deps/
│   │       └── nightstream-audio/
│   │           └── audio.wit       nightstream:audio@0.0.1 (push-based audio)
│   └── build.sh                wit-deps → cargo build → wasm-tools component new
├── host/
│   └── desktop/                wasmtime host application
│       ├── src/
│       │   ├── main.rs             wasmtime setup, wasi-gfx, event loop
│       │   └── audio.rs           cpal + ringbuf audio backend
│       └── build.sh            Builds guest, then cargo run --release
└── README.md
```

## Building & Running

**Prerequisites:**
- Rust nightly with `wasm32-wasip2` target
- `wasm-tools` CLI
- `wit-deps` CLI
- `libasound2-dev` (Linux, for cpal audio)

**Build & run:**

```bash
cd host/desktop && ./build.sh
```

This builds the guest WASM component, then compiles and runs the host. The host opens a window with two panels: the Game Boy screen (left) and a debug/ROM browser panel (right).

**Run tests:**

```bash
cd lib && cargo test
```

**Controls:**

| Key | Action |
|-----|--------|
| Arrow keys | D-pad |
| X / J | A button |
| Z / K | B button |
| Enter | Start |
| Right Shift | Select |
| Escape | Toggle focus (emulator / debug panel) |
| Arrow keys (debug panel) | Navigate ROM browser |
| Enter (debug panel) | Open directory / load ROM |
| Backspace (debug panel) | Go up one directory |

## Emulator Subsystems

### CPU

Sharp SM83 (often mislabeled as "Z80-like"). All 512 opcodes implemented: 256 main + 256 CB-prefix.

- **Pure ALU**: `alu_binary()`, `alu_shift()`, `alu_daa()`, etc. — functions return `(result, flags)` without mutation
- **Atomic instruction execution**: each instruction completes in one `step()` call (deliberate — no sub-instruction timing)
- **Interrupts**: 5 sources (VBlank, STAT, Timer, Serial, Joypad), IME + IE + IF dispatch
- **HALT bug**: when IME=0 with pending interrupts, the byte after HALT is read twice
- **EI delay**: IME is set after the instruction following EI, not immediately

See `crates/cpu/src/cpu.rs` for the full design doc.

### PPU

4-mode dot-based state machine: OAM Search (mode 2) -> Data Transfer (mode 3) -> HBlank (mode 0) -> VBlank (mode 1).

- **Scanline renderer**: BG layer, window layer, sprite layer (10-sprite-per-line limit)
- **Sprites**: 8x8 and 8x16 modes, X/Y flip, behind-BG priority, OAM sorting by X coordinate
- **Fixed timing**: 80/172/204 dots for modes 2/3/0 — no SCX or sprite-dependent penalties (deliberate ZK simplification)
- **STAT IRQ blocking**: edge-triggered internal signal line — only LOW-to-HIGH transitions fire the interrupt, preventing duplicate STAT IRQs
- **LCD on/off**: turning LCD off freezes LYC flag and STAT signal; turning on starts in mode 0 then transitions to mode 2

See `crates/ppu/src/lib.rs` for the full design doc.

### APU

4 channels: 2 pulse (CH1 with sweep, CH2 without), 1 wave (CH3), 1 noise (CH4).

- **Frame sequencer**: 512 Hz (8192 T-cycle period), 8-step dispatch for length, sweep, and envelope
- **Self-contained counter**: NOT synced to DIV register (deliberate ZK simplification)
- **Mixer**: NR50 master volume (0-7 per side), NR51 per-channel L/R routing
- **Downsampler**: Bresenham algorithm, 4,194,304 Hz -> 48,000 Hz
- **High-pass filter**: single-pole IIR, alpha=0.999 (~7.6 Hz cutoff at 48 kHz) — removes DC offset
- **Output**: interleaved signed 16-bit PCM stereo `[L, R, L, R, ...]`
- **Test accuracy**: Blargg dmg_sound 01-08 + 11 pass; 09, 10, 12 ignored (simplified wave RAM access)

See `crates/apu/src/lib.rs` for the full design doc.

### Timer

Falling-edge model with a shared 16-bit internal counter.

- **DIV** ($FF04): bits 8-15 of the internal counter; writing resets the full 16-bit counter to 0
- **TIMA** ($FF05): timer counter, incremented when the TAC-selected bit of the internal counter falls
- **TMA** ($FF06): timer modulo, loaded into TIMA on overflow
- **TAC** ($FF07): timer control — enable bit + clock select (4096/262144/65536/16384 Hz)
- **AND gate edge detection**: the timer increments TIMA when `(old_bit AND enable) = 1` transitions to `(new_bit AND enable) = 0`

See `crates/render/src/timer.rs` for the full design doc.

### Memory Banking (MBC)

Auto-detected from ROM header byte $0147:

| MBC | ROM | RAM | Notes |
|-----|-----|-----|-------|
| MBC1 | up to 2 MB | up to 32 KB | MBC1M multicart auto-detection |
| MBC2 | up to 256 KB | built-in 512x4-bit | Upper nibble reads as $F |
| MBC3 | up to 4 MB (8 MB MBC30) | up to 64 KB (MBC30) | RTC stubbed to 0 |
| MBC5 | up to 8 MB | up to 128 KB | 9-bit ROM bank, no zero-adjust |

See `crates/render/src/bus.rs` for implementation details.

### Joypad

Active-low button matrix with direction/action select lines. Directly maps keyboard events to the 8 Game Boy buttons via `set_button()`.

## Audio System (Host Implementor Guide)

This section is for developers building new host frontends that need to receive and play audio from the guest.

### WIT Interface

```wit
package nightstream:audio@0.0.1;

interface audio {
    record audio-config {
        sample-rate: u32,   // always 48000
        channels: u32,      // always 2 (stereo)
    }

    resource audio-output {
        constructor(config: audio-config);
        write: func(samples: list<s16>) -> u32;
        available: func() -> u32;
    }
}
```

### What the Guest Sends

- **Format**: interleaved signed 16-bit PCM, stereo (L, R, L, R, ...)
- **Sample rate**: 48,000 Hz
- **Channels**: 2 (stereo)
- **Volume per frame**: ~804 stereo frames (~1,608 samples) per Game Boy frame (70,224 T-cycles / 87.38 T-cycles per output sample)
- **DC offset**: already removed by the guest's high-pass filter
- **APU off**: silence (all zeros) when NR52 bit 7 is cleared

### Implementing a Host

1. **Create a ring buffer** — ~100 ms capacity is recommended (9,600 samples at 48 kHz stereo = 4,800 stereo frames)
2. **On `constructor(config)`** — open the platform audio device at the requested sample rate and channel count
3. **On `write(samples)`** — push samples into the ring buffer; return the number of samples actually written (not stereo frames)
4. **On `available()`** — return the ring buffer vacancy in samples
5. **Audio callback** — pull from the ring buffer into the platform audio callback; fill any remainder with silence (zeros)

**Frame timing**: the Game Boy produces samples at 4,194,304 / 87.38 ≈ 48,000.46 Hz. At 60 fps this is ~800.007 stereo frames per Game Boy frame vs. exactly 800 consumed. The excess is ~5 samples/frame. `write()` should silently drop overflow — the ring buffer absorbs the drift with imperceptible audio loss.

See `host/desktop/src/audio.rs` for a reference implementation using cpal + ringbuf.

## Design Decisions (ZK Context)

Nightboy is built to eventually run inside the Nightstream zkVM, where every instruction must be provable. Several deliberate simplifications keep the emulator ZK-friendly:

| Simplification | Rationale |
|----------------|-----------|
| **Audio not proven** | APU registers are pure I/O — audio output has no effect on game state that needs proving |
| **Fixed PPU timing** | No SCX scroll or sprite-count-dependent mode 3 duration — avoids variable-length constraint rows |
| **Atomic CPU instructions** | No sub-instruction bus modeling — each `step()` is one constraint row |
| **Self-contained frame sequencer** | APU counter not coupled to DIV register — avoids cross-subsystem dependencies in the trace |
| **No wave RAM access restrictions** | Simplified read/write during CH3 playback — avoids per-dot mode tracking |
| **RTC stubbed to 0** | Real-time clock is fundamentally unprovable without an external time oracle |

These trade-offs cause a small number of Mooneye/Blargg tests to fail by design (see [Test Coverage](#test-coverage) below), but do not affect the correctness of game logic for the vast majority of titles.

## Nightstream Integration

The provable version of the SM83 CPU lives in the Nightstream repo at `nightstream/crates/neo-memory/src/sm83/`. It re-implements the same CPU semantics using Nightstream's trait protocol:

- **`VmCpu`** — trace-producing CPU that records every operation
- **`Twist`** — memory abstraction that logs every load/store for proving
- **`Shout`** — lookup tables for ALU operations (proven via lookup arguments, not in-circuit arithmetic)

The reference emulator (`nightboy/lib/crates/cpu/`) is the source of truth for SM83 semantics. The Nightstream integration is cross-validated: every opcode is tested against all 65,536 input pairs for bit-identical ALU behavior, and full programs are compared step-by-step (registers, memory, PC) between both implementations.

```
nightboy (reference emulator)            nightstream/sm83 (provable CPU)
┌──────────────────────────────┐         ┌──────────────────────────────┐
│  GbCpu<Bus>                  │ cross-  │  Sm83Cpu: VmCpu<u16, u16>   │
│  alu_binary/shift/daa        │ valid.  │  compute_op() via Shout     │
│  Bus::read/write             │ ──────> │  Twist::load/store          │
│  All 512 opcodes             │         │  All 512 opcodes            │
└──────────────────────────────┘         └──────────┬───────────────────┘
                                                    │ trace_program()
                                                    ▼
                                         ┌──────────────────────────────┐
                                         │  VmTrace → Sm83ExecTable    │
                                         │  → Event tables             │
                                         │  → Witness → CCS            │
                                         └──────────────────────────────┘
```

## Test Coverage

291 tests total:

| Suite | Count | Description |
|-------|------:|-------------|
| APU unit tests | 75 | Channel behavior, frame sequencer, mixer, registers |
| CPU unit tests | 101 | Opcode execution, flags, interrupts, HALT, EI delay |
| Blargg cpu_instrs | 14 | 11 test ROMs (some ROMs test multiple sub-tests) |
| Blargg dmg_sound | 9 | Tests 01-08, 11 (09, 10, 12 ignored — wave RAM) |
| APU diagnostics | 3 | Channel trigger/length/envelope edge cases |
| SameSuite | 1 | `ei_delay_halt` (EI+HALT interrupt priority) |
| Memory | 3 | Bus trait, test bus behavior |
| PPU | 65 | Mode transitions, STAT IRQ, scanline rendering, OAM |
| Render | 20 | Font, debug panel, ROM browser, app state |

### Known Failing by Design

**CPU / Bus:**
- All `boot_*` tests — no boot ROM, execution starts at PC=$0100
- 14 sub-instruction timing tests — atomic instruction execution
- 3 OAM DMA timing tests — instantaneous DMA transfer
- `halt_ime0_nointr_timing` — requires PPU-dependent halt wake timing

**PPU:**
- 7 Mooneye dot-precise timing tests — fixed mode 3 duration (no SCX/sprite penalties)

**Timer:**
- `rapid_toggle` — sub-instruction counter offset (8T boundary shift)
- `tima_write_reloading` — writing TIMA during 4-cycle reload delay
- `tma_write_reloading` — writing TMA during 4-cycle reload delay

**APU:**
- Blargg dmg_sound 09, 10, 12 — simplified wave RAM access timing

**Mooneye tests passing:** `ie_push`, `oam_dma/reg_read`, `oam_dma/sources-GS`, `stat_irq_blocking`, `stat_lyc_onoff`, `vblank_stat_intr-GS`, `timer/div_write`, `timer/tim00`, `timer/tim01`, `timer/tim10`, `timer/tim11`, `timer/tima_reload`, `ei_sequence`
