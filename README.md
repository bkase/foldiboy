# Foldiboy

A Game Boy (DMG) emulator built as a [WASM Component](https://component-model.bytecodealliance.org/), designed for the [Nightstream](https://github.com/LFDT-Nightstream/Nightstream) zkVM. The emulator runs as a guest module inside a wasmtime host, communicating through WIT interfaces for graphics, audio, input, and filesystem access.

## Why another Gameboy emulator?

There are multiple requirements that have driven us to create a new Gameboy emulator:
1. **Efficient provability**: Foldiboy is fully ZK-provable. Doing this efficiently requires:
    1. **Filtered traces**: An easy way to get a trace of all read, write, opcodes that need to be proven by the proof system (most emulators have no way to get traces, let alone stream them in over time)
    2. **Fine-tuned provability**: Filter out from traces any opcodes that do not need to be proven (ex: some UI and audio state). Note that these can be a bit subtle, as it requires us to error/warn on any game that uses behavior that cannot be proven (ex: the game logic somehow reads from the graphic state - but this is extremely rare in practice)
    3. **External inputs into proving system**: Manage external input (ex: user inputs) as witnesses injected into the game console (as opposed to them being entirely internal to the emulator)
    4. **Direct opcode proving**: most attempts to prove other systems work by taking software, compiling to to a known instruction set (riscv, wasm), and then proving this. Since this means that running a single sm83 opcode means proving 10+ riscv opcodes due to compilation overhead, this leads to massive proof overhead. 
    5. **Disable dangerous features**: some features in the Gameboy like eram (data loaded from save files) cannot be supported, as it would allow injecting unproven state into the system. We have to disable these features in a logical way on a case-by-case basis to ensure there are no attack vectors.
2. **Containerization**: Foldiboy needs to be able to run even on sensitive devices (and therefore cannot trust installing software). To achieve this, we use sandboxing through Wasm of all components. Notably, we do sandboxing through Wasm Components (and not Wasm modules like some other emulators that support this) in order to easily get sandboxing even on the desktop, as well as leverage standards like wasi-gfx for webgpu-rendered UIs (which can be sandboxed)

Note that, despite these many ZK optimizations, Foldiboy is not actually hard-coded to any proof system.

You can learn more about subtle points in relation to which component is proven and how in the following folders:
- human-written managed documentation [here](./docs)
- AI-assisted documentation [here](./machine-docs/)

## Architecture

```
Guest (WASM Component)                    Host (native, wasmtime)
┌──────────────────────────────────────┐  ┌───────────────────────────┐
│  CPU (SM83, all 512 opcodes)         │  │  WebGPU surface + window  │
│  PPU (scanline renderer, 4 modes)    │  │  cpal audio backend       │
│  APU (4 channels, 48kHz stereo)      │  │  Input event polling      │
│  Timer (falling-edge model)          │  │  WASI filesystem (ROMs)   │
│  Bus (MBC1/2/3/5, OAM DMA, I/O)      │  │                           │
│  Joypad (active-low, 8 buttons)      │  │                           │
├──────────────────────────────────────┤  ├───────────────────────────┤
│  WIT interfaces:                     │  │  Implements:              │
│    import wasi:webgpu                │◄─┤    wasi-gfx (WebGPU)      │
│    import wasi:surface               │  │    nightstream:audio      │
│    import nightstream:audio          │  │    wasi:filesystem        │
│    import wasi:filesystem            │  │    wasi:cli               │
│    export wasi:cli/run               │  │                           │
└──────────────────────────────────────┘  └───────────────────────────┘
```

The guest produces a 160x144 RGBA8 framebuffer and interleaved i16 stereo audio samples each frame. The host consumes these via WebGPU texture uploads and a lock-free ring buffer audio pipeline.

## Repository Layout

```
foldiboy/
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
│   │           ├── app_state.rs    AppFocus, EmulatorState, AppState
│   │           ├── debug_panel.rs  Debug panel renderer (dirty-flag caching)
│   │           ├── rom_browser.rs  WASI filesystem ROM browser (TUI)
│   │           ├── memory_panel.rs MemoryPanel (owns WideTextBuffer + RamViewer)
│   │           ├── ram_viewer.rs   RAM viewer: hex dump, tab bar, region switching
│   │           └── font.rs         8x8 bitmap font, TextGrid<C,R> generic
│   ├── wit/                    WIT interface definitions
│   │   ├── gameboy.wit             nightstream:foldiboy/app world
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

This builds the guest WASM component, then compiles and runs the host. The host opens a window with three panels (see [Debug UI](#debug-ui) below).

**Run tests:**

```bash
cd lib && cargo test
```

**Controls:**

| Key | Context | Action |
|-----|---------|--------|
| Arrow keys | Emulator | D-pad |
| X / J | Emulator | A button |
| Z / K | Emulator | B button |
| Enter | Emulator | Start |
| Right Shift | Emulator | Select |
| Escape | Any | Toggle focus: Emulator <-> last debug panel |
| Tab | Debug panels | Cycle focus: ROM Browser <-> RAM Viewer |
| Up/Down | ROM Browser | Navigate entries |
| Enter | ROM Browser | Open directory / load ROM |
| Backspace | ROM Browser | Go up one directory |
| Up/Down | RAM Viewer | Scroll one row (16 bytes) |
| PgUp/PgDn | RAM Viewer | Scroll one page (21 rows) |
| Left/Right | RAM Viewer | Switch memory region |
| Click | Any panel | Focus that panel |
| Click tab | RAM Viewer header | Switch to clicked region |

## Debug UI

Three-panel layout at 320x240 logical resolution (4:3 aspect ratio, letterboxed to window):

```
+----------+----------+
|   Game   |   ROM    |
| 160x144  |  Browser |
|          | 160x144  |
+----------+----------+
|     RAM Viewer      |
|      320x96         |
+---------------------+
```

**Focus system:** only one panel is active at a time. The focused panel renders at full brightness; others are dimmed. Escape toggles between Emulator and the last-used debug panel. Tab cycles between ROM Browser and RAM Viewer. Clicking a panel focuses it.

### ROM Browser (top-right)

WASI filesystem browser for loading ROMs. Navigates preopened directories, shows `.gb`/`.gbc` files and subdirectories. Double-click or Enter to open.

### RAM Viewer (bottom)

Hex dump inspector for Game Boy memory. Renders into an 80x24 character grid (640x192 pixels) using an 8x8 bitmap font, then GPU-downscaled to 320x96 via bilinear filtering for half-size text with maximum data density.

**Layout (80 columns x 24 rows):**
```
Row  0:  XXXX-XXXX | WRAM VRAM HRAM OAM I/O ERAM    <- header: address range + tab bar
Row  1:  ADDR: 00 01 02 ... 0F  ASCII                <- column offset headers
Rows 2-22: XXXX: HH HH HH ... HH  ................  <- 21 data rows (16 bytes each)
Row 23:  Up/Down:scroll  PgUp/PgDn:page  ...         <- help bar
```

**Memory regions** are identified by `MemoryRegion` enum variants for the different kinds of RAM

The tab bar in row 0 shows all 6 viewable regions. The active tab is highlighted (white-on-black). Tabs are clickable, or switch with Left/Right arrow keys.

`read_region(region, offset)` reads bytes by linear offset within each region without bus side effects. For banked regions (ERAM), this reads the currently-mapped bank's data.

**Future additions:**
- **ROM tab** — infrastructure exists (`read_region` can read the full ROM). Needs bank indicator like ERAM
- **Registers tab** — requires passing CPU state (AF, BC, DE, HL, SP, PC, flags) into the viewer and a formatted display instead of hex dump

## Emulator Subsystems

### CPU

Sharp SM83. All 512 opcodes implemented: 256 main + 256 CB-prefix.

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

Foldiboy is built to be proven under any zkVM that supports lookups and folding.

We have [provability](./docs/provability.md) docs to keep track of:
1. Exactly what is provable
2. What deliberate simplifications we make to keep the emulator ZK-friendly

| Simplification | Rationale |
|----------------|-----------|
| **Audio not proven** | APU registers are pure I/O — audio output has no effect on game state that needs proving |
| **Fixed PPU timing** | No SCX scroll or sprite-count-dependent mode 3 duration — avoids variable-length constraint rows |
| **Atomic CPU instructions** | No sub-instruction bus modeling — each `step()` is one constraint row |
| **Self-contained frame sequencer** | APU counter not coupled to DIV register — avoids cross-subsystem dependencies in the trace |
| **No wave RAM access restrictions** | Simplified read/write during CH3 playback — avoids per-dot mode tracking |
| **RTC stubbed to 0** | Real-time clock is fundamentally unprovable without an external time oracle |

These trade-offs cause a small number of Mooneye/Blargg tests to fail by design (see [Test Coverage](#test-coverage) below), but do not affect the correctness of game logic for the vast majority of titles.

## zk proving via Nightstream Integration

Foldiboy is optimized to be integrated with [Nightstream](https://github.com/LFDT-Nightstream/Nightstream), but avoids direct tight coupling (does not depend on any Nightstream-specific crates).
