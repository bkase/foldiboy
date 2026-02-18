# The Ideal Game Boy Emulator

The target architecture for Nightboy — a Game Boy emulator designed for
zero-knowledge proof generation in the Nightstream zkVM.

> **Audience**: Developers working on Nightboy or the Nightstream Game Boy
> integration. Assumes familiarity with the Twist & Shout proof primitives.
>
> **Purpose**: This document describes the architectural ideal we are building
> toward. It is prescriptive, not descriptive — it defines the target architecture,
> not the current state of the implementation.
>
> **Companion**: [`provability.md`](provability.md) classifies every memory
> region, I/O register, and state element into proof categories (Twist,
> Shout, Computed, Witness, Unproven) with full justifications. This document
> takes those classifications as given and describes the emulator architecture
> that implements them.

---

## Table of Contents

- [1. Design Principles](#1-design-principles)
- [2. Architecture Layers](#2-architecture-layers)
- [3. Bus Architecture](#3-bus-architecture)
  - [3.1 Bus Trait](#31-bus-trait)
  - [3.2 Address Classification](#32-address-classification-in-the-bus)
  - [3.3 Bus Implementations](#33-bus-implementations)
- [4. CPU Architecture](#4-cpu-architecture)
  - [4.1 Register Model](#41-register-model)
  - [4.2 Instruction Hierarchy](#42-instruction-hierarchy)
  - [4.3 Pure ALU](#43-pure-alu)
  - [4.4 Step Function](#44-step-function)
  - [4.5 Interrupt Dispatch](#45-interrupt-dispatch)
  - [4.6 Halt Bug and EI Delay](#46-halt-bug-and-ei-delay)
- [5. ROM and Banking](#5-rom-and-banking)
- [6. Peripheral Architecture](#6-peripheral-architecture)
  - [6.1 Per-Instruction Ticking](#61-per-instruction-ticking)
  - [6.2 Timer](#62-timer)
  - [6.3 Computed Registers (IF, JOYP)](#63-computed-registers-if-joyp)
  - [6.4 OAM DMA](#64-oam-dma)
  - [6.5 Witness Tape Architecture](#65-witness-tape-architecture)
- [7. Integration Requirements](#7-integration-requirements)
  - [7.1 Trace Pipeline Overview](#71-trace-pipeline-overview)
  - [7.2 Per-Step Bus Operation Budget](#72-per-step-bus-operation-budget)
  - [7.3 ALU Lookup Tables](#73-alu-lookup-tables)
  - [7.4 Register Events from Opcode Table](#74-register-events-from-opcode-table)
  - [7.5 Witness Tapes](#75-witness-tapes)
- [8. Data Export Interface](#8-data-export-interface)
  - [8.1 Modes of Operation](#81-modes-of-operation)
  - [8.2 Per-Step Export](#82-per-step-export)
  - [8.3 Bus Operation Buffering](#83-bus-operation-buffering)
  - [8.4 WIT Interface for Trace Mode](#84-wit-interface-for-trace-mode)
  - [8.5 Bulk Data Export](#85-bulk-data-export)
  - [8.6 Replay Mode](#86-replay-mode)
- [9. Initial State](#9-initial-state)
- [10. Static ROM Validation](#10-static-rom-validation)
- [11. Testing expectations](#11-testing-expectations)


---

## 1. Design Principles

Ordered by priority. When they conflict, higher-ranked principles win.

1. **Proof correctness over hardware fidelity.** Timing simplifications are
   acceptable when they don't affect the proof boundary (fixed PPU mode
   durations, per-instruction peripheral ticking).

2. **Never gate Twist access on a witnessed value.** This invariant is
   absolute — it is what makes our simplified PPU/OAM model safe. See
   [`provability.md` §5.8](provability.md#58-stat-mixed-ownership) for the
   full analysis.

3. **Subsystems tick after the CPU step, never during.** Every bus operation
   during `cpu.step()` is CPU-initiated. No PPU/DMA/timer contamination.

4. **One implementation per operation.** The same pure ALU function serves
   execution, lookup table construction, and test validation.

5. **The Bus trait is the single observation point.** All CPU memory access
   flows through `Bus::read(&mut self)` / `Bus::write(&mut self)`. No direct
   memory array access from the CPU.

6. **Minimal witness surface.** Prove everything that can be proved cheaply
   (timer, MBC bank registers). Only witness things that depend on external
   input. See [`provability.md` "Decision Criteria"](provability.md#decision-criteria)
   for the full rationale.

---

## 2. Architecture Layers

The emulator is structured into layers separated by trait boundaries. The
layering is driven by a central requirement: the proof system needs the CPU
and its memory interactions, but must not depend on unproven subsystems
(PPU, APU) or platform-specific code (WASM, GPU rendering).

### 2.1 The Proving Core

The **CPU** and **memory abstraction** (the `Bus` trait) form the proving
core. This layer contains everything the proof system needs:

- Instruction decode, execution, and ALU (pure functions)
- Register model (`Copy`-able, snapshotable)
- The `Bus` trait as the sole memory access interface
- Interrupt dispatch, halt bug, EI delay

The CPU is generic over any `Bus` implementation — it has no knowledge of
what sits behind the trait. This is what makes it usable both for runtime
emulation and for proof-generating execution via a TracingBus.

The proving core must be `no_std`-compatible.
It must have no dependency on any peripheral, rendering, or platform crate.

### 2.2 Proven Peripherals

The **timer** is the only peripheral inside the proof boundary (see
[`provability.md` §3](provability.md#3-the-timer)). It is deterministic and
adds ~4 constraints per step.

Architecturally, the timer sits between the proving core and the unproven
peripherals. It must be accessible to both the runtime bus (which ticks it
per-instruction) and the integration layer (which constrains its state transitions).
Whether it lives in the bus implementation or in a shared crate is an
implementation detail — what matters is that the integration layer can
model its behavior.

### 2.3 Unproven Peripherals

**PPU** and **APU** exist for playability — they render graphics and
generate audio so the emulator is usable as a game player. They run during
emulation but are invisible to the proof. Their outputs (STAT, LY,
VBlank/STAT interrupts) enter the proof only as witness tape values.

These crates may depend on the memory abstraction (PPU owns VRAM and OAM)
but the proving core must never depend on them. The dependency arrow is
strictly one-directional.

### 2.4 Bus Implementations and Platform Layer

Concrete bus implementations wire the layers together:

- **GameBoyBus** (runtime): Owns all subsystems (timer, PPU, APU, joypad,
  MBC state). Implements the full DMG memory map. This is what runs games.
- **TracingBus** (proof generation): Wraps the runtime bus, intercepts every
  operation, and emits proof events per [§3.2](#32-address-classification-in-the-bus).
- **TestBus** (testing): Flat 64KB RAM. No peripherals. Processor test mode.

The proven/unproven separation is **logical**, not physical — GameBoyBus
owns all subsystems in one struct, and the TracingBus classifies operations
by address. There is no requirement to split subsystems into separate
crates along the proof boundary unless integration work reveals a concrete
need.

The platform layer (WASM bindings, GPU rendering, host audio bridge) sits
above everything and is irrelevant to the proof.

### 2.5 Integration Layer (Future)

A dedicated integration crate will bridge the emulator and Nightstream. It
depends on the proving core + nightstream traits (`VmCpu<u16, u16>`, `Twist`,
`Shout`) and implements the full trace pipeline: TracingBus with address
routing, Shout tables, ExecTable conversion, witness layout, and CCS wiring.

This crate must not depend on the unproven peripherals or the platform layer.

---

## 3. Bus Architecture

### 3.1 Bus Trait

```rust
pub trait Bus {
    fn read(&mut self, addr: u16) -> u8;
    fn write(&mut self, addr: u16, value: u8);
}
```

`&mut self` on reads enables trace recording without `RefCell`. The CPU is
generic over `B: Bus` — swapping bus implementations requires zero changes
to CPU logic.

### 3.2 Address Classification in the Bus

Every bus address belongs to exactly one proof category (see
[`provability.md` §6](provability.md#6-complete-classification) for the
definitive map). The emulator's bus architecture must make this classification
**observable from outside** — an external integration layer needs to inspect
each bus operation and determine its category without modifying the CPU or
bus internals.

This means the bus must expose enough information for each operation:

1. **The address** — determines the category and region
2. **The operation type** (read vs write) — matters for $0000-$7FFF where
   reads are ROM (read-only) and writes are MBC register updates
3. **The value** — the byte read or written
4. **Banking state** — for $4000-$7FFF reads and $A000-$BFFF accesses, the
   current MBC bank determines the effective physical address

The bus does not need to know *what the proof system does* with this
information. It just needs to ensure that every CPU memory operation is
observable through a single trait boundary (`Bus::read` / `Bus::write`),
and that the address-to-region mapping is unambiguous.

**Key architectural properties** the bus must preserve:

- **$0000-$7FFF asymmetry**: Reads come from ROM (immutable), writes go to
  MBC registers (mutable internal state). The bus handles this naturally —
  the same address range dispatches differently by operation type.
- **Echo RAM normalization**: $E000-$FDFF must resolve to the same physical
  memory as $C000-$DFFF. This is already how all correct Game Boy emulators
  work; the proof layer will see identical (region, offset) pairs for both.
- **Computed registers**: IF ($FF0F) and JOYP ($FF00) are registers whose
  read value depends on a mix of CPU-written state and external input. The
  bus must implement the correct read semantics (e.g., JOYP muxing button
  state based on selection bits). An external layer can then verify that the
  computation was correct.
- **Witness registers**: STAT ($FF41) and LY ($FF44) return values driven by
  the PPU. The bus returns whatever the PPU produces; the proof layer will
  treat these as externally-provided values.
- **Unproven addresses**: Reads from PPU config, APU, serial, unmapped I/O
  return hardware-appropriate values for emulation correctness, but an
  external layer will reject traces that depend on them.

### 3.3 Bus Implementations

**GameBoyBus** (runtime): Full memory map with all subsystems. Owns PPU,
APU, timer, joypad, MBC state, OAM DMA, serial stub. This is what runs
games. Every read and write flows through the `Bus` trait, making all
operations observable to any wrapping layer.

**LoggingBus\<B\>** (trace recording): Wraps any bus implementation,
recording every `read()` and `write()` into a per-step log. Used in
trace mode ([§8.3](#83-bus-operation-buffering)) so the host can extract
bus operations via WIT. The inner bus (typically GameBoyBus) runs
normally — the CPU doesn't know it's being recorded.

**TracingBus** (proof generation, future — integration layer): Replays
pre-recorded witness tapes instead of running live peripherals. Returns
tape values for STAT/LY reads, injects external interrupt bits into IF,
and emits proof events per address classification
([§3.2](#32-address-classification-in-the-bus)). This is NOT part of the
emulator — it lives in the integration layer ([§2.5](#25-integration-layer-future)).

**TestBus** (testing): Flat 64KB RAM. No peripherals. Processor test mode.

---

## 4. CPU Architecture

### 4.1 Register Model

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisterFile {
    pub a: u8, pub f: u8,    // Flags: Z(7) N(6) H(5) C(4), bits 3-0 = 0
    pub b: u8, pub c: u8,
    pub d: u8, pub e: u8,
    pub h: u8, pub l: u8,
    pub sp: u16, pub pc: u16,
}
```

`Copy` enables trivial snapshotting (`regs_before` / `regs_after` are just
copies). Flags stored as a byte, not individual bools — avoids assembly
overhead on every ALU operation and snapshot. Register pair accessors
(`bc()`, `hl()`, `set_bc()`, etc.) provide 16-bit views without redundant
state.

The register file's `Copy` + `PartialEq` derivation also enables
structural diffing: given `regs_before` and `regs_after`, an external
layer can derive exactly which registers changed without runtime
instrumentation inside the CPU (see [§7.4](#74-register-events-from-opcode-table)).

### 4.2 Instruction Hierarchy

```rust
pub enum GbInstruction {
    Load(Load),
    U8Arithmetic(U8Arith),
    U16Arithmetic(U16Arith),
    BitShift(BitShift),
    Jumps(Jump),
    Stack(Stack),
    Flag(Flag),
    Interrupt(InterruptCtl),
    Misc(Misc),
}
```

**Block-based decoding**: `opcode >> 6` selects one of four decode blocks.
All 512 opcodes decoded (256 main + 256 CB-prefix). The decoder uses a
`fetch` callback (closure over the bus) to read immediate bytes, advancing
PC as it goes.

**Why sub-enums**: Exhaustive match per category. Each variant carries only
its relevant data. A flat enum with 30+ variants mixes unrelated fields.

**Why match dispatch, not function pointers**: Match arms are transparent
to static analysis. An integration layer can map each match arm to its
expected memory access pattern without runtime tracing.

### 4.3 Pure ALU

Every ALU operation is a pure function returning `AluResult { value: u8, flags: u8 }` with no CPU state mutation:

- `alu_binary(op, a, b, carry_in)` — ADD, ADC, SUB, SBC, AND, OR, XOR, CP
- `alu_inc(val, old_flags)` / `alu_dec(val, old_flags)` — preserves carry
- `alu_shift(op, val, carry_in)` — RLC, RRC, RL, RR, SLA, SRA, SRL, SWAP
- `alu_bit(bit, val)` — BIT test
- `alu_daa(a, flags)` — BCD adjust (must use original A, not partially-adjusted)

Same function serves execution, lookup table construction (for the
integration layer), and testing.

### 4.4 Step Function

```rust
impl<B: Bus> GbCpu<B> {
    pub fn step(&mut self) -> StepResult {
        // 1. Check halt/stop — wake on pending interrupt
        // 2. Decode instruction at PC (block-based, fetch advances PC)
        // 3. Execute instruction (all memory through self.bus)
        // 4. Step EI delay counter
        // 5. Check pending interrupts (if IME=true)
        // 6. Return step metadata
    }
}
```

Every memory access goes through `self.bus.read()` / `self.bus.write()`.
This is the two-function funnel — the single observation point for trace
generation.

**Step metadata**: `step()` must return enough information for an external
consumer to reconstruct what happened, without that consumer needing to
inspect CPU internals:

```rust
pub struct StepResult {
    pub m_cycles: u32,
    pub opcode: u16,        // 0x000-0x0FF main, 0x100-0x1FF CB-prefix
    pub step_type: StepType, // Normal, Interrupt, Halt, Stop
    pub halt_bug: bool,     // duplicate fetch occurred
}
```

The CPU itself is unchanged between play mode and trace mode — it calls
`self.bus.read()` and `self.bus.write()` regardless of whether the bus
records operations or not. The bus implementation determines what happens
with each operation (see [§8](#8-data-export-interface)).

### 4.5 Interrupt Dispatch

Handled at instruction boundaries. Hardware-accurate 2-cycle PC push: high
byte first, then low byte. This matters because the high byte write can
modify IE (if SP points to $FFFF), potentially canceling the interrupt
mid-dispatch.

From the bus's perspective, interrupt dispatch looks like a CALL (two stack
writes + a jump). An integration layer can recognize it as a distinct step
type by the synthetic opcode marker in the trace.

### 4.6 Halt Bug and EI Delay

**Halt bug**: HALT with `IME=false` and pending interrupt causes the next
instruction byte to be read twice (PC not incremented). Modeled via a
`halt_bug` flag suppressing one PC increment. This is observable through
the bus — a duplicate `read()` at the same PC address — and must be
handled correctly by any integration layer.

**EI delay**: `ime_delay = Some(1)` → decrements after each instruction →
IME set true when counter reaches 0. IME becomes true after the *next*
instruction, not immediately.

**EI+HALT edge case**: EI immediately before HALT with pending interrupt
must NOT trigger halt bug. The CPU backs up PC to the HALT opcode and
dispatches the interrupt normally.

**HALT in the trace**: When the CPU is halted, each call to `step()`
returns `StepResult { step_type: Halt, m_cycles: 1, .. }` with no bus
operations. The CPU wakes when an enabled interrupt becomes pending
(IE & IF != 0). Each waiting step consumes one entry from every witness
tape ([§7.5](#75-witness-tapes)), producing a near-empty trace row. A
game HALTing until VBlank may generate ~1140 trivial rows per instance.
This is cheap to prove (no bus ops, no register changes) but inflates
trace size.

**STOP**: STOP halts the CPU until a button press (DMG). Like HALT, each
waiting step returns `StepResult { step_type: Stop, m_cycles: 1, .. }`.
The CPU wakes when any button is pressed — the button tape must
eventually show a pressed button. STOP is rare in games (primarily used
for battery savings on real hardware).

---

## 5. ROM and Banking

ROM is immutable and banking state is deterministic — both are provable.
See [`provability.md` §5.1](provability.md#51-rom-as-shout) and
[§5.2](provability.md#52-mbc-bank-registers) for the classification rationale.

The emulator must preserve these architectural properties:

**ROM immutability**: ROM data ($0000-$7FFF reads) is never modified at
runtime. The bus returns bytes from the loaded ROM image. This means an
integration layer can model ROM as precomputed lookup tables (one per
bank) rather than mutable memory.

**Bank register observability**: Every MBC register write ($0000-$7FFF
writes) flows through the bus trait and changes a small set of internal
bank registers. The bus must expose enough state for an external layer to
know which bank is active at any point:

| Register | Purpose |
|----------|---------|
| ROM bank | Selects which ROM bank appears at $4000-$7FFF |
| BANK2 / RAM bank | Secondary banking (ROM high bits or ERAM bank) |
| Mode | MBC1 only — how BANK2 applies |
| RAM enable | Gates ERAM access |

**Banked read decomposition**: A $4000-$7FFF read is logically two
operations — read the current bank register, then index into that bank's
ROM data. The bus performs this transparently; an integration layer can
decompose it into separate proof events.

**Fixed bank simplicity**: $0000-$3FFF always reads bank 0, with no
banking state dependency. This is simpler to prove than the banked region.

**Supported MBCs**: MBC1 (+ MBC1M multicart), MBC2, MBC3, MBC5. Each has
its own banking logic but all expose the same observable structure (a small
set of bank registers mutated by writes to $0000-$7FFF). Auto-detected
from ROM header byte $0147. MBC3 RTC is stubbed (unprovable — see
[`provability.md` §5.9](provability.md#59-serial-and-link-cable) note on
external time oracles).

**ERAM access when RAM is disabled**: When the RAM enable register is
clear, reads from $A000-$BFFF return $FF (hardware behavior) regardless
of ERAM contents. The bus operation log records `(addr, 0xFF, read)`.
The integration layer must check `bank_state.ram_enabled` — when
disabled, it skips the ERAM Twist load and instead verifies the value is
$FF. This is a special case in address routing: the same address range
maps to ERAM (Twist) when enabled, or to a constant $FF when disabled.

---

## 6. Peripheral Architecture

### 6.1 Per-Instruction Ticking

Subsystems tick **after** the CPU step completes, never during:

```rust
fn run_step(cpu: &mut GbCpu<GameBoyBus>) -> StepResult {
    let result = cpu.step();                                      // CPU only
    let timer_overflow = cpu.bus.timer.update(result.m_cycles);   // Timer
    let (ppu_evt, ppu_irqs) = cpu.bus.ppu.update(result.m_cycles); // PPU
    cpu.bus.apu.update(result.m_cycles);                           // APU
    // Apply interrupts to IF...
    result
}
```

This guarantees every bus operation during `cpu.step()` is CPU-initiated.
No filtering or context tracking needed to distinguish CPU operations from
subsystem operations.

### 6.2 Timer

The timer is fully deterministic and proven inside the proof boundary
(see [`provability.md` §3](provability.md#3-the-timer) for the full model).
The architectural consequences are:

- DIV, TIMA, TMA, TAC are proven I/O state — no witness tape entries needed
- Timer interrupts (IF bit 2) are deterministic, not externally provided
- The timer's state transitions must be reproducible from its register
  values and the cycle count alone — no hidden state

The current implementation uses a falling-edge model with a shared 16-bit
internal counter. It updates per-instruction (not per-T-cycle within an
instruction), creating a deliberate ~8 T-cycle lag. Three Mooneye tests
fail by design; no game depends on these sub-instruction edge cases.

### 6.3 Computed Registers (IF, JOYP)

IF and JOYP are **Computed** — their read values depend on a mix of
CPU-written state and external inputs (see
[`provability.md` §4](provability.md#4-the-if-register-model) and
[§5.7](provability.md#57-joyp-mixed-ownership) for the models).

The emulator must implement these registers with clear separation of their
input sources:

**IF ($FF0F)**:
- CPU writes set/clear bits directly
- Timer overflow sets bit 2 (proven, deterministic)
- VBlank/STAT/joypad interrupts set bits 0, 1, 4 (external, witnessed)
- Reads return the combined result

**JOYP ($FF00)**:
- CPU writes the selection bits (bits 5-4)
- Button state provides bits 3-0 (external, witnessed)
- Reads mux the button state based on the selection bits

This decomposition is what makes these registers provable despite depending
on external input — the computation is deterministic given the inputs. An
integration layer can verify the computation was correct.

**Contrast with pure Witness registers**: STAT ($FF41) and LY ($FF44) are
entirely PPU-driven — the bus returns whatever the PPU produces, with no
CPU-writable component affecting the read value. See
[`provability.md` §5.8](provability.md#58-stat-mixed-ownership) for why
STAT doesn't need the same computation model as IF/JOYP.

### 6.4 OAM DMA

Writing to $FF46 triggers a 160-byte copy that far exceeds the per-step
bus operation budget (~12 operations vs 320 needed). See
[`provability.md` §5.4](provability.md#54-oam-dma) for the tiered approach.

Architecturally, the key decision is whether DMA is **expanded** as
individual bus operations or treated as a single atomic transfer. In the
higher proof tiers (Tier 2/1), each DMA copy becomes 160 individual
read-write pairs (1 source read + 1 OAM write). The emulator currently
copies all 160 bytes in a single `write()` call — an integration layer
would need to expand this into observable per-byte operations.

The DMA source routing must match the hardware DMA bus, which differs from
the CPU bus at $E000-$FFFF. See [`provability.md` §5.5](provability.md#55-dma-trigger)
for the routing table.

### 6.5 Witness Tape Architecture

Several registers depend on external input that the proof system cannot
derive: PPU-driven values (STAT, LY, VBlank/STAT interrupts), and
player-driven values (button state, joypad interrupt). The emulator must
be architected so these values can be **recorded** during full emulation
and **replayed** during proof generation, without changing the CPU or bus
trait.

#### The recording/replay split

Witness data flows through two phases (see [§8.1](#81-modes-of-operation)
for the full mode taxonomy):

- **Full emulation** (GameBoyBus): PPU, APU, joypad all run live. After
  each CPU step, the bus can record what the CPU would observe — the
  current STAT byte, LY value, which interrupt bits fired, and button
  state. This produces the witness tapes.

- **Proof generation** (TracingBus): No PPU or APU runs. Instead, the
  TracingBus reads the pre-recorded tapes to answer reads of STAT, LY,
  and to inject external interrupt bits into IF. The CPU sees identical
  values in both modes.

This works because of design principle §1.3: subsystems tick **after** the
CPU step. During `cpu.step()`, the CPU only sees values that were set
*before* the step began. The recording point is the same boundary — after
the previous step's peripheral tick, before the current step's `cpu.step()`.

#### What the emulator must expose

The bus must make the following observable per step, so that a wrapping
layer can record them:

1. **External interrupt bits** (3 bits): Which of {VBlank, STAT, joypad}
   fired this step. These come from PPU and joypad — the timer interrupt
   is excluded because it is proven internally.

2. **STAT register value** (8 bits): The full byte at $FF41 as seen by
   the CPU. Only consumed when the CPU actually reads $FF41, but recorded
   every step for uniform tape layout.

3. **LY register value** (8 bits): The scanline counter at $FF44. Same
   consumption model as STAT.

4. **Button state** (8 bits): All 8 buttons, active-low. Consumed when
   the CPU reads JOYP ($FF00) and the selection bits are set.

The recording doesn't require any changes to the bus trait — it's a
wrapping concern. The bus just needs to expose these values through
accessors (e.g., `ppu.stat()`, `ppu.ly()`, `joypad.button_state()`),
which it already does for its own `Bus::read()` implementation.

#### Internal architecture for tape support

The key constraint is that computed registers ([§6.3](#63-computed-registers-if-joyp))
must decompose their inputs cleanly. IF in particular merges three sources:

- CPU writes (proven — tracked by the bus)
- Timer overflow (proven — deterministic from timer state)
- External interrupts (witnessed — from the tape)

The bus already separates these in its `run_step` loop: timer fires are
applied as `if_reg |= timer_bit`, and PPU/joypad fires are applied as
`if_reg |= ppu_bits`. This separation is exactly what the tape needs —
the external bits are the ones that get recorded and replayed.

For JOYP, the split is between the CPU-written selection bits (bits 5-4)
and the button state (bits 3-0). The bus already implements this as a mux
in its `read()` handler. Replay just substitutes the button source.

For STAT and LY, there is no CPU-writable component — the tape value
replaces the PPU output entirely.

---

## 7. Integration Requirements

This section describes what the integration layer (the bridge between
Nightboy and Nightstream) will need from the emulator. The emulator itself
does not implement any of this — it just needs to expose the right
architectural properties for the integration layer to work.

### 7.1 Trace Pipeline Overview

The integration layer wraps the emulator's bus to capture every CPU memory
operation, then transforms the execution trace into proof structures:

```
GbCpu<TracingBus> execution
    |  step() → captured bus operations per instruction
    v
VmTrace (one row per step: regs_before, regs_after, bus ops)
    |  row-per-step decomposition
    v
ExecTable → event tables (register, RAM, ROM lookup)
    |  column-major transform
    v
TraceWitness (fixed-width columns over time)
    |
    v
Proof system (constraint wiring, folding, verification)
```

### 7.2 Per-Step Bus Operation Budget

The worst-case bus operations per step determines the proof layout width.
Every `Bus::read()` and `Bus::write()` call is one observable operation.

**Bus operations** (recorded by LoggingBus, see [§8.3](#83-bus-operation-buffering)):

| Operation type | Count | Example |
|----------------|-------|---------|
| Instruction fetch reads | 1-3 | `CALL n16`: 3 bytes |
| Data reads | 0-1 | `LD A,[HL]` |
| Data writes | 0-1 | `LD [HL],A` |
| Stack reads | 0-2 | `RET`: pop PC |
| Stack writes | 0-2 | `CALL`: push PC |
| **Bus total** | **1-6** | |

**Derived proof events** (not bus operations — computed by the
integration layer from opcode table + register snapshots):

| Event type | Count | Source |
|------------|-------|--------|
| Register reads | 0-3 | Opcode table ([§7.4](#74-register-events-from-opcode-table)) |
| Register writes | 0-2 | Opcode table + regs_before/regs_after diff |
| Bank register read | 0-1 | bank-state ([§8.4](#84-wit-interface-for-trace-mode)) |

The proof layout must provision for worst case across both categories.
Variable-length instructions use conditional slots for optional bytes.

### 7.3 ALU Lookup Tables

The pure ALU functions ([§4.3](#43-pure-alu)) enable precomputation of
every possible ALU result as a lookup table. Each ALU operation produces a
table of 2^16 entries (all 8-bit × 8-bit input pairs). Carry-dependent
operations (ADC, SBC, RL, RR) need two tables (carry=0 and carry=1).
Entries pack result + flags: `(flags << 8) | result`.

ROM data is similarly structured as precomputed per-bank lookup tables.

Because the same pure function builds the table and runs during execution,
correctness is guaranteed by construction.

### 7.4 Register Events from Opcode Table

Every opcode's register access pattern is deterministic from the opcode byte
alone. A static 512-entry table maps each opcode to its register reads and
writes:

```rust
struct OpcodeRegPattern {
    reads: &'static [Reg8],
    writes: &'static [Reg8],
}
static OPCODE_REG_TABLE: [OpcodeRegPattern; 512] = [ /* ... */ ];
```

Combined with `regs_before` / `regs_after` snapshots (enabled by
`Copy` on `RegisterFile`), register access events are derived without
runtime register instrumentation. This avoids invasive modifications to
the register struct and adds zero runtime overhead during execution.

### 7.5 Witness Tapes

The integration layer consumes the witness data described in
[§6.5](#65-witness-tape-architecture) as fixed-layout tapes — one entry
per CPU step, no conditional advancement. This uniform layout simplifies
the proof witness columns (each tape becomes a single column in the
TraceWitness).

| Tape | Width | Content |
|------|-------|---------|
| External interrupt | 3 bits | {VBlank, STAT, joypad} OR'd into IF |
| Button state | 8 bits | All 8 buttons, active-low |
| STAT | 8 bits | Full STAT byte (consumed on $FF41 reads) |
| LY | 8 bits | Current scanline (consumed on $FF44 reads) |

**Why uniform layout**: Every step has an entry in every tape, even if the
CPU doesn't read that register on that step. This avoids conditional tape
advancement, which would require proving the advancement condition itself.
The cost is ~27 bits per step of redundant witness data — negligible
compared to the bus operation columns.

**Tape generation**: The prover runs the full emulator in trace mode
([§8.4](#84-wit-interface-for-trace-mode)), collecting witness values at
each step boundary. Per step, `tick-peripherals()` returns the external
interrupt bits and `get-witness()` returns STAT, LY, and button state —
these are the values described in [§6.5](#65-witness-tape-architecture).
The host appends each step's values to four arrays (one per tape). The
proof then verifies the CPU behaved correctly *given* those values — it
does not verify that the values themselves are correct (that would
require proving the PPU, which we explicitly avoid).

**Tape consumption in TracingBus**: On each step, the TracingBus reads
the current tape entries. External interrupt bits are merged into the
Computed IF register ([§6.3](#63-computed-registers-if-joyp)). STAT and LY
values are returned directly on reads to $FF41/$FF44. Button state feeds
the JOYP mux on reads to $FF00.


**Passthrough (emulator) as part of the tape**: The emulator passthrough
is implemented as a tape as discussed in [§5.17](provability.md#517-unproven-sub-types)
for all unconstrained witnesses.
The reason are as follows:
1. This is the more canonical mental model
2. This is likely more efficient for streaming traces (see [§8.1](#81-modes-of-operation))
3. This is easier to debug, as the transitions are explicit
4. This is easier to connect to a shared proof system (compared to one proof system bundled per app, such as one per Gameboy emulator)
5. This is easier to connect to replay systems

---

## 8. Data Export Interface

The emulator runs as a WASM component. The prover runs on the host. All
data needed for proof generation must cross the WASM boundary through a
defined interface (WIT). This section describes what the emulator must
export and how it structures that export.

### 8.1 Modes of Operation

The emulator supports three modes through its WIT interface, all sharing
the same CPU, bus, and peripheral code:

**Play mode**: The host calls frame-level functions. The emulator runs a
full frame internally (CPU + PPU + APU + timer), renders to a
framebuffer, and pushes audio samples. The host provides input events.
No trace data is generated. This is what makes the emulator playable.

**Trace mode**: The host drives execution step-by-step. After each step,
the emulator exports a complete snapshot of what happened — step metadata,
register state, bus operation log, and witness values. The host decides
what to do with this data:

- **Stream** (online proving): The host feeds each step's data directly
  to the proof system, which processes it online. Trace data is not
  persisted — a ring buffer on the host side is sufficient. Once the
  proof system has consumed a step, the data can be discarded.
- **Record**: The host saves the complete trace to a replay file. The
  file captures everything needed to reproduce the execution: ROM hash,
  initial state, and per-step records (witness values, step metadata).
  This is the same data the proof system consumes, persisted to disk.

From the emulator's perspective, stream and record are identical — it
exports the same data either way. The host controls retention.

**Replay mode**: The host loads a previously-recorded replay file and
drives the emulator step-by-step, injecting recorded witness values
(button state, external interrupts) at each step boundary. The emulator
re-executes with these inputs and renders the game visually. This shows
exactly what the game looks like from the proof system's point of view —
same witness values, same CPU behavior, same bus operations. See
[§8.6](#86-replay-mode) for the full architecture.

All modes use the same `GbCpu<B: Bus>` and the same `step()` function.
The difference is granularity of control, what data crosses the WIT
boundary, and the source of external inputs (live peripherals vs
recorded trace).

**Trace bandwidth**: A rough estimate for trace/record mode. A frame is
70,224 T-cycles = 17,556 M-cycles. The number of steps per frame depends
on the game: each step consumes at least 1 M-cycle (HALT) and typically
2-4 M-cycles (normal instructions average ~3). A HALT-heavy game (common
— game logic during VBlank, HALT the rest) produces ~15,000 steps; a busy
game ~10,000; the upper bound is ~17,500 (every M-cycle is a 1-cycle HALT
step). Per-step size varies thanks to the `witness-snapshot` variant
encoding: a HALT step is ~37 bytes (12 + 12 regs + 4 metadata + 0 bus ops
+ 1 witness `none` + 8 bank state), while a full instruction with
witnessed register reads is ~71 bytes (regs + metadata + ~30 bus ops + 5
witness `full` + bank state). For the upper bound (17,500 steps, mostly
HALT): ~0.65 MB/frame or ~39 MB/s. For a busy game (10,000 steps, heavier
instructions): ~0.5 MB/frame or ~30 MB/s. A one-minute record session
generates ~1.8-2.3 GB uncompressed. Compression is recommended for replay
files — the data is highly structured (many repeated opcodes,
slowly-changing registers, long runs of trivial HALT rows) and should
compress well. In stream mode, the proof system must consume steps at
this rate to keep up with real-time emulation.

### 8.2 Per-Step Export

In trace mode, each step produces a **step record** that the host reads
via WIT exports:

**Step metadata** (from `StepResult`, see [§4.4](#44-step-function)):
- Opcode byte (or CB-prefixed opcode)
- Step type (normal instruction, interrupt dispatch, halt, stop)
- Cycle count
- Whether the halt bug fired

**Register snapshots**: The full `RegisterFile` before and after the step.
The host takes the "before" snapshot, calls `step()`, then reads the
"after" state. Both snapshots cross the WIT boundary as flat byte arrays
(A, F, B, C, D, E, H, L, SP-lo, SP-hi, PC-lo, PC-hi = 12 bytes).

**Bus operation log**: Every `Bus::read()` and `Bus::write()` call during
the step, in order. Each entry is `(address: u16, value: u8, is_write: bool)`.
The bus implementation buffers these during `step()` and the host reads the
buffer afterward.

The maximum number of bus operations per step is bounded
([§7.2](#72-per-step-bus-operation-budget)), so the buffer has a fixed
upper size.

**Witness values** (from [§6.5](#65-witness-tape-architecture)):
Encoded as a `witness-snapshot` variant — `none` when no external
interrupts fired and no witnessed registers were read (the common case),
`irq-only(u8)` when only external interrupts fired, or `full` with all
four values (buttons, external-irqs, stat, ly) when the step read a
witnessed register. See [§8.6](#86-replay-mode) for the WIT definition.

These are recorded at the step boundary (after the previous step's
peripheral tick, before the current step's `cpu.step()`).

Together, these pieces form the logical **trace row** for one step. The
concrete struct layout and serialization format are integration concerns
— this document defines the semantic content and ordering
([§8.4](#84-wit-interface-for-trace-mode)), not the wire format.

### 8.3 Bus Operation Buffering

In play mode, the bus executes operations directly with no logging
overhead. In trace mode, a **logging bus** wraps the runtime bus and
records each operation:

```rust
pub struct LoggingBus<B: Bus> {
    inner: B,
    log: Vec<BusOp>,  // cleared between steps
}
```

This is a bus implementation like any other — the CPU doesn't know it
exists. The host reads the log after each step via a WIT export, then the
log is cleared before the next step.

The logging bus also exposes the inner bus's banking state (current ROM
bank, RAM bank) and witness values ([§6.5](#65-witness-tape-architecture))
through additional WIT accessors. This avoids the host needing to
reconstruct banking state from the bus operation log.

### 8.4 WIT Interface for Trace Mode

The trace-mode WIT interface extends the play-mode interface with
step-level functions:

```wit
/// Trace-mode execution — host drives step by step
resource trace-session {
    /// Create from a loaded ROM
    constructor(rom: list<u8>);

    /// Read current register state (12 bytes)
    get-registers: func() -> list<u8>;

    /// Execute one CPU step, return metadata
    step: func() -> step-result;

    /// Read bus operations from the last step
    drain-bus-log: func() -> list<bus-op>;

    /// Read current witness values
    get-witness: func() -> witness-snapshot;

    /// Tick peripherals after step (timer, PPU, APU)
    /// Returns which external interrupts fired
    tick-peripherals: func(m-cycles: u32) -> u8;

    /// Read current MBC banking state
    get-bank-state: func() -> bank-state;
}
```

The host loop for trace generation:

```
// Before loop: capture initial peripheral state
witness = get-witness()
irq_bits = 0          // no external IRQs before first step
bank = get-bank-state()

// Per step:
1. witness_before = witness       // carried from previous iteration
2. irq_before = irq_bits         // carried from previous iteration
3. bank_before = bank            // carried from previous iteration
4. regs_before = get-registers()
5. result = step()               // CPU executes, bus log fills
6. bus_ops = drain-bus-log()
7. regs_after = get-registers()
8. irq_bits = tick-peripherals(result.m_cycles) // advance PPU/timer/APU
9. witness = get-witness()       // post-tick state for NEXT step
10. bank = get-bank-state()
11. Assemble trace row from: regs_before, regs_after, result,
    bus_ops, witness_before, irq_before, bank_before
```

**Timing note**: Steps 8-10 produce the peripheral state AFTER this
step's tick — these values are what the NEXT step's CPU will observe.
The trace row for step N uses `witness_before` and `irq_before` (from
the previous iteration), not the freshly-read values. This matches the
proof model in [`provability.md` §4](provability.md#4-the-if-register-model):
external IRQs are applied after the CPU step and become visible to the
next step.

Steps 8-9 separate peripheral ticking from the CPU step, matching
[§6.1](#61-per-instruction-ticking). The host sees the same boundary the
emulator uses internally.

**`bank-state` contents**: The record includes both raw MBC register
values and effective bank numbers. Raw values (BANK1, BANK2/RAM bank,
mode, RAM enable — per the [§5](#5-rom-and-banking) register table) let
the integration layer track register mutations as proof events. Effective
values (the actual ROM bank mapped at $4000-$7FFF, the actual RAM bank
at $A000-$BFFF) let it select the correct per-bank lookup table. The
host can derive effective from raw using MBC-type-specific logic
(zero-adjust, masking), but exporting both avoids duplicating MBC decode
logic on the host side.

**`witness-snapshot` contents**: Defined as a WIT variant in
[§8.6](#86-replay-mode). Three cases: `none` (no external interrupts,
no witnessed register reads — the common case), `irq-only(u8)` (only
external interrupt bits), or `full(witness-full)` (buttons, external-irqs,
stat, ly). The variant encoding keeps trace size compact: most steps are
`none` (1 byte tag), with `full` only needed when the CPU actually reads
$FF00, $FF41, or $FF44. These are the witness inputs described in
[§6.5](#65-witness-tape-architecture).

**`tick-peripherals` return value**: A bitmask of external interrupts
that fired this step, using IF bit positions: bit 0 = VBlank, bit 1 =
STAT, bit 4 = joypad. Timer interrupt (bit 2) is **excluded** — it is
proven independently by the integration layer
([§6.2](#62-timer)). The host records these bits for the witness tape
and the integration layer OR's them into its Computed IF model
([§6.3](#63-computed-registers-if-joyp)).

**Bank state tracking for ROM decomposition**: Bank state cannot change
mid-instruction — only MBC register writes ($0000-$7FFF writes) alter it,
and the change takes effect on the next instruction's fetch. So all ROM
reads in a step use the bank state from *before* the step. The host
tracks this across loop iterations: `bank_before` for step N is `bank`
from step N-1 (or the known initial bank state for step 0: bank 0 for
MBC1/2/3, bank 1 for MBC5). This gives the integration layer the bank
context needed to decompose each $4000-$7FFF read into a per-bank lookup
([§5](#5-rom-and-banking)).

### 8.5 Bulk Data Export

Some data is per-ROM rather than per-step and can be exported once:

- **ROM bank tables**: The host already has the ROM data (passed to the
  trace-session constructor). It splits the ROM into per-bank tables
  (16KB each) to build read-only lookup tables for the proof. No
  additional WIT export is needed — the host knows the MBC type from
  the ROM header and can derive bank boundaries itself.
- **ALU lookup tables**: Built from the pure ALU functions
  ([§4.3](#43-pure-alu)). Can be built on either side of the WASM
  boundary — the host can call the same pure functions, or the guest
  can export precomputed tables.
- **Opcode register table**: The static 512-entry table mapping each
  opcode to its register read/write pattern
  ([§7.4](#74-register-events-from-opcode-table)). Exported once.

### 8.6 Replay Mode

Replay mode re-executes a previously-recorded trace, allowing the user
to see the game exactly as the proof system would see it. This is a
debugging and validation tool: if replay produces different results than
the original execution, there is a bug in the trace pipeline.

#### The replay file

The replay file IS the trace from record mode — the same data the proof
system consumes. It contains:

- **Header**: ROM hash (to verify the correct ROM is loaded), initial
  state (post-boot register values, MBC type)
- **Per-step records**: Witness values (button state, external interrupt
  bits, STAT, LY), step metadata (opcode, step type, cycle count)

Optionally, the replay file can include per-step register snapshots and
bus operation logs for full verification. The minimal replay file (header
+ witness values only) is sufficient to reproduce execution, since the
emulator is deterministic given the same witness inputs.

The concrete binary format (field encoding, compression, framing) is an
implementation detail outside this architecture document. What matters is
the logical content described above.

#### Replay execution

The host loads the replay file and drives the emulator step-by-step,
injecting recorded witness values before each step:

1. Load ROM from hash, initialize emulator
2. For each step in the replay file:
   a. `inject-witness(w)` — inject the full witness snapshot from the
      replay (buttons, external IRQs, STAT, LY)
   b. `step()` — CPU executes using injected witness values
   c. `tick-peripherals(m_cycles)` — PPU/timer/APU advance for rendering
   d. Optionally verify: do registers, bus ops match the recorded values?
      Compare live PPU's STAT/LY against injected values to detect drift.
   e. Render the frame (PPU produces scanlines from CPU's writes)

The emulator is deterministic by construction: per-instruction ticking
([§6.1](#61-per-instruction-ticking)), fixed PPU timing, and identical
initial state mean the same button inputs produce the same execution.
STAT, LY, and external interrupts are all derivable from the button
sequence (because the PPU is deterministic from CPU execution). Replay
injects ALL recorded witness values to show the exact proof system
perspective, and compares the live PPU's derived values against them —
any discrepancy reveals a bug in the emulator or trace pipeline.

#### WIT requirements

Replay mode extends the trace-session WIT interface with full witness
injection:

```wit
/// Full witness data — only needed when the step reads witnessed registers
record witness-full {
    buttons: u8,         // 8-bit button state, active-low
    external-irqs: u8,   // bits 0,1,4 = VBlank, STAT, joypad
    stat: u8,            // full STAT byte ($FF41)
    ly: u8,              // scanline counter ($FF44)
}

/// Per-step witness — variant encoding for compact traces.
/// Most steps need no witness data at all.
variant witness-snapshot {
    /// No external interrupts fired, no witnessed registers read.
    /// The vast majority of steps (HALT, normal non-IO instructions).
    none,
    /// External interrupts fired, but no witnessed registers read.
    /// Occurs at VBlank/STAT/joypad interrupt boundaries.
    irq-only(u8),
    /// Step read one or more witnessed registers ($FF00, $FF41, $FF44)
    /// and/or external interrupts fired.
    full(witness-full),
}

resource trace-session {
    // ... existing functions from §8.4 ...

    /// Inject witness values for the next step (replay mode).
    /// When set, the emulator uses these instead of live peripheral
    /// outputs for STAT/LY reads and external interrupt injection.
    inject-witness: func(w: witness-snapshot);
}
```

When `inject-witness` has been called before `step()`, the emulator
uses the injected values instead of live peripheral outputs:
- `none`: No external interrupts applied, witnessed register reads
  return defaults (buttons=$FF, stat/ly from live PPU — not expected
  to be read, but safe if they are)
- `irq-only(bits)`: External interrupt bits OR'd into IF; no witnessed
  register overrides
- `full(w)`: External interrupt bits from `w.external-irqs`, STAT/LY
  reads return `w.stat`/`w.ly`, button state from `w.buttons`

The host still calls `tick-peripherals()` to advance the PPU/timer/APU
(keeping the live emulator in sync for rendering), but the CPU-visible
values come from the injection. This shows the exact proof system
perspective: the CPU sees the same witness values the proof constrains.

If the live PPU's output diverges from the injected values, the
rendering (driven by live PPU) and the CPU's behavior (driven by
injected witnesses) may differ — this divergence IS the debugging
signal that replay is designed to surface.

#### Witness completeness

The witness snapshot must include every value that cannot be inferred
from deterministic CPU execution alone. The variant encoding captures
exactly what each step needs: `none` for steps with no external input,
`irq-only` when only interrupts fired, and `full` when the CPU read a
witnessed register (buttons via $FF00, STAT via $FF41, LY via $FF44).
The emulator determines the correct variant by observing which
witnessed registers were read during the step (visible in the bus
operation log) and whether `tick-peripherals` returned nonzero IRQ bits.

#### Why replay matters

- **Proof validation**: Verify that a trace is self-consistent before
  spending resources on proof generation
- **Debugging**: If replay diverges from the original execution, the
  divergence point reveals a bug in the emulator or trace pipeline
- **User transparency**: Show players exactly what their proof covers —
  the game as the proof system constrains it, with no hidden state

---

## 9. Initial State

All memory regions start at **all zeros** (see
[`provability.md` §5.10](provability.md#510-initial-state) for rationale,
particularly ERAM's anti-injection property). CPU registers start at
`RegisterFile::post_boot_dmg()`. No boot ROM — start at PC=$0100.

All-zeros initialization has a proof-side benefit: the initial memory
commitment is trivial (a known polynomial), so only addresses actually
written during execution need non-trivial entries.

---

## 10. Static ROM Validation

At ROM load time, scan for instructions reading unproven addresses. The
definitive address map is [`provability.md` §6](provability.md#6-complete-classification).

- **Direct**: `$F0 xx` (LDH A,[xx]) and `$FA lo hi` (LD A,[nnnn]) — fully
  detectable
- **Indirect**: `$F2` (LDH A,[C]), `$7E` (LD A,[HL]), etc. — static
  analysis limited; fall back to runtime check during trace generation

For indirect reads that escape static analysis, the logging bus
([§8.3](#83-bus-operation-buffering)) provides a runtime fallback: since
it records every bus operation, it can detect reads from unproven
addresses during trace generation and flag the trace as unprovable.

The proof system enforces this independently (unproven addresses have no
proof mechanism → unsatisfiable constraints). The static scan and runtime
check are fast-fail mechanisms to reject incompatible ROMs before the
host attempts proof generation.

---

## 11. Testing expectations

The architecture of this ideal emulator leads to some expected test failures.

More information about which tests are run, which are expected to fail, and why can be found in [`testing.md`](testing.md)

---
