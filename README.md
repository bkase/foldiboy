# Nightboy (zk-gameboy)

A provable implementation of the Game Boy's Sharp LR35902 (SM83) CPU, built for the [Nightstream](../nightstream/) zkVM.

- **Lookup-first architecture**: ALU operations are proven via Shout lookup tables rather than in-circuit arithmetic, making it straightforward to plug in a new opcode set.
- **Memory checking arguments**: RAM and register correctness is proven via Twist memory arguments, not just CPU instruction constraints.
- **Folding schemes**: Neo's IVC folding enables efficiently proving long-running programs like a full console boot.

## Repository layout

This workspace contains the **reference emulator** — a standalone, fully tested SM83 CPU:

```
nightboy/
  lib/crates    Implementation of the emulator itself
    cpu/        Pure SM83 CPU: decode, execute, ALU, registers (all 512 opcodes)
    memory/     Bus trait, TestBus, BlarggBus test harness
    render/     Rendering logic for the screen was a Wasm Component for a host the implements WebGPU
  host/         Different frontends for running the emulator
    desktop/    wasmtime-based desktop app using wasi-gfx to extend the host to support WebGPU
```

The **Nightstream integration** (the provable version) lives in the Nightstream repo:

```
nightstream/crates/neo-memory/src/sm83/
  lookups/
    isa.rs      GbOpcode, GbInstruction, GbReg8 — ISA type definitions
    alu.rs      compute_op() — pure ALU returning packed (flags << 8 | result)
    bits.rs     gb_interleave/gb_uninterleave — operand packing into Shout keys
    tables.rs   GbShoutTables — 34 ShoutIds implementing Shout<u16>
    decode.rs   decode_at() — byte-buffer decoder for Twist-based fetch
    cpu.rs      Sm83Cpu — VmCpu<u16, u16> impl (trace-producing CPU)
    memory.rs   Sm83Memory — Twist<u16, u16> impl (sparse HashMap-based)
  exec_table.rs Sm83ExecTable — structured trace rows, validation, event tables
```

## How the two halves fit together

The reference emulator (`nightboy/crates/cpu`) is the **source of truth** for SM83 semantics. It passes all 11 Blargg `cpu_instrs` tests, `instr_timing`, and `halt_bug` — 117 tests total covering every opcode, flag edge case, and timing behavior.

The Nightstream integration (`nightstream/.../sm83/`) is a **re-implementation of the same CPU** that speaks Nightstream's trait protocol (`VmCpu`, `Twist`, `Shout`). Instead of reading memory directly, it goes through `Twist` (which records every access). Instead of computing ALU results inline, it calls `Shout` lookups (which the prover can verify). The result is a CPU whose execution trace is structured for zero-knowledge proving.

The ALU functions in the integration were adapted from `nightboy/crates/cpu/src/alu.rs` and are exhaustively cross-validated — every opcode is tested against all 65,536 input pairs to ensure bit-identical behavior. The CPU trace is further validated by oracle comparison: running the same programs through both implementations and comparing register state, memory accesses, and PC transitions step by step.

```
nightboy (reference emulator)          nightstream/sm83 (provable CPU)
┌─────────────────────────┐              ┌──────────────────────────────┐
│  GbCpu<Bus>             │  validates   │  Sm83Cpu: VmCpu<u16, u16>   │
│  alu_binary/shift/daa   │ ──────────>  │  compute_op() via Shout     │
│  Bus::read/write        │              │  Twist::load/store          │
│  All 512 opcodes        │              │  All 512 opcodes            │
└─────────────────────────┘              └──────────┬───────────────────┘
                                                    │ trace_program()
                                                    ▼
                                         ┌──────────────────────────────┐
                                         │  VmTrace<u16, u16>           │
                                         │    → Sm83ExecTable           │
                                         │    → Event tables            │
                                         │    → (future) Witness → CCS  │
                                         └──────────────────────────────┘
```

## Current status

- **Reference emulator**: Complete. All opcodes, interrupts, HALT bug, timing.
- **Nightstream Phases 1-3**: Complete (51 tests). Shout tables, VmCpu, ExecTable with validation.
- **Remaining**: MLE evaluations, column-major trace witness, CCS constraints, end-to-end proving.

See [TODO.md](./TODO.md) for detailed progress tracking.
