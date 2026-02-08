# nightboy — Progress Tracker

## Completed

### CPU Emulator (standalone)

- [x] Workspace scaffolding (`memory` + `cpu` crates, `no_std` compatible)
- [x] Bus trait with `&mut self` (enables future TracingBus without RefCell)
- [x] TestBus — flat 64KB RAM with LY=0x90 stub
- [x] RegisterFile — flag accessors, pair accessors, AF masking, post-boot DMG state
- [x] Pure ALU — all operations return `AluResult { value, flags }`, no mutation
  - `alu_binary` (ADD/ADC/SUB/SBC/AND/XOR/OR/CP)
  - `alu_inc`, `alu_dec`
  - `alu_daa` (BCD correction, offset from original A)
  - `alu_shift` (RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL)
  - `alu_bit`, `alu_add_hl`, `alu_add_sp_i8`
- [x] Instruction types — sub-enum hierarchy (Load, U8Arith, U16Arith, BitShift, Jump, Stack, Flag, InterruptCtl, Misc)
- [x] Decoder — block-based (opcode >> 6), all 256 main + 256 CB-prefix opcodes
- [x] Execution — match-based dispatch, correct cycle counts for taken/not-taken branches
- [x] GbCpu step loop — decode → execute → EI delay → interrupt handling
- [x] Interrupt dispatch — priority by lowest bit, synthetic CALL to vector, 5 M-cycles
- [x] EI delay — deferred by 1 instruction, DI cancels pending EI
- [x] HALT — wake on IE & IF match, 1 M-cycle per halted tick
- [x] HALT bug — IME=false + pending interrupt: next opcode byte read twice
- [x] STOP — sets stopped flag (minimal implementation)

### Test Coverage (117 tests)

- [x] Exhaustive ALU: ADD, SUB, ADC, SBC — 262K iterations each for value + all 4 flags
- [x] Unit tests for every instruction category (registers, ALU, decode, execute, cpu)
- [x] Decode coverage: all 512 opcodes decode without panic, instruction lengths verified
- [x] Blargg cpu_instrs: all 11 tests pass (01-special through 11-op a,(hl))
- [x] Blargg instr_timing: pass (validates all cycle counts)
- [x] Blargg halt_bug: pass (validates HALT bug with 9 IE/IF combinations)

### Test Harness (BlarggBus)

- [x] Serial output capture (0xFF01/0xFF02)
- [x] Timer emulation (DIV, TIMA, TMA, TAC with correct prescaler frequencies)
- [x] V-Blank interrupt generation (every 70224 T-cycles)
- [x] IF register upper-bit masking (bits 7-5 always read as 1)
- [x] VRAM scanning for console-only ROMs (halt_bug has no serial output)
- [x] Tight-loop detection (catches `JR -2` forever loops, ignores HALT)

### Nightstream zkVM Integration — Phases 1–3

Code lives in `nightstream/crates/neo-memory/src/sm83/`. 51 tests pass across all three phases.

#### Phase 1: Shout Lookup Tables (17 tests)

- [x] `GbOpcode` enum — 34 variants (carry-split ADC/SBC/RL/RR, 8 BIT tests, 4 DAA tables)
- [x] `GbInstruction` sub-enum hierarchy mirroring nightboy (Load, U8Arith, U16Arith, BitShift, Jump, Stack, Flag, InterruptCtl, Misc)
- [x] `gb_interleave` / `gb_uninterleave` — 8-bit specialization packing two operands into u16 key
- [x] `compute_op()` — pure ALU adapted from nightboy, returns packed u16 `(flags << 8) | result`
- [x] `GbShoutTables` implementing `Shout<u16>` — 34 ShoutIds mapped to ALU operations
- [x] Exhaustive cross-validation: all 65,536 input pairs verified for every opcode

#### Phase 2: VmCpu Trait Implementation (18 tests)

- [x] `Sm83Cpu` implementing `VmCpu<u16, u16>` — full 512-opcode dispatch
- [x] `Sm83Memory` implementing `Twist<u16, u16>` — sparse HashMap-based, F register masked to 0xF0
- [x] `decode_at()` — byte-buffer decoder adapted from nightboy (3-byte fixed buffer)
- [x] Regfile-as-Twist model: `PROG_ID=TwistId(0)`, `REG_ID=TwistId(1)`, `RAM_ID=TwistId(2)`
- [x] Register addresses: A=0, F=1, B=2, C=3, D=4, E=5, H=6, L=7, SP_lo=8, SP_hi=9
- [x] Variable-length fetch using `load_if_lane()` for conditional PROG reads (1–3 bytes)
- [x] 16-bit arithmetic (ADD HL, INC/DEC r16, ADD SP e8) computed in-CPU without Shout
- [x] Lane-based register access: lane 0 for primary src/dst, lane 1 for secondary
- [x] Oracle cross-validation against nightboy for representative programs

#### Phase 3: ExecTable Pipeline (16 tests)

- [x] `Sm83ExecRow` / `Sm83ExecTable` — structured per-instruction rows from VmTrace
- [x] Validation methods: `validate_pc_chain`, `validate_cycle_chain`, `validate_halted_tail`, `validate_inactive_rows_are_empty`, `validate_prog_reads`, `validate_regfile_semantics`, `validate_ram_semantics`
- [x] `Sm83RegEventTable`, `Sm83RamEventTable`, `Sm83ShoutEventTable` — ordered event tables with prev/next values
- [x] `from_trace_padded()` / `from_trace_padded_pow2()` — power-of-two padding for NTT-friendly sizing
- [x] Tamper detection: validation catches corrupted pc_after, register values, etc.

## Not Started

### Nightstream zkVM Integration — Remaining Phases

The following phases correspond to steps 4, 7b, 8, and 9 of `plan/adding-new-opcode-set.md`.

#### Phase 4: MLE Evaluations

- [ ] Naive MLE evaluator for 8-bit tables (O(2^16) per evaluation — feasible for all SM83 tables)
- [ ] Optional closed-form MLEs for AND, XOR, OR, ADD, SUB (word-size independent formulas from RISC-V)
- [ ] `evaluate_opcode_mle()` dispatcher selecting naive vs closed-form per opcode
- [ ] Cross-validate MLE evaluations against precomputed table values at Boolean points

Reference: `nightstream/.../riscv/lookups/mle.rs`

#### Phase 5: Trace Layout & Witness (column-major)

- [ ] `Sm83TraceLayout` — column-major layout defining columns for control, fetch, regfile, RAM, Shout views
- [ ] Handle variable-length instructions: 3 PROG columns (prog_addr0/1/2, prog_value0/1/2, prog_has_read1/2)
- [ ] `Sm83TraceWitness::from_exec_table()` — fill column-major matrix from ExecTable
- [ ] Sidecar extraction: Twist/Shout lane extraction for bus region

Reference: `nightstream/.../riscv/trace/layout.rs`, `nightstream/.../riscv/trace/witness.rs`, `nightstream/.../riscv/trace/sidecar_extract.rs`

#### Phase 6: CCS Constraint System

- [ ] `Sm83TraceCcsLayout` / `Sm83TraceTwistCcsLayout` — CCS layout wrapping trace with public I/O and bus region
- [ ] Wiring constraints: boolean columns, inactive padding, PC chain, cycle chain, active/halted monotonicity
- [ ] Instruction-length constraint: `pc_out = pc_in + 1×is_one_byte + 2×is_two_byte + 3×is_three_byte`
- [ ] Bus bindings for PROG (read-only, 3 lanes), REG (read+write, laned), RAM (read+write), Shout
- [ ] Address bit packing constraints for Twist subprotocol
- [ ] Canonical padding constraints for unused bus cells
- [ ] Witness generation: `sm83_trace_twist_ccs_witness_from_exec_table()`
- [ ] `ccs.check_witness_xw(&x, &w)` satisfiability test

Reference: `nightstream/.../riscv/ccs/trace.rs`, `nightstream/.../riscv/ccs/constraint_builder.rs`

#### Phase 7: Integration & End-to-End Testing

- [ ] Shard/session pipeline integration (`Sm83ProverConfig`)
- [ ] End-to-end test: ROM → trace → ExecTable → witness → CCS → verify constraints
- [ ] Blargg test ROMs through full trace + ExecTable validation pipeline (requires I/O stub from recorded traces)
- [ ] Neo folding: IVC fold → accumulate → final proof

### Beyond CPU (not currently in scope)

- [ ] PPU (picture processing unit)
- [ ] APU (audio processing unit)
- [ ] Cartridge mappers (MBC1/2/3/5)
- [ ] DMA controller
- [ ] Serial link
- [ ] Joypad input
