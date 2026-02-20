# Provability Considerations

Foldiboy is designed as a ZK-optimized Gameboy emulator.
Notably, we assume that this zkVM is:
- Folding-based
- Lookup-based

Therefore, we need to very explicitly decide how we handle the provability of every concept in the Gameboy to ensure soundness.

## 1. The Machine Cycle

At its core, a CPU is made up of:
- `T-cycle`: one tick of the CPU’s main clock
- `M-cycle`: one machine cycle (ex: add two values)
- `instruction cycle`: one opcode (ex: `ADD A, (HL)` is two M-cycles as it needs to fetch from memory, then add)

However, the zkVM's cycles do not necessarily align with the real Gameboy's machine cycles. This is become operations such as opcodes are not necessarily in the format we desire in our proof system.

There are two main reasons for this:
1. **Efficiency**: some operations are faster as lookups compared to proving the raw computation.
For example, in riscv's `div` opcode (which doesn't exist on the Gameboy, as is just an example),
it's faster to check (as `a*x + r = b`) than it is to compute (`b/x = a with remainder r`).
Therefore, whenever we see such an operator in the ROM, we rewrite it to this expanded operator (see later sections for more detail). Some operations may even require multiple lookups, which we denote **Lookup [N]** (indicating it needs N lookups to accomplish)
2. **Atomicity**: some opcodes are not atomic, but the proof system needs everything broken up into atomic steps.
For example, in riscv's `lw x3, 4(x4)` operation, we have to compute a `4(x4)` offset before computing the main opcode. Notably, this important for cases where:
    1. The result of the expansion is statically known (ex: does not depend on the value of the registers). This can occur in a few different ways
        1. **Op-limit [N]**: `lw x3, 4(x4)` exceeds the number of logical operations we can do in a single zk-cycle *(instead, needs N operations)*, but we can expand it into an `add` followed by `lw`.
        2. **RAM-limit [N]**: some opcode sets have instructions that do more read/writes than may be supported in a single zk-cycle *(instead, needs N operations)*, but can be split up into multiple read & writes.
        3. **Case**: some opcode sets have different behavior depending some statically known labels (ex: `swap r1, r1` may have some special behavior compared to `swap r1, r2`)
        4. **Cond [_]**: some opcode sets have instructions that implicitly depends on a separate state. We specify the implicit state in `[_]`.
        5. **Wide**: some opcode sets allow atomic operations on values larger than a single register (ex: represent 64-bits as two 32-bit registers)
    2. The result of the execution is not statically known (ex: in `lw x3, 4(x4)`, the offset is dynamic (based on `x4`) and not static (ex: a constant `0xA000` offset))

## 2. SM83 realities

SM83 (used by the Gameboy) consists of eight 8-bit registers: A,B,C,D,E,F,H,L.
These consist of
- `A, B, C, D, E, H, L` are used as 7 general-purpose 8-bit registers
- `F` is used as a flag register, containing Z, N, H, C (stored in upper nibble of F)

Additionally, register pairs are used for 16-bit addressing and arithmetic
- BC, DE: general purpose
- AF: restricted (compared BC,DE), as F is a flag register (ex: no `LD AF`)
- HL: extended (compared to BC,DE) as HL can be used as a memory pointer (ex: `LD A,(HL)` has `(HL+)` and `(HL-)` variants)

Restrictions on what opcodes can do (or pairs of opcodes can do like `AF`) are implemented at the opcode level.
For example, `LD` is not a real opcode. Rather, it's a family of opcodes. Each different combination of `LD` usage is a different "opcode"
- `LD BC,u16` is an opcode (opcode `0x01`)
- `LD DE,u16` is an opcode (opcode `0x11`)
- `LD AF,u16` is not an opcode (does not exist in the opcode table)

There are also two 16-bit registers
- `SP` for the stack pointer
- `PC` for the program counter

The architecture is accumulator-centric: almost every ALU op is `A ← A op src`

## 3. zk-cycle model

The goal of the zk-cycle, therefore, is to find the minimal amount of expressivity we need to be able to prove every instruction cycle (possibly by breaking it down, adding new virtual opcodes, etc.)

### 3.1 How many register operations do we need in a zk-cycle?

Many opcodes implicitly access registers, making the answer trickier than it sounds.

For example, `ADD HL,DE`:
- Reads 4 registers (H,L,D,E for the input)
- Writes 2 registers (H,L for the result of the addition)
- (implicit) Read & Writes to the PC
- (implicit) Read & Writes to F (read to preserve unmodified flags, F to add in new flag state)

Therefore, we split the task up into different considerations:

#### 3.1.1 Register READs

Although many (~20%) of the SM83 opcodes read from 2 registers, the following few read from more:
- Instructions that take 3 reads (~3% of opcodes)
    - `LD (BC),A`
    - `LD (DE),A`
    - `LD (HL+),A`
    - `LD (HL-),A`
    - `LD (HL),B`
    - `LD (HL),C`
    - `LD (HL),D`
    - `LD (HL),E`
    - `LD (HL),A`
    - `ADD A,(HL)`
    - `ADC A,(HL)`
    - `SUB A,(HL)`
    - `SBC A,(HL)`
    - `AND A,(HL)`
    - `XOR A,(HL)`
    - `OR A,(HL)`
    - `CP A,(HL)`
- Instructions that take 4 reads
    - `ADD HL,BC`
    - `ADD HL,DE`

While these instructions fortunately have very natural expansions, there are two main considerations for expanding these opcodes:
1. **Effect on the trace size (height):**: If one of these instructions is extremely common, then expanding it may make the trace longer (growing proof time)
1. **Effect on the things to track (width):**: for example, to break up an opcode like `LD (BC),A`, we have to
    1. Track the intermediate result of `(BC)` into an intermediate state: `TEMP = BC`
    2. Have a new opcode to do a 16-bit register LD (as there is no variant of `LD` that access a 16-bit register)

Therefore, to decide if we want to expand these or not, we have to consider how often they are used in actual games (to know the effect on the trace size).

- 4-read `ADDs`
    1. For Pokemon Red's title screen, 1~2% of executed opcodes are 4-read `ADD`s - primarily coming from the audio system
    2. For Tetris's title screen, <0.1% of executed opcodes are 4-read `ADD`s
- 3-read opcodes
    1. For Pokemon Red's title screen, ~5% of executed opcodes are 3-read opcodes
    2. For Tetris's title screen, ~17% of executed opcodes are 3-read opcodes

Therefore, the sweet spot seems to be 3 reads per zk-cycle, as splitting up 3-read writes would make Tetris's trace ~17% longer (larger height) only for a small change in width (one less register read column in the trace - a smaller than 17% change).

#### 3.1.2 Register WRITEs

Although most opcodes use 0-1 write, 19 opcodes write to 2 registers. These represent:
1. `LD` to 2-digit registers (or to memory addresses represented by 2-digit registers)
2. `INC`/`DEC` from 2-digit registers
3. `POP`ing to 2-digit registers
4. `ADD`ing to 2-digit registers

Given these kinds of operations are extremely common, it's not worth expanding them

However, two opcodes specifically require 3 registers:
- `LD A,(HL+)`
- `LD A,(HL-)`

but these are easily expanded (as `HL+` an `HL-` are easy to expand into separate operations)

Therefore, the sweet spot seems to be 2 writes per zk-cycle.

#### 3.3.3 Final register model

we define the register state of any zk-cycle as follows:
```rust
pub trait InstructionRegisterState {
  pub reads: [Option<u8>; 3],
  pub writes: [Option<u8>; 2],
}
```

Note:
- which register is used by which value (ex: is `reads[0]` register A? B? C?) is implicit based on the opcode

#### 3.1.5 CPU state handled separately

Note that we explicitly do not include the following in `InstructionRegisterState`:
1. The `PC` register, as
    1. It's never explicitly used in an opcode (only implicit), so no need to ever put it inside `InstructionRegisterState`
    2. It has special behavior in relation to expanded opcodes (they don't increase the PC in the original ROM)
    3. Need to ensure PC points to a valid position (actually is in the code)
2. The `SP` register, as
    1. It's 16-bit, which would require breaking it up into parts to fit in `InstructionRegisterState`
    2. It's often implicitly used in opcodes (ex: `RET`) although it *does* occasionally explicitly appear (ex: `INC SP`)
    3. Handling it in `InstructionRegisterState` would mean we need 4 writes in some case (like `POP AF`)
3. The `F` register, as
    1. It appears implicitly in ~50% of opcodes
    2. It rarely appears explicitly (but does happen explicitly like `POP AF`, and implicitly like `CALL NZ,u16`)
4. Other implicit state (`HALT`, `IME`, `STOP`, etc.)

### 3.2 How do memory (RAM) operations work in a zk-cycle?

Note that
- Some opcodes read from RAM (ex: `LD A,(DE)`)
- Some opcodes write to RAM (ex: `LD (DE),A`)
- Some opcodes read AND write to RAM (ex: `INC (HL)`)

RAM access is not always explicit though, as the SP always points to a position in RAM, and so opcodes that affect the stack are also reading/writing to RAM (ex: `CALL` and `RET` modify RAM)

Additionally, although memory operations always use a 16-bit address,
- Some operations only read/write 8-bits (ex: `LD (HL),A` or `LD (FF00+C),A`)
- Some operations read/write two bytes:
    1. `1R+1W` to the same address (ex: `INC (HL)`). That's two bytes (but the same byte twice)
    2. `2R` from the consecutive addresses (ex: `POP rr` reads the stack (but doesn't clear it, so there are no writes))
    3. `2W` from the consecutive addresses (ex: `PUSH rr`)
- Some operations read from IO registers, which are not necessarily mapped to consecutive addresses
    - ex: `Halt` depends on `IE` and `IF` (mapped to `$FFFF` and `$FF0F` respectively)

This means we can model RAM reads & writes as follows:
```rust
pub struct RAMRead {
    pub address: u16,
    pub value: u8,
}
pub struct RAMWrite {
    pub address: u16,
    pub pre_value: u8,
    pub post_value: u8,
}
pub enum RAMAccess {
    Read(RAMRead),
    Write(RAMWrite),
    NoOp,
}
type MemoryOps = (RAMAccess, RAMAccess)
```

Note: We allow two RAM modifications per opcode. We don't constrain at the type-level that these have to either be the same address or sequential, but encode this in the constraints of the opcode.

#### 3.2.1 Memory Mapped IO

The Gameboy itself contains many memory-mapping IO fields (ex: `IE` and `IF`), and some opcodes depend on these fields (ex: `HALT`).

Typically, these would be tracked as separate IO state that is memory-mapped into RAM (from `$FF00-$FF7F`, as well as `$FFFF` for IE specifically). However, for simplicity, we consider the RAM as the *source of truth* for these values (so accessing them is a `RAMAccess` in our zk-cycle)

### 3.3 Virtual opcodes

Out of all the SM83 opcodes, the following need to be expanded

#### 3.3.1 Expansion Type Primer

General notes on the following tables:
- Updates triggered by opcodes are split in a few separate categories:
    - The key computation (the [ALU](https://en.wikipedia.org/wiki/Arithmetic_logic_unit)) is generally done with [Lookups](./constraints.md#1-lookup-tables)
        - Most operations use at most one lookup (ex: `INC r` uses a lookup for the increment result)
        - Some operations use two lookups per opcode. (ex: `INC rr` uses two lookups, one per register)\
            This is because generally for lookup systems,
            1. doing two 8-bit lookups is cheaper than a a single 16-bit lookup
            2. it allows us to re-use existing tables instead of having to store precomputed 8-bit and 16-bit variant
    - F is not explicitly included in `Reg R` or `Reg W`, but rather part of the `Flags` column. We also therefore don't specify `1 (F)` unless explicitly referenced (ex: `JR Z,i8`).
    - CPU state modifications are rare, but occur and are put in their own `CPU state` column
- All the opcodes (for reference) can be found [here](https://raw.githubusercontent.com/izik1/gbops/refs/heads/master/dmgops.json)

Note: although we previously outlined behavior that *could* require expansion (ex: *Wide*, *Cond*, etc.), Given our *specific* zk-cycle design outlined in [§3](#3-zk-cycle-model), we do not mention these in the `Expansion Type` unless they are required.

#### 3.3.2 Main Opcodes (0x00–0x3F)

| Opcode | Mnemonic | Expansion Type | Reg R | Reg W | RAM | Lookup | Flags | CPU State |
|--------|----------|----------------|-------|-------|-----|--------|-------|----------|
| 0x00 | NOP | None | 0 | 0 | — | [no-alu] | —— ||
| 0x01 | LD BC,u16 | None | 0 | 2 (B,C) | — | [no-alu] | —— ||
| 0x02 | LD (BC),A | None | 3 (A,B,C) | 0 | W | [no-alu] | —— ||
| 0x03 | INC BC | None | 2 (B,C) | 2 (B,C) | — | [INC]+[INC] | —— ||
| 0x04 | INC B | None | 1 (B) | 1 (B) | — | [INC] | z0h- ||
| 0x05 | DEC B | None | 1 (B) | 1 (B) | — | [DEC] | z1h- ||
| 0x06 | LD B,u8 | None | 0 | 1 (B) | — | [no-alu] | —— ||
| 0x07 | RLCA | None | 1 (A) | 1 (A) | — | [RLCA] | 000c ||
| 0x08 | LD (u16),SP | None | 0 | 0 | W+W | [no-alu] | —— | R (SP) |
| 0x09 | ADD HL,BC | OP-limit[4] | 4 (H,L,B,C) | 2 (H,L) | — | [ADD]+[ADC] | -0hc ||
| 0x0A | LD A,(BC) | None | 2 (B,C) | 1 (A) | R | [no-alu] | —— ||
| 0x0B | DEC BC | None | 2 (B,C) | 2 (B,C) | — | [DEC]+[DEC] | —— ||
| 0x0C | INC C | None | 1 (C) | 1 (C) | — | [INC] | z0h- ||
| 0x0D | DEC C | None | 1 (C) | 1 (C) | — | [DEC] | z1h- ||
| 0x0E | LD C,u8 | None | 0 | 1 (C) | — | [no-alu] | —— ||
| 0x0F | RRCA | None | 1 (A) | 1 (A) | — | [RRCA] | 000c ||
| 0x10 | STOP | None | 0 | 0 | — | [no-alu] | —— | W (STOP) |
| 0x11 | LD DE,u16 | None | 0 | 2 (D,E) | — | [no-alu] | —— ||
| 0x12 | LD (DE),A | None | 3 (A,D,E) | 0 | W | [no-alu] | —— ||
| 0x13 | INC DE | None | 2 (D,E) | 2 (D,E) | — | [INC]+[INC] | —— ||
| 0x14 | INC D | None | 1 (D) | 1 (D) | — | [INC] | z0h- ||
| 0x15 | DEC D | None | 1 (D) | 1 (D) | — | [DEC] | z1h- ||
| 0x16 | LD D,u8 | None | 0 | 1 (D) | — | [no-alu] | —— ||
| 0x17 | RLA | None | 1 (A) | 1 (A) | — | [RL] | 000c ||
| 0x18 | JR i8 | None | 0 | 0 | — | [no-alu] | —— | R (PC) W (PC) |
| 0x19 | ADD HL,DE | OP-limit[4] | 4 (H,L,D,E) | 2 (H,L) | — | [ADD]+[ADC] | -0hc ||
| 0x1A | LD A,(DE) | None | 2 (D,E) | 1 (A) | R | [no-alu] | —— ||
| 0x1B | DEC DE | None | 2 (D,E) | 2 (D,E) | — | [DEC]+[DEC] | —— ||
| 0x1C | INC E | None | 1 (E) | 1 (E) | — | [INC] | z0h- ||
| 0x1D | DEC E | None | 1 (E) | 1 (E) | — | [DEC] | z1h- ||
| 0x1E | LD E,u8 | None | 0 | 1 (E) | — | [no-alu] | —— ||
| 0x1F | RRA | None | 1 (A) | 1 (A) | — | [RR] | 000c ||
| 0x20 | JR NZ,i8 | None | 1 (F) | 0 | — | [no-alu] | —— | R (PC) W (PC) |
| 0x21 | LD HL,u16 | None | 0 | 2 (H,L) | — | [no-alu] | —— ||
| 0x22 | LD (HL+),A | None | 3 (A,H,L) | 2 (H,L) | W | [no-alu] | —— ||
| 0x23 | INC HL | None | 2 (H,L) | 2 (H,L) | — | [INC]+[INC] | —— ||
| 0x24 | INC H | None | 1 (H) | 1 (H) | — | [INC] | z0h- ||
| 0x25 | DEC H | None | 1 (H) | 1 (H) | — | [DEC] | z1h- ||
| 0x26 | LD H,u8 | None | 0 | 1 (H) | — | [no-alu] | —— ||
| 0x27 | DAA | None | 1 (A) | 1 (A) | — | [DAA] | z-0c ||
| 0x28 | JR Z,i8 | None | 1 (F) | 0 | — | [no-alu] | —— | R (PC) W (PC) |
| 0x29 | ADD HL,HL | None | 2 (H,L) | 2 (H,L) | — | [ADD]+[ADC] | -0hc ||
| 0x2A | LD A,(HL+) | Op-limit[3] | 2 (H,L) | 3 (A,H,L) | R | [no-alu] | —— ||
| 0x2B | DEC HL | None | 2 (H,L) | 2 (H,L) | — | [DEC]+[DEC] | —— ||
| 0x2C | INC L | None | 1 (L) | 1 (L) | — | [INC] | z0h- ||
| 0x2D | DEC L | None | 1 (L) | 1 (L) | — | [DEC] | z1h- ||
| 0x2E | LD L,u8 | None | 0 | 1 (L) | — | [no-alu] | —— ||
| 0x2F | CPL | None | 1 (A) | 1 (A) | — | [linear] | -11- ||
| 0x30 | JR NC,i8 | None | 1 (F) | 0 | — | [no-alu] | —— | R (PC) W (PC) |
| 0x31 | LD SP,u16 | None | 0 | 0 | — | [no-alu] | —— | W (SP) |
| 0x32 | LD (HL-),A | None | 3 (A,H,L) | 2 (H,L) | W | [no-alu] | —— ||
| 0x33 | INC SP | None | 0 | 0 | — | [INC]+[INC] | —— | R (SP) W (SP) |
| 0x34 | INC (HL) | None | 2 (H,L) | 0 | R+W | [INC] | z0h- ||
| 0x35 | DEC (HL) | None | 2 (H,L) | 0 | R+W | [DEC] | z1h- ||
| 0x36 | LD (HL),u8 | None | 2 (H,L) | 0 | W | [no-alu] | —— ||
| 0x37 | SCF | None | 0 | 0 | — | [const] | -001 ||
| 0x38 | JR C,i8 | None | 1 (F) | 0 | — | [no-alu] | —— | R (PC) W (PC) |
| 0x39 | ADD HL,SP | None | 2 (H,L) | 2 (H,L) | — | [ADD]+[ADC] | -0hc | R (SP) |
| 0x3A | LD A,(HL-) | Op-limit[3] | 2 (H,L) | 3 (A,H,L) | R | [no-alu] | —— ||
| 0x3B | DEC SP | None | 0 | 0 | — | [DEC]+[DEC] | —— | R (SP) W (SP) |
| 0x3C | INC A | None | 1 (A) | 1 (A) | — | [INC] | z0h- ||
| 0x3D | DEC A | None | 1 (A) | 1 (A) | — | [DEC] | z1h- ||
| 0x3E | LD A,u8 | None | 0 | 1 (A) | — | [no-alu] | —— ||
| 0x3F | CCF | None | 0 | 0 | — | [linear] | -00c ||

---

##### 3.3.2.1 handling `HL+`/`HL-`
- `LD A,(HL-)` will be expanded into `LD A,(HL);DEC HL`
- `LD A,(HL+)` will be expanded into `LD A,(HL);INC HL`

##### 3.3.2.2 handling 4-register `ADD`

For the four-register ADDs, we split them up into two smaller ADDs with one clever trick: typically we would need a new virtual register to store the temporary carry bit between the two add steps. However, note that `ADC` already has to modify the `F` register anyway. That means that the 2-register `ADD` can freely modify the `F` register to feed the carry into the `ADC`.

- `ADD HL,BC` will be expanded into 
    1. `ADD L,C`, `F=---c`
    2. `ADC H,B`, `F=-0hc`
- `ADD HL,DE` will be expanded into 
    1. `ADD L,E`, `F=---c`
    2. `ADC H,D`, `F=-0hc`

However, note that instructions such as `ADD L,C` do not exist on the Gameboy. To handle this, we override UNUSED opcodes slots to introduce these:

| Opcode | Mnemonic | Expansion Type | Reg R | Reg W | RAM | Lookup | Flags | Implicit |
|--------|----------|----------------|-------|-------|-----|--------|-------|----------|
| 0xD3 | ADD L,C | None | 2 (L,C) | 1 (L) | — | [ADD] | ---c ||
| 0xDB | ADC H,B | None | 2 (H,B) | 1 (H) | — | [ADC] | -0hc ||
| 0xDD | ADD L,E | None | 2 (L,E) | 1 (L) | — | [ADD] | ---c ||
| 0xE3 | ADC H,D | None | 2 (H,D) | 1 (H) | — | [ADC] | -0hc ||

[repurposed-ADD]: #3322-handling-4-register-add

Note: these virtual opcodes use the **same** ADD lookup table as `ADD A,r` and `ADC A,r`. The `ADC` virtual opcodes additionally apply the carry-in constraint ([§2.3.3](./constraints.md#233-carry-in-for-adcsbc)), taking carry from the preceding `ADD` step's F register output. The `---c` flag constraint means only the carry is written; Z/N/H are not updated

##### 3.3.2.3 handling 16-bit `INC`/`DEC`

INC rr and DEC rr operate on 16-bit register pairs but our registers are 8-bit. The carry/borrow from the low byte to the high byte is proven using two lookups from the **same** table (INC+INC or DEC+DEC) plus three R1CS constraints per cycle. No expansion is needed — this avoids doubling trace height for these very common operations.

Full constraint specification: [constraints.md §2.3.1](./constraints.md#231-incdec-rr--dual-lookup-carry-propagation).

Note: no flags are modified by INC/DEC rr — the flag outputs of both INC/DEC lookups are discarded by the circuit (no flag routing to F).

#### 3.3.3 Opcodes 0x40–0x7F (LD block + HALT)

| Opcode | Mnemonic | Expansion Type | Reg R | Reg W | RAM | Lookup | Flags | CPU State |
|--------|----------|----------------|-------|-------|-----|--------|-------|----------|
| 0x40 | LD B,B | None | 1 (B) | 1 (B) | — | [no-alu] | —— ||
| 0x41 | LD B,C | None | 1 (C) | 1 (B) | — | [no-alu] | —— ||
| 0x42 | LD B,D | None | 1 (D) | 1 (B) | — | [no-alu] | —— ||
| 0x43 | LD B,E | None | 1 (E) | 1 (B) | — | [no-alu] | —— ||
| 0x44 | LD B,H | None | 1 (H) | 1 (B) | — | [no-alu] | —— ||
| 0x45 | LD B,L | None | 1 (L) | 1 (B) | — | [no-alu] | —— ||
| 0x46 | LD B,(HL) | None | 2 (H,L) | 1 (B) | R | [no-alu] | —— ||
| 0x47 | LD B,A | None | 1 (A) | 1 (B) | — | [no-alu] | —— ||
| 0x48 | LD C,B | None | 1 (B) | 1 (C) | — | [no-alu] | —— ||
| 0x49 | LD C,C | None | 1 (C) | 1 (C) | — | [no-alu] | —— ||
| 0x4A | LD C,D | None | 1 (D) | 1 (C) | — | [no-alu] | —— ||
| 0x4B | LD C,E | None | 1 (E) | 1 (C) | — | [no-alu] | —— ||
| 0x4C | LD C,H | None | 1 (H) | 1 (C) | — | [no-alu] | —— ||
| 0x4D | LD C,L | None | 1 (L) | 1 (C) | — | [no-alu] | —— ||
| 0x4E | LD C,(HL) | None | 2 (H,L) | 1 (C) | R | [no-alu] | —— ||
| 0x4F | LD C,A | None | 1 (A) | 1 (C) | — | [no-alu] | —— ||
| 0x50 | LD D,B | None | 1 (B) | 1 (D) | — | [no-alu] | —— ||
| 0x51 | LD D,C | None | 1 (C) | 1 (D) | — | [no-alu] | —— ||
| 0x52 | LD D,D | None | 1 (D) | 1 (D) | — | [no-alu] | —— ||
| 0x53 | LD D,E | None | 1 (E) | 1 (D) | — | [no-alu] | —— ||
| 0x54 | LD D,H | None | 1 (H) | 1 (D) | — | [no-alu] | —— ||
| 0x55 | LD D,L | None | 1 (L) | 1 (D) | — | [no-alu] | —— ||
| 0x56 | LD D,(HL) | None | 2 (H,L) | 1 (D) | R | [no-alu] | —— ||
| 0x57 | LD D,A | None | 1 (A) | 1 (D) | — | [no-alu] | —— ||
| 0x58 | LD E,B | None | 1 (B) | 1 (E) | — | [no-alu] | —— ||
| 0x59 | LD E,C | None | 1 (C) | 1 (E) | — | [no-alu] | —— ||
| 0x5A | LD E,D | None | 1 (D) | 1 (E) | — | [no-alu] | —— ||
| 0x5B | LD E,E | None | 1 (E) | 1 (E) | — | [no-alu] | —— ||
| 0x5C | LD E,H | None | 1 (H) | 1 (E) | — | [no-alu] | —— ||
| 0x5D | LD E,L | None | 1 (L) | 1 (E) | — | [no-alu] | —— ||
| 0x5E | LD E,(HL) | None | 2 (H,L) | 1 (E) | R | [no-alu] | —— ||
| 0x5F | LD E,A | None | 1 (A) | 1 (E) | — | [no-alu] | —— ||
| 0x60 | LD H,B | None | 1 (B) | 1 (H) | — | [no-alu] | —— ||
| 0x61 | LD H,C | None | 1 (C) | 1 (H) | — | [no-alu] | —— ||
| 0x62 | LD H,D | None | 1 (D) | 1 (H) | — | [no-alu] | —— ||
| 0x63 | LD H,E | None | 1 (E) | 1 (H) | — | [no-alu] | —— ||
| 0x64 | LD H,H | None | 1 (H) | 1 (H) | — | [no-alu] | —— ||
| 0x65 | LD H,L | None | 1 (L) | 1 (H) | — | [no-alu] | —— ||
| 0x66 | LD H,(HL) | None | 2 (H,L) | 1 (H) | R | [no-alu] | —— ||
| 0x67 | LD H,A | None | 1 (A) | 1 (H) | — | [no-alu] | —— ||
| 0x68 | LD L,B | None | 1 (B) | 1 (L) | — | [no-alu] | —— ||
| 0x69 | LD L,C | None | 1 (C) | 1 (L) | — | [no-alu] | —— ||
| 0x6A | LD L,D | None | 1 (D) | 1 (L) | — | [no-alu] | —— ||
| 0x6B | LD L,E | None | 1 (E) | 1 (L) | — | [no-alu] | —— ||
| 0x6C | LD L,H | None | 1 (H) | 1 (L) | — | [no-alu] | —— ||
| 0x6D | LD L,L | None | 1 (L) | 1 (L) | — | [no-alu] | —— ||
| 0x6E | LD L,(HL) | None | 2 (H,L) | 1 (L) | R | [no-alu] | —— ||
| 0x6F | LD L,A | None | 1 (A) | 1 (L) | — | [no-alu] | —— ||
| 0x70 | LD (HL),B | None | 3 (B,H,L) | 0 | W | [no-alu] | —— ||
| 0x71 | LD (HL),C | None | 3 (C,H,L) | 0 | W | [no-alu] | —— ||
| 0x72 | LD (HL),D | None | 3 (D,H,L) | 0 | W | [no-alu] | —— ||
| 0x73 | LD (HL),E | None | 3 (E,H,L) | 0 | W | [no-alu] | —— ||
| 0x74 | LD (HL),H | None | 2 (H,L) | 0 | W | [no-alu] | —— ||
| 0x75 | LD (HL),L | None | 2 (H,L) | 0 | W | [no-alu] | —— ||
| 0x76 | HALT | None | 0 | 0 | 2R (IF, IE) | [no-alu] | —— | W (HALT, HALT_BUG), R (IME) |
| 0x77 | LD (HL),A | None | 3 (A,H,L) | 0 | W | [no-alu] | —— ||
| 0x78 | LD A,B | None | 1 (B) | 1 (A) | — | [no-alu] | —— ||
| 0x79 | LD A,C | None | 1 (C) | 1 (A) | — | [no-alu] | —— ||
| 0x7A | LD A,D | None | 1 (D) | 1 (A) | — | [no-alu] | —— ||
| 0x7B | LD A,E | None | 1 (E) | 1 (A) | — | [no-alu] | —— ||
| 0x7C | LD A,H | None | 1 (H) | 1 (A) | — | [no-alu] | —— ||
| 0x7D | LD A,L | None | 1 (L) | 1 (A) | — | [no-alu] | —— ||
| 0x7E | LD A,(HL) | None | 2 (H,L) | 1 (A) | R | [no-alu] | —— ||
| 0x7F | LD A,A | None | 1 (A) | 1 (A) | — | [no-alu] | —— ||

---

Note: in practice, operations like `LD A,A` can be optimized to do no register reads at all (as it is a no-op)

#### 3.3.4 Opcodes 0x80–0xBF (ALU block)

| Opcode | Mnemonic | Expansion Type | Reg R | Reg W | RAM | Lookup | Flags | CPU State |
|--------|----------|----------------|-------|-------|-----|--------|-------|----------|
| 0x80 | ADD A,B | None | 2 (A,B) | 1 (A) | — | [ADD] | z0hc ||
| 0x81 | ADD A,C | None | 2 (A,C) | 1 (A) | — | [ADD] | z0hc ||
| 0x82 | ADD A,D | None | 2 (A,D) | 1 (A) | — | [ADD] | z0hc ||
| 0x83 | ADD A,E | None | 2 (A,E) | 1 (A) | — | [ADD] | z0hc ||
| 0x84 | ADD A,H | None | 2 (A,H) | 1 (A) | — | [ADD] | z0hc ||
| 0x85 | ADD A,L | None | 2 (A,L) | 1 (A) | — | [ADD] | z0hc ||
| 0x86 | ADD A,(HL) | None | 3 (A,H,L) | 1 (A) | R | [ADD] | z0hc ||
| 0x87 | ADD A,A | None | 1 (A) | 1 (A) | — | [ADD] | z0hc ||
| 0x88 | ADC A,B | None | 2 (A,B) | 1 (A) | — | [ADC] | z0hc ||
| 0x89 | ADC A,C | None | 2 (A,C) | 1 (A) | — | [ADC] | z0hc ||
| 0x8A | ADC A,D | None | 2 (A,D) | 1 (A) | — | [ADC] | z0hc ||
| 0x8B | ADC A,E | None | 2 (A,E) | 1 (A) | — | [ADC] | z0hc ||
| 0x8C | ADC A,H | None | 2 (A,H) | 1 (A) | — | [ADC] | z0hc ||
| 0x8D | ADC A,L | None | 2 (A,L) | 1 (A) | — | [ADC] | z0hc ||
| 0x8E | ADC A,(HL) | None | 3 (A,H,L) | 1 (A) | R | [ADC] | z0hc ||
| 0x8F | ADC A,A | None | 1 (A) | 1 (A) | — | [ADC] | z0hc ||
| 0x90 | SUB A,B | None | 2 (A,B) | 1 (A) | — | [SUB] | z1hc ||
| 0x91 | SUB A,C | None | 2 (A,C) | 1 (A) | — | [SUB] | z1hc ||
| 0x92 | SUB A,D | None | 2 (A,D) | 1 (A) | — | [SUB] | z1hc ||
| 0x93 | SUB A,E | None | 2 (A,E) | 1 (A) | — | [SUB] | z1hc ||
| 0x94 | SUB A,H | None | 2 (A,H) | 1 (A) | — | [SUB] | z1hc ||
| 0x95 | SUB A,L | None | 2 (A,L) | 1 (A) | — | [SUB] | z1hc ||
| 0x96 | SUB A,(HL) | None | 3 (A,H,L) | 1 (A) | R | [SUB] | z1hc ||
| 0x97 | SUB A,A | None | 1 (A) | 1 (A) | — | [SUB] | z1hc ||
| 0x98 | SBC A,B | None | 2 (A,B) | 1 (A) | — | [SBC] | z1hc ||
| 0x99 | SBC A,C | None | 2 (A,C) | 1 (A) | — | [SBC] | z1hc ||
| 0x9A | SBC A,D | None | 2 (A,D) | 1 (A) | — | [SBC] | z1hc ||
| 0x9B | SBC A,E | None | 2 (A,E) | 1 (A) | — | [SBC] | z1hc ||
| 0x9C | SBC A,H | None | 2 (A,H) | 1 (A) | — | [SBC] | z1hc ||
| 0x9D | SBC A,L | None | 2 (A,L) | 1 (A) | — | [SBC] | z1hc ||
| 0x9E | SBC A,(HL) | None | 3 (A,H,L) | 1 (A) | R | [SBC] | z1hc ||
| 0x9F | SBC A,A | None | 1 (A) | 1 (A) | — | [SBC] | z1hc ||
| 0xA0 | AND A,B | None | 2 (A,B) | 1 (A) | — | [AND] | z010 ||
| 0xA1 | AND A,C | None | 2 (A,C) | 1 (A) | — | [AND] | z010 ||
| 0xA2 | AND A,D | None | 2 (A,D) | 1 (A) | — | [AND] | z010 ||
| 0xA3 | AND A,E | None | 2 (A,E) | 1 (A) | — | [AND] | z010 ||
| 0xA4 | AND A,H | None | 2 (A,H) | 1 (A) | — | [AND] | z010 ||
| 0xA5 | AND A,L | None | 2 (A,L) | 1 (A) | — | [AND] | z010 ||
| 0xA6 | AND A,(HL) | None | 3 (A,H,L) | 1 (A) | R | [AND] | z010 ||
| 0xA7 | AND A,A | None | 1 (A) | 1 (A) | — | [AND] | z010 ||
| 0xA8 | XOR A,B | None | 2 (A,B) | 1 (A) | — | [XOR] | z000 ||
| 0xA9 | XOR A,C | None | 2 (A,C) | 1 (A) | — | [XOR] | z000 ||
| 0xAA | XOR A,D | None | 2 (A,D) | 1 (A) | — | [XOR] | z000 ||
| 0xAB | XOR A,E | None | 2 (A,E) | 1 (A) | — | [XOR] | z000 ||
| 0xAC | XOR A,H | None | 2 (A,H) | 1 (A) | — | [XOR] | z000 ||
| 0xAD | XOR A,L | None | 2 (A,L) | 1 (A) | — | [XOR] | z000 ||
| 0xAE | XOR A,(HL) | None | 3 (A,H,L) | 1 (A) | R | [XOR] | z000 ||
| 0xAF | XOR A,A | None | 1 (A) | 1 (A) | — | [XOR] | z000 ||
| 0xB0 | OR A,B | None | 2 (A,B) | 1 (A) | — | [OR] | z000 ||
| 0xB1 | OR A,C | None | 2 (A,C) | 1 (A) | — | [OR] | z000 ||
| 0xB2 | OR A,D | None | 2 (A,D) | 1 (A) | — | [OR] | z000 ||
| 0xB3 | OR A,E | None | 2 (A,E) | 1 (A) | — | [OR] | z000 ||
| 0xB4 | OR A,H | None | 2 (A,H) | 1 (A) | — | [OR] | z000 ||
| 0xB5 | OR A,L | None | 2 (A,L) | 1 (A) | — | [OR] | z000 ||
| 0xB6 | OR A,(HL) | None | 3 (A,H,L) | 1 (A) | R | [OR] | z000 ||
| 0xB7 | OR A,A | None | 1 (A) | 1 (A) | — | [OR] | z000 ||
| 0xB8 | CP A,B | None | 2 (A,B) | 0 | — | [SUB] | z1hc ||
| 0xB9 | CP A,C | None | 2 (A,C) | 0 | — | [SUB] | z1hc ||
| 0xBA | CP A,D | None | 2 (A,D) | 0 | — | [SUB] | z1hc ||
| 0xBB | CP A,E | None | 2 (A,E) | 0 | — | [SUB] | z1hc ||
| 0xBC | CP A,H | None | 2 (A,H) | 0 | — | [SUB] | z1hc ||
| 0xBD | CP A,L | None | 2 (A,L) | 0 | — | [SUB] | z1hc ||
| 0xBE | CP A,(HL) | None | 3 (A,H,L) | 0 | R | [SUB] | z1hc ||
| 0xBF | CP A,A | None | 1 (A) | 0 | — | [SUB] | z1hc ||

---

#### 3.3.5 Opcodes 0xC0–0xFF (Control + misc)

| Opcode | Mnemonic | Expansion Type | Reg R | Reg W | RAM | Lookup | Flags | CPU State |
|--------|----------|----------------|-------|-------|-----|--------|-------|----------|
| 0xC0 | RET NZ | None | 1 (F) | 0 | 2R | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xC1 | POP BC | None | 0 | 2 (B,C) | 2R | [no-alu] | —— | R (SP) W (SP) |
| 0xC2 | JP NZ,u16 | None | 1 (F) | 0 | — | [no-alu] | —— | W (PC) |
| 0xC3 | JP u16 | None | 0 | 0 | — | [no-alu] | —— | W (PC) |
| 0xC4 | CALL NZ,u16 | None | 1 (F) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xC5 | PUSH BC | None | 2 (B,C) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) |
| 0xC6 | ADD A,u8 | None | 1 (A) | 1 (A) | — | [ADD] | z0hc ||
| 0xC7 | RST 00h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xC8 | RET Z | None | 1 (F) | 0 | 2R | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xC9 | RET | None | 0 | 0 | 2R | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xCA | JP Z,u16 | None | 1 (F) | 0 | — | [no-alu] | —— | W (PC) |
| 0xCB | PREFIX CB | None | — | — | — | — | —— | |
| 0xCC | CALL Z,u16 | None | 1 (F) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xCD | CALL u16 | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xCE | ADC A,u8 | None | 1 (A) | 1 (A) | — | [ADC] | z0hc ||
| 0xCF | RST 08h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xD0 | RET NC | None | 1 (F) | 0 | 2R | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xD1 | POP DE | None | 0 | 2 (D,E) | 2R | [no-alu] | —— | R (SP) W (SP) |
| 0xD2 | JP NC,u16 | None | 1 (F) | 0 | — | [no-alu] | —— | W (PC) |
| 0xD3 | [repurposed-ADD] | — | — | — | — | — | —— ||
| 0xD4 | CALL NC,u16 | None | 1 (F) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xD5 | PUSH DE | None | 2 (D,E) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) |
| 0xD6 | SUB A,u8 | None | 1 (A) | 1 (A) | — | [SUB] | z1hc ||
| 0xD7 | RST 10h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xD8 | RET C | None | 1 (F) | 0 | 2R | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xD9 | RETI | None | 0 | 0 | 2R | [no-alu] | —— | R (SP) W (SP) W (PC) W (IME) |
| 0xDA | JP C,u16 | None | 1 (F) | 0 | — | [no-alu] | —— | W (PC) |
| 0xDB | [repurposed-ADD] | — | — | — | — | — | —— ||
| 0xDC | CALL C,u16 | None | 1 (F) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xDD | [repurposed-ADD] | — | — | — | — | — | —— ||
| 0xDE | SBC A,u8 | None | 1 (A) | 1 (A) | — | [SBC] | z1hc ||
| 0xDF | RST 18h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xE0 | LD (FF00+u8),A | None | 1 (A) | 0 | W | [no-alu] | —— ||
| 0xE1 | POP HL | None | 0 | 2 (H,L) | 2R | [no-alu] | —— | R (SP) W (SP) |
| 0xE2 | LD (FF00+C),A | None | 2 (A,C) | 0 | W | [no-alu] | —— ||
| 0xE3 | [repurposed-ADD] | — | — | — | — | — | —— ||
| 0xE4 | UNUSED | — | — | — | — | — | —— ||
| 0xE5 | PUSH HL | None | 2 (H,L) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) |
| 0xE6 | AND A,u8 | None | 1 (A) | 1 (A) | — | [AND] | z010 ||
| 0xE7 | RST 20h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xE8 | ADD SP,i8 | None | 0 | 0 | — | [ADD]+[ADC] | 00hc | R (SP) W (SP) |
| 0xE9 | JP HL | None | 2 (H,L) | 0 | — | [no-alu] | —— | W (PC) |
| 0xEA | LD (u16),A | None | 1 (A) | 0 | W | [no-alu] | —— ||
| 0xEB | UNUSED | — | — | — | — | — | —— ||
| 0xEC | UNUSED | — | — | — | — | — | —— ||
| 0xED | UNUSED | — | — | — | — | — | —— ||
| 0xEE | XOR A,u8 | None | 1 (A) | 1 (A) | — | [XOR] | z000 ||
| 0xEF | RST 28h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xF0 | LD A,(FF00+u8) | None | 0 | 1 (A) | R | [no-alu] | —— ||
| 0xF1 | POP AF | None | 0 | 1 (A) | 2R | [no-alu] | znhc | R (SP) W (SP) |
| 0xF2 | LD A,(FF00+C) | None | 1 (C) | 1 (A) | R | [no-alu] | —— ||
| 0xF3 | DI | None | 0 | 0 | — | [no-alu] | —— | W (IME) |
| 0xF4 | UNUSED | — | — | — | — | — | —— ||
| 0xF5 | PUSH AF | None | 2 (A,F) | 0 | 2W | [no-alu] | —— | R (SP) W (SP) |
| 0xF6 | OR A,u8 | None | 1 (A) | 1 (A) | — | [OR] | z000 ||
| 0xF7 | RST 30h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |
| 0xF8 | LD HL,SP+i8 | None | 0 | 2 (H,L) | — | [ADD]+[ADC] | 00hc | R (SP) |
| 0xF9 | LD SP,HL | None | 2 (H,L) | 0 | — | [no-alu] | —— | W (SP) |
| 0xFA | LD A,(u16) | None | 0 | 1 (A) | R | [no-alu] | —— ||
| 0xFB | EI | None | 0 | 0 | — | [no-alu] | —— | W (IME_DELAY) |
| 0xFC | UNUSED | — | — | — | — | — | —— ||
| 0xFD | UNUSED | — | — | — | — | — | —— ||
| 0xFE | CP A,u8 | None | 1 (A) | 0 | — | [SUB] | z1hc ||
| 0xFF | RST 38h | None | 0 | 0 | 2W | [no-alu] | —— | R (SP) W (SP) W (PC) |

Note: `PREFIX` is not modelled as setting a flag for a future cycle (no CPU State). It causes the next byte to be read as an opcode right away

---

#### 3.3.6 CB Opcodes (0x00–0xFF)

| Opcode | Mnemonic | Expansion Type | Reg R | Reg W | RAM | Lookup | Flags | CPU State |
|--------|----------|----------------|-------|-------|-----|--------|-------|-----------|
| 0x00 | RLC B | None | 1 (B) | 1 (B) | — | [RLC] | z00c ||
| 0x01 | RLC C | None | 1 (C) | 1 (C) | — | [RLC] | z00c ||
| 0x02 | RLC D | None | 1 (D) | 1 (D) | — | [RLC] | z00c ||
| 0x03 | RLC E | None | 1 (E) | 1 (E) | — | [RLC] | z00c ||
| 0x04 | RLC H | None | 1 (H) | 1 (H) | — | [RLC] | z00c ||
| 0x05 | RLC L | None | 1 (L) | 1 (L) | — | [RLC] | z00c ||
| 0x06 | RLC (HL) | None | 2 (H,L) | 0 | R+W | [RLC] | z00c ||
| 0x07 | RLC A | None | 1 (A) | 1 (A) | — | [RLC] | z00c ||
| 0x08 | RRC B | None | 1 (B) | 1 (B) | — | [RRC] | z00c ||
| 0x09 | RRC C | None | 1 (C) | 1 (C) | — | [RRC] | z00c ||
| 0x0A | RRC D | None | 1 (D) | 1 (D) | — | [RRC] | z00c ||
| 0x0B | RRC E | None | 1 (E) | 1 (E) | — | [RRC] | z00c ||
| 0x0C | RRC H | None | 1 (H) | 1 (H) | — | [RRC] | z00c ||
| 0x0D | RRC L | None | 1 (L) | 1 (L) | — | [RRC] | z00c ||
| 0x0E | RRC (HL) | None | 2 (H,L) | 0 | R+W | [RRC] | z00c ||
| 0x0F | RRC A | None | 1 (A) | 1 (A) | — | [RRC] | z00c ||
| 0x10 | RL B | None | 1 (B) | 1 (B) | — | [RL] | z00c ||
| 0x11 | RL C | None | 1 (C) | 1 (C) | — | [RL] | z00c ||
| 0x12 | RL D | None | 1 (D) | 1 (D) | — | [RL] | z00c ||
| 0x13 | RL E | None | 1 (E) | 1 (E) | — | [RL] | z00c ||
| 0x14 | RL H | None | 1 (H) | 1 (H) | — | [RL] | z00c ||
| 0x15 | RL L | None | 1 (L) | 1 (L) | — | [RL] | z00c ||
| 0x16 | RL (HL) | None | 2 (H,L) | 0 | R+W | [RL] | z00c ||
| 0x17 | RL A | None | 1 (A) | 1 (A) | — | [RL] | z00c ||
| 0x18 | RR B | None | 1 (B) | 1 (B) | — | [RR] | z00c ||
| 0x19 | RR C | None | 1 (C) | 1 (C) | — | [RR] | z00c ||
| 0x1A | RR D | None | 1 (D) | 1 (D) | — | [RR] | z00c ||
| 0x1B | RR E | None | 1 (E) | 1 (E) | — | [RR] | z00c ||
| 0x1C | RR H | None | 1 (H) | 1 (H) | — | [RR] | z00c ||
| 0x1D | RR L | None | 1 (L) | 1 (L) | — | [RR] | z00c ||
| 0x1E | RR (HL) | None | 2 (H,L) | 0 | R+W | [RR] | z00c ||
| 0x1F | RR A | None | 1 (A) | 1 (A) | — | [RR] | z00c ||
| 0x20 | SLA B | None | 1 (B) | 1 (B) | — | [SLA] | z00c ||
| 0x21 | SLA C | None | 1 (C) | 1 (C) | — | [SLA] | z00c ||
| 0x22 | SLA D | None | 1 (D) | 1 (D) | — | [SLA] | z00c ||
| 0x23 | SLA E | None | 1 (E) | 1 (E) | — | [SLA] | z00c ||
| 0x24 | SLA H | None | 1 (H) | 1 (H) | — | [SLA] | z00c ||
| 0x25 | SLA L | None | 1 (L) | 1 (L) | — | [SLA] | z00c ||
| 0x26 | SLA (HL) | None | 2 (H,L) | 0 | R+W | [SLA] | z00c ||
| 0x27 | SLA A | None | 1 (A) | 1 (A) | — | [SLA] | z00c ||
| 0x28 | SRA B | None | 1 (B) | 1 (B) | — | [SRA] | z00c ||
| 0x29 | SRA C | None | 1 (C) | 1 (C) | — | [SRA] | z00c ||
| 0x2A | SRA D | None | 1 (D) | 1 (D) | — | [SRA] | z00c ||
| 0x2B | SRA E | None | 1 (E) | 1 (E) | — | [SRA] | z00c ||
| 0x2C | SRA H | None | 1 (H) | 1 (H) | — | [SRA] | z00c ||
| 0x2D | SRA L | None | 1 (L) | 1 (L) | — | [SRA] | z00c ||
| 0x2E | SRA (HL) | None | 2 (H,L) | 0 | R+W | [SRA] | z00c ||
| 0x2F | SRA A | None | 1 (A) | 1 (A) | — | [SRA] | z00c ||
| 0x30 | SWAP B | None | 1 (B) | 1 (B) | — | [SWAP] | z000 ||
| 0x31 | SWAP C | None | 1 (C) | 1 (C) | — | [SWAP] | z000 ||
| 0x32 | SWAP D | None | 1 (D) | 1 (D) | — | [SWAP] | z000 ||
| 0x33 | SWAP E | None | 1 (E) | 1 (E) | — | [SWAP] | z000 ||
| 0x34 | SWAP H | None | 1 (H) | 1 (H) | — | [SWAP] | z000 ||
| 0x35 | SWAP L | None | 1 (L) | 1 (L) | — | [SWAP] | z000 ||
| 0x36 | SWAP (HL) | None | 2 (H,L) | 0 | R+W | [SWAP] | z000 ||
| 0x37 | SWAP A | None | 1 (A) | 1 (A) | — | [SWAP] | z000 ||
| 0x38 | SRL B | None | 1 (B) | 1 (B) | — | [SRL] | z00c ||
| 0x39 | SRL C | None | 1 (C) | 1 (C) | — | [SRL] | z00c ||
| 0x3A | SRL D | None | 1 (D) | 1 (D) | — | [SRL] | z00c ||
| 0x3B | SRL E | None | 1 (E) | 1 (E) | — | [SRL] | z00c ||
| 0x3C | SRL H | None | 1 (H) | 1 (H) | — | [SRL] | z00c ||
| 0x3D | SRL L | None | 1 (L) | 1 (L) | — | [SRL] | z00c ||
| 0x3E | SRL (HL) | None | 2 (H,L) | 0 | R+W | [SRL] | z00c ||
| 0x3F | SRL A | None | 1 (A) | 1 (A) | — | [SRL] | z00c ||
| 0x40 | BIT 0,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x41 | BIT 0,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x42 | BIT 0,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x43 | BIT 0,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x44 | BIT 0,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x45 | BIT 0,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x46 | BIT 0,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x47 | BIT 0,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x48 | BIT 1,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x49 | BIT 1,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x4A | BIT 1,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x4B | BIT 1,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x4C | BIT 1,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x4D | BIT 1,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x4E | BIT 1,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x4F | BIT 1,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x50 | BIT 2,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x51 | BIT 2,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x52 | BIT 2,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x53 | BIT 2,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x54 | BIT 2,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x55 | BIT 2,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x56 | BIT 2,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x57 | BIT 2,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x58 | BIT 3,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x59 | BIT 3,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x5A | BIT 3,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x5B | BIT 3,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x5C | BIT 3,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x5D | BIT 3,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x5E | BIT 3,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x5F | BIT 3,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x60 | BIT 4,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x61 | BIT 4,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x62 | BIT 4,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x63 | BIT 4,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x64 | BIT 4,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x65 | BIT 4,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x66 | BIT 4,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x67 | BIT 4,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x68 | BIT 5,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x69 | BIT 5,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x6A | BIT 5,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x6B | BIT 5,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x6C | BIT 5,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x6D | BIT 5,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x6E | BIT 5,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x6F | BIT 5,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x70 | BIT 6,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x71 | BIT 6,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x72 | BIT 6,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x73 | BIT 6,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x74 | BIT 6,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x75 | BIT 6,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x76 | BIT 6,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x77 | BIT 6,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x78 | BIT 7,B | None | 1 (B) | 0 | — | [BIT] | z01- ||
| 0x79 | BIT 7,C | None | 1 (C) | 0 | — | [BIT] | z01- ||
| 0x7A | BIT 7,D | None | 1 (D) | 0 | — | [BIT] | z01- ||
| 0x7B | BIT 7,E | None | 1 (E) | 0 | — | [BIT] | z01- ||
| 0x7C | BIT 7,H | None | 1 (H) | 0 | — | [BIT] | z01- ||
| 0x7D | BIT 7,L | None | 1 (L) | 0 | — | [BIT] | z01- ||
| 0x7E | BIT 7,(HL) | None | 2 (H,L) | 0 | R | [BIT] | z01- ||
| 0x7F | BIT 7,A | None | 1 (A) | 0 | — | [BIT] | z01- ||
| 0x80 | RES 0,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0x81 | RES 0,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0x82 | RES 0,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0x83 | RES 0,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0x84 | RES 0,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0x85 | RES 0,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0x86 | RES 0,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0x87 | RES 0,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0x88 | RES 1,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0x89 | RES 1,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0x8A | RES 1,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0x8B | RES 1,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0x8C | RES 1,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0x8D | RES 1,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0x8E | RES 1,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0x8F | RES 1,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0x90 | RES 2,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0x91 | RES 2,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0x92 | RES 2,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0x93 | RES 2,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0x94 | RES 2,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0x95 | RES 2,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0x96 | RES 2,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0x97 | RES 2,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0x98 | RES 3,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0x99 | RES 3,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0x9A | RES 3,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0x9B | RES 3,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0x9C | RES 3,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0x9D | RES 3,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0x9E | RES 3,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0x9F | RES 3,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0xA0 | RES 4,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0xA1 | RES 4,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0xA2 | RES 4,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0xA3 | RES 4,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0xA4 | RES 4,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0xA5 | RES 4,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0xA6 | RES 4,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0xA7 | RES 4,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0xA8 | RES 5,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0xA9 | RES 5,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0xAA | RES 5,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0xAB | RES 5,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0xAC | RES 5,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0xAD | RES 5,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0xAE | RES 5,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0xAF | RES 5,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0xB0 | RES 6,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0xB1 | RES 6,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0xB2 | RES 6,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0xB3 | RES 6,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0xB4 | RES 6,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0xB5 | RES 6,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0xB6 | RES 6,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0xB7 | RES 6,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0xB8 | RES 7,B | None | 1 (B) | 1 (B) | — | [RES] | —— ||
| 0xB9 | RES 7,C | None | 1 (C) | 1 (C) | — | [RES] | —— ||
| 0xBA | RES 7,D | None | 1 (D) | 1 (D) | — | [RES] | —— ||
| 0xBB | RES 7,E | None | 1 (E) | 1 (E) | — | [RES] | —— ||
| 0xBC | RES 7,H | None | 1 (H) | 1 (H) | — | [RES] | —— ||
| 0xBD | RES 7,L | None | 1 (L) | 1 (L) | — | [RES] | —— ||
| 0xBE | RES 7,(HL) | None | 2 (H,L) | 0 | R+W | [RES] | —— ||
| 0xBF | RES 7,A | None | 1 (A) | 1 (A) | — | [RES] | —— ||
| 0xC0 | SET 0,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xC1 | SET 0,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xC2 | SET 0,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xC3 | SET 0,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xC4 | SET 0,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xC5 | SET 0,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xC6 | SET 0,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xC7 | SET 0,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||
| 0xC8 | SET 1,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xC9 | SET 1,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xCA | SET 1,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xCB | SET 1,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xCC | SET 1,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xCD | SET 1,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xCE | SET 1,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xCF | SET 1,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||
| 0xD0 | SET 2,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xD1 | SET 2,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xD2 | SET 2,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xD3 | SET 2,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xD4 | SET 2,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xD5 | SET 2,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xD6 | SET 2,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xD7 | SET 2,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||
| 0xD8 | SET 3,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xD9 | SET 3,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xDA | SET 3,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xDB | SET 3,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xDC | SET 3,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xDD | SET 3,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xDE | SET 3,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xDF | SET 3,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||
| 0xE0 | SET 4,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xE1 | SET 4,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xE2 | SET 4,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xE3 | SET 4,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xE4 | SET 4,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xE5 | SET 4,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xE6 | SET 4,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xE7 | SET 4,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||
| 0xE8 | SET 5,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xE9 | SET 5,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xEA | SET 5,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xEB | SET 5,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xEC | SET 5,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xED | SET 5,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xEE | SET 5,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xEF | SET 5,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||
| 0xF0 | SET 6,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xF1 | SET 6,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xF2 | SET 6,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xF3 | SET 6,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xF4 | SET 6,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xF5 | SET 6,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xF6 | SET 6,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xF7 | SET 6,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||
| 0xF8 | SET 7,B | None | 1 (B) | 1 (B) | — | [SET] | —— ||
| 0xF9 | SET 7,C | None | 1 (C) | 1 (C) | — | [SET] | —— ||
| 0xFA | SET 7,D | None | 1 (D) | 1 (D) | — | [SET] | —— ||
| 0xFB | SET 7,E | None | 1 (E) | 1 (E) | — | [SET] | —— ||
| 0xFC | SET 7,H | None | 1 (H) | 1 (H) | — | [SET] | —— ||
| 0xFD | SET 7,L | None | 1 (L) | 1 (L) | — | [SET] | —— ||
| 0xFE | SET 7,(HL) | None | 2 (H,L) | 0 | R+W | [SET] | —— ||
| 0xFF | SET 7,A | None | 1 (A) | 1 (A) | — | [SET] | —— ||

### 3.7 Full structure

Note: the structs below model the **emulator's execution** (what the prover must demonstrate). The prover-side representation differs: lookup results are single scalars, flag computation is handled by circuit flags and constraints (see [§4](#4-lookups)), and the `Cpu` fields become witness columns rather than mutable state.

```rust
pub struct Cpu {
    ime: bool;
    ime_delay: bool;
    halt: bool;
    halt_bug: bool;
    stop: bool;
    sp: u16;
    pc: u16;
    f: u8;
}
pub trait SM83Instruction
{
    type Format: InstructionFormat;
    type MemoryOps: Into<MemoryOps>;

    fn operands(&self) -> &Self::Format;
    fn new(word: u16, address: u16, validate: bool, compressed: bool) -> Self;
    fn execute(&self, cpu: &mut Cpu, ram_access: &mut Self::MemoryOps);
}

pub trait InstructionFormat
{
    type RegisterState: InstructionRegisterState;

    fn parse(word: u16) -> Self;
    fn capture_pre_execution_state(&self, state: &mut Self::RegisterState, cpu: &mut Cpu);
    fn capture_post_execution_state(&self, state: &mut Self::RegisterState, cpu: &mut Cpu);
}
pub struct SM83Cycle<T: SM83Instruction> {
    pub instruction: T,
    pub register_state: <T::Format as InstructionFormat>::RegisterState,
    pub ram_access: T::MemoryOps,
}
```

## 4. Lookups & Constraints

Lookup table definitions, constraint specifications, and open design questions are documented in [constraints.md](./constraints.md).

<!-- Link references: point to constraints.md lookup table sections -->
[no-alu]: ./constraints.md#no-alu--no-alu-computation
[linear]: ./constraints.md#linear--linear-constraints
[const]: ./constraints.md#const--constant-outputs
[INC]: ./constraints.md#11-unary-tables-u8--u8
[DEC]: ./constraints.md#11-unary-tables-u8--u8
[RLC]: ./constraints.md#11-unary-tables-u8--u8
[RRC]: ./constraints.md#11-unary-tables-u8--u8
[SLA]: ./constraints.md#11-unary-tables-u8--u8
[SRA]: ./constraints.md#11-unary-tables-u8--u8
[SRL]: ./constraints.md#11-unary-tables-u8--u8
[SWAP]: ./constraints.md#11-unary-tables-u8--u8
[RLCA]: ./constraints.md#11-unary-tables-u8--u8
[RRCA]: ./constraints.md#11-unary-tables-u8--u8
[RL]: ./constraints.md#232-carry-in-for-rlrr-rotate-through-carry
[RR]: ./constraints.md#232-carry-in-for-rlrr-rotate-through-carry
[BIT]: ./constraints.md#12-unary-bit-position-variant-tables-u8--07--u8
[RES]: ./constraints.md#12-unary-bit-position-variant-tables-u8--07--u8
[SET]: ./constraints.md#12-unary-bit-position-variant-tables-u8--07--u8
[DAA]: ./constraints.md#13-daa--open-design-question
[ADD]: ./constraints.md#14-binary-tables-u8--u8--u8
[SUB]: ./constraints.md#14-binary-tables-u8--u8--u8
[AND]: ./constraints.md#14-binary-tables-u8--u8--u8
[XOR]: ./constraints.md#14-binary-tables-u8--u8--u8
[OR]: ./constraints.md#14-binary-tables-u8--u8--u8
[ADC]: ./constraints.md#233-carry-in-for-adcsbc
[SBC]: ./constraints.md#233-carry-in-for-adcsbc

## TODO

### zk-cycle model
- What to do about the fact A is *also* often implicitly used? At least I think it's only implicit in opcodes that never use registers in the first place (need to verify this though). This is really just a mnemonic convention though. For example, in some resources, `ADD A, B` is just written as `ADD B`. We could just render all opcodes that use A with A explicit as a convention.
- Opcode tables maybe should keep track of which opcodes require a prover-provided witness
- Do we want to allow 2 lookups in one zk-cycle? Jolt does this by breaking things down into virtual opcodes
- `Halt` depends on multiple internal READ/WRITEs (HALT, HALT_BUG, IME). It's the only instruction that does multiple internal READ & WRITEs, and it can easily be split up (but HALT often runs every frame). Do we want a maximum number of internal READ/WRITEs? Should it even be explicit in the zk-cycle? If you exclude SP & PC, it's:
    - EI (W IME_DELAY)
    - DI (W IME)
    - RETI (W IME)
    - HALT (W HALT, W HALT_BUG, R IME)
    - STOP (W STOP)
- Do we want to expand CALL/RET? (RETI could be EI+RET, but tricky because order and EI timing matters, and this would require the EI timer to include virtual opcodes)
- Do I need `validate: bool, compressed: bool` in the `SM83Instruction` trait?
- Specify in more detail the circuit flags

#### Higher-level CPU step

We still need to fine where/how the higher-level step required to process flags in the CPU like f, pc, sp, and other flags are handled

#### SP decomposition

SP is 16-bit and lives outside `InstructionRegisterState` (see [§3.1.5](#315-cpu-state-handled-separately)) — it is explicitly *not* broken into 8-bit register cells. However, several opcodes need to operate on SP's constituent bytes via 8-bit lookup tables:

- `INC SP` (0x33) / `DEC SP` (0x3B) — dual-lookup carry propagation (see [constraints.md §2.3.1](./constraints.md#231-incdec-rr--dual-lookup-carry-propagation))
- `ADD HL,SP` (0x39) — dual ADD+ADC on SP bytes
- `ADD SP,i8` (0xE8) / `LD HL,SP+i8` (0xF8) — signed offset arithmetic on SP bytes

This is **not contradictory** to §3.1.5. The register model stores SP as a single 16-bit value (not two 8-bit cells). Decomposition into SP_hi/SP_lo happens at the *constraint level*: a higher-level mechanism (outside the SM83Cycle) decomposes SP for the cycle that needs it, and the constraint system verifies `SP = SP_hi × 256 + SP_lo` with range checks on both bytes. The lookups then operate on these derived witnesses, not on register cells.

**Open question**: What exactly is this higher-level mechanism? Options:
1. **Constraint-only decomposition**: The prover provides SP_hi/SP_lo as witness variables, and a constraint enforces `SP = SP_hi × 256 + SP_lo` (plus range checks). SP remains a single 16-bit value in storage.
2. **Dual storage**: Store SP as both a 16-bit value *and* two 8-bit Twist cells. Redundant but avoids per-cycle decomposition constraints.
3. **Always-decomposed**: Store SP only as SP_hi/SP_lo in Twist memory (like other register pairs). This contradicts the §3.1.5 rationale but simplifies constraint wiring.

This decision affects constraints.md §2.3.5 and all opcodes that touch SP arithmetically.

### Memory-mapped I/O
- Using `LD` to write to specific addresses can trigger specific behavior (ex: writing to `$FF46` triggers OAM DMA, writing to `$FF04` resets DIV). 
- Games can depend on reading these values (ex: reading from scx/scy to know what is in the screen)
- Any `LD` that reads from `$FF00` (`JOYP`) needs to somehow interact with the witness tape as well (as all user inputs need to appear in the witness tape). The lower 4 bits of JOYP state can change at any time, so a read from it needs to be modeled as adding the value to the witness. Only the 5th-6th bits should be a Twist value (which means writes to this memory do need to be tracked).
    - this is also true for SB,SC,RTC, but we explicitly do not prove these.

How do we model these in the zk-cycle? The constraint needs to detect the target address and apply side-effect rules.

### Constraints & lookups (see [constraints.md](./constraints.md))
- Specify R1CS constraints for all flag derivation patterns (constraints.md §2.1)
- Specify sub-constraints: is_zero, half_carry, carry (constraints.md §2.2)
- Specify carry chaining for dual ADD+ADC lookups (constraints.md §2.3.4)
- Resolve SP decomposition open question (see [above](#sp-decomposition)), then specify constraints.md §2.3.5
- Specify ADD SP,i8 / LD HL,SP+i8 sign-extension constraint (constraints.md §2.3.6)
- Specify POP AF lower-nibble masking constraint (`F & 0x0F == 0`) (constraints.md §2.3.7)
- Specify control flow constraints: PC, jumps, calls, returns, stack (constraints.md §2.4)
- Specify interrupt dispatch virtual opcode (synthetic CALL + DI + IF clear) (constraints.md §2.4.6)
- Resolve DAA flag-as-input (constraints.md §1.3, open question #8)
- Explore: which other opcode pairs can share tables with different flag routing? (e.g., ADD A,r with `z0hc` and virtual ADD L,C with `---c` use the same ADD table — the constraint just ignores Z/N/H for the virtual variant)
- Explore: Do we want to use ADD/SUB/ADC/SBC via field arithmetic and then only do a lookup for range-check (instead of a full table)? This is less JOLT-y, but may be okay given our smaller field size
- We should be able to use d=1 or d=2 for Twist and Shout given the size of the tables, and the size of total memory used by the Gameboy. Depends on
    1. Our choice of step size for folding
    2. The per-commit overhead for lattices in general
- We can maybe use explicit (and not implicit) Shout tables for everything
