# Constraints & Lookups

This document specifies **how** the proof system enforces correct SM83 execution. It is the companion to [provability.md](./provability.md), which specifies **what** each opcode needs (register reads/writes, RAM access, lookup references, flag patterns) and general architecture.

The proof system has two mechanisms:
1. **Lookup tables** ([§1](#1-lookup-tables)) - precomputed functions queried via the Shout argument. The prover demonstrates correct ALU output by showing each (input, output) pair exists in the table.
2. **R1CS constraints** ([§2](#2-constraints)) - circuit equations that enforce flag derivation, carry propagation, control flow, and structural invariants.

## Design principles

### lookup tables as pure functions

Lookup tables are **pure function** that handle a specific task, rather than having one lookup that handles every concern of an opcode.

Notably, when it comes to opcodes that are ALU-based, **lookup tables return only the ALU result** (a single scalar). In other words, they are **pure functions**. CPU flags are NOT part of the table output. Instead, concerns like flags (ex: the `F` register) are handled by separately as required. 

This principle
1. keeps the table set minimal
2. avoids duplicating tables for carry-variant or flag-variant operations.
3. keeps the table size powers of 2 (needed for most lookup systems)

### flags output computation as subroutines

Opcodes may require updating (often multiple) flags as part of the opcode result.

The most common flags are the four stored in the `F` register. While, both *when* and *how* they are computed is opcode-specific, generally there are families of opcodes that share the same behavior when updating flags.

The time these flag outputs are computed has three categories:
1. `parallel`: the resulting flag state doesn't depend on an underlying lookup at all, and can be done in parallel
2. `sequential`: the resulting flag state depends on an underlying lookup, and therefore has to done done afterwards (they are sequential)
3. `interleave`: the resulting flag both depends on an underlying lookup, as well as feeds into another lookup afterwards

For example (with the exception of `POP AF`), the time of computation is as follows:
| Flag | Time of computation |
|------|---------------------|
| Z    | sequential |
| N    | parallel |
| H    | *arithmetic*: sequential<br> *logical*: parallel<br> *cpu control*: parallel |
| C    | *arithmetic*: sequential/interleave<br> *rotate*: sequential<br> *logical*: sequential<br> *DAA*: sequential<br> *cpu control*: parallel |

However,
- `H` has a different computation depending on the opcode (addition vs subtraction, 8-bit vs 16-bit)
- `C` not only has a different computation depending on the opcode (addition vs subtraction, 8-bit vs 16-bit), it is often computed twice during a single opcode (ex: opcodes that use `ADD`+`ADC` use the original carry output from `ADD` as the carry-in for `ADC`)

Therefore, it is useful to think of flag outputs as reusable subroutines that are shared amongst opcodes as,
1. this gives maximum flexibility on *when* they are used (instead of having a "flag output update step")
2. helps code reuse (different opcodes that have the same flags can use the same subroutine)
3. best models the reality of certain opcodes (ex: interleaving flag updates between lookups)
4. every opcode already needs a constraint that packs flag values into the F register byte (`Z×128 + N×64 + H×32 + C×16 = F_value`) regardless of how the flag values were derived.

### Lookups vs constraints

The two mechanisms serve complementary roles:

- **R1CS constraints** are useful for:
- simple arithmetic
     - arithmetic identities (carry from `a + b = result + C × 256`)
- enforcing types
     - boolean forcing (`x × (x - 1) = 0`)
     - zero detection (`result × result_inv = 1 - Z`)
- gluing lookups together (interleaving)
- conditional selection (cases / MUX)

**Lookup tables** are useful for:
- evaluating pure functions (ALU operations)
- sub-field extraction (nibbles, bits) where R1CS can't range-check efficiently

**Key heuristic**: If the relationship is a polynomial identity between values already available as witness variables, use R1CS. If you need to extract or range-check sub-word fields, use a lookup.

---

## 1. Lookup Tables

### 1.1 Unary tables (u8 → u8)

| Name | Size | Flags | Description |
|------|------|-------|-------------|
| INC | 256 | z0h- | `x → (x + 1) mod 256` |
| DEC | 256 | z1h- | `x → (x - 1) mod 256` |
| RLC | 256 | z00c | Rotate left circular. Bit 7 → carry and bit 0 |
| RRC | 256 | z00c | Rotate right circular. Bit 0 → carry and bit 7 |
| SLA | 256 | z00c | Shift left arithmetic. Bit 7 → carry, bit 0 = 0 |
| SRA | 256 | z00c | Shift right arithmetic. Bit 0 → carry, bit 7 preserved |
| SRL | 256 | z00c | Shift right logical. Bit 0 → carry, bit 7 = 0 |
| SWAP | 256 | z000 | Swap nibbles. `(hi‖lo) → (lo‖hi)` |
| LOWER_NIBBLE | 256 | ---- | `x → x & 0xF` (utility: nibble extraction for half-carry) |

Note: `LOWER_NIBBLE` is a utility table for constraint support ([§2.2.2](#222-half_carry-addition), [§2.2.3](#223-half_carry-subtraction)), not a direct ALU operation. No opcode references it as a primary lookup - it is only used internally by half-carry sub-constraints to extract and range-check the low nibble of operands.

**Table reuse for rotate-through-carry and main-opcode rotates:**

The CB rotate-through-carry instructions (`RL`, `RR`) and the main-opcode rotates (`RLCA`, `RRCA`, `RLA`, `RRA`) do **not** have their own lookup tables. They reuse existing tables as follows:

| Instruction | Base table | Carry-in handling | Z flag |
|-------------|------------|-------------------|--------|
| CB `RLC` | RLC | - (no carry input) | computed from result |
| CB `RRC` | RRC | - (no carry input) | computed from result |
| CB `RL` | SLA | carry-in constraint ([§2.3.2](#232-carry-in-for-rlrr-rotate-through-carry)) | computed from result |
| CB `RR` | SRL | carry-in constraint ([§2.3.2](#232-carry-in-for-rlrr-rotate-through-carry)) | computed from result |
| `RLCA` (0x07) | RLC | - (no carry input) | forced 0 (`ForceZeroFlag`) |
| `RRCA` (0x0F) | RRC | - (no carry input) | forced 0 (`ForceZeroFlag`) |
| `RLA` (0x17) | SLA | carry-in constraint ([§2.3.2](#232-carry-in-for-rlrr-rotate-through-carry)) | forced 0 (`ForceZeroFlag`) |
| `RRA` (0x1F) | SRL | carry-in constraint ([§2.3.2](#232-carry-in-for-rlrr-rotate-through-carry)) | forced 0 (`ForceZeroFlag`) |

The key identities:
- `RL(x, carry_in) = SLA(x) + carry_in` - SLA always produces bit 0 = 0, so adding carry_in (0 or 1) sets bit 0 without overflow
- `RR(x, carry_in) = SRL(x) + carry_in × 128` - SRL always produces bit 7 = 0, so adding carry_in × 128 sets bit 7 without overflow
- Carry-out is identical to the base table's carry: bit 7 of input for RL/SLA, bit 0 of input for RR/SRL

The opcode tables in [provability.md](./provability.md) reference `[RL]` and `[RR]` as lookup names - these denote the base table plus carry-in constraint, with `ForceZeroFlag` additionally applied for the main-opcode variants (`RLA`, `RRA`). `[RLCA]` and `[RRCA]` are aliases for `RLC`/`RRC` with `ForceZeroFlag`.

### 1.2 Unary bit-position-variant tables (u8 × {0..7} → u8)

The bit position is statically known from the opcode, so each position is a separate sub-table selected via opcode-derived flag multiplexing.

| Name | Size | Flags | Description |
|------|------|-------|-------------|
| BIT_0 … BIT_7 | 8 × 256 | z01- | Test bit `n` of input. Output: flags only (no register write). `Z = !(input >> n & 1)` |
| RES_0 … RES_7 | 8 × 256 | ---- | Clear bit `n`. `x → x & ~(1 << n)` |
| SET_0 … SET_7 | 8 × 256 | ---- | Set bit `n`. `x → x \| (1 << n)` |

Note: the bit position is a compile-time constant derived from the opcode encoding, not runtime CPU state. This is consistent with the [design principle](#design-principle-tables-as-pure-functions) - the sub-table selection is statically determined by the opcode, not by any flag or register value.

### 1.3 DAA - open design question

| Name | Size | Flags | Description |
|------|------|-------|-------------|
| DAA | 8 × 256 | z-0c | Decimal-adjust accumulator. 8 sub-tables indexed by `(N, H, C)` flag inputs. Applies BCD correction offset to A |

> **Note**: DAA currently violates the [design principle](#design-principle-tables-as-pure-functions) by using three flag bits (N, H, C) as table inputs. This is flagged as [open question #8](#3-open-design-questions). Possible resolutions:
> 1. **Decompose into conditional constraints**: derive the BCD correction offset (+0x06, +0x60, or both) from flag values and nibble comparisons via R1CS, then apply the adjustment using the ADD/SUB table
> 2. **Accept as a documented exception**: DAA's 3-flag dependency makes constraint decomposition complex, and DAA is rare enough that 8 × 256 = 2048 entries (= 2^11, still power-of-2) may be acceptable
> 3. **Encode flags into the operand**: transform `(A, N, H, C)` into a single index `(N << 10 | H << 9 | C << 8 | A)` before lookup, making the table a pure function of one 11-bit index
>
> Until resolved, the 8 × 256 representation is retained as a placeholder.

### 1.4 Binary tables (u8 × u8 → u8)

| Name | Size | Flags | Description |
|------|------|-------|-------------|
| ADD | 65,536 | z0hc | `(a, b) → (a + b) mod 256`. Also used by `ADC` via carry-in constraint ([§2.3.3](#233-carry-in-for-adcsbc)), virtual opcodes (ADD L,C etc.), and low-byte step of dual-lookup ADD+ADC |
| SUB | 65,536 | z1hc | `(a, b) → (a - b) mod 256`. Also used by `SBC` via carry-in constraint ([§2.3.3](#233-carry-in-for-adcsbc)), and by `CP` (same computation, result discarded by constraint) |
| AND | 65,536 | z010 | `(a, b) → a & b` |
| XOR | 65,536 | z000 | `(a, b) → a ^ b` |
| OR  | 65,536 | z000 | `(a, b) → a \| b` |

### 1.5 Opcodes without lookups

Most opcodes marked [no-alu] in the Lookup column are self-evident: register/memory moves (LD), control flow (JR, JP, CALL, RET, RST), state transitions (DI, EI, HALT, STOP), and no-ops (NOP, PREFIX CB) perform no ALU computation.

The following opcodes *do* compute something but use constraints instead of lookups, because the computation is simple enough to express directly:

#### [no-alu] - No ALU computation

Register/memory moves, control flow, and state transitions - the opcode routes data but performs no arithmetic or logic that would require a lookup.

#### [linear] - Linear constraints

A single constraint of the form `a + b = constant`. No bit decomposition, no lookup argument overhead.

| Opcode | Mnemonic | Constraint | Flags |
|--------|----------|------------|-------|
| 0x2F | CPL | `result + input = 255` | -11- |
| 0x3F | CCF | `c_new + c_old = 1` | -00c |

#### [const] - Constant outputs

All outputs are compile-time constants - no input-dependent computation at all, just hardwired circuit flag values.

| Opcode | Mnemonic | Output | Flags |
|--------|----------|--------|-------|
| 0x37 | SCF | (none) | -001 |

---

## 2. Constraints

This section specifies the R1CS constraints that enforce correct execution. Constraints are organized by **pattern** - many opcodes share identical constraint structures, differing only in register routing.

### 2.1 Flag output patterns

The Flags column in the opcode tables uses a 4-character notation: `znhc`, where each position is either a literal value (`0`, `1`), a computed value (`z`, `n`, `h`, `c`), or unchanged (`-`).

The flag patterns that appear across all SM83 opcodes are listed below. Each pattern needs a constraint specification defining how the flag values are derived from the lookup inputs/outputs.

<!-- TODO: maybe link to the key sub-constraint sections here -->

| Pattern | Used by | Z | N | H | C |
|---------|---------|---|---|---|---|
| `z0hc` | ADD, ADC A,r/u8 | computed | 0 | computed | computed |
| `z1hc` | SUB, SBC A,r/u8, CP | computed | 1 | computed | computed |
| `z010` | AND | computed | 0 | 1 | 0 |
| `z000` | XOR, OR, SWAP | computed | 0 | 0 | 0 |
| `z00c` | RLC, RRC, RL, RR, SLA, SRA, SRL | computed | 0 | 0 | computed |
| `z01-` | BIT | computed | 0 | 1 | unchanged |
| `z0h-` | INC r | computed | 0 | computed | unchanged |
| `z1h-` | DEC r | computed | 1 | computed | unchanged |
| `000c` | RLCA, RRCA, RLA, RRA | 0 | 0 | 0 | computed |
| `00hc` | ADD SP,i8, LD HL,SP+i8 | 0 | 0 | computed | computed |
| `---c` | virtual ADD L,x ([§3.3.2.2][provability-virt-add]) | unchanged | unchanged | unchanged | computed |
| `-0hc` | virtual ADC H,x ([§3.3.2.2][provability-virt-add]), ADD HL,rr (visible result) | unchanged | 0 | computed | computed |
| `z-0c` | DAA | computed | unchanged | 0 | computed |
| `-11-` | CPL | unchanged | 1 | 1 | unchanged |
| `-00c` | CCF | unchanged | 0 | 0 | computed |
| `-001` | SCF | unchanged | 0 | 0 | 1 |
| `znhc` | POP AF | from popped byte | from popped byte | from popped byte | from popped byte |
| `----` | LD, NOP, JP, JR, CALL, RET, RST, PUSH, POP (non-AF), DI, EI, HALT, STOP, INC/DEC rr | - | - | - | - |

### 2.2 Sub-constraints

These are shared building blocks used by multiple flag derivation patterns. Defining them once avoids repetition and ensures consistency.

#### 2.2.1 is_zero

Used by: every pattern with computed Z flag.

**Mechanism**: R1CS (no lookup needed)

Determines whether the lookup result is zero. Produces a boolean `Z` such that `Z = 1` iff `result = 0`.

Witness variables:
- `result_inv` - multiplicative inverse of result (arbitrary when result = 0, as 0 doesn't have a multiplicative inverse and it doesn't matter for constraints)

Constraints:
1. `result × result_inv = 1 - Z` - forces Z=1 if result=0
2. `Z × result = 0` - forces Z=0 if result≠0

Correctness: two cases:
1. When result = 0, constraint 2 is trivially satisfied for any Z, while constraint 1 becomes `0 = 1 - Z`, forcing `Z = 1`
2. When result ≠ 0, constraint 2 forces `Z = 0`, and constraint 1 forces `result_inv = 1/result`. `Z ∈ {0,1}` is implied - no separate boolean constraint needed.

Cost: 2 R1CS constraints + 1 witness variable.

#### 2.2.2 half_carry (addition)

Used by: `z0hc`, `z0h-`, `-0hc`, `00hc`.

**Mechanism**: LOWER_NIBBLE lookups + R1CS constraint

Determines whether a carry occurred from bit 3 to bit 4 during addition.
ex: in `ADD A B`, if `A=0000_1000; B=0000_1000`, then `A+B = 0001_0000` and H is set.

Note: the behavior is opcode-specific
- `ADD` and `SUB` work different (see subtraction case [§2.2.3](#223-half_carry-subtraction))
- `ADC` works differently by including the carry bit `C` (ex: `1000`+`0111` sets `H` if `C=1`)

Lookups:
- `nibble_a = LOWER_NIBBLE(a)`
- `nibble_b = LOWER_NIBBLE(b)` (for binary ops; for INC, b = 1 is a constant)
- `nibble_result = LOWER_NIBBLE(result)`

Witness variables:
- H (boolean)

Constraints:
1. `nibble_a + nibble_b [+ carry_in] = nibble_result + H × 0b1_0000` - constrain `H`
2. `H × (H - 1) = 0` - boolean

Correctness:
- All nibbles ∈ [0, 15] from lookups (so no need for range checks)
- carry_in ∈ [0, 1] because it comes from the system (`[0,1]` by definition), so no need to constrain it
- Sum ∈ [0, 31]. With H boolean and nibble_result range-checked by lookup, H is uniquely determined.

For `ADC`: include `+ carry_in` (from F register or carry chain). See [§2.3.3](#233-carry-in-for-adcsbc).

Cost: 2–3 lookups (unary: 2, binary: 3) + 2 R1CS constraints.

#### 2.2.3 half_carry (subtraction)

Used by: `z1hc`, `z1h-`.

**Mechanism**: LOWER_NIBBLE lookups + R1CS constraint

Determines whether a borrow occurred from bit 4 during subtraction.
i.e. `H = 1` iff `(a & 0xF) < (b & 0xF) [+ carry_in]`.

Witness variables:
- H (boolean)

Same mechanism as addition, but all the signs (three of them) are flipped in the constraint
- `nibble_a - nibble_b [- carry_in] = nibble_result - H × 0b1_0000`

ex: for `SBC`: include `- carry_in`. See [§2.3.3](#233-carry-in-for-adcsbc).

Cost: 2–3 lookups + 2 R1CS constraints.

#### 2.2.4 carry (8-bit) - addition/subtraction

Used by: `z0hc`, `z1hc`, `00hc`, and indirectly `-0hc` via carry chaining.

**Mechanism**: R1CS arithmetic identity (no lookup needed)

Addition: , C boolean.
Subtraction: 

Witness variables:
- C (boolean)

Constraints:
1. the following to constrain C:
     1. For addition: `a + b = result + C × 256`
     2. For subtraction, `a - b = result - C × 256` (both signs flipped)
2. `C × (C - 1) = 0` - boolean 

Correctness: 
- note: a,b,result ∈ [0, 255] through lookups (no range check needed)
- C is uniquely determined by addition/subtraction case.

Note: this is used as a sub-routine in `ADC` and `SBC` in [§2.3.3](#233-carry-in-for-adcsbc) (add_carry + inc_overflow pattern).

Cost: 2 R1CS constraints (identity + boolean).

#### 2.2.5 carry (8-bit) - rotates/shifts

Used by: `z00c`, `000c`.

**Mechanism**: R1CS arithmetic identity (no lookup or bit extraction needed)

Each rotate/shift has a specific identity that derives C from the input `x` and lookup `result`:

| Operation | Identity | Witnesses |
|-----------|----------|-----------|
| SLA | `2·x = result + 256·C` | C (boolean) |
| SRL | `x = 2·result + C` | C (boolean) |
| RLC | `2·x = result + 255·C` | C (boolean) |
| RRC | `x = 2·result - 255·C` | C (boolean) |
| SRA | `x = 2·result - 256·msb + C` | C (boolean), msb (boolean) |

`SRA` needs an extra witness (Most Significant Bit (`msb`) = bit 7 of x = bit 7 of result, since `SRA` preserves sign). `msb` is uniquely determined by `x` and `result`.

Derivation notes:
- **SLA**:
     - math: `SLA(x) = (x << 1) & 0xFF`
     - constraint: If bit 7 of x is set, `2x ≥ 256` and C = 1.
      `256·C` captures this
- **SRL**:
     - math: `SRL(x) = x >> 1`
     - constraint:`x = 2·result + C` is equivalent to `x/2` with C as the remainder (bit 0).
- **RLC**:
     - math: `RLC(x) = ((x << 1) | (x >> 7)) & 0xFF`, with `C = x >> 7`.
     - constraint:
          - When C = 0: `result = 2x`
          - When C = 1: `result = 2x - 256 + 1` → `2x = 256 + result - 1` 
          - Combined: `result = 2x - 255·C` → `2·x = result + 255·C`
- **RRC**:
     - math: `RRC(x) = ((x >> 1) | (x << 7)) & 0xFF`, with `C = x & 1`.
     - constraint:
          - When C = 0: `x = 2·result`
          - When C = 1: `x = 2·result - 255`
          - Combined: `x = 2·result - 255·C`.
- **SRA**:
     - math: `SRA(x) = (x >> 1) | (x & 0x80)`, with `C = x & 1`.
     - constraint: `x = 2·result - 256·msb + C`, where `msb` accounts for the sign bit duplication.

Cost:
- 2 constraints + 1 witness (SLA/SRL/RLC/RRC)
- 3 constraints + 2 witnesses (SRA).

### 2.3 Structural constraints

These handle multi-step operations, data routing, and state management that go beyond simple flag derivation.

#### 2.3.1 INC/DEC rr - dual-lookup carry propagation

`INC rr` and `DEC rr` operate on 16-bit register pairs but SM83 registers are 8-bit.

To avoid having to create a 16-bit lookup, or have to avoid splitting these instructions into two steps (costly as these opcodes specifically occur often either directly or as part of the expansion of `LD A,(HL+)`/`LD A,(HL-)`), we use two lookups from the **same** table + three R1CS constraints per cycle.

**INC rr** (e.g., INC BC):

Witness variables (prover-supplied, constrained below):
- `carry` - carry bit from incrementing the low byte (`old_lo = 255`)

1. **Lookup 1**: `new_lo = INC(old_lo)`
2. **Lookup 2**: `inc_hi = INC(old_hi)`
3. **Constraint**: `old_lo + 1 = new_lo + carry × 256` - derives carry
4. **Constraint**: `carry × (carry - 1) = 0` - boolean
5. **Constraint**: `new_hi = old_hi + carry × (inc_hi - old_hi)` - MUX

The carry is uniquely determined by the field equation and boolean constraint: 
- if `old_lo < 255`, the INC table gives `new_lo = old_lo + 1`, forcing `carry = 0`.
- If `old_lo = 255`, the INC table gives `new_lo = 0`, forcing `carry × 256 = 256`, so `carry = 1`. 

Note:
- No is-zero check is needed.
- No range check is required on the result. This is because there are only two case in the MUX constraint:
     1. `old_hi = new_hi` if no carry from `INC old_lo`: it's in range because we didn't modify the high bits
     2. `old_hi != new_hi` is carry comes from `INC old_lo`: the value of `new_hi` comes from the `INC` lookup ([0, 255] by construction).

**DEC rr** (e.g., DEC BC):

Witness variables (prover-supplied, constrained below):
- `borrow` - borrow bit from decrementing the low byte (`old_lo = 0`)

1. **Lookup 1**: `new_lo = DEC(old_lo)`
2. **Lookup 2**: `dec_hi = DEC(old_hi)`
3. **Constraint**: `old_lo - 1 + borrow × 256 = new_lo` - derives borrow
4. **Constraint**: `borrow × (borrow - 1) = 0` - boolean
5. **Constraint**: `new_hi = old_hi + borrow × (dec_hi - old_hi)` - MUX

Symmetric with INC:
- if `old_lo > 0`, `borrow = 0`;
- if `old_lo = 0` (so `new_lo = 255`), `borrow = 1`.

**INC SP / DEC SP** would follow the same pattern if SP is decomposed into SP_hi/SP_lo. However, SP lives outside the 8-bit register model (see [provability.md §3.1.5](./provability.md#315-cpu-state-handled-separately)), so the decomposition mechanism is an open question - see [provability.md TODO: SP decomposition](./provability.md#sp-decomposition).

Note: no flags are modified by INC/DEC rr - the flag outputs of both INC/DEC lookups are discarded by the circuit (no flag routing to F).

#### 2.3.2 Carry-in for RL/RR (rotate through carry)

*Eliminates the need for carry-variant rotate tables*

`RL` (rotate left through carry) and `RR` (rotate right through carry) depend on the current carry flag as input. Rather than doubling the table size for a single bit (required to keep the table size a power of 2), we reuse the existing `SLA` and `SRL` tables and handle carry-in via constraints.

**RL(x, carry_in) - rotate left through carry:**

1. **Lookup**: `sla_result = SLA(x)` - shift left, bit 0 = 0
2. **Constraint**: `result = sla_result + carry_in` - sets bit 0 to carry_in
3. **Carry-out (C)**: same as SLA - bit 7 of input `x` (derived by existing carry constraint)

Key idea for correctness:
- `SLA(x)` always sets bit 0 to 0. That means that `sla_result + carry_in` is guaranteed to never overflow. This means no range check is needed (result is always `[0, 254]` from lookup table + `carry_in` (`[0, 1]`))

**RR(x, carry_in) - rotate right through carry:**

1. **Lookup**: `srl_result = SRL(x)` - shift right, bit 7 = 0
2. **Constraint**: `result = srl_result + carry_in × 128` - sets bit 7 to carry_in
3. **Carry-out (C)**: same as SRL - bit 0 of input `x` (derived by existing carry constraint)

Key idea for correctness:
- `SRL(x)` always sets bit 7 to 0 (so `SRL(x)` < 128). That means that `sla_result + (carry_in × 128)` is guaranteed to never overflow. This means no range check is needed (result is always `[0, 127]` from lookup table + `carry_in × 128` (`0 / 128`))

**Flags**:
- The Z flag is computed from `result` (via [§2.2.1 is_zero](#221-is_zero)). For main-opcode variants (`RLA`, `RRA`), `ForceZeroFlag` overrides Z to 0.
- The C flag is the carry-out (a bit of the original input, unchanged by carry-in)
- N and H are always 0

**Cost**: 1 lookup + 1 R1CS constraint per RL/RR, identical to what SLA/SRL already cost.

#### 2.3.3 Carry-in for ADC/SBC

*Eliminates the need for carry-variant binary tables*

`ADC` (add with carry) and `SBC` (subtract with carry) depend on the current carry flag as input. Rather than doubling the ADD/SUB tables (required to keep the table size a power of 2), we reuse the existing `ADD` and `SUB` tables and handle carry-in via constraints.

**ADC(a, b, carry_in) → result, carry_out:**

Witness variables (prover-supplied, constrained below):
- `add_carry` - carry bit from the `ADD` step (`a + b ≥ 256`)
- `inc_overflow` - overflow bit from adding carry input (`carry_in`) to `ADD` result (`add_result`). i.e. `(add_result + carry_in) ≥ 256`

Note: `add_carry` and `inc_overflow` cannot both be 1
1. Suppose `add_carry = 1`
2. `ADD(a,b) = a + b ∈ [256, 510]`
3. `ADD(a,b) % 256` = `a + b (mod 256) = ∈ [0, 254] = add_result`
4. Therefore, `(add_result + carry_in) ≤ 255`

This gives us the following flow:
1. **Lookup**: `add_result = ADD(a, b)` - standard binary lookup
2. **[§2.2.4](#224-carry-8-bit---additionsubtraction)**: `add_carry` derived from `a + b = add_result + add_carry × 256` (addition identity + boolean)
3. **Constraint**: `result = add_result + carry_in - (inc_overflow × 256)` - derives inc_overflow
4. **Constraint**: `inc_overflow × (inc_overflow - 1) = 0` - boolean
5. **Total carry**: `carry_out = add_carry + inc_overflow` - `add_carry OR inc_overflow`

Note: no range check is needed (lookups + constraints ensure it's ∈ [0, 255])

**SBC(a, b, carry_in) → result, carry_out (borrow):**

Witness variables (prover-supplied, constrained below):
- `borrow` - borrow bit from the `SUB` step (`a < b`)
- `dec_underflow` - underflow bit from subtracting carry input (`carry_in`) from `SUB` result (`sub_result`). i.e. (`sub_result - carry_in < 0`)

Note: `borrow` and `dec_underflow` cannot both be 1
1. Suppose `borrow = 1`
2. `SUB(a,b) = a - b ∈ [-1, -255]`
3. `SUB(a,b) % 256` = `a - b (mod 256) = ∈ [1, 255] = sub_result`
4. Therefore, `(sub_result - carry_in) ≥ 0`

This gives us the following flow:
1. **Lookup**: `sub_result = SUB(a, b)` - standard binary lookup
2. **[§2.2.4](#224-carry-8-bit---additionsubtraction)**: `borrow` derived from `a - b + borrow × 256 = sub_result` (subtraction identity + boolean)
3. **Constraint**: `result = sub_result - carry_in + dec_underflow × 256` - derives dec_underflow
4. **Constraint**: `dec_underflow × (dec_underflow - 1) = 0` - boolean
5. **Total borrow**: `carry_out = borrow + dec_underflow` - `borrow OR dec_underflow`

Note: no range check is needed (lookups + constraints ensure it's ∈ [0, 255])

**Half-carry note**: For `ADC`/`SBC`, the half-carry includes `carry_in` as an input (see [§2.2.2](#222-half_carry-addition) and [§2.2.3](#223-half_carry-subtraction) for which opcodes set `carry_in` to true).

**Cost**: 1 lookup + 5 R1CS constraints per ADC/SBC (2 from [§2.2.4](#224-carry-8-bit---additionsubtraction) + 2 for inc_overflow/dec_underflow + 1 total carry). The register write provides the range check on `result` at no additional cost.

#### 2.3.4 Carry chaining for dual ADD+ADC lookups

<!-- TODO: specify. Applies to opcodes 0x29 ADD HL,HL, 0x39 ADD HL,SP,
     0xE8 ADD SP,i8, 0xF8 LD HL,SP+i8.
     The carry output of the first lookup (ADD on low byte) feeds into
     the carry-in of the second step (ADC on high byte) via the
     carry-in constraint from §2.3.3. The carry chain is:
     1. ADD(lo_a, lo_b) → lo_result, with add_carry derived by constraint
     2. ADC(hi_a, hi_b, add_carry) → hi_result, using §2.3.3
     The key difference from regular ADC (where carry_in comes from F)
     is that here carry_in comes from the first lookup within the same
     zk-cycle. The constraint is identical - carry_in is just sourced
     from a different witness variable.
     Note: distinct from the expanded 4-read ADDs (0x09/0x19) where
     carry flows between two separate zk-cycles via F. -->

#### 2.3.5 SP decomposition

<!-- TODO: blocked on resolving the SP decomposition open question in
     provability.md (see "SP decomposition" section under TODOs).
     Once the storage model is decided, specify the constraint wiring
     here for opcodes 0x33, 0x3B, 0x39, 0xE8, 0xF8. -->

#### 2.3.6 ADD SP,i8 sign extension

<!-- TODO: specify. Applies to 0xE8 ADD SP,i8 and 0xF8 LD HL,SP+i8.
     The high-byte ADC step uses a second operand of 0x00 (positive i8)
     or 0xFF (negative i8) depending on bit 7 of the immediate.
     The constraint must prove this sign-extension byte is correctly
     derived from the immediate. This is data-dependent. -->

#### 2.3.7 POP AF flag masking

<!-- TODO: specify. POP AF writes the popped low byte into F, but hardware
     masks the lower nibble to 0 (only bits 7-4 are flag bits).
     The constraint needs to enforce F & 0x0F == 0.
     Options:
     - Nibble decomposition: F = F_hi * 16, F_hi ∈ [0, 15]
     - Bit decomposition of lower nibble: constrain bits 0-3 = 0 -->

### 2.4 Control flow

<!-- TODO: specify constraints for each control flow pattern.
     These are the constraints that don't involve ALU lookups
     but enforce correct PC/SP updates. -->

#### 2.4.1 PC increment (normal execution)

<!-- TODO: PC += instruction_length. Constraint ties PC_next to PC_curr
     plus the byte width of the current instruction (1, 2, or 3 bytes).
     Virtual opcodes (from expansions) do NOT increment PC. -->

#### 2.4.2 Relative jumps (JR)

<!-- TODO: JR i8 - PC += 2 + sign_extend(i8). Conditional variants
     (JR NZ, JR Z, JR NC, JR C) need flag-gated MUX:
     PC_next = taken ? (PC + 2 + offset) : (PC + 2) -->

#### 2.4.3 Absolute jumps (JP, CALL, RST)

<!-- TODO: JP u16 - PC = immediate. CALL u16 - push PC+3, PC = immediate.
     RST - push PC+1, PC = vector. Conditional variants need flag-gated MUX.
     CALL/RST involve stack operations (see §2.4.5). -->

#### 2.4.4 Returns (RET, RETI)

<!-- TODO: RET - pop 2 bytes from stack into PC. RETI - same + set IME.
     Conditional RET variants need flag-gated MUX.
     Stack operations involved (see §2.4.5). -->

#### 2.4.5 Stack operations (PUSH/POP)

<!-- TODO: PUSH - SP -= 2, write 2 bytes to [SP+1] and [SP].
     POP - read 2 bytes from [SP] and [SP+1], SP += 2.
     These involve SP modification (±2) and two RAM accesses.
     SP ± 2 may need its own carry-propagation constraint
     (similar to INC/DEC rr but with ±2 instead of ±1). -->

#### 2.4.6 Interrupt dispatch

<!-- TODO: specify as virtual opcode sequence. When an interrupt fires:
     1. Clear IME
     2. Push PC onto stack (2 RAM writes)
     3. Jump to vector address
     4. Clear corresponding IF bit
     Resource profile: R(IF), R(IE), W(IF), W(IME), W(PC), R(SP), W(SP), 2×RAM write. -->

---

## 3. Open design questions

1. **`RL`/`RR`/`RLA`/`RRA`**: Right now we don't expand how `RLA`and`RRA` handle carry-in inputs. Additionally, `ForceZeroFlag` usage is not clear enough. 

2. **Carry chaining on `00hc`**: both `ADD SP,i8` and `LD HL,SP+i8` derive their flags from the low-byte ADD directly. `LD HL,SP+i8` additionally requires carry chaining for the high-byte result (→ H register). Whether `ADD SP,i8` also requires carry chaining depends on the SP storage model - see [§2.3.5](#235-sp-decomposition). If SP is monolithic, no carry chain is needed for the result; if SP is decomposed into hi/lo, it is.

3. **Carry chaining for dual lookups**: Opcodes that use `ADD+ADC` in a single zk-cycle (0x29 ADD HL,HL, 0x39 ADD HL,SP, 0xE8 ADD SP,i8, 0xF8 LD HL,SP+i8) require the carry output of the first lookup to feed into the carry-in of the second step. The mechanism is specified in [§2.3.4](#234-carry-chaining-for-dual-addadc-lookups) - the carry-in constraint from [§2.3.3](#233-carry-in-for-adcsbc) applies, with the carry sourced from the first lookup rather than F. The TODO is to fully specify the constraint wiring. (Note: distinct from the expanded 4-read ADDs like 0x09/0x19 where carry flows between two separate zk-cycles via F.)

4. **ADD SP,i8 / LD HL,SP+i8 sign extension**: The high-byte ADC step uses a second operand of `0x00` (positive i8) or `0xFF` (negative i8) depending on bit 7 of the immediate. The constraint must prove this sign-extension byte is correctly derived from the immediate. This is data-dependent and not currently modeled.

6. **POP AF flag masking**: POP AF writes the popped low byte into F, but hardware masks the lower nibble to 0 (only bits 7–4 are flag bits). No lookup is used. The constraint system needs to enforce `F & 0x0F == 0`, which requires either a dedicated constraint or a range check. This is not captured in the current tables.

7. **Interrupt dispatch**: When an interrupt fires, the CPU clears IME, pushes PC onto the stack (2 RAM writes), jumps to the vector address, and clears the corresponding IF bit. This is functionally a synthetic `CALL vector` + `DI` + IF modification. It needs a virtual opcode or equivalent model. Resource profile: R(IF), R(IE), W(IF), W(IME), W(PC), R(SP), W(SP), 2×RAM write.

8. **DAA flag-as-input**: DAA uses three flag bits (N, H, C) as table inputs, violating the [design principle](#design-principle-tables-as-pure-functions). See [§1.3](#13-daa--open-design-question) for discussion and resolution options.

9. **MLE investigation**: Jolt's MLE-based lookup argument makes bit extraction essentially free - each input bit is an MLE variable. Given Nightstream's Shout supports similar MLE decomposition, some operations specified as separate lookups (e.g., LOWER_NIBBLE) may be achievable at zero additional cost within existing table evaluations. Additionally, our `LOWER_NIBBLE` approach currently may require certain opcodes to trigger 3+ lookups (ideally, we bound the number of lookups per opcode. However, if it's the most efficient way of doing things, we can increase the limit).

10. **16-bit half-carry**: the `half_carry` section currently doesn't mention special handling in the 16-bit case.

[linear]: #linear--linear-constraints
[const]: #const--constant-outputs
[provability-virt-add]: ./provability.md#3322-handling-4-register-add
