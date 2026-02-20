# Game Boy Provability

How every memory region, I/O register, and internal state element is
classified for zero-knowledge proving in the Nightstream zkVM.

## Table of Contents

- [The Five Categories](#the-five-categories)
- [Decision Criteria](#decision-criteria)
- [1. Memory Regions](#1-memory-regions)
- [2. I/O Registers](#2-io-registers)
- [3. The Timer](#3-the-timer)
- [4. The IF Register Model](#4-the-if-register-model)
- [5. Design Decisions](#5-design-decisions)
  - [5.1 ROM as Shout](#51-rom-as-shout)
  - [5.2 MBC Bank Registers](#52-mbc-bank-registers)
  - [5.3 ERAM and the Save System](#53-eram-and-the-save-system)
  - [5.4 OAM DMA](#54-oam-dma)
  - [5.5 DMA Trigger](#55-dma-trigger)
  - [5.6 Echo RAM](#56-echo-ram)
  - [5.7 JOYP (Mixed Ownership)](#57-joyp-mixed-ownership)
  - [5.8 STAT (Mixed Ownership)](#58-stat-mixed-ownership)
  - [5.9 Serial and Link Cable](#59-serial-and-link-cable)
  - [5.10 Initial State](#510-initial-state)
  - [5.11 Static ROM Scan](#511-static-rom-scan)
  - [5.12 CPU Register Events](#512-cpu-register-events)
  - [5.13 CPU R/W Latch Registers](#513-cpu-rw-latch-registers)
  - [5.14 HALT and STOP](#514-halt-and-stop)
  - [5.15 Instruction Fetch Proving](#515-instruction-fetch-proving)
  - [5.16 Range Checks and Field Size](#516-range-checks-and-field-size)
  - [5.17 Unproven Sub-types](#517-unproven-sub-types)
- [6. Complete Classification](#6-complete-classification)

---

## The Five Categories

Every memory operation in the proof falls into one of five categories:

- **Twist (read-write, internally proven)**: Read/write consistency is verified
  by the proof. Every read must return the last value written to that address.
  Used for RAM, HRAM, VRAM, OAM, CPU registers, and select I/O registers.

- **Shout (read-only, internally proven)**: Lookup consistency is verified by
  the proof against a committed table. The table is immutable — there are no
  writes, only reads. Used for ROM (per-bank lookup tables) and ALU operations
  (precomputed result tables).

- **Computed (internal register with external tape)**: The proof owns the
  register as internal state and computes its read value from a mix of proven
  sources (CPU writes, deterministic subsystems) and witnessed external input
  (button state, interrupt events). Neither pure Twist (because external input
  contributes) nor pure Witness (because the proof constrains part of the
  value). Used for IF ($FF0F) and JOYP ($FF00).

- **Witness (externally provided)**: The prover supplies the value on a tape.
  The proof verifies the CPU behaved correctly *given that value*, but does
  not prove the value itself is correct. Used for state that depends on the
  outside world or on unproven subsystems.

- **Unproven**: The proof does not verify these registers/values as part
  of any Twist, Shout, Witness, or Computed mechanism. CPU writes are not
  tracked. Three sub-types control how reads are handled:

  - **Unproven (reject)**: No proof mechanism exists for this address. A
    bus read targeting this address has no TwistId, ShoutId, or witness
    routing — the constraints are unsatisfiable and no valid proof can be
    produced. The static ROM scan rejects games that read from these
    addresses. Used for the unusable range ($FEA0-$FEFF) where hardware
    behavior is undefined and revision-dependent.

  - **Unproven (passthrough — constant)**: The value is a deterministic
    hardware constant (e.g., $FF for unmapped registers, $FF for SB with
    no cable). The proof constrains the read to the exact known value —
    no witness needed, no forgery possible. Used for unmapped/CGB-only
    addresses (always $FF on DMG) and serial registers (constrained to
    "no cable" values to prevent serial data forgery).

  - **Unproven (passthrough — emulator)**: The prover's emulator knows
    the value from its own internal subsystem state. The proof treats
    reads as unconstrained 8-bit witness values — the CPU's behavior
    given the value is proven, but the value itself is not verified. No
    witness tape infrastructure is needed; the value is inline in the
    step row. Used for APU registers and DMA readback. Safe because the
    prover only affects their own proof (no multiplayer/external-trust
    concern).

  - **Unproven (tape)**: Like emulator passthrough in security model
    (unconstrained 8-bit witness), but the value comes from an explicit
    witness tape recorded during the user's play session, rather than
    from an emulator embedded in the prover. Tape and emulator
    passthrough are architecturally equivalent — see
    [§5.17](#517-unproven-sub-types) for trade-off analysis. No DMG
    addresses currently use tape (all use emulator passthrough instead).

---

## Decision Criteria

**Must be Twist** if the CPU both writes and reads the register, and the value
is entirely CPU-controlled (no subsystem modifies it between steps).

**Must be Witness** if the value can change between CPU steps without the CPU
writing to it (subsystem-modified or external input), AND the CPU reads it.

**Must be Computed** if the register has mixed ownership — the CPU writes
some bits (proven), and an external source sets other bits (witnessed) — AND
the proof needs the read value to be consistent with both. The proof owns
the register as internal state and computes reads from proven + witnessed
inputs. See IF ([§4](#4-the-if-register-model)) and JOYP
([§5.7](#57-joyp-mixed-ownership)).

**Can be Unproven (reject)** if the address has no well-defined hardware
behavior (varies by chip revision, undefined memory region) AND reading it
is not useful for any legitimate game logic. The constraints have no
routing entry — reads are unsatisfiable.

**Can be Unproven (passthrough — constant)** if the address always
returns the same value on DMG hardware regardless of CPU or subsystem
state (unmapped → $FF, CGB-only → $FF, serial with no cable → $FF/$7E).
The proof constrains the read to the exact value. This is stronger than
an unconstrained witness — it prevents the prover from claiming a
different value. SB is constrained to $FF to prevent serial data forgery
(see [§5.9](#59-serial-and-link-cable)).

**Can be Unproven (passthrough — emulator)** if the address is part of
a subsystem we don't prove (APU) AND the prover's emulator fully models
the read value AND there is no external-trust concern (no multiplayer
data, no cross-device interaction). The proof treats reads as
unconstrained 8-bit witnesses. The prover has no incentive to lie — they
are proving their own execution. A malicious prover forging a wrong
passthrough value would need to construct a valid execution trace through
the game's logic given that wrong value, gaining nothing (the prover is
proving their own play session). The prover already controls button
inputs and interrupt timing, which provide the same code-path
manipulation ability.

**Can be Unproven (tape)** as an alternative to emulator passthrough.
Both deliver the same unconstrained 8-bit witness with the same security
model. Tape records the values during the user's play session and feeds
them to the prover; emulator passthrough re-derives them from a headless
emulator embedded in the prover. The choice is an engineering trade-off
(see [§5.17](#517-unproven-sub-types)), not a security distinction. No
DMG addresses currently use tape — all use emulator passthrough instead.

**Mixed ownership does not always mean Computed.** If the CPU-written bits
have no causal effect inside the proof boundary (they only matter to an
unproven subsystem), the register can remain Witness despite having mixed
ownership. See STAT ([§5.8](#58-stat-mixed-ownership)) for an example where
this applies, vs JOYP ([§5.7](#57-joyp-mixed-ownership)) where the
CPU-written bits DO affect the proven read value.

**Never gate Twist access on a witnessed value.** If a Twist region's
read behavior were conditioned on a witnessed register (e.g., returning $FF
when a witnessed PPU mode indicates bus contention), a malicious prover
could manipulate the witness to corrupt proven memory reads. This invariant
holds regardless of whether the gating register is Witness or Computed —
the mode bits come from an external tape in both cases. The only way to
safely gate memory access on PPU mode is to prove PPU mode transitions.
See [§5.8](#58-stat-mixed-ownership) for full analysis.

**Deterministic subsystem** (special case): If a subsystem is fully
deterministic (computable from CPU cycle count + configuration), it can be
proven inside the proof boundary rather than witnessed. The Game Boy timer
falls into this category — see [§3](#3-the-timer).

---

## 1. Memory Regions

See [§6](#6-complete-classification) for the complete address-ordered table.

| Region | Address Range | Category | TwistId | Notes |
|--------|--------------|----------|---------|-------|
| ROM | $0000-$7FFF | **Shout** | PROG_BANK_SHOUT(N+bank) | Per-bank read-only lookup tables. See [§5.1](#51-rom-as-shout). |
| VRAM | $8000-$9FFF | Twist | VRAM_ID(3) | CPU reads/writes. Not gated on PPU mode (see [§5.8](#58-stat-mixed-ownership)). |
| ERAM | $A000-$BFFF | Twist | ERAM_ID(7) | Cartridge RAM, all-zeros init. See [§5.3](#53-eram-and-the-save-system). |
| WRAM | $C000-$DFFF | Twist | RAM_ID(0) | Work RAM, CPU-only access. |
| Echo | $E000-$FDFF | Twist | RAM_ID(0) | Hardware alias of WRAM, normalized to same offset. See [§5.6](#56-echo-ram). |
| OAM | $FE00-$FE9F | Twist | OAM_ID(6) | Conditional per-game config. See [§5.4](#54-oam-dma). |
| Unusable | $FEA0-$FEFF | — | — | Modeled as returning $FF. Actual DMG behavior varies by revision. Reads rejected by static ROM scan. |
| IO | $FF00-$FF7F | Twist | ?? | Memory mapped I/O
| HRAM | $FF80-$FFFE | Twist | HRAM_ID(5) | CPU-only access (not affected by DMA). |

ROM is read-only (Shout). All other regions are CPU-controlled read/write
(Twist). ERAM is Twist with enforced all-zeros initialization (no save data
injection — see [§5.3](#53-eram-and-the-save-system)).

---

## 2. I/O Registers

Each I/O register is classified by its role in the proof. See
[§6](#6-complete-classification) for the complete address-ordered map covering
all $FF00-$FF7F addresses (including unmapped and CGB-only registers).

### Twist (proven — CPU-only writes, CPU reads back)

| Address | Name | Justification |
|---------|------|---------------|
| $FFFF | IE | Interrupt enable. CPU-only writes and reads. Proving this constrains which interrupt types the CPU can respond to. Even though IF timing is witnessed, IE being Twist means the prover can only trigger interrupt types the game explicitly enabled. |

### Twist (proven — deterministic timer subsystem)

The Game Boy timer is fully deterministic: it's driven by an internal counter
that increments every T-cycle. There is no external clock (unlike MBC3 RTC).
Given the CPU cycle count and TAC/TMA configuration, every timer event is
computable. See [§3](#3-the-timer) for full analysis.

| Address | Name | Justification |
|---------|------|---------------|
| $FF04 | DIV | Upper 8 bits of internal 16-bit counter. Derived state — computable from elapsed T-cycles + DIV write history. |
| $FF05 | TIMA | Timer counter. Derived state — computable from counter + TAC + TMA + TIMA write history. |
| $FF06 | TMA | Timer modulo (reload value). CPU-only writes. Timer reads it on TIMA overflow but never modifies it. |
| $FF07 | TAC | Timer control (enable + clock select). CPU-only writes. Timer reads it but never modifies it. |

Proving the timer means IF bit 2 (timer interrupt) is constrained by the
proof rather than witnessed. This is valuable because many games are
timer-interrupt-driven (music, game logic timers).

### Witness (externally provided)

| Address | Name | Why Witness |
|---------|------|-------------|
| $FF41 | STAT | LCD status. Mode bits (0-1) and LYC flag (bit 2) set by PPU. CPU writes bits 6-3 (interrupt enables) but these have no causal effect inside the proof — they only matter to the unproven PPU. Witness for the whole byte. See [§5.8](#58-stat-mixed-ownership) for the STAT-OAM interaction analysis. |
| $FF44 | LY | Current scanline. Driven by PPU. |

### Computed (internal registers with external witness tapes)

| Address | Name | Justification |
|---------|------|---------------|
| $FF00 | P1/JOYP | Joypad. Mixed ownership — CPU writes bits 5-4 (selection), external tape provides 8-bit button state. Proof computes read value: `0xC0 \| (cpu_selection & 0x30) \| mux(selection, buttons)`. Full model in [§5.7](#57-joyp-mixed-ownership). |
| $FF0F | IF | Interrupt flags. CPU writes (proven), timer overflow on bit 2 (proven), external interrupt tape providing bits 0,1,3,4 (witnessed). Full model in [§4](#4-the-if-register-model). |

### Twist (CPU R/W latch — PPU reads but never writes)

These registers are written exclusively by the CPU and read back by the CPU.
The PPU reads them for rendering but never modifies them via the bus. Twist
classification means "CPU reads return the last CPU-written value" — nothing
more. This does NOT mean rendering is proven or that the PPU's consumption
of these values enters the proof.

Cost: zero — they share IO_ID(4) with existing Twist registers (IE, timer).
Benefit: avoids rejecting games that read these back for game logic
(parallax scrolling checks, palette readback, window position queries, LCD
enable bit checks).

| Address | Name | Justification |
|---------|------|---------------|
| $FF40 | LCDC | CPU R/W latch. PPU reads but never writes. Games read bit 7 (LCD enable). |
| $FF42 | SCY | CPU R/W latch. Games read for parallax scrolling logic. |
| $FF43 | SCX | CPU R/W latch. Same as SCY. |
| $FF45 | LYC | CPU R/W latch. PPU compares with LY but never modifies LYC itself. |
| $FF47 | BGP | CPU R/W latch. Some games read palette back. |
| $FF48 | OBP0 | CPU R/W latch. Same as BGP. |
| $FF49 | OBP1 | CPU R/W latch. Same as BGP. |
| $FF4A | WY | CPU R/W latch. Games read for dynamic window effects. |
| $FF4B | WX | CPU R/W latch. Same as WY. |

### Unproven (sub-typed — see §5.17)

These registers are written by the CPU to configure subsystems we don't
prove. CPU writes are not tracked. Reads are handled per sub-type — see
[§5.17](#517-unproven-sub-types) for the full model.

- **SB/SC** ($FF01-$FF02): **Passthrough (constant)** — $FF/$7E ("no
  cable"). See [§5.9](#59-serial-and-link-cable).
- **APU** ($FF10-$FF3F): **Passthrough (emulator)** — prover's APU
  state. Audio excluded from proving.
- **DMA** ($FF46): **Passthrough (emulator)** when OAM is unproven
  (Tier 3). Proven structural trigger when OAM is Twist (Tier 1/2).
  See [§5.4](#54-oam-dma) and [§5.5](#55-dma-trigger).
- **Unmapped / CGB-only** ($FF03, $FF08-$FF0E, $FF4C-$FF7F, etc.):
  **Passthrough (constant)** — $FF on DMG.

At ROM load time, a static scan rejects games that read from **Unproven
(reject)** addresses — see [§5.11](#511-static-rom-scan). Passthrough
addresses (both constant and emulator) are allowed.

---

## 3. The Timer

The Game Boy timer is fully deterministic — it has **no external clock
source**. The entire mechanism is:

```
Internal 16-bit counter (increments every T-cycle at 4.194304 MHz)
    |
    +-- Bits 15-8 -> DIV register ($FF04)
    |
    `-- Bit selected by TAC[1:0] --> AND TAC[2] (enable)
                                          |
                                     falling edge detector
                                          |
                                      TIMA += 1
                                          |
                                   overflow (FF->00)?
                                      +-- yes: TIMA <- TMA, set IF bit 2
                                      `-- no:  continue
```

Given:
- Initial counter value (0 at power-on, or known post-boot value)
- CPU cycle count at each step (deterministic from the trace)
- DIV write history (CPU resets counter to 0)
- TAC write history (CPU enables/configures timer)
- TMA write history (CPU sets reload value)
- TIMA write history (CPU can write directly to TIMA)

...every DIV value, TIMA value, and timer interrupt (IF bit 2) is fully
computable. No witness needed for timer behavior.

### Proof cost

The timer adds roughly **4-8 constraints per CPU step**:

1. Advance internal counter by `t_cycles` (= m_cycles * 4)
2. Check if the selected counter bit had a falling edge
3. If falling edge + TAC enabled: increment TIMA
4. If TIMA overflowed: reload from TMA, assert IF bit 2

The 4-constraint case is the common path (no timer register writes in the step).
Steps that write to TAC or DIV push the count higher:

- **DIV write** resets the internal counter to 0, which may cause a falling
  edge on the currently-selected bit (extra edge-detection constraint)
- **TAC write** can change the selected bit or the enable flag, either of
  which can trigger a falling edge (extra edge-detection constraint)
- **TIMA overflow countdown**: if the step includes a TIMA overflow, the
  TMA reload check and IF bit 2 assertion add ~2 more constraints

Worst case (step writes TAC or DIV while timer is running) is ~8 constraints.
This is still trivial compared to the CPU instruction constraints (~20-50 per step).

**Overflow model**: The proof uses instantaneous overflow: when TIMA
overflows, TMA is loaded and IF bit 2 is set in the same step. Real DMG
hardware has a 4-T-cycle delay between overflow and TMA reload (during
which TIMA reads as 0x00 and writing TIMA cancels the reload). The
instantaneous model is a deliberate simplification — it changes the value
a game sees if it reads TIMA in the 4-cycle reload window, but this is
an extremely rare code pattern. The constraint count estimate (~4-8 per
step) reflects the instantaneous model.

### What this buys us

- Timer interrupts are **proven correct**, not just witnessed
- IF bit 2 is constrained (prover can't inject fake timer interrupts)
- Games using timer for music/logic have verified interrupt timing
- TAC/TMA/DIV/TIMA don't need witness tape entries

---

## 4. The IF Register Model

IF ($FF0F) has mixed ownership — some bits are proven, others depend on
external events:

| Bit | Source | Ownership |
|-----|--------|-----------|
| 0 | VBlank (PPU) | External interrupt tape (PPU unproven) |
| 1 | STAT (PPU) | External interrupt tape (PPU unproven) |
| 2 | Timer | **Proven** (computed by timer subsystem) |
| 3 | Serial | **Always 0** (link cable unsupported). Future: recursive SNARK sets this bit. |
| 4 | Joypad | External interrupt tape (player input) |

### Why IF is not a simple witness

IF is a sticky-bit register: each bit is independently SET by its source and
only CLEARED by CPU writes. The value persists across steps. A raw witness
byte (where the prover provides the full IF value each step) is a poor fit —
it obscures the update semantics and creates tension between CPU writes and
witness values.

### Model: Computed internal register

IF is owned by the proof system as internal state. It is **computed** each step
from three sources:

1. **CPU activity** (proven): The CPU can read IF and write to it (e.g.,
   replacing the whole byte during interrupt dispatch, or explicit
   `LD [$FF0F], A`). CPU writes are part of the instruction trace.

2. **Timer contribution** (proven): The deterministic timer subsystem computes
   whether an overflow occurred. If so, bit 2 is OR'd into IF.

3. **External interrupt tape** (witnessed): A 3-bit mask per step indicating
   which external interrupt sources fired: `{vblank, stat, joypad}`.
   These bits are OR'd into IF. (Serial bit 3 is always 0 — link cable
   unsupported. See [§5.9](#59-serial-and-link-cable).)

### Per-step update sequence

    1. CPU reads IF          -> current internal value (used for interrupt check)
    2. CPU may write IF      -> replaces entire byte (e.g., clearing serviced bit)
    3. Timer advances        -> if overflow since last step: IF |= 0x04
    4. External tape         -> IF |= ext_bits (bits 0, 1, 4 only; bit 3 always 0)

After step 4, IF holds the value that the next step's CPU will read.

### What the prover controls

The prover provides the external interrupt tape — a 3-bit mask per step. This
controls when VBlank, STAT, and joypad interrupts fire. The prover does NOT
control:

- Timer interrupts (bit 2) — computed by the proven timer subsystem
- Which interrupt types the CPU responds to — constrained by IE (Twist)

For single-player proofs, this is the correct trust model: the prover ran the
real emulator and is proving their actual execution. The external tape records
what really happened. A malicious prover forging fake interrupts would need to
construct a valid execution trace through the game's interrupt handlers —
extremely difficult in practice, and the CPU's behavior given those interrupts
is still fully proven.

### CPU writes to IF

When the CPU writes to IF (during interrupt dispatch or explicit store), the
written value replaces IF entirely. This is an internal state change — no
witness interaction. The timer and external tape then OR their contributions
on top of the CPU-written value before the next step reads IF.

Example — interrupt dispatch clears bit 0 (VBlank serviced):

    Step N:   CPU reads IF = 0x05 (VBlank + Timer pending)
              CPU dispatches VBlank, writes IF = 0x04 (clears bit 0)
              Timer: no overflow -> IF stays 0x04
              Ext tape: no new events -> IF stays 0x04
    Step N+1: CPU reads IF = 0x04 (Timer still pending)

### Extensibility

If we later prove the PPU (making VBlank/STAT deterministic), we move bits 0
and 1 from the external tape to the computation — same model, just fewer
witnessed bits. The external tape shrinks to 1 bit (joypad only). Similarly,
if recursive SNARK multiplayer is implemented, bit 3 (serial) moves from
"always 0" to a proven contribution from the composed proof.

### Witness temporal consistency

Witnessed values (LY, STAT mode, external interrupt bits) are **temporally
unconstrained** — the prover could provide LY=0 then LY=140 on consecutive
steps. This is by design: the prover ran the real emulator and the proof
verifies CPU behavior *given those values*, not the values themselves. If
PPU proving is added later, these witnessed values become constrained by the
PPU state machine and temporal consistency follows automatically.

---

## 5. Design Decisions

Subsections 5.1-5.6 cover memory regions and banking. Subsections 5.7-5.9
cover I/O registers. Subsections 5.10-5.12 cover cross-cutting concerns.

### 5.1 ROM as Shout

ROM is never written during execution. Twist is designed for read-write
memory — its proof mechanism tracks `prev_val / next_val` deltas at every
access to verify consistency. For ROM, every read has delta = 0, meaning all
that write-tracking machinery is wasted work.

ROM uses **Shout** (read-only lookup), not Twist.

**Why Shout is the right fit**:

1. **Semantically exact**: Shout is a read-only lookup: given a key, return a
   value. ROM is literally a read-only lookup: given an address, return a byte.
   No write tracking, no delta computation.

2. **Infrastructure supports it**: Investigation of the Nightstream Shout trait
   (`neo-vm-trace/src/lib.rs`) confirms:
   - `Shout::lookup(shout_id, key) -> Word` — key is any `Word`, no
     interleaving requirement. Direct `address -> byte` works natively.
   - `ShoutId(u32)` — unlimited, freely assignable. No hardcoded set.
   - Tables are arbitrary size (`LutTable` with `k = log2(size)`).
   - Multiple tables per shard fully supported and tested.

3. **Per-bank ROM tables**: Each ROM bank gets its own ShoutId with a 14-bit
   within-bank offset as the key. Only banks actually accessed during a shard
   incur proving cost. For a 512KB ROM (32 banks) where a shard touches 4
   banks, proving cost covers 4 x 16KB = 64KB, not the full 512KB.

4. **Cost model**: O(steps x ports + log k), where k = bank size. For a 16KB
   bank (k=14), that's ~14 bits of work per lookup. Trivial compared to CPU
   constraints.

**ROM bank Shout layout**:

```
PROG_BANK_SHOUT(0)  -> ShoutId(N+0), keys 0x0000-0x3FFF  (bank 0, always mapped)
PROG_BANK_SHOUT(1)  -> ShoutId(N+1), keys 0x0000-0x3FFF  (bank 1)
...
PROG_BANK_SHOUT(B)  -> ShoutId(N+B), keys 0x0000-0x3FFF  (bank B)
```

Where N is the first ShoutId after ALU tables. The MBC bank register state
(tracked as MBC_ID Twist — see [§5.2](#52-mbc-bank-registers)) determines
which ShoutId each $4000-$7FFF read maps to.

**Public input**: The ROM image (or its hash) is the public input that the
verifier uses to check the Shout table commitments. The prover cannot
substitute a different ROM.

**Implication for adding-new-opcode-set.md**: Replace all `PROG_ID` Twist
references with Shout-based ROM lookups. The `twist.load(PROG_ID, pc)` calls
become `shout.lookup(PROG_BANK_SHOUT(bank), offset)`.

### 5.2 MBC Bank Registers

MBC bank registers control which ROM and ERAM banks are mapped. They live in
cartridge address space ($0000-$7FFF) — the same range as ROM reads. Every ROM
read at $4000-$7FFF needs the current bank value to select the correct Shout
table (`PROG_BANK_SHOUT(bank)`). If the bank register is unproven, a malicious
prover could claim any bank is mapped and read arbitrary ROM data.

MBC bank registers are **Twist** under a new `MBC_ID` TwistId.

The bank register is CPU-controlled write-only state (CPU writes to it, the
address decoder reads from it). Twist is the natural fit: `twist.store()` on
writes, `twist.load()` when translating banked ROM reads. The Twist memory
argument automatically proves that every load returns the last stored value —
no custom CCS constraints needed.

**Why Twist**: The bank register value must be cryptographically bound to the
proof. The user is running the proof system client-side so we have to ensure
that every in-memory value (even if it's purely in the prover system) is
secure against client-side modification (i.e. included in the proof generation
process).

**Address separation**: Writes to $0000-$7FFF go to MBC_ID Twist (bank
registers). Reads from $0000-$7FFF go to ROM Shout tables. The proof
distinguishes these by operation type: `twist.store(MBC_ID, ...)` for writes,
`shout.lookup(PROG_BANK_SHOUT(...), ...)` for reads. There is no ambiguity
because MBC registers are write-only and ROM is read-only.

**MBC_ID address layout** (internal to the Twist region, not bus addresses):

| MBC_ID addr | Register | Used by |
|-------------|----------|---------|
| 0 | ROM bank low (BANK1 / ROMB_LO) | All MBC types |
| 1 | ROM bank high (ROMB_HI) | MBC5 only (1 bit). Unused by MBC1/2/3 (store 0). |
| 2 | RAM bank / BANK2 | MBC1: BANK2 (2-bit, affects ROM+RAM). MBC3: RAM bank or RTC select (0-$0C). MBC5: RAMB (4-bit). MBC2: unused. |
| 3 | Mode | MBC1 only (0 or 1). Unused by MBC2/3/5. |
| 4 | RAM enable | All MBC types with RAM. |

Address 1 is split out from the old "BANK2 / RAM bank" to accommodate
MBC5's separate ROMB_HI register. MBC1/2/3 store 0 at address 1 (they
have no high ROM bank bit). The RAM bank for MBC1 uses address 2 (what
MBC1 calls BANK2). This layout covers MBC1, MBC2, MBC3, and MBC5 without
per-type branching in the address mapping.

**Cost**: One extra Twist load per step that fetches from banked ROM ($4000-
$7FFF) to read the current bank value. MBC5 banked reads additionally load
address 1 (ROMB_HI) to form the full 9-bit bank number. The bank cannot
change mid-instruction, so one load per step suffices (two for MBC5).
Worst-case Twist budget: 11 -> 13 events/step.

**ROM read sequence**:
1. `bank = twist.load(MBC_ID, 0)` — get current ROM bank
2. `offset = addr & 0x3FFF` — within-bank offset
3. `byte = shout.lookup(PROG_BANK_SHOUT(bank), offset)` — ROM lookup

For $0000-$3FFF (always bank 0): skip step 1, use `PROG_BANK_SHOUT(0)`
directly. No MBC_ID load needed for fixed-bank reads.

### 5.3 ERAM and the Save System

ERAM ($A000-$BFFF) is **Twist** under `ERAM_ID(7)`. Always initialized to
all zeros.

**Why ERAM must be proven**: The Pan Docs MBC1 page states:

> "External RAM is no slower than the Game Boy's internal RAM, so many games
> use part of the external RAM as extra working RAM, even if they use another
> part of it for battery-backed saves."
>
> — [Pan Docs: MBC1](https://gbdev.io/pandocs/MBC1.html)

ERAM is not just for save data. Games actively use $A000-$BFFF as overflow
working memory during normal execution — reading and writing it the same way
they use WRAM. Making ERAM unproven would break many common games.

**Why initialization must be all zeros (no save data injection)**:

On real hardware, ERAM is battery-backed — it retains data across power
cycles, allowing games to save progress. A user could modify their cartridge's
save file to inject arbitrary data into ERAM before starting a play session.

In our proof model, ERAM starts at all zeros (matching a fresh cartridge with
no save data). This is enforced by the Twist initial state commitment. The
consequences:

**Divergence from hardware**: Real DMG SRAM powers on to indeterminate
values, and uninitialized/dead-battery cartridges typically read $FF
(pull-up resistors). Our all-zeros initialization is a deliberate choice —
it provides a deterministic starting state that satisfies the Twist
commitment. Games with save systems use checksums or magic signatures to
detect valid save data; all-zeros fails these checks identically to $FF
(both are "no valid save"), causing the game to offer "New Game" only.
Games that use ERAM as working RAM always write before read, so the
initial value is irrelevant.

1. **No save file loading.** The Game Boy has no built-in save system — it's
   entirely cartridge-level (MBC writes to SRAM). Since ERAM starts at zeros,
   games that check for a save file will find none and start a new game. This
   is correct behavior for proving a fresh playthrough.

2. **Save writes are proven but ephemeral.** Games that auto-save during
   gameplay (e.g., Pokemon writing to SRAM after catching a Pokemon) execute
   normally — the writes go through Twist and are proven. But the saved data
   only exists within the current proof session's state. It cannot be
   extracted and injected into a future session as raw bytes.

3. **Anti-cheat.** A user cannot inject modified save data because the Twist
   initial state is committed to as all zeros. Any ERAM value read during
   execution must trace back to a proven write during the same session.

**Save & resume via proof composition**: To support play sessions that span
multiple sittings, the save mechanism is at the proof level, not the Game Boy
level:

- **Saving** = the prover produces a proof covering execution up to the save
  point. The accumulated IVC proof/accumulator IS the save file. It includes
  all proven state (WRAM, HRAM, VRAM, ERAM, registers, timer) as the final
  commitments of the folding chain.

- **Resuming** = the new session starts from the previous session's final
  accumulator. The proof chain continues. No raw memory dump is involved —
  the state is cryptographically bound to the prior execution. ERAM's
  contents are part of this cryptographic state.

- **Anti-cheat**: A user cannot inject modified state because the accumulator
  is cryptographically linked to the execution that produced it. There is no
  "load save file" operation that could accept untrusted data.

**MBC register implications**: Since ERAM is Twist, the MBC RAM bank
register (MBC_ID address 2) and RAM enable register (MBC_ID address 4) must
also be proven. See [§5.2](#52-mbc-bank-registers) for MBC_ID details.

### 5.4 OAM DMA

Writing to $FF46 triggers a 160-byte copy from a source region to OAM
($FE00-$FE9F). The source depends on the high byte written. On real hardware
this takes 160 M-cycles; in foldiboy it's instantaneous.

**Key constraint**: The CCS has a fixed number of Twist lanes per step row
(~11 max). A single step cannot emit 320 Twist events (160 reads + 160
writes). Dynamic mid-execution activation of OAM-as-Twist is not feasible
because the Twist memory argument needs the complete write history from
initial state, and the CCS structure is fixed at proof time.

**Decision**: Per-game configuration with tiered fallbacks.

**Tier 1 (Ideal) — per-game configuration with detect-and-reject:**

Most games only write to OAM (via DMA) and never read it back through the
CPU — the PPU reads OAM for rendering, but the PPU is unproven. For these
games, OAM can be entirely **unproven** (no OAM_ID Twist region, no DMA
steps, cheapest proof).

For the minority of games that do read OAM through the CPU (collision
detection, sprite management), OAM is declared as **Twist** upfront. DMA is
modeled as **160 synthetic "DMA steps"** in the trace — each step has 2
Twist events (1 source read + 1 OAM write), well within the per-step lane
budget. Cost: ~160 extra rows per frame (~1% overhead on ~10-17k CPU steps).

Safety is enforced by the proof system, not by trust:
- When OAM is unproven, OAM_ID doesn't exist in the CCS
- If the execution trace contains a load from $FE00-$FE9F, the address-to-
  TwistId routing constraint has no matching region -> constraints are
  unsatisfiable -> no valid proof can be produced
- A malicious prover cannot "hide" an OAM read or fake an OAM value
- On the user side: the emulator detects the OAM read during trace
  generation and shows "this code path is not provable under current config"
- On the verifier side: the verifier contract declares per ROM hash whether
  OAM proof is required, and rejects proofs that don't match

**Tier 2 (Fallback) — OAM always Twist:**

If per-game configuration proves too complex to implement initially, OAM is
Twist for all games unconditionally. Every game pays the ~1% DMA overhead.
No configuration needed, always correct.

**Tier 3 (Cheapest fallback) — OAM always unproven:**

Games that read OAM are unsupported. An imperfect static ROM scan can warn
at load time (catches `LD A,(nn)` with literal OAM addresses, but not
indirect reads via HL/BC/DE).

**Starting point**: Tier 3 (always unproven). Simplest to implement.
Move to Tier 1 if/when:
1. per-game configuration infrastructure exists.
2. we've validated that our proof system is fast enough to run on a user's
   device even with added OAM proof time overhead.
Error if game ever uses this functionality (either statically or dynamically).

**Not feasible**: Dynamic mid-execution OAM activation. The Twist memory
argument needs complete write history from step 0. Past DMA writes that
weren't tracked cannot be retroactively proven. The CCS structure (which
Twist regions exist) is fixed at proof generation time.

### 5.5 DMA Trigger

The classification of $FF46 follows the OAM tier (see
[§5.4](#54-oam-dma)). It does **not** get its own TwistId — it is a
structural trigger, not a memory location.

When OAM is Twist, the 160 synthetic DMA steps in the trace must be
legitimized by a real CPU write to $FF46. Without this link, a malicious
prover could inject synthetic DMA steps without a corresponding $FF46
write, fabricating OAM state.

**Note on readback**: $FF46 is technically readable on hardware (returns
the last-written value). $FF46 readback is **Unproven (passthrough —
emulator)**. The emulator returns the last-written value (`dma_reg`).
The static scan does not reject this read. When OAM is unproven (Tier
3), the DMA trigger write is ignored but readback still returns
`dma_reg` as a passthrough witness.

#### Tier 3 (OAM unproven): $FF46 is unproven

$FF46 write is a dead write. No DMA steps in the trace. No tracking.
This is the starting-point configuration (see [§5.4](#54-oam-dma)).

#### Tier 1/2 (OAM is Twist): $FF46 write is a proven trigger

$FF46 is not a register in the memory model — nobody reads it back for
game logic. (The emulator stores `dma_reg` for open-bus behavior, but the
proof doesn't model open-bus.) It is a **trigger**: a CPU write to this
address causes a side effect (the 160-byte DMA copy).

The CPU write to $FF46 is already captured in the instruction trace — it's
a normal bus write whose destination address ($FF46) and written value
(the source high byte) are part of the proven step. The proof does not
need to `twist.store()` to $FF46. Instead, it needs a **structural CCS
constraint** that links the trigger write to the subsequent DMA rows:

1. **Trigger detection**: The address-routing constraint recognizes a write
   to $FF46. The written value V (source high byte) is extracted from the
   proven instruction.

2. **DMA row requirement**: The next 160 trace rows must be synthetic DMA
   steps. Each DMA row i (0 <= i < 160) has exactly 2 Twist events:
   - Source read: `twist.load(source_twist_id, source_addr)` where
     `source_addr = (V << 8) + i` and `source_twist_id` is determined by
     the address range (same routing as `dma_read` in the emulator — see
     below)
   - OAM write: `twist.store(OAM_ID, 0xFE00 + i, byte)`

3. **Value consistency**: The byte read from the source must equal the byte
   written to OAM. This is a simple equality constraint per DMA row.

4. **Completeness**: Exactly 160 DMA rows must follow the trigger, no more,
   no fewer. A partial DMA or extra DMA rows fail the structural constraint.

**DMA source routing** (matches `dma_read` in `bus.rs`):

The DMA bus is different from the CPU bus — addresses $E000-$FFFF map to
WRAM (extended echo), not to IO/OAM/HRAM. The source TwistId for a DMA
read at address A is:

| Source address range | TwistId / ShoutId | Notes |
|---------------------|-------------------|-------|
| $0000-$7FFF | ROM Shout (per-bank) | Requires MBC_ID load for $4000+ |
| $8000-$9FFF | VRAM_ID(3) | Tile data |
| $A000-$BFFF | ERAM_ID(7) | Cartridge RAM |
| $C000-$DFFF | RAM_ID(0) | WRAM |
| $E000-$FFFF | RAM_ID(0), offset = addr - $E000 | Extended echo (all maps to WRAM) |

This routing is a fixed function of the source address — no runtime
decision. The proof encodes it as a constraint that selects the correct
TwistId/ShoutId based on `(V << 8) + i`.

**Why not a TwistId for $FF46**: Twist is for memory that is both written
and read back, with the proof verifying read-after-write consistency.
$FF46 is write-only — no instruction ever reads it back for game logic.
Allocating a TwistId would add write-tracking overhead for a value that
is never loaded. The structural constraint approach is cheaper and
semantically precise: it says "this write causes this effect" rather than
"this memory location holds this value."

### 5.6 Echo RAM

Echo RAM ($E000-$FDFF) is **proven**, normalized to WRAM.

**What echo RAM actually is**: Echo RAM is not a separate memory region.
It is a hardware wiring artifact — the Game Boy's address decoder only
connects the lower 13 bits to the WRAM chip. Accesses to $E000 hit the
same physical transistors as $C000 because bit 13 is not wired to the
WRAM chip. Two addresses, one piece of memory.

Nintendo's prohibition ("developers must not use this range") means "don't
rely on this alias existing in future hardware revisions," not "this
memory is dangerous." It is a portability warning, not a safety concern.

**Why proven (not excluded)**: Proving echo RAM costs exactly zero. There
is no extra Twist region, no extra address space, no extra memory to
commit. A write to $E000 and a write to $C000 both resolve to
`(RAM_ID, 0x0000)` — the same Twist entry. The only "cost" is one extra
match arm in the address routing constraint, which is negligible.

Making echo RAM unproven would actually be more work for no benefit:
- Requires adding $E000-$FDFF to the static ROM rejection scan
- Risks breaking games where stray pointer arithmetic lands in the echo
  range (even well-behaved games can have this)
- Saves zero proving cost (it is the same physical memory — same Twist
  entries, same commitments)

**Normalization rule**:

```
$C000-$DFFF -> (RAM_ID, addr - 0xC000)   // canonical WRAM
$E000-$FDFF -> (RAM_ID, addr - 0xE000)   // echo -> same offset
```

Both produce identical `(TwistId, offset)` pairs for mirrored addresses.
The Twist memory argument does not know the difference — it sees accesses
to RAM_ID at the same offsets regardless of which alias was used.

Note: echo only mirrors $C000-$DDFF (offsets 0x0000-0x1DFF). The top 512
bytes of WRAM ($DE00-$DFFF, offsets 0x1E00-0x1FFF) are only accessible
via their canonical addresses — $FE00+ is OAM/IO/HRAM, not echo.

### 5.7 JOYP (Mixed Ownership)

JOYP has mixed ownership — the CPU writes selection bits and external input
provides button state. A pure witness would not constrain the relationship
between them:

- Bits 7-6: Unused, always 1 (DMG)
- Bits 5-4: CPU-writable (select button group: action vs d-pad)
- Bits 3-0: External (button state for selected group, active-low)

As a pure witness, the prover could provide JOYP values where bits 5-4 don't
match the CPU's last write. The read value has a causal dependency on CPU
state *inside* the proof boundary (the selection bits determine which button
group the read returns), so the proof must compute it.

JOYP is a **computed register** (like IF). The proof owns JOYP as internal
state and computes the read value from two sources:

```
JOYP_read = 0xC0 | (cpu_selection & 0x30) | mux(cpu_selection, button_tape)
```

Where `mux` returns the correct 4 bits from the 8-bit button tape based on
the CPU's selection state:

```
mux(selection, buttons):
    bit 4 clear (d-pad selected):   buttons[3:0]  (Down, Up, Left, Right)
    bit 5 clear (action selected):  buttons[7:4]  (Start, Select, B, A)
    both clear:                     buttons[3:0] & buttons[7:4]
    both set:                       0x0F (no group selected, all released)
```

CPU writes to $FF00 update the internal selection state (bits 5-4 only).
The proof tracks this via the instruction trace.

#### Button tape granularity

8 bits of button state on **every step**, regardless of whether the step
reads JOYP.

Each Game Boy instruction is its own step, so "per-step" and "per-JOYP-read"
are distinct only in whether non-reading steps have tape entries. A uniform
tape (one entry per step) is strongly preferred:

- **Uniform CCS layout**: Every step row has the same columns. No
  variable-length pointer into a separate JOYP tape. The 8-bit button field
  is simply a column in the witness, ignored on steps that don't read $FF00.
- **Tiny overhead**: 8 bits per step is negligible. A frame has ~17k steps;
  JOYP is read ~4-8 times. The 99.95% of entries that go unused cost 8 bits
  each in the witness commitment — trivial compared to the instruction data
  already committed per step.
- **No conditional tape advancement**: A per-read tape requires the proof to
  advance a pointer only on JOYP reads, adding conditional constraints.
  Per-step avoids this entirely.

#### Button tape format

The button tape provides **8 bits** representing all physical button states,
independent of the CPU's selection. The proof applies the selection mask to
compute the 4 result bits.

4 pre-selected bits would require the tape to "know" the CPU's current
selection state, creating a circular dependency (the witness depends on
proven internal state). 8 raw bits keep the witness purely external — it
answers "what buttons are physically pressed right now?" with no coupling to
CPU behavior. The proof handles the selection mux as a ~2-constraint
computation per JOYP read.

The 8-bit layout matches our emulator's internal representation (`Joypad`
stores `directions: u8` and `buttons: u8` separately). Bits 3-0 = d-pad
(Down, Up, Left, Right), bits 7-4 = action (Start, Select, B, A). All
active-low (0 = pressed).

#### Joypad interrupt enforcement

The proof does **not** enforce consistency between the button tape and IF
bit 4 (joypad interrupt) on the external interrupt tape.

- **Rarely used**: Most games never enable the joypad interrupt. They poll
  JOYP directly in their VBlank handler or main loop. The joypad interrupt
  exists on hardware mainly for waking from STOP mode.
- **No security benefit**: The prover controls both the button tape and the
  external interrupt tape. Enforcing consistency would only prevent the prover
  from sending a joypad interrupt without a corresponding button transition
  (or vice versa). But a forged joypad interrupt just makes the CPU enter
  the handler, read JOYP, and act on whatever buttons it sees — which are
  already on the witness tape. There is no exploit.
- **Constraint cost**: Edge detection (high-to-low transition on selected
  button bits) requires comparing the current button tape with the previous
  step's tape and the current selection state. This adds ~4 constraints per
  step for a feature almost no game uses.

If we later prove the PPU (making VBlank/STAT deterministic) and want full
interrupt consistency, joypad interrupt enforcement can be added as an
optional constraint — same model, just more proved bits.

**Optimization opportunity**: At ~17k steps per frame, the per-step
button tape adds ~17KB of witness data per frame, >99.9% identical to the
previous entry. A future optimization could use delta encoding or a
"change-only" tape with a step counter, reducing witness size to ~bytes
per frame. This requires additional constraints for the tape advancement
logic but may be worthwhile for proof size.

### 5.8 STAT (Mixed Ownership)

STAT ($FF41) has the same mixed-ownership pattern as JOYP — CPU writes bits
6-3 (interrupt enables), PPU sets bits 2-0 (mode/LYC flag). As a pure
witness, the prover could lie about the enable bits the CPU wrote.

**Bit 7**: Always reads as 1 on DMG hardware. The witness tape must provide
values with bit 7 set. A range check or mask (`val | 0x80`) in the constraint
enforces this at near-zero cost.

STAT stays as a **pure Witness**. Unlike JOYP, the mixed ownership does not
create a security concern.

**Enable-bit security argument**: The prover controls bits 3-6 on STAT
reads. A game that reads STAT and branches on its own enable bits gets a
potentially-wrong value. However, the prover already controls all
PPU-dependent code paths via the interrupt tape and LY/STAT mode
witnesses. Lying about STAT enable bits changes which path the game takes,
but the prover can already force any code path through interrupt timing.
No additional attack surface is created.

**Why STAT is different from JOYP**:

JOYP has a **causal dependency inside the proof boundary**: the CPU writes
selection bits (5-4), and those bits change what the next read returns (which
button group is visible). A raw witness could provide a read value
inconsistent with the CPU's own selection — the proof would accept an
impossible state. That's why JOYP must be Computed.

STAT's CPU-written bits (interrupt enables, bits 6-3) have **no causal
effect inside the proof**. Those enable bits only matter to the PPU, which
generates STAT interrupts based on them. Since the PPU is unproven, nobody
inside the proof boundary reads those enable bits and acts on them. The CPU
reads STAT to check mode/LYC (PPU-driven witness bits) — the CPU-written
enable bits come back unchanged as a side effect, not as a causal input to
any proven computation.

Making STAT Computed would add ~2 constraints per step for zero security
gain. The prover already controls all PPU-dependent interrupt timing via the
external tape.

#### STAT and OAM interaction

On real hardware, STAT mode bits (1-0) gate OAM bus access:

| STAT Mode | OAM Access |
|-----------|------------|
| Mode 0 (HBlank) | CPU can read/write OAM |
| Mode 1 (VBlank) | CPU can read/write OAM |
| Mode 2 (OAM Search) | OAM **locked** — reads return $FF |
| Mode 3 (Data Transfer) | OAM **locked** — reads return $FF |

Games commonly use STAT to wait for HBlank before touching OAM:

```asm
.wait:
    ldh a, [STAT]     ; read STAT mode
    and $03
    jr nz, .wait      ; spin until mode 0
    ; now safe to touch OAM
```

**Could a malicious prover manipulate STAT mode bits to affect OAM reads?**

If our proof model gated OAM access on STAT mode (returning $FF during
modes 2/3 like real hardware), then STAT-as-Witness + OAM-as-Twist would
be an attack surface: the prover could lie about STAT mode to make proven
OAM reads return $FF instead of Twist-consistent values, or bypass the
lock to read OAM data that should be inaccessible.

**This attack does not exist in our model.** Our emulator deliberately does
not implement OAM bus locking. This is a direct consequence of the
architectural decision in `ideal-emulator.md` Section 2.3: subsystems tick
*after* `cpu.step()`, and we do not model per-M-cycle bus contention. OAM
reads always return the actual Twist-consistent value, regardless of PPU
mode. Therefore:

1. **OAM reads always succeed** — no mode-dependent gating in the proof
2. **STAT only affects program flow** — it controls how many iterations a
   wait-loop takes (i.e., *when* the game accesses OAM), not *what value*
   the OAM read returns
3. **OAM values are Twist-guaranteed** regardless of what STAT says

**OAM corruption bug**: On real DMG hardware, writing to OAM during PPU
mode 2 corrupts OAM data in a specific pattern. This bug does not exist in
our model because OAM writes always succeed (no mode-dependent gating).
Games that accidentally trigger this bug on real hardware work correctly
in our emulator — a minor compatibility improvement.

The prover lying about STAT can change the program's execution path (e.g.,
making a STAT wait-loop exit sooner), but on whatever path executes, every
OAM read returns the correct Twist value. There is no way to use STAT to
inject fake OAM data.

**VRAM bus contention**: The same invariant applies to VRAM. On real
hardware, VRAM reads during PPU mode 3 return $FF. In our model, VRAM
reads always return the Twist-consistent value regardless of PPU mode —
the proof never gates VRAM access on a witnessed STAT mode. This means a
small number of games that rely on VRAM bus contention (e.g., code that
reads VRAM to detect PPU mode 3 by checking for $FF) are unsupported.
The security argument is identical to OAM: gating Twist access on a
witnessed value would allow the prover to corrupt proven memory reads.

**Note: making STAT Computed does not help.** Even if STAT were Computed
(like JOYP), the mode bits (1-0) would still come from the witness tape:

```
STAT_read = 0x80 | (cpu_wrote & 0x78) | (ppu_witness & 0x07)
                                          ^^^^^^^^^^^^^^^
                                          mode bits still witnessed
```

The prover controls the mode bits in both the Witness and Computed models.
The defense against this attack is not the STAT classification — it is the
**absence of OAM bus gating in the proof model**. No amount of constraint
engineering on STAT changes this; the only way to close this attack surface
(if bus conflict emulation were added) would be to **prove PPU mode
transitions**, making the mode bits deterministic rather than witnessed.
That is a fundamentally different (and much larger) change than adjusting
STAT's category.

**Invariant**: The proof model must never gate memory access (OAM, VRAM, or
any Twist region) on a witnessed value. If OAM bus conflict emulation is
ever added, PPU mode transitions must be proven — not merely witnessed or
computed from a tape. This is the same simplification that makes Mooneye's
sub-instruction timing tests fail by design — it is a deliberate
architectural choice, not an oversight.

### 5.9 Serial and Link Cable

The Game Boy serial port enables communication between two devices via a
link cable. One device drives the clock (internal clock, SC bit 0 = 1), the
other receives (external clock, SC bit 0 = 0). Data is exchanged through
the SB register ($FF01), and a serial interrupt (IF bit 3) fires on transfer
completion.

SB and SC are **Unproven (passthrough — constant)** registers. SB is
constrained to $FF and SC is constrained to $7E — the hardware "no cable
attached" values. Games that depend on link cable features (requiring
received data from another device) won't function correctly — they get
$FF instead of real data. Games that merely check for a cable and handle
"no cable" gracefully work fine.

**Why serial data from another device is unprovable**:

Serial data received from another Game Boy is externally provided — the
prover could fabricate any incoming byte. Unlike joypad input (where the
prover controls their own buttons and has no incentive to lie), serial data
represents another player's state. A malicious prover could fake receiving
specific Pokemon in a trade, claim victory in a link battle that never
happened, or inject arbitrary data into game logic.

Verifying serial data requires proof that the other device actually produced
it — i.e., a proof of the other player's execution.

**Future path — recursive SNARK composition**:

Properly supporting link cable communication requires the proof system (not
the emulator) to validate external data:

1. Player A produces a proof of their execution up to the serial exchange
2. Player B produces a proof of their execution up to the serial exchange
3. A recursive SNARK verifies both proofs and confirms the exchanged bytes
   are consistent (A sent what B received, and vice versa)
4. The proof system writes the verified received byte into the game's SB
   register and fires the serial interrupt (IF bit 3)

This is a proof-system-level construct, not an emulator-level one. Foldiboy
does not manage or validate external proofs — it only produces execution
traces. The recursive composition happens in Nightstream.

**Why this is not hardcoded into Foldiboy**: The emulator should not be
coupled to a specific proof system's recursive SNARK implementation. Foldiboy
produces a single-player execution trace. Multi-player proof composition is
handled entirely by Nightstream (or whatever proof system consumes the trace).

**Current behavior**: CPU writes to SB/SC are dead writes. IF bit 3
(serial interrupt) is always 0 on the external interrupt tape. The proof
constrains SB reads to $FF and SC reads to $7E — the hardware "no cable"
values. A malicious prover cannot claim serial data was received. Games
that initiate a serial transfer with **external clock** (SC bit 0 = 0)
and poll SC bit 7 will hang indefinitely — the clock never arrives
without a cable. **Internal-clock** transfers (SC = $81) complete
normally even without a cable (SB receives $FF, SC bit 7 clears after
~1ms). Most single-player games that touch serial use internal clock for
printer support or cable detection, and handle "no device" gracefully.

**Emulator return values**: These values are the passthrough constants
used by the proof. SB=$FF and SC=$7E are built into the constraint system
as fixed values, not emulator-dependent witnesses. The Game Boy's serial
data line has pull-up resistors, so unconnected pins float high ($FF) —
these constants match authentic hardware behavior for "no cable attached."

**Static ROM validation**: SB and SC reads are no longer rejected by the
static scan — they are passthrough (constant) addresses with routing
entries in the CCS. Games that read SB for cable detection get $FF and
proceed normally. Most single-player games never depend on the received
serial data being anything other than $FF.

### 5.10 Initial State

Every Twist region needs an initial state so the memory argument can compute
`prev_val` at the first access to each address. Event table construction
requires these explicitly: `GbRegEventTable::from_exec_table(init_regs)`,
`GbRamEventTable::from_exec_table(init_ram)`.

All Twist memory regions start at **all zeros** (matching our emulator's
behavior). Registers start at known DMG post-boot values. Timer starts at
known post-boot counter value.

| Region | Initial State | Rationale |
|--------|--------------|-----------|
| CPU Registers (REG_ID) | `RegisterFile::post_boot_dmg()` values | Known DMG constants. Public input. |
| Timer internal counter | 0 | Timer internal counter starts at 0 (not the ~$AB00 value that real DMG hardware has post-boot-ROM). Since we skip the boot ROM, this is a deterministic choice. Games that check DIV immediately may see different values than real hardware. |
| WRAM (RAM_ID) | All zeros | DMG RAM is undefined at power-on, but all-zeros is deterministic and matches our emulator. Well-behaved games always write before read. |
| HRAM (HRAM_ID) | All zeros | Same as WRAM. |
| VRAM (VRAM_ID) | All zeros | Same as WRAM. |
| OAM (OAM_ID) | All zeros | Same as WRAM. (Only relevant when OAM is Twist — see [§5.4](#54-oam-dma).) |
| ERAM (ERAM_ID) | All zeros | Enforced to prevent save data injection. Games that check for saves find none and start fresh. See [§5.3](#53-eram-and-the-save-system). |
| MBC registers (MBC_ID) | Bank 0, mode 0, RAM disabled | Hardware power-on state. ROM bank defaults vary by MBC type (MBC5: bank 1). |
| IE (IO_ID) | 0x00 | No interrupts enabled at boot. |
| Timer regs (IO_ID) | DIV=0, TIMA=0, TMA=0, TAC=0 | Standard post-boot state. |

**Optimization opportunity — sparse initial commitment**: If the proof system
knows the initial state is all zeros, it does not need to commit to every byte
individually. A Twist region initialized to all zeros has a trivial initial
polynomial (the zero polynomial). Only addresses that are actually written
during execution need non-trivial entries in the commitment. This means a game
that uses 2KB of the 8KB WRAM pays proving cost proportional to 2KB, not 8KB,
even though the addressable range is larger. This optimization is internal to
the Twist memory argument and requires no changes to the emulator or trace
format.

### 5.11 Static ROM Scan

At ROM load time, scan for instructions that read from **Unproven
(reject)** addresses. Passthrough addresses (both constant and emulator)
have routing entries in the CCS and do not trigger scan rejection. The
[§6](#6-complete-classification) address map is the definitive reference —
any address classified as **Unproven (reject)** there triggers rejection.
In practice, $FEA0-$FEFF is the only reject range. Detection approach:

- `$F0 xx` (LDH A,[xx]): Check if `$FF00 + xx` is an Unproven (reject)
  address per the [§6](#6-complete-classification) table
- `$FA lo hi` (LD A,[nnnn]): Check if nnnn is an Unproven (reject)
  address ($FEA0-$FEFF)
- `$F2` (LDH A,[C]): Conservative — flag if the ROM contains this opcode
  AND ever loads C with an offset targeting a reject address (harder to
  detect statically; may need runtime check or blanket rejection)

For indirect reads (`LD A,[HL]`, `LD A,[BC]`, `LD A,[DE]`), static analysis
cannot determine the target address. These require a **runtime check** during
trace generation: if the CPU reads from an **Unproven (reject)** address,
the emulator flags the trace as unprovable. The proof system enforces this
independently — a reject address has no TwistId, ShoutId, or witness
mechanism, so the constraints are unsatisfiable and no valid proof can be
produced.

**Proof-level enforcement**: Any bus read — including instruction fetches,
stack operations (PUSH/POP/CALL/RET), and indirect loads — targeting an
**Unproven (reject)** address has no TwistId or ShoutId in the constraint
system. The address-to-region routing constraint has no matching entry,
making the constraints unsatisfiable. No valid proof can be produced.
Stack operations are normal bus reads/writes routed through the same
address mapping; if SP points to an Unproven (reject) range, the
constraints fail identically.

The static ROM scan is an **optimization to fail early** (at load time
rather than after trace generation), not the security boundary. The proof
system's address routing constraints are the actual security mechanism.

### 5.12 CPU Register Events

Register Twist events (REG_ID) are derived from the opcode table, not the bus.
Whether the trace viewer shows synthetic sub-lines like `REG R A=42` is a UI
concern independent of the proof classification. Deferred until VmCpu trait
integration.

### 5.13 CPU R/W Latch Registers

Nine PPU configuration registers (LCDC, SCY, SCX, LYC, BGP, OBP0, OBP1,
WY, WX) are classified as **Twist** under IO_ID(4), despite the PPU being
unproven.

**Rationale**: These registers are written exclusively by the CPU and read
back by the CPU. The PPU reads them for rendering but never modifies them
via the bus. Twist classification means "CPU reads return the last
CPU-written value" — nothing more. This does NOT mean rendering is proven
or that the PPU's consumption of these values enters the proof.

**Why this matters**: Many games read these registers back for game logic:

- **LCDC bit 7**: Games check LCD enable to gate PPU-dependent operations
- **SCY/SCX**: Parallax scrolling engines read scroll position to compute
  layer offsets
- **BGP/OBP0/OBP1**: Palette fade effects read current palette to compute
  next fade step
- **WY/WX**: Dynamic window effects (e.g., status bar toggle) read window
  position
- **LYC**: Games that set LYC for mid-frame effects may read it back to
  verify or update

Classifying these as Unproven would reject any game that reads them — a
significant compatibility loss for zero proving cost savings.

**Cost**: Zero additional overhead. These registers share IO_ID(4) with
existing Twist registers (IE, DIV, TIMA, TMA, TAC). Each is a single-byte
address within the IO_ID Twist region. The Twist memory argument already
covers IO_ID; adding more addresses within the same region costs nothing
beyond the per-access events that would exist anyway.

### 5.14 HALT and STOP

**HALT**: The CPU stops executing until `(IE & IF & 0x1F) != 0`. Each
halted cycle is a trace row consuming 1 M-cycle with no Twist events
beyond timer advancement. The timer (proven) continues advancing, so
timer interrupts can wake HALT. External interrupts (VBlank/STAT/Joypad)
are witnessed — the prover controls when HALT ends via the external
interrupt tape.

Since the proof is generated client-side, an unbounded HALT just creates
more proving work for the prover (no DoS vector). The halt bug (IME=0 +
pending interrupts) is a proven CPU behavior — the proof constrains that
the next byte after HALT is read twice when halt bug triggers.

**STOP**: Enters low-power mode, wakes on button press. In practice, STOP
is used almost exclusively for CGB speed switching (which we don't
support). DMG games rarely use STOP. Classification: if a game uses STOP,
the prover provides the wake-up via the button tape. Same
unbounded-duration consideration as HALT — no security issue since the
prover only harms themselves.

### 5.15 Instruction Fetch Proving

Instruction fetches (opcode reads at PC) go through the same
address-to-TwistId/ShoutId routing as data loads. The constraint system
does not distinguish "instruction fetch" from "data read" at the bus
level — both produce the same Twist/Shout events:

- **ROM fetches** → Shout (same per-bank lookup as data reads)
- **RAM/HRAM/VRAM fetches** → Twist (games execute DMA wait loops from
  HRAM, some games run code from WRAM)
- **ERAM fetches** → Twist (some games with large code bases run routines
  from cartridge RAM)

This means a game that self-modifies code in WRAM has its code changes
fully proven — the instruction bytes fetched are the same Twist-verified
values that data reads would return.

### 5.16 Range Checks and Field Size

All Twist memory values and register contents must be range-checked to
their architectural width (8-bit for bytes, 16-bit for addresses).
Without range checks, a malicious prover could store field elements > 255
in "byte" positions, potentially violating assumptions in the CPU
instruction constraints (e.g., carry flag computation, overflow
detection).

The SM83's 8-bit data / 16-bit address architecture is well-suited to
small ZK-friendly prime fields (e.g., Goldilocks p = 2^64 - 2^32 + 1,
Mersenne-31 p = 2^31 - 1). The architectural widths fit comfortably
within any such field, and smaller fields yield faster proofs. Range
checks for 8-bit and 16-bit values are inexpensive in these fields.

### 5.17 Unproven Sub-types

The original design treated "Unproven" as a monolithic category: no reader
in the proof boundary → reject all reads via static scan. This was overly
conservative — most unproven addresses have well-defined read values that
the prover's emulator knows. Three sub-types refine the model.

#### Sub-type definitions with CCS implications

**Reject**: No routing entry in the CCS. The address-to-region constraint
has no match → unsatisfiable. The static scan rejects games that read from
these addresses. Used only for $FEA0-$FEFF where hardware behavior is
undefined and revision-dependent.

**Passthrough (constant)**: The routing entry produces a fixed value. The
constraint asserts `read_value == CONSTANT`. Zero witness cost — the value
is built into the constraints. Near-zero constraint cost (one equality
check per read).

**Passthrough (emulator)**: The routing entry produces an unconstrained
8-bit witness column. Only range-checked (0-255). The prover fills it from
emulator state during trace generation. No witness tape infrastructure
needed — the value is inline in the step row.

**Tape**: The routing entry reads from a dedicated witness tape recorded
during the user's play session. Requires tape infrastructure in the CCS
(tape pointer advancement, per-read tape entries). Produces the same
unconstrained 8-bit witness as emulator passthrough — the distinction is
architectural, not security-related. No DMG addresses currently use
tape — all use emulator passthrough instead. See
[below](#emulator-vs-tape-architectural-equivalence) for trade-off
analysis.

### 5.18 Expanded operations

Sometimes, operations such as opcodes are not in the format we desire in our proof system.
There are two main reasons for this:
1. **Efficiency**: some operations are faster as lookups compared to proving the raw computation.
For example, in riscv's `div` opcode (which doesn't exist on the Gameboy, as is just an example),
it's faster to check (as `a*x + r = b`) than it is to compute (`b/x = a with remainder r`).
Therefore, whenever we see such an operator in the ROM, we rewrite it to this expanded operator
2. **Atomicity**: some opcodes are not atomic, but the proof system needs everything broken up into atomic steps.
For example, in riscv's `lw x3, 4(x4)` operation, we have to compute a `4(x4)` offset before computing the main opcode.
Notably, its expansion *has to be done at runtime* (as the offset depends on the specific ocurrence of the opcode). Another common case are opcodes that implicitly depend on the state of another flag.

Therefore, for SM83, we also need to create a list of which opcodes can/should be expanded, and what they expand into.

Notably, we expand the above in the following types:
| Category   | Type   | Description |
|-------------|---------|-------------|
| — | **None** | Fully atomic. ≤2 register reads, 1 ALU op, 1 register write + flags. No data memory access. |
| Efficiency | **Lookup** | Operation is cheaper to verify via a precomputed table than to constrain algebraically. Analogous to your `div → a*x+r=b` example. |
| Atomicity | **Mem** | Instruction accesses data memory (read, write, or read-modify-write) through an address in a register pair or computed address. Each memory access requires its own trace step. Subtypes: **R** (read), **W** (write), **RMW** (read + modify + write back). |
| Atomicity | **Wide** | 16-bit operation on 8-bit register pairs. Must decompose into 8-bit steps with carry/borrow propagation (arithmetic) or multiple register writes (transfers). |
| Atomicity | **Multi** | Instruction requires >1 data memory access. Stack operations (push/pop 2 bytes), stores to consecutive addresses. Each access is a separate trace step. |
| Atomicity | **Cond** | The expansion structure itself varies at runtime based on a CPU flag. A conditional CALL either expands to a full Multi push + jump (taken) or a single NOP-like advance (not taken). This is your "has to be done at runtime" category. |


Note:
- virtual optocdes
- old trace

#### Security analysis — why constant vs emulator matters

Serial (SB) is the key example. If SB were an unconstrained witness (like
emulator passthrough), a malicious prover could claim to receive arbitrary
serial data, faking multiplayer interactions (traded Pokemon, link battle
results). Constraining SB to $FF enforces "no cable attached" — the prover
cannot claim a link cable interaction occurred without a recursive SNARK
proof from the other player (see [§5.9](#59-serial-and-link-cable)).

APU registers are safe as unconstrained (emulator passthrough) because:

1. The prover already controls code-path selection via button inputs and
   interrupt timing
2. APU state has no multiplayer/external-trust implications
3. Providing wrong APU values only produces a proof showing different
   audio behavior in the prover's own play session

#### Why passthrough is not Witness

Witness (STAT, LY) has dedicated tape infrastructure because the values
change between CPU steps due to external subsystem timing that the proof
needs to reason about (interrupt dispatch, timing-dependent code paths
with security implications). Passthrough values either are constants or
change only in response to CPU writes (APU registers respond to NRxx
writes).

The operational distinction: Witness values participate in the proof's
control flow model (IF register, interrupt dispatch), while passthrough
values are consumed by game logic without proof-level consequence.

#### Emulator vs tape: architectural equivalence

Emulator passthrough and tape are not fundamentally different sub-types —
they are two architectures for delivering the same unconstrained 8-bit
witness value to the proof. The security model is identical: the value is
not cryptographically verified, only range-checked. The choice between
them is an engineering trade-off.

**Emulator passthrough** (current approach for DMG): The prover contains
a headless Game Boy emulator that replays the execution step-by-step
alongside the CPU trace. When a step reads an APU register, the prover's
embedded emulator has the APU state and fills in the witness column
directly.

- **Pro**: No tape storage or transmission — the prover derives values
  on the fly
- **Pro**: No synchronization concerns — the embedded emulator is
  always at the correct step
- **Con**: The prover must contain a full headless emulator (APU, PPU
  state, timer, etc.) — a second Game Boy instance in addition to the
  one the user interacted with
- **Con**: Proving wall-clock time includes emulator ticks per step

**Tape** (alternative architecture): The user's "real" emulator (the one
they interact with) records passthrough values into a tape during
gameplay. The prover reads from this tape instead of running its own
emulator — it has only one Game Boy instance total (the user's).

- **Pro**: Prover is simpler — no embedded emulator, just tape lookups
- **Pro**: Potentially faster proving (tape read vs emulator tick)
- **Con**: Tape grows with every passthrough read across every step —
  at ~17k steps/frame with potential APU register reads per step, tape
  data can be significant
- **Con**: Tape must be generated, stored, and fed to the prover
- **Con**: Requires CCS tape pointer infrastructure (advancement
  constraints per read)

**Which is more efficient for Game Boy?** Hard to tell without
benchmarking. The embedded emulator is small (headless APU/PPU, no
rendering) but runs per-step. The tape avoids per-step emulation but
adds per-read storage and CCS pointer constraints. The balance depends
on folding step size: larger folds accumulate more tape entries but also
require more emulator replay. For the Game Boy specifically, APU reads
are relatively infrequent in most games (sound engines poll NR52 a few
times per frame, not per step), which favors tape. But games that
read-back APU registers heavily would shift the balance toward the
embedded emulator. The choice is deferred until benchmarking is feasible.

#### Complete classification table

Every previously-Unproven address, classified by sub-type:

| Address | Register | Sub-type | Value / Source |
|---------|----------|----------|----------------|
| $FEA0-$FEFF | Unusable | **Reject** | Undefined HW behavior, varies by revision. |
| $FF01 | SB | **Constant** | $FF (pull-up, no cable). Constrained to prevent serial data forgery. |
| $FF02 | SC | **Constant** | $7E (no transfer, no cable). |
| $FF03 | Unmapped | **Constant** | $FF. |
| $FF08-$FF0E | Unmapped (7) | **Constant** | $FF. |
| $FF10-$FF14 | NR10-NR14 | **Emulator** | APU CH1 state from emulator. |
| $FF15 | Unmapped | **Constant** | $FF. |
| $FF16-$FF19 | NR21-NR24 | **Emulator** | APU CH2 state from emulator. |
| $FF1A-$FF1E | NR30-NR34 | **Emulator** | APU CH3 state from emulator. |
| $FF1F | Unmapped | **Constant** | $FF. |
| $FF20-$FF23 | NR41-NR44 | **Emulator** | APU CH4 state from emulator. |
| $FF24-$FF25 | NR50-NR51 | **Emulator** | APU mixer state from emulator. |
| $FF26 | NR52 | **Emulator** | APU power + channel status from emulator. |
| $FF27-$FF2F | Unmapped (9) | **Constant** | $FF. |
| $FF30-$FF3F | Wave RAM | **Emulator** | APU wave RAM from emulator. |
| $FF46 | DMA (readback) | **Emulator** | Last CPU-written value (dma_reg) from emulator. |
| $FF4C | KEY0 | **Constant** | $FF (no CGB on DMG). |
| $FF4D | KEY1 | **Constant** | $FF. |
| $FF4E | Unmapped | **Constant** | $FF. |
| $FF4F | VBK | **Constant** | $FF. |
| $FF50 | BANK | **Constant** | $FF (boot ROM unmapped). |
| $FF51-$FF55 | HDMA1-5 | **Constant** | $FF. |
| $FF56 | RP | **Constant** | $FF. |
| $FF57-$FF67 | Unmapped (17) | **Constant** | $FF. |
| $FF68-$FF6B | BCPS/D, OCPS/D | **Constant** | $FF. |
| $FF6C | OPRI | **Constant** | $FF. |
| $FF6D-$FF6F | Unmapped (3) | **Constant** | $FF. |
| $FF70 | SVBK | **Constant** | $FF. |
| $FF71-$FF75 | Unmapped (5) | **Constant** | $FF. |
| $FF76-$FF77 | PCM12, PCM34 | **Constant** | $FF. |
| $FF78-$FF7F | Unmapped (8) | **Constant** | $FF. |

No DMG addresses currently use **tape**. All unconstrained witnesses use
emulator passthrough. Tape is an architecturally equivalent alternative
— see [above](#emulator-vs-tape-architectural-equivalence). Any
emulator-passthrough address could be reclassified to tape (or vice
versa) without changing the security model.

#### Reclassification trigger

If recursive SNARK multiplayer is added, SB must be reclassified from
constant ($FF) to tape (received byte verified by the other player's
proof). SC would similarly need reclassification to reflect transfer state.

---

## 6. Complete Classification

Every bus-addressable location is listed below, ordered by address. Non-bus
proof elements (CPU registers, ALU, MBC state) follow at the end. The static
ROM scan ([§5.11](#511-static-rom-scan)) uses this table as its definitive
reference: any address classified as **Unproven (reject)** is rejected.
Passthrough addresses (both constant and emulator) have CCS routing entries
and are not rejected.

### Memory regions

| Address | Category | What | TwistId | Reason |
|---------|----------|------|---------|--------|
| $0000-$7FFF | **Shout** | ROM (per-bank) | PROG_BANK_SHOUT(N+bank) | Read-only lookup. Per-bank tables. See [§5.1](#51-rom-as-shout). |
| $8000-$9FFF | **Twist** | VRAM | VRAM_ID(3) | CPU reads/writes. PPU reads but doesn't write via bus. Not gated on PPU mode — reads always return Twist value. See [§5.8](#58-stat-mixed-ownership). |
| $A000-$BFFF | **Twist** | ERAM | ERAM_ID(7) | Cartridge RAM. All-zeros init (no save injection). See [§5.3](#53-eram-and-the-save-system). |
| $C000-$DFFF | **Twist** | WRAM | RAM_ID(0) | Work RAM, CPU-only access. |
| $E000-$FDFF | **Twist** | Echo RAM | RAM_ID(0) | Hardware alias of WRAM. Normalized to same offset. See [§5.6](#56-echo-ram). |
| $FE00-$FE9F | **Twist** | OAM | OAM_ID(6) | Conditional — Tier 3: unproven, Tier 1/2: Twist. See [§5.4](#54-oam-dma). |
| $FEA0-$FEFF | **Unproven (reject)** | Unusable | — | No memory behind this range. Undefined HW behavior varies by revision. Reads rejected by static ROM scan. |
| $FF80-$FFFE | **Twist** | HRAM | HRAM_ID(5) | CPU-only access (not affected by DMA). |
| $FFFF | **Twist** | IE | IO_ID(4) | Interrupt enable. CPU-only writes and reads. |

### I/O registers ($FF00-$FF7F)

Audited against the complete Pan Docs DMG hardware register list. Every
address is accounted for — unmapped addresses and CGB-only registers are
explicitly listed so nothing is overlooked.

| Address | Category | What | TwistId | Reason |
|---------|----------|------|---------|--------|
| $FF00 | **Computed** | JOYP | — (internal) | CPU writes selection (proven) + button tape (witnessed). See [§5.7](#57-joyp-mixed-ownership). |
| $FF01-$FF02 | **Unproven (passthrough)** | SB, SC (serial) | — | Passthrough — constant $FF/$7E ("no cable"). Prevents serial data forgery. See [§5.9](#59-serial-and-link-cable). |
| $FF03 | **Unproven (passthrough)** | Unmapped | — | Passthrough — constant $FF. |
| $FF04 | **Twist** | DIV | IO_ID(4) | Deterministic timer. Upper 8 bits of internal counter. See [§3](#3-the-timer). |
| $FF05 | **Twist** | TIMA | IO_ID(4) | Deterministic timer. Counter, incremented on falling edge. See [§3](#3-the-timer). |
| $FF06 | **Twist** | TMA | IO_ID(4) | Timer reload value. CPU-only writes. |
| $FF07 | **Twist** | TAC | IO_ID(4) | Timer control. CPU-only writes. |
| $FF08-$FF0E | **Unproven (passthrough)** | Unmapped (7 addr) | — | Passthrough — constant $FF. |
| $FF0F | **Computed** | IF | — (internal) | CPU writes + timer bit 2 (proven) + external tape bits 0,1,4 (witnessed). See [§4](#4-the-if-register-model). |
| $FF10-$FF14 | **Unproven (passthrough)** | NR10-NR14 (CH1) | — | Passthrough — emulator APU state. |
| $FF15 | **Unproven (passthrough)** | Unmapped | — | Passthrough — constant $FF. |
| $FF16-$FF19 | **Unproven (passthrough)** | NR21-NR24 (CH2) | — | Passthrough — emulator APU state. |
| $FF1A-$FF1E | **Unproven (passthrough)** | NR30-NR34 (CH3) | — | Passthrough — emulator APU state. |
| $FF1F | **Unproven (passthrough)** | Unmapped | — | Passthrough — constant $FF. |
| $FF20-$FF23 | **Unproven (passthrough)** | NR41-NR44 (CH4) | — | Passthrough — emulator APU state. |
| $FF24-$FF26 | **Unproven (passthrough)** | NR50-NR52 (master) | — | Passthrough — emulator APU state. NR52 bit 7 readable — see note below. |
| $FF27-$FF2F | **Unproven (passthrough)** | Unmapped (9 addr) | — | Passthrough — constant $FF. |
| $FF30-$FF3F | **Unproven (passthrough)** | Wave RAM (16 bytes) | — | Passthrough — emulator APU state. CH3 wave pattern data. |
| $FF40 | **Twist** | LCDC | IO_ID(4) | CPU R/W latch. PPU reads but never writes. Games read bit 7 (LCD enable). |
| $FF41 | **Witness** | STAT | — | PPU sets mode/LYC bits. Bit 7 always reads 1 (DMG). CPU reads for timing. See [§5.8](#58-stat-mixed-ownership). |
| $FF42 | **Twist** | SCY | IO_ID(4) | CPU R/W latch. Games read for parallax scrolling logic. |
| $FF43 | **Twist** | SCX | IO_ID(4) | CPU R/W latch. Same as SCY. |
| $FF44 | **Witness** | LY | — | Current scanline. Driven by PPU. CPU reads for timing/sync. |
| $FF45 | **Twist** | LYC | IO_ID(4) | CPU R/W latch. PPU compares with LY but never modifies LYC itself. |
| $FF46 | **Conditional** | DMA | — | Readback: passthrough — emulator dma_reg. Tier 1/2: proven structural trigger. See [§5.4](#54-oam-dma) and [§5.5](#55-dma-trigger). |
| $FF47 | **Twist** | BGP | IO_ID(4) | CPU R/W latch. Some games read palette back. |
| $FF48 | **Twist** | OBP0 | IO_ID(4) | CPU R/W latch. Same as BGP. |
| $FF49 | **Twist** | OBP1 | IO_ID(4) | CPU R/W latch. Same as BGP. |
| $FF4A | **Twist** | WY | IO_ID(4) | CPU R/W latch. Games read for dynamic window effects. |
| $FF4B | **Twist** | WX | IO_ID(4) | CPU R/W latch. Same as WY. |
| $FF4C | **Unproven (passthrough)** | KEY0 | — | Passthrough — constant $FF. CGB mode select, no register on DMG. |
| $FF4D | **Unproven (passthrough)** | KEY1 | — | Passthrough — constant $FF. CGB speed switch, no register on DMG. |
| $FF4E | **Unproven (passthrough)** | Unmapped | — | Passthrough — constant $FF. |
| $FF4F | **Unproven (passthrough)** | VBK | — | Passthrough — constant $FF. CGB VRAM bank, no register on DMG. |
| $FF50 | **Unproven (passthrough)** | BANK | — | Passthrough — constant $FF. Boot ROM unmapped. |
| $FF51-$FF55 | **Unproven (passthrough)** | HDMA1-5 | — | Passthrough — constant $FF. CGB HDMA, no registers on DMG. |
| $FF56 | **Unproven (passthrough)** | RP | — | Passthrough — constant $FF. CGB infrared, no register on DMG. |
| $FF57-$FF67 | **Unproven (passthrough)** | Unmapped (17 addr) | — | Passthrough — constant $FF. |
| $FF68 | **Unproven (passthrough)** | BCPS | — | Passthrough — constant $FF. CGB BG palette index, no register on DMG. |
| $FF69 | **Unproven (passthrough)** | BCPD | — | Passthrough — constant $FF. CGB BG palette data, no register on DMG. |
| $FF6A | **Unproven (passthrough)** | OCPS | — | Passthrough — constant $FF. CGB OBJ palette index, no register on DMG. |
| $FF6B | **Unproven (passthrough)** | OCPD | — | Passthrough — constant $FF. CGB OBJ palette data, no register on DMG. |
| $FF6C | **Unproven (passthrough)** | OPRI | — | Passthrough — constant $FF. CGB object priority, no register on DMG. |
| $FF6D-$FF6F | **Unproven (passthrough)** | Unmapped (3 addr) | — | Passthrough — constant $FF. |
| $FF70 | **Unproven (passthrough)** | SVBK | — | Passthrough — constant $FF. CGB WRAM bank, no register on DMG. |
| $FF71-$FF75 | **Unproven (passthrough)** | Unmapped (5 addr) | — | Passthrough — constant $FF. Some undocumented CGB regs. |
| $FF76-$FF77 | **Unproven (passthrough)** | PCM12, PCM34 | — | Passthrough — constant $FF. CGB audio digital outputs, no registers on DMG. |
| $FF78-$FF7F | **Unproven (passthrough)** | Unmapped (8 addr) | — | Passthrough — constant $FF. |

**NR52 note**: NR52 ($FF26) is a mixed register. Bit 7 is read/write (APU
power on/off). Bits 0-3 are **read-only channel status flags** reflecting
whether each sound channel is currently active — these bits are set by the
APU hardware, not the CPU.

NR52 is **Unproven (passthrough — emulator)**. The prover's emulator
provides the APU power/channel state as a passthrough witness value.
Games that poll NR52 channel status bits work — the CPU's behavior given
those values is proven, though the channel status bits themselves are not
cryptographically verified.

Sound engines in commercial games commonly poll NR52 bits 0-3 to check if
a channel has finished playing before starting a new sound. This pattern
(e.g., `LDH A,[NR52] / AND $01 / JR NZ,.wait`) is used by popular sound
drivers including hUGEDriver and GBT Player, and by the sound engines in
many commercial titles. These games are supported under passthrough.

**Future path**: Promoting NR52 to full Witness or proving the APU would
add cryptographic verification of channel status, but passthrough already
supports the games.

### Non-bus proof elements

These are not addressed via the bus — they are internal to the proof system.

| Category | What | TwistId / ShoutId | Reason |
|----------|------|-------------------|--------|
| **Twist** | CPU Registers | REG_ID(2) | Derived from opcode table, not bus reads/writes. |
| **Shout** | ALU operations | ShoutId per op | Precomputed result tables. |
| **Twist** | MBC bank registers | MBC_ID(8) | Write-only via bus. Read by address decoder for ROM/ERAM banking. See [§5.2](#52-mbc-bank-registers). |
