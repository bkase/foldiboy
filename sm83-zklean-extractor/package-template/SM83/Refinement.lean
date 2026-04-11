import Mathlib.Algebra.Field.ZMod
import SM83.ConstraintProofs
import SM83.Constraints
import SM83.Decode
import SM83.FullSoundness
import SM83.RegFile
import SM83.Spec
import SM83.StepInputs
import SM83.ZmodBitVecBridge

/-! # One-step refinement (binary-AND block)

This module assembles the auto-extracted Lean mirrors of the Rust types
(`SM83.RegFile`, `SM83.Decode`) and the constraint-system bridge
(`SM83.ZmodBitVecBridge.and_bv_bridge`) plus the auto-extracted register
coupling sub-constraint (`SM83.Constraints.register_coupling_constraints`)
into a *self-contained refinement theorem*: a statement that says "the
ZK constraint system computes the same thing the Rust ALU would compute"
— for the AND opcode, with no external coupling hypotheses.

The key trick: `master_constraints` now emits a register-coupling
sub-constraint that ties `alu_operand_a` to `step.reg_a` and
`alu_operand_b` to a one-hot MUX over the source registers. With this
in place, a single `master_constraints_bridge` call gives us *every*
fact the refinement theorem needs — including the connection between
the abstract ALU operands and the register file.

## Important: zero duplicated logic

The `RegisterFile` record, the `Reg8` enum, the `AluOp` enum, the
opcode-to-`(op, src)` decode table, and the `AluOp.apply` dispatch are
all *generated* from the Rust `cpu` crate by `sm83-zklean-extractor`.
The only hand-written content here is the proof; the data definitions
are extracted, so the Rust emulator is the single source of truth for
the SM83 semantics referenced by this theorem.
-/

open SM83.ConstraintProofs SM83.FullSoundness SM83.ZmodBitVecBridge

/-! ## Round-trip helper

`SM83.ZmodBitVecBridge.zmodToBitVec8_cast_bounded` proves the
`BitVec → ZMod → BitVec` direction. Here we close the
`ZMod ← BitVec ← ZMod` direction: a value cast in from a `BitVec 8`
round-trips back to the same `BitVec 8` via `zmodToBitVec8`. -/

private theorem zmodToBitVec8_natCast {p : ℕ} [Fact p.Prime]
    (hp_big : 256 < p) (bv : BitVec 8) :
    zmodToBitVec8 ((bv.toNat : ZMod p)) = bv := by
  unfold zmodToBitVec8
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ZMod.val_natCast]
  have h_lt_p : bv.toNat < p := by
    have := bv.isLt
    omega
  rw [Nat.mod_eq_of_lt h_lt_p]
  exact Nat.mod_eq_of_lt bv.isLt

/-! ## RegisterFile.from_step

Constructs the abstract `RegisterFile` view of a single ZK step's
witness columns. The 7 ALU-block registers (A through L, excluding F)
come from the step's `reg_*` columns; `f`, `sp`, `pc` are not in the
single-step view and are filled with placeholder zeros — they aren't
referenced by the AND-block refinement. -/

/-! ## ZKField instance for `ZMod p`

`SM83StepInputs g` is parametric over a field type `g`, and the proof
machinery (`master_constraints_bridge`, etc.) requires `[ZKField g]`.
We register a generic `ZKField (ZMod p)` instance that *delegates*
parent-class structure (`Field`, `BEq`, `Inhabited`, `LawfulBEq`,
`Hashable`) to the canonical Mathlib instances. This avoids creating
a parallel `Field (ZMod p)` hierarchy that would diamond against
`ZMod.commRing p`. The `field_to_bits` / `field_to_nat` / `hash`
methods are stubs — they're not exercised by any of the proofs in
this module. -/

instance instZKField_ZMod_p (p : ℕ) [Fact p.Prime] : ZKField (ZMod p) where
  field_to_bits {num_bits} _ := Vector.replicate num_bits 0
  field_to_nat x := x.val
  hash _ := 0

def RegisterFile.from_step {p : ℕ} [Fact p.Prime]
    (step : SM83StepInputs (ZMod p)) : RegisterFile :=
  { a  := zmodToBitVec8 step.reg_a.eval
  , f  := 0
  , b  := zmodToBitVec8 step.reg_b.eval
  , c  := zmodToBitVec8 step.reg_c.eval
  , d  := zmodToBitVec8 step.reg_d.eval
  , e  := zmodToBitVec8 step.reg_e.eval
  , h  := zmodToBitVec8 step.reg_h.eval
  , l  := zmodToBitVec8 step.reg_l.eval
  , sp := 0
  , pc := 0 }

namespace SM83.Refinement

variable {p : ℕ} [Fact p.Prime]

/-! ## One-step refinement for the AND opcode

Given that `master_constraints` is satisfied AND `is_and = 1`, the
constraint system's `alu_result`, viewed as a `BitVec 8`, equals
`AluOp.And.apply` of the accumulator (`(rf_in).a`) and the value the
ZK step has selected as the second ALU operand
(`zmodToBitVec8 step.alu_operand_b.eval`).

Self-contained: every fact this theorem needs is extracted from
`master_constraints_bridge`. There are *no* external coupling
hypotheses connecting the step to a register file — the new
`register_coupling_constraints` sub-gadget supplies them as part of
the constraint bundle. -/

theorem and_step_refinement
    (hp_big : 256 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_and : step.is_and.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = AluOp.And.apply rf_in.a (zmodToBitVec8 step.alu_operand_b.eval) := by
  -- Extract every primitive fact from the master constraint bundle.
  have facts := master_constraints_bridge step st h_master
  -- ----- Range check: all 24 bits boolean + 3 sum equations -----
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  -- Convert R1CS booleans to disjunction form (what `and_bv_bridge` consumes).
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  -- ----- Table lookup: 8 per-bit AND constraints -----
  obtain ⟨and_constraints, _, _⟩ := facts.table_lookup
  obtain ⟨and_c0, and_c1, and_c2, and_c3, and_c4, and_c5, and_c6, and_c7⟩ := and_constraints
  -- Replace `step.is_and.eval` with `1` in the bit-level constraints, since
  -- `and_bv_bridge` takes the multiplied form. (h_is_and rewrites it.)
  -- ----- Register coupling: alu_operand_a = reg_a -----
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  -- ----- Apply and_bv_bridge -----
  have h_bridge := and_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_and := step.is_and.eval)
    hp_big h_is_and
    ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
    hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
    hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
    ha_sum hb_sum hr_sum
    and_c0 and_c1 and_c2 and_c3 and_c4 and_c5 and_c6 and_c7
  -- h_bridge : step.alu_result.eval =
  --   ((spec_and (zmodToBitVec8 step.alu_operand_a.eval)
  --              (zmodToBitVec8 step.alu_operand_b.eval)).toNat : ZMod p)
  -- ----- Round-trip back to BitVec on both sides -----
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_and (zmodToBitVec8 step.alu_operand_a.eval)
                (zmodToBitVec8 step.alu_operand_b.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast hp_big _
  -- ----- Substitute the register coupling: alu_operand_a's BV view = rf_in.a -----
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  -- ----- Conclude -----
  show zmodToBitVec8 step.alu_result.eval =
      AluOp.And.apply (RegisterFile.from_step step).a
        (zmodToBitVec8 step.alu_operand_b.eval)
  rw [h_eq, h_rf_a]
  rfl

/-! ## One-step refinement for the XOR opcode

Identical structure to `and_step_refinement` but uses
`xor_bv_bridge` and the per-bit XOR constraint slice from
`facts.table_lookup`. -/

theorem xor_step_refinement
    (hp_big : 256 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_xor : step.is_xor.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = AluOp.Xor.apply rf_in.a (zmodToBitVec8 step.alu_operand_b.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  obtain ⟨_, xor_constraints, _⟩ := facts.table_lookup
  obtain ⟨xc0, xc1, xc2, xc3, xc4, xc5, xc6, xc7⟩ := xor_constraints
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := xor_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_xor := step.is_xor.eval)
    hp_big h_is_xor
    ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
    hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
    hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
    ha_sum hb_sum hr_sum
    xc0 xc1 xc2 xc3 xc4 xc5 xc6 xc7
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_xor (zmodToBitVec8 step.alu_operand_a.eval)
                (zmodToBitVec8 step.alu_operand_b.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast hp_big _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      AluOp.Xor.apply (RegisterFile.from_step step).a
        (zmodToBitVec8 step.alu_operand_b.eval)
  rw [h_eq, h_rf_a]
  rfl

/-! ## One-step refinement for the OR opcode -/

theorem or_step_refinement
    (hp_big : 256 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_or : step.is_or.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = AluOp.Or.apply rf_in.a (zmodToBitVec8 step.alu_operand_b.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  obtain ⟨_, _, or_constraints⟩ := facts.table_lookup
  obtain ⟨oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7⟩ := or_constraints
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := or_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_or := step.is_or.eval)
    hp_big h_is_or
    ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
    hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
    hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
    ha_sum hb_sum hr_sum
    oc0 oc1 oc2 oc3 oc4 oc5 oc6 oc7
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_or (zmodToBitVec8 step.alu_operand_a.eval)
               (zmodToBitVec8 step.alu_operand_b.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast hp_big _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      AluOp.Or.apply (RegisterFile.from_step step).a
        (zmodToBitVec8 step.alu_operand_b.eval)
  rw [h_eq, h_rf_a]
  rfl

/-! ## One-step refinement for the ADD opcode

Closes the second caveat: now that `master_constraints` emits the
value-level carry constraint (`table_constraint_add`) plus a global
`flag_c` Boolean, the ADD refinement needs no `h_table` hypothesis
either. The proof uses `add_bv_bridge` (the new value-level Gap T
closure for ADD) instead of `and_bv_bridge`.

Requires `512 < p` because `add_bv_bridge`'s Nat lift can reach 510. -/

theorem add_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_add : step.is_add.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = AluOp.Add.apply rf_in.a (zmodToBitVec8 step.alu_operand_b.eval) := by
  -- Extract every primitive fact from the master constraint bundle.
  have facts := master_constraints_bridge step st h_master
  -- Range bounds: derive from the bit decomposition equations + Boolean facts.
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  -- Derive value bounds via `bit_decomposition_val_le`.
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_b_le : step.alu_operand_b.eval.val ≤ 255 := by
    rw [hb_sum]
    exact bit_decomposition_val_le hp_256 hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  -- Register coupling: alu_operand_a = reg_a.
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  -- Apply `add_bv_bridge` to derive: alu_result = ((spec_add ...).toNat : ZMod p)
  have h_bridge := add_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_add := step.is_add.eval)
    (flag_c := step.flag_c.eval)
    hp_big h_a_le h_b_le h_r_le h_is_add facts.table_constraint_add facts.flag_c_boolean
  -- Round-trip back to BitVec.
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_add (zmodToBitVec8 step.alu_operand_a.eval)
                (zmodToBitVec8 step.alu_operand_b.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  -- Substitute the register coupling: alu_operand_a's BV view = rf_in.a.
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  -- Conclude.
  show zmodToBitVec8 step.alu_result.eval =
      AluOp.Add.apply (RegisterFile.from_step step).a
        (zmodToBitVec8 step.alu_operand_b.eval)
  rw [h_eq, h_rf_a]
  rfl

/-! ## One-step refinement for the SUB opcode

Mirrors `add_step_refinement`, using `sub_bv_bridge` instead. -/

theorem sub_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_sub : step.is_sub.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = AluOp.Sub.apply rf_in.a (zmodToBitVec8 step.alu_operand_b.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_b_le : step.alu_operand_b.eval.val ≤ 255 := by
    rw [hb_sum]
    exact bit_decomposition_val_le hp_256 hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := sub_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_sub := step.is_sub.eval)
    (flag_c := step.flag_c.eval)
    hp_big h_a_le h_b_le h_r_le h_is_sub facts.table_constraint_sub facts.flag_c_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_sub (zmodToBitVec8 step.alu_operand_a.eval)
                (zmodToBitVec8 step.alu_operand_b.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      AluOp.Sub.apply (RegisterFile.from_step step).a
        (zmodToBitVec8 step.alu_operand_b.eval)
  rw [h_eq, h_rf_a]
  rfl

/-! ## Unary refinements: INC and DEC

INC and DEC are unary — they consume only the accumulator. The
refinement statement has no `alu_operand_b` term; the conclusion is
purely about A. -/

theorem inc_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_inc : step.is_inc.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_inc rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := inc_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_inc := step.is_inc.eval)
    (inc_overflow := step.inc_overflow.eval)
    hp_big h_a_le h_r_le h_is_inc facts.table_constraint_inc facts.inc_overflow_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_inc (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_inc (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

theorem dec_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_dec : step.is_dec.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_dec rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := dec_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_dec := step.is_dec.eval)
    (inc_overflow := step.inc_overflow.eval)
    hp_big h_a_le h_r_le h_is_dec facts.table_constraint_dec facts.inc_overflow_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_dec (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_dec (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

/-! ## Shifts: SLA and SRL refinements

These follow the same skeleton as `inc_step_refinement`, replacing the
INC-specific bridge with `sla_bv_bridge` / `srl_bv_bridge`. -/

theorem sla_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_sla : step.is_sla.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_sla rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := sla_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_sla := step.is_sla.eval)
    (flag_c := step.flag_c.eval)
    hp_big h_a_le h_r_le h_is_sla facts.table_constraint_sla facts.flag_c_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_sla (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_sla (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

theorem srl_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_srl : step.is_srl.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_srl rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := srl_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_srl := step.is_srl.eval)
    (flag_c := step.flag_c.eval)
    hp_big h_a_le h_r_le h_is_srl facts.table_constraint_srl facts.flag_c_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_srl (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_srl (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

/-! ## RLC, RRC, SRA, SWAP refinements

These need the bit decomposition (specifically a_bit_7 or a_bit_0 or
all 8 bits) in addition to the value-level facts. The pattern follows
`sla_step_refinement` but threads the bit booleans + the bit
decomposition equation to the corresponding `*_bv_bridge`. -/

theorem rlc_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_rlc : step.is_rlc.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_rlc rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := rlc_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_rlc := step.is_rlc.eval)
    (flag_c := step.flag_c.eval)
    (a₀ := step.a_bit_0.eval) (a₁ := step.a_bit_1.eval)
    (a₂ := step.a_bit_2.eval) (a₃ := step.a_bit_3.eval)
    (a₄ := step.a_bit_4.eval) (a₅ := step.a_bit_5.eval)
    (a₆ := step.a_bit_6.eval) (a₇ := step.a_bit_7.eval)
    hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇ ha_sum h_a_le h_r_le h_is_rlc
    facts.table_constraint_rlc.1 facts.table_constraint_rlc.2
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_rlc (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_rlc (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

theorem rrc_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_rrc : step.is_rrc.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_rrc rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := rrc_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_rrc := step.is_rrc.eval)
    (flag_c := step.flag_c.eval)
    (a₀ := step.a_bit_0.eval) (a₁ := step.a_bit_1.eval)
    (a₂ := step.a_bit_2.eval) (a₃ := step.a_bit_3.eval)
    (a₄ := step.a_bit_4.eval) (a₅ := step.a_bit_5.eval)
    (a₆ := step.a_bit_6.eval) (a₇ := step.a_bit_7.eval)
    hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇ ha_sum h_a_le h_r_le h_is_rrc
    facts.table_constraint_rrc.1 facts.table_constraint_rrc.2
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_rrc (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_rrc (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

theorem sra_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_sra : step.is_sra.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_sra rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := sra_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_sra := step.is_sra.eval)
    (flag_c := step.flag_c.eval)
    (a₀ := step.a_bit_0.eval) (a₁ := step.a_bit_1.eval)
    (a₂ := step.a_bit_2.eval) (a₃ := step.a_bit_3.eval)
    (a₄ := step.a_bit_4.eval) (a₅ := step.a_bit_5.eval)
    (a₆ := step.a_bit_6.eval) (a₇ := step.a_bit_7.eval)
    hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇ ha_sum h_a_le h_r_le h_is_sra
    facts.table_constraint_sra.1 facts.table_constraint_sra.2
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_sra (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_sra (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

theorem swap_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_swap : step.is_swap.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_swap rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  obtain ⟨sw0, sw1, sw2, sw3, sw4, sw5, sw6, sw7⟩ := facts.table_constraint_swap
  have h_bridge := swap_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_swap := step.is_swap.eval)
    (a₀ := step.a_bit_0.eval) (a₁ := step.a_bit_1.eval)
    (a₂ := step.a_bit_2.eval) (a₃ := step.a_bit_3.eval)
    (a₄ := step.a_bit_4.eval) (a₅ := step.a_bit_5.eval)
    (a₆ := step.a_bit_6.eval) (a₇ := step.a_bit_7.eval)
    (r₀ := step.r_bit_0.eval) (r₁ := step.r_bit_1.eval)
    (r₂ := step.r_bit_2.eval) (r₃ := step.r_bit_3.eval)
    (r₄ := step.r_bit_4.eval) (r₅ := step.r_bit_5.eval)
    (r₆ := step.r_bit_6.eval) (r₇ := step.r_bit_7.eval)
    hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
    hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
    ha_sum hr_sum h_is_swap
    sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_swap (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]
    rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_swap (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

/-! ## CCF, SCF, CPL: simple result-side refinements -/

theorem ccf_step_refinement
    (hp_big : 256 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_ccf : step.is_ccf.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_ccf rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, _r_bools, _hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := ccf_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval) (is_ccf := step.is_ccf.eval)
    hp_big h_a_le h_is_ccf facts.table_constraint_ccf
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_ccf (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_ccf (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

theorem scf_step_refinement
    (hp_big : 256 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_scf : step.is_scf.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_scf rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, _r_bools, _hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := scf_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval) (is_scf := step.is_scf.eval)
    hp_big h_a_le h_is_scf facts.table_constraint_scf
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_scf (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_scf (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

theorem cpl_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_cpl : step.is_cpl.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_cpl rf_in.a := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := cpl_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval) (is_cpl := step.is_cpl.eval)
    hp_big h_a_le h_r_le h_is_cpl facts.table_constraint_cpl
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_cpl (zmodToBitVec8 step.alu_operand_a.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_cpl (RegisterFile.from_step step).a
  rw [h_eq, h_rf_a]

/-! ## CP: aliased to SUB shape -/

theorem cp_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_cp : step.is_cp.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_cp rf_in.a (zmodToBitVec8 step.alu_operand_b.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_b_le : step.alu_operand_b.eval.val ≤ 255 := by
    rw [hb_sum]
    exact bit_decomposition_val_le hp_256 hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := cp_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_cp := step.is_cp.eval)
    (flag_c := step.flag_c.eval)
    hp_big h_a_le h_b_le h_r_le h_is_cp facts.table_constraint_cp facts.flag_c_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_cp (zmodToBitVec8 step.alu_operand_a.eval)
              (zmodToBitVec8 step.alu_operand_b.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_cp (RegisterFile.from_step step).a (zmodToBitVec8 step.alu_operand_b.eval)
  rw [h_eq, h_rf_a]

/-! ## ADC, SBC: with carry input -/

theorem adc_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_adc : step.is_adc.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_adc rf_in.a (zmodToBitVec8 step.alu_operand_b.eval)
                              (zmodToBitVec8 step.carry_in.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_b_le : step.alu_operand_b.eval.val ≤ 255 := by
    rw [hb_sum]
    exact bit_decomposition_val_le hp_256 hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := adc_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_adc := step.is_adc.eval)
    (carry_in := step.carry_in.eval)
    (flag_c := step.flag_c.eval)
    hp_big h_a_le h_b_le h_r_le h_is_adc facts.table_constraint_adc
    facts.carry_in_boolean facts.flag_c_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_adc (zmodToBitVec8 step.alu_operand_a.eval)
                (zmodToBitVec8 step.alu_operand_b.eval)
                (zmodToBitVec8 step.carry_in.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_adc (RegisterFile.from_step step).a
                (zmodToBitVec8 step.alu_operand_b.eval)
                (zmodToBitVec8 step.carry_in.eval)
  rw [h_eq, h_rf_a]

theorem sbc_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_sbc : step.is_sbc.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_sbc rf_in.a (zmodToBitVec8 step.alu_operand_b.eval)
                              (zmodToBitVec8 step.carry_in.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, b_bools, hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨b_b0, b_b1, b_b2, b_b3, b_b4, b_b5, b_b6, b_b7⟩ := b_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hb₀ : step.b_bit_0.eval = 0 ∨ step.b_bit_0.eval = 1 := boolean_of_r1cs b_b0
  have hb₁ : step.b_bit_1.eval = 0 ∨ step.b_bit_1.eval = 1 := boolean_of_r1cs b_b1
  have hb₂ : step.b_bit_2.eval = 0 ∨ step.b_bit_2.eval = 1 := boolean_of_r1cs b_b2
  have hb₃ : step.b_bit_3.eval = 0 ∨ step.b_bit_3.eval = 1 := boolean_of_r1cs b_b3
  have hb₄ : step.b_bit_4.eval = 0 ∨ step.b_bit_4.eval = 1 := boolean_of_r1cs b_b4
  have hb₅ : step.b_bit_5.eval = 0 ∨ step.b_bit_5.eval = 1 := boolean_of_r1cs b_b5
  have hb₆ : step.b_bit_6.eval = 0 ∨ step.b_bit_6.eval = 1 := boolean_of_r1cs b_b6
  have hb₇ : step.b_bit_7.eval = 0 ∨ step.b_bit_7.eval = 1 := boolean_of_r1cs b_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_b_le : step.alu_operand_b.eval.val ≤ 255 := by
    rw [hb_sum]
    exact bit_decomposition_val_le hp_256 hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := sbc_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_operand_b := step.alu_operand_b.eval)
    (alu_result := step.alu_result.eval)
    (is_sbc := step.is_sbc.eval)
    (carry_in := step.carry_in.eval)
    (flag_c := step.flag_c.eval)
    hp_big h_a_le h_b_le h_r_le h_is_sbc facts.table_constraint_sbc
    facts.carry_in_boolean facts.flag_c_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_sbc (zmodToBitVec8 step.alu_operand_a.eval)
                (zmodToBitVec8 step.alu_operand_b.eval)
                (zmodToBitVec8 step.carry_in.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_sbc (RegisterFile.from_step step).a
                (zmodToBitVec8 step.alu_operand_b.eval)
                (zmodToBitVec8 step.carry_in.eval)
  rw [h_eq, h_rf_a]

/-! ## RL, RR: rotate-through-carry -/

theorem rl_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_rl : step.is_rl.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_rl rf_in.a (zmodToBitVec8 step.carry_in.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := rl_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_rl := step.is_rl.eval)
    (carry_in := step.carry_in.eval)
    (flag_c := step.flag_c.eval)
    (a₀ := step.a_bit_0.eval) (a₁ := step.a_bit_1.eval)
    (a₂ := step.a_bit_2.eval) (a₃ := step.a_bit_3.eval)
    (a₄ := step.a_bit_4.eval) (a₅ := step.a_bit_5.eval)
    (a₆ := step.a_bit_6.eval) (a₇ := step.a_bit_7.eval)
    hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇ ha_sum h_a_le h_r_le h_is_rl
    facts.table_constraint_rl.1 facts.table_constraint_rl.2
    facts.carry_in_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_rl (zmodToBitVec8 step.alu_operand_a.eval)
              (zmodToBitVec8 step.carry_in.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_rl (RegisterFile.from_step step).a (zmodToBitVec8 step.carry_in.eval)
  rw [h_eq, h_rf_a]

theorem rr_step_refinement
    (hp_big : 512 < p)
    (step : SM83StepInputs (ZMod p)) (st : ZKState (ZMod p))
    (h_master : (runZKBuilder (master_constraints step) st).isSome)
    (h_is_rr : step.is_rr.eval = 1) :
    let rf_in := RegisterFile.from_step step
    let new_a := zmodToBitVec8 step.alu_result.eval
    new_a = spec_rr rf_in.a (zmodToBitVec8 step.carry_in.eval) := by
  have facts := master_constraints_bridge step st h_master
  obtain ⟨a_bools, ha_sum, _b_bools, _hb_sum, r_bools, hr_sum⟩ := facts.range_check
  obtain ⟨a_b0, a_b1, a_b2, a_b3, a_b4, a_b5, a_b6, a_b7⟩ := a_bools
  obtain ⟨r_b0, r_b1, r_b2, r_b3, r_b4, r_b5, r_b6, r_b7⟩ := r_bools
  have ha₀ : step.a_bit_0.eval = 0 ∨ step.a_bit_0.eval = 1 := boolean_of_r1cs a_b0
  have ha₁ : step.a_bit_1.eval = 0 ∨ step.a_bit_1.eval = 1 := boolean_of_r1cs a_b1
  have ha₂ : step.a_bit_2.eval = 0 ∨ step.a_bit_2.eval = 1 := boolean_of_r1cs a_b2
  have ha₃ : step.a_bit_3.eval = 0 ∨ step.a_bit_3.eval = 1 := boolean_of_r1cs a_b3
  have ha₄ : step.a_bit_4.eval = 0 ∨ step.a_bit_4.eval = 1 := boolean_of_r1cs a_b4
  have ha₅ : step.a_bit_5.eval = 0 ∨ step.a_bit_5.eval = 1 := boolean_of_r1cs a_b5
  have ha₆ : step.a_bit_6.eval = 0 ∨ step.a_bit_6.eval = 1 := boolean_of_r1cs a_b6
  have ha₇ : step.a_bit_7.eval = 0 ∨ step.a_bit_7.eval = 1 := boolean_of_r1cs a_b7
  have hr₀ : step.r_bit_0.eval = 0 ∨ step.r_bit_0.eval = 1 := boolean_of_r1cs r_b0
  have hr₁ : step.r_bit_1.eval = 0 ∨ step.r_bit_1.eval = 1 := boolean_of_r1cs r_b1
  have hr₂ : step.r_bit_2.eval = 0 ∨ step.r_bit_2.eval = 1 := boolean_of_r1cs r_b2
  have hr₃ : step.r_bit_3.eval = 0 ∨ step.r_bit_3.eval = 1 := boolean_of_r1cs r_b3
  have hr₄ : step.r_bit_4.eval = 0 ∨ step.r_bit_4.eval = 1 := boolean_of_r1cs r_b4
  have hr₅ : step.r_bit_5.eval = 0 ∨ step.r_bit_5.eval = 1 := boolean_of_r1cs r_b5
  have hr₆ : step.r_bit_6.eval = 0 ∨ step.r_bit_6.eval = 1 := boolean_of_r1cs r_b6
  have hr₇ : step.r_bit_7.eval = 0 ∨ step.r_bit_7.eval = 1 := boolean_of_r1cs r_b7
  have hp_256 : 256 < p := by omega
  have h_a_le : step.alu_operand_a.eval.val ≤ 255 := by
    rw [ha_sum]
    exact bit_decomposition_val_le hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_r_le : step.alu_result.eval.val ≤ 255 := by
    rw [hr_sum]
    exact bit_decomposition_val_le hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_couple : step.alu_operand_a.eval = step.reg_a.eval :=
    facts.register_coupling.2.2.2.2.2.2.2.2.1
  have h_bridge := rr_bv_bridge (alu_operand_a := step.alu_operand_a.eval)
    (alu_result := step.alu_result.eval)
    (is_rr := step.is_rr.eval)
    (carry_in := step.carry_in.eval)
    (flag_c := step.flag_c.eval)
    (a₀ := step.a_bit_0.eval) (a₁ := step.a_bit_1.eval)
    (a₂ := step.a_bit_2.eval) (a₃ := step.a_bit_3.eval)
    (a₄ := step.a_bit_4.eval) (a₅ := step.a_bit_5.eval)
    (a₆ := step.a_bit_6.eval) (a₇ := step.a_bit_7.eval)
    hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇ ha_sum h_a_le h_r_le h_is_rr
    facts.table_constraint_rr.1 facts.table_constraint_rr.2
    facts.carry_in_boolean
  have h_eq : zmodToBitVec8 step.alu_result.eval =
      spec_rr (zmodToBitVec8 step.alu_operand_a.eval)
              (zmodToBitVec8 step.carry_in.eval) := by
    rw [h_bridge]
    exact zmodToBitVec8_natCast (by omega) _
  have h_rf_a : zmodToBitVec8 step.alu_operand_a.eval =
      (RegisterFile.from_step step).a := by
    rw [h_a_couple]; rfl
  show zmodToBitVec8 step.alu_result.eval =
      spec_rr (RegisterFile.from_step step).a (zmodToBitVec8 step.carry_in.eval)
  rw [h_eq, h_rf_a]

end SM83.Refinement
