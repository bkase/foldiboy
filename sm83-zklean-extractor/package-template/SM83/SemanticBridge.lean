import zkLean
import SM83.Constraints
import SM83.StepInputs
import Mathlib.Algebra.Field.ZMod

/-! # Semantic Bridge: ZKBuilder → Algebraic Hypotheses (Gap 1)

Proves that when ZKBuilder constraint gadgets accept a witness,
the evaluated field elements satisfy the algebraic equations
used in `ConstraintProofs.lean`.
-/

namespace SM83.SemanticBridge

variable {f : Type} [ZKField f]

-- Key technical facts: `liftM none` (a StateT function) is NOT in the simp set,
-- so we capture the definitional equalities as private helpers.
private theorem liftM_none_eq (s : ZKState f) :
    (liftM (none : Option PUnit) : StateT (ZKState f) Option PUnit) s = none := rfl

private theorem liftM_none_bind_apply {β : Type} {k : PUnit → StateT (ZKState f) Option β} (s : ZKState f) :
    ((liftM (none : Option PUnit) : StateT (ZKState f) Option PUnit) >>= k) s = none := rfl

-- Common tactic block for single-constraint proofs:
-- `dsimp only [runZKBuilder, ZKBuilder.constrainR1CS, Cslib.FreeM.lift, Cslib.FreeM.foldFreeM,
--   ZKOpInterp, StateT.pure, Pure.pure, Bind.bind, StateT.bind, Cslib.FreeM.bind, Cslib.FreeM.instMonad]`
-- works for a single liftBind node because foldFreeM does one iota reduction on liftBind.
-- 
-- For multi-constraint gadgets (2+ sequential constraints):
-- Use the 3-simp approach: normalize FreeM tree → reduce foldFreeM → expand ZKOpInterp.
-- Then split at h + beq_iff_eq.mp to extract field equalities.

/-! ### Primitives -/

set_option maxHeartbeats 400000 in
/-- If `constrainR1CS a b c` succeeds, then `a.eval * b.eval = c.eval`. -/
theorem constrainR1CS_sound (a b c : ZKExpr f) (st : ZKState f) :
    (runZKBuilder (ZKBuilder.constrainR1CS a b c) st).isSome →
    a.eval * b.eval = c.eval := by
  dsimp only [runZKBuilder, ZKBuilder.constrainR1CS, Cslib.FreeM.lift,
    Cslib.FreeM.foldFreeM, ZKOpInterp, StateT.pure, Pure.pure,
    Bind.bind, StateT.bind, Cslib.FreeM.bind, Cslib.FreeM.instMonad]
  intro h
  split at h
  · next heq => rw [beq_iff_eq] at heq; exact heq
  · contradiction

set_option maxHeartbeats 400000 in
/-- If `constrainEq x y` succeeds, then `x.eval = y.eval`. -/
theorem constrainEq_sound (x y : ZKExpr f) (st : ZKState f) :
    (runZKBuilder (ZKBuilder.constrainEq x y) st).isSome →
    x.eval = y.eval := by
  dsimp only [runZKBuilder, ZKBuilder.constrainEq, Cslib.FreeM.lift,
    Cslib.FreeM.foldFreeM, ZKOpInterp, StateT.pure, Pure.pure,
    Bind.bind, StateT.bind, Cslib.FreeM.bind, Cslib.FreeM.instMonad]
  intro h
  split at h
  · next heq => rw [beq_iff_eq] at heq; exact heq
  · contradiction

/-! ### Sub-gadget bridges -/

-- For multi-constraint proofs, use the 3-simp normalization approach.
-- See BridgeTest.lean for the full explanation.

set_option maxHeartbeats 1600000 in
/-- If `is_zero_constraint step` succeeds, both algebraic equations hold. -/
theorem is_zero_bridge (step : SM83StepInputs f) (st : ZKState f) :
    (runZKBuilder (is_zero_constraint step) st).isSome →
    step.alu_result.eval * step.result_inv.eval = 1 - step.flag_z.eval ∧
    step.flag_z.eval * step.alu_result.eval = 0 := by
  simp only [is_zero_constraint, ZKBuilder.constrainR1CS,
    Cslib.FreeM.bind_eq_bind, Cslib.FreeM.lift_def,
    Cslib.FreeM.liftBind_bind, Cslib.FreeM.pure_bind]
  simp only [runZKBuilder, Cslib.FreeM.foldFreeM_liftBind, Cslib.FreeM.foldFreeM_pure]
  simp only [ZKOpInterp]
  intro h
  split at h
  · next h_c1 =>
    constructor
    · exact beq_iff_eq.mp h_c1
    · simp only [bind, StateT.bind, StateT.pure, Pure.pure] at h
      split at h
      · next h_c2 => exact beq_iff_eq.mp h_c2
      · simp [liftM_none_eq] at h
  · simp [liftM_none_bind_apply] at h

set_option maxHeartbeats 1600000 in
theorem half_carry_add_bridge (step : SM83StepInputs f) (st : ZKState f) :
    (runZKBuilder (half_carry_add step) st).isSome →
    step.nibble_a.eval + step.nibble_b.eval =
      step.nibble_result.eval + step.flag_h.eval * 16 ∧
    step.flag_h.eval * (step.flag_h.eval - 1) = 0 := by
  simp only [half_carry_add, ZKBuilder.constrainEq, ZKBuilder.constrainR1CS,
    Cslib.FreeM.bind_eq_bind, Cslib.FreeM.lift_def,
    Cslib.FreeM.liftBind_bind, Cslib.FreeM.pure_bind]
  simp only [runZKBuilder, Cslib.FreeM.foldFreeM_liftBind, Cslib.FreeM.foldFreeM_pure]
  simp only [ZKOpInterp]
  intro h
  split at h
  · next h_c1 =>
    constructor
    · exact beq_iff_eq.mp h_c1
    · simp only [bind, StateT.bind, StateT.pure, Pure.pure] at h
      split at h
      · next h_c2 => exact beq_iff_eq.mp h_c2
      · simp [liftM_none_eq] at h
  · simp [liftM_none_bind_apply] at h

set_option maxHeartbeats 1600000 in
theorem half_carry_sub_bridge (step : SM83StepInputs f) (st : ZKState f) :
    (runZKBuilder (half_carry_sub step) st).isSome →
    step.nibble_a.eval + step.flag_h.eval * 16 =
      step.nibble_result.eval + step.nibble_b.eval ∧
    step.flag_h.eval * (step.flag_h.eval - 1) = 0 := by
  simp only [half_carry_sub, ZKBuilder.constrainEq, ZKBuilder.constrainR1CS,
    Cslib.FreeM.bind_eq_bind, Cslib.FreeM.lift_def,
    Cslib.FreeM.liftBind_bind, Cslib.FreeM.pure_bind]
  simp only [runZKBuilder, Cslib.FreeM.foldFreeM_liftBind, Cslib.FreeM.foldFreeM_pure]
  simp only [ZKOpInterp]
  intro h
  split at h
  · next h_c1 =>
    constructor
    · exact beq_iff_eq.mp h_c1
    · simp only [bind, StateT.bind, StateT.pure, Pure.pure] at h
      split at h
      · next h_c2 => exact beq_iff_eq.mp h_c2
      · simp [liftM_none_eq] at h
  · simp [liftM_none_bind_apply] at h

set_option maxHeartbeats 1600000 in
theorem carry_add_bridge (step : SM83StepInputs f) (st : ZKState f) :
    (runZKBuilder (carry_add step) st).isSome →
    step.alu_operand_a.eval + step.alu_operand_b.eval =
      step.alu_result.eval + step.flag_c.eval * 256 ∧
    step.flag_c.eval * (step.flag_c.eval - 1) = 0 := by
  simp only [carry_add, ZKBuilder.constrainEq, ZKBuilder.constrainR1CS,
    Cslib.FreeM.bind_eq_bind, Cslib.FreeM.lift_def,
    Cslib.FreeM.liftBind_bind, Cslib.FreeM.pure_bind]
  simp only [runZKBuilder, Cslib.FreeM.foldFreeM_liftBind, Cslib.FreeM.foldFreeM_pure]
  simp only [ZKOpInterp]
  intro h
  split at h
  · next h_c1 =>
    constructor
    · exact beq_iff_eq.mp h_c1
    · simp only [bind, StateT.bind, StateT.pure, Pure.pure] at h
      split at h
      · next h_c2 => exact beq_iff_eq.mp h_c2
      · simp [liftM_none_eq] at h
  · simp [liftM_none_bind_apply] at h

set_option maxHeartbeats 1600000 in
theorem carry_sub_bridge (step : SM83StepInputs f) (st : ZKState f) :
    (runZKBuilder (carry_sub step) st).isSome →
    step.alu_operand_a.eval + step.flag_c.eval * 256 =
      step.alu_result.eval + step.alu_operand_b.eval ∧
    step.flag_c.eval * (step.flag_c.eval - 1) = 0 := by
  simp only [carry_sub, ZKBuilder.constrainEq, ZKBuilder.constrainR1CS,
    Cslib.FreeM.bind_eq_bind, Cslib.FreeM.lift_def,
    Cslib.FreeM.liftBind_bind, Cslib.FreeM.pure_bind]
  simp only [runZKBuilder, Cslib.FreeM.foldFreeM_liftBind, Cslib.FreeM.foldFreeM_pure]
  simp only [ZKOpInterp]
  intro h
  split at h
  · next h_c1 =>
    constructor
    · exact beq_iff_eq.mp h_c1
    · simp only [bind, StateT.bind, StateT.pure, Pure.pure] at h
      split at h
      · next h_c2 => exact beq_iff_eq.mp h_c2
      · simp [liftM_none_eq] at h
  · simp [liftM_none_bind_apply] at h

end SM83.SemanticBridge
