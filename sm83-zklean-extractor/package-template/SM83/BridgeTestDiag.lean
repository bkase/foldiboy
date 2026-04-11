import zkLean
import SM83.Constraints  
import SM83.StepInputs

variable {f : Type} [ZKField f]

private theorem liftM_none_eq (s : ZKState f) :
    (liftM (none : Option PUnit) : StateT (ZKState f) Option PUnit) s = none := rfl

set_option maxHeartbeats 800000 in
theorem test_is_zero (step : SM83StepInputs f) (st : ZKState f) :
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
  · next h_c1 => exact ⟨beq_iff_eq.mp h_c1, by sorry⟩
  · -- outer isFalse: what exactly does h look like? Print goal state via failing tactic.
    exact h  -- This will fail showing the type of h
