import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import SM83.SemanticBridge
import SM83.ConstraintProofs
import SM83.EndToEnd
import SM83.Proofs
import SM83.BitVecBridge

/-! # Full Soundness: Closing Remaining Gaps

This file closes the remaining verification gaps identified in the audit.

## Closed here (with proofs)

- **Gap F (compositional instruction theorem)**: A single theorem for ADD
  that takes ZKBuilder success of the three sub-gadgets plus one-hot
  assumption plus table-lookup hypothesis, and produces the full
  soundness conclusion.

- **Gap G (pointwise lookup extraction)**: Extracts pointwise lookup
  equalities from Phase 2's `List.all` bridge proofs.

## Partial / structural limitations (documented, NOT closed)

- **Gap C (master_constraints bridge)**: SemanticBridge covers individual
  sub-gadgets but not the composite `master_constraints`. Proving this
  directly requires a 7-level nested unfolding that hits Lean's simp
  step limits. Alternative: prove a sequencing lemma (generic monad
  morphism for `runZKBuilder`) — requires FreeM induction, complex.
  The compositional theorem below uses the sub-gadget bridges directly
  as separate hypotheses, which covers the same ground for ADD.

- **Gap H (range constraints) [STRUCTURAL]**: The constraint system does
  NOT enforce that field elements represent 8-bit values. A dishonest
  prover could witness `alu_operand_a = 500`, pass constraints vacuously,
  and produce garbage flag values. Closing this requires adding
  range-check lookups to the ZKBuilder constraint generator. This is
  the primary reason the current proofs do not constitute full soundness
  against adversarial provers.

- **Gap I (one-hot enforcement) [STRUCTURAL]**: The constraint system does
  NOT prove `sum(is_*) = 1` or that each `is_*` is Boolean. Closing this
  requires adding one-hot constraints to the generator. Here, one-hot
  is taken as explicit hypothesis (`h_n : N = 0` for ADD).

- **Gap A (lookup invocation missing) [STRUCTURAL]**: The ZKBuilder
  constraints do not actually invoke a lookup table for the ALU result.
  In a real circuit, there would be a `LookupMLE` constraint tying
  `alu_result` to `add_lookup_table(alu_operand_a, alu_operand_b)`. The
  compositional theorem takes this as a hypothesis (`h_table`).
-/

namespace SM83.FullSoundness

open SM83.SemanticBridge SM83.ConstraintProofs

/-! ### Gap G: Pointwise lookup extraction from Phase 2 bridges -/

private abbrev F := ProofField

/-- For each n : Fin 65536, the field MLE of add_8 equals the BitVec evaluator. -/
theorem add_8_lookup_pointwise : ∀ (n : Fin 65536),
    @add_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((add_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F) := by
  intro n
  have h := add_8_field_eq_bv
  have h' : ((@add_8_lookup_table F _ (@bitsOf16 F _ n)) ==
             (((add_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F))) = true :=
    (List.all_eq_true).mp h n (List.mem_finRange n)
  exact beq_iff_eq.mp h'

theorem sub_8_lookup_pointwise : ∀ (n : Fin 65536),
    @sub_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((sub_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F) := by
  intro n
  have h := sub_8_field_eq_bv
  have h' : ((@sub_8_lookup_table F _ (@bitsOf16 F _ n)) ==
             (((sub_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F))) = true :=
    (List.all_eq_true).mp h n (List.mem_finRange n)
  exact beq_iff_eq.mp h'

theorem and_8_lookup_pointwise : ∀ (n : Fin 65536),
    @and_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((and_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F) := by
  intro n
  have h := and_8_field_eq_bv
  have h' : ((@and_8_lookup_table F _ (@bitsOf16 F _ n)) ==
             (((and_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F))) = true :=
    (List.all_eq_true).mp h n (List.mem_finRange n)
  exact beq_iff_eq.mp h'

theorem xor_8_lookup_pointwise : ∀ (n : Fin 65536),
    @xor_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((xor_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F) := by
  intro n
  have h := xor_8_field_eq_bv
  have h' : ((@xor_8_lookup_table F _ (@bitsOf16 F _ n)) ==
             (((xor_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F))) = true :=
    (List.all_eq_true).mp h n (List.mem_finRange n)
  exact beq_iff_eq.mp h'

theorem or_8_lookup_pointwise : ∀ (n : Fin 65536),
    @or_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((or_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F) := by
  intro n
  have h := or_8_field_eq_bv
  have h' : ((@or_8_lookup_table F _ (@bitsOf16 F _ n)) ==
             (((or_8_mle_bv (BitVec.ofNat 16 n.val)).toNat : F))) = true :=
    (List.all_eq_true).mp h n (List.mem_finRange n)
  exact beq_iff_eq.mp h'

/-- Combining pointwise bridge with Phase 2 table correctness:
    the add lookup table at Boolean field points equals the BitVec spec. -/
theorem add_8_lookup_matches_spec : ∀ (n : Fin 65536),
    @add_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((spec_add_bv (BitVec.ofNat 16 n.val)).toNat : F) := fun n => by
  rw [add_8_lookup_pointwise, add_8_correct]

theorem sub_8_lookup_matches_spec : ∀ (n : Fin 65536),
    @sub_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((spec_sub_bv (BitVec.ofNat 16 n.val)).toNat : F) := fun n => by
  rw [sub_8_lookup_pointwise, sub_8_correct]

theorem and_8_lookup_matches_spec : ∀ (n : Fin 65536),
    @and_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((spec_and_bv (BitVec.ofNat 16 n.val)).toNat : F) := fun n => by
  rw [and_8_lookup_pointwise, and_8_correct]

theorem xor_8_lookup_matches_spec : ∀ (n : Fin 65536),
    @xor_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((spec_xor_bv (BitVec.ofNat 16 n.val)).toNat : F) := fun n => by
  rw [xor_8_lookup_pointwise, xor_8_correct]

theorem or_8_lookup_matches_spec : ∀ (n : Fin 65536),
    @or_8_lookup_table F _ (@bitsOf16 F _ n) =
    ((spec_or_bv (BitVec.ofNat 16 n.val)).toNat : F) := fun n => by
  rw [or_8_lookup_pointwise, or_8_correct]

/-! ### Gap F: Fully compositional ADD theorem

Takes ZKBuilder-success of the three sub-gadgets + one-hot + table lookup
and produces the full ADD soundness conclusion. Parameterized over any
prime field `ZMod p` (which has both `ZKField` capabilities via Field and
the `[Fact p.Prime]` needed for `ConstraintProofs`).

To use this at `ZMod p`, the caller must first construct a `ZKField (ZMod p)`
instance (e.g. via `fieldToBits` similar to the ZMod 7 example in zkLean's
`CircuitSoundness.lean`). For now, this theorem uses the `ZKField f` that
the SM83StepInputs and constraints carry; at call sites, f is instantiated
to the concrete field used for proof (e.g., ProofField = ZMod 257). -/

variable {p : ℕ} [Fact p.Prime]

/-- ADD instruction: full compositional soundness over ZMod p.

    The proof uses `is_zero_bridge` etc. under the assumption that
    `ZMod p` has a `ZKField (ZMod p)` instance in scope (caller's
    responsibility). We access `ConstraintProofs.is_zero_sound` directly,
    which works generically over `ZMod p`.

    This is the key end-to-end theorem showing all layers compose. -/
theorem add_compositional_algebraic
    {result result_inv Z N H C : ZMod p}
    (a_bv b_bv : BitVec 8)
    -- Gap A (table): result = spec_add(a_bv, b_bv) [caller-verified]
    (h_table : result = ((spec_add a_bv b_bv).toNat : ZMod p))
    -- Gap 1 (SemanticBridge output): algebraic equations from sub-gadget success
    (h_iz1 : result * result_inv = 1 - Z) (h_iz2 : Z * result = 0)
    (h_hbool : H * (H - 1) = 0)
    (h_cbool : C * (C - 1) = 0)
    -- Gap I (one-hot): N = 0 for ADD [caller-verified]
    (h_n : N = 0) :
    -- Full conclusion: result correct, all flags sound
    result = ((spec_add a_bv b_bv).toNat : ZMod p) ∧
    (result = 0 ↔ Z = 1) ∧ (Z = 0 ∨ Z = 1) ∧
    N = 0 ∧ (H = 0 ∨ H = 1) ∧ (C = 0 ∨ C = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2,
   is_zero_z_boolean h_iz1 h_iz2,
   h_n,
   boolean_of_r1cs h_hbool,
   boolean_of_r1cs h_cbool⟩

/-- SUB instruction: full compositional soundness. Symmetric to ADD. -/
theorem sub_compositional_algebraic
    {result result_inv Z N H C : ZMod p}
    (a_bv b_bv : BitVec 8)
    (h_table : result = ((spec_sub a_bv b_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - Z) (h_iz2 : Z * result = 0)
    (h_hbool : H * (H - 1) = 0)
    (h_cbool : C * (C - 1) = 0)
    (h_n : N = 1) :
    result = ((spec_sub a_bv b_bv).toNat : ZMod p) ∧
    (result = 0 ↔ Z = 1) ∧ (Z = 0 ∨ Z = 1) ∧
    N = 1 ∧ (H = 0 ∨ H = 1) ∧ (C = 0 ∨ C = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2,
   is_zero_z_boolean h_iz1 h_iz2,
   h_n,
   boolean_of_r1cs h_hbool,
   boolean_of_r1cs h_cbool⟩

/-! ### Gap C attempt: master_constraints bridge via simp equations

Strategy: Prove `runZKBuilder` equation lemmas for each primitive constraint
as `@[simp]`. Then `master_constraints` reduces step-by-step via simp.
-/

variable {g : Type} [ZKField g]

set_option maxHeartbeats 1600000 in
/-- Equation form: `runZKBuilder` on a single `constrainR1CS` reduces to
    an explicit `if`. Marked `@[simp]` for reuse. -/
theorem runZKBuilder_constrainR1CS_eq (a b c : ZKExpr g) (st : ZKState g) :
    runZKBuilder (ZKBuilder.constrainR1CS a b c) st =
    (if (a.eval * b.eval == c.eval) = true then some ((), st) else none) := by
  simp only [ZKBuilder.constrainR1CS, Cslib.FreeM.lift_def]
  simp only [runZKBuilder, Cslib.FreeM.foldFreeM_liftBind, Cslib.FreeM.foldFreeM_pure]
  simp only [ZKOpInterp]
  dsimp only [bind, StateT.bind, StateT.pure, Pure.pure]
  split <;> [rfl; rfl]

set_option maxHeartbeats 1600000 in
theorem runZKBuilder_constrainEq_eq (x y : ZKExpr g) (st : ZKState g) :
    runZKBuilder (ZKBuilder.constrainEq x y) st =
    (if (x.eval == y.eval) = true then some ((), st) else none) := by
  simp only [ZKBuilder.constrainEq, Cslib.FreeM.lift_def]
  simp only [runZKBuilder, Cslib.FreeM.foldFreeM_liftBind, Cslib.FreeM.foldFreeM_pure]
  simp only [ZKOpInterp]
  dsimp only [bind, StateT.bind, StateT.pure, Pure.pure]
  split <;> [rfl; rfl]

/-! ### Monad morphism: `runZKBuilder` distributes over bind

Key lemma enabling compositional bridges: `runZKBuilder (m >>= k)` can be
computed sequentially, first running `m` then running `k` on the result.
-/

set_option maxHeartbeats 1600000 in
theorem runZKBuilder_bind {α β : Type} (m : ZKBuilder g α) (k : α → ZKBuilder g β) (st : ZKState g) :
    runZKBuilder (m >>= k) st =
    ((runZKBuilder m st).bind (fun p => runZKBuilder (k p.1) p.2)) := by
  induction m generalizing st with
  | pure a =>
    show runZKBuilder ((Cslib.FreeM.pure a : Cslib.FreeM (ZKOp g) α) >>= k) st = _
    simp only [Cslib.FreeM.bind_eq_bind, Cslib.FreeM.pure_bind]
    show _ = (runZKBuilder (Cslib.FreeM.pure a) st).bind _
    dsimp only [runZKBuilder, Cslib.FreeM.foldFreeM, StateT.pure, Pure.pure, Option.bind]
  | liftBind op cont ih =>
    show runZKBuilder ((Cslib.FreeM.liftBind op cont : Cslib.FreeM (ZKOp g) α) >>= k) st = _
    simp only [Cslib.FreeM.bind_eq_bind, Cslib.FreeM.liftBind_bind]
    show runZKBuilder (Cslib.FreeM.liftBind op (fun x => (cont x).bind k)) st =
         (runZKBuilder (Cslib.FreeM.liftBind op cont) st).bind _
    dsimp only [runZKBuilder, Cslib.FreeM.foldFreeM,
      bind, StateT.bind, Cslib.FreeM.instMonad, Cslib.FreeM.bind]
    -- Both sides match on ZKOpInterp op st
    cases h : ZKOpInterp op st with
    | none => simp [Option.bind]
    | some p =>
      simp [Option.bind]
      exact ih p.1 p.2

/-- Generic split lemma: peel one layer of `>>=` separating a
    `PUnit`-valued monadic action from its continuation. If the whole
    sequence succeeds on `st`, then the first action succeeds on `st` AND
    the continuation succeeds on *some* intermediate state. The state is
    existentially quantified because primitive bridges are state-agnostic
    (their conclusions only mention `step`). -/
theorem runZKBuilder_seq_isSome_split {α : Type}
    {m : ZKBuilder g PUnit} {k : PUnit → ZKBuilder g α} {st : ZKState g}
    (h : (runZKBuilder (m >>= k) st).isSome) :
    (runZKBuilder m st).isSome ∧ ∃ st', (runZKBuilder (k ()) st').isSome := by
  rw [runZKBuilder_bind] at h
  cases h_m : runZKBuilder m st with
  | none =>
    rw [h_m] at h
    simp [Option.bind] at h
  | some p =>
    refine ⟨?_, p.2, ?_⟩
    · exact rfl
    · rw [h_m] at h
      simp only [Option.bind] at h
      exact h

/-! ### Gap C: master_constraints bridge (via runZKBuilder equation lemmas)

Now that we have `runZKBuilder_constrainR1CS_eq` and `runZKBuilder_constrainEq_eq`,
we can prove the master_constraints bridge by repeated rewriting.
-/

/-! ### Gap I: Small one_hot bridges (chunks of ≤ 6 constraints each)

One big 23-constraint bridge would hit Lean's split/simp step limits.
Instead we prove 4 small chunks separately and compose at use sites.
-/

set_option maxHeartbeats 3200000 in
theorem one_hot_bool_chunk_1_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (one_hot_bool_chunk_1 step) st).isSome →
    step.is_add.eval * (step.is_add.eval - 1) = 0 ∧
    step.is_adc.eval * (step.is_adc.eval - 1) = 0 ∧
    step.is_sub.eval * (step.is_sub.eval - 1) = 0 ∧
    step.is_sbc.eval * (step.is_sbc.eval - 1) = 0 ∧
    step.is_and.eval * (step.is_and.eval - 1) = 0 ∧
    step.is_xor.eval * (step.is_xor.eval - 1) = 0 := by
  simp only [one_hot_bool_chunk_1, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h1 : (step.is_add.eval * (step.is_add.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1] at h
  by_cases h2 : (step.is_adc.eval * (step.is_adc.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2] at h
  by_cases h3 : (step.is_sub.eval * (step.is_sub.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3] at h
  by_cases h4 : (step.is_sbc.eval * (step.is_sbc.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4] at h
  by_cases h5 : (step.is_and.eval * (step.is_and.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.is_xor.eval * (step.is_xor.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4, h5, h6] at h
  exact ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6⟩

set_option maxHeartbeats 3200000 in
theorem one_hot_bool_chunk_2_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (one_hot_bool_chunk_2 step) st).isSome →
    step.is_or.eval * (step.is_or.eval - 1) = 0 ∧
    step.is_cp.eval * (step.is_cp.eval - 1) = 0 ∧
    step.is_inc.eval * (step.is_inc.eval - 1) = 0 ∧
    step.is_dec.eval * (step.is_dec.eval - 1) = 0 ∧
    step.is_rlc.eval * (step.is_rlc.eval - 1) = 0 ∧
    step.is_rrc.eval * (step.is_rrc.eval - 1) = 0 := by
  simp only [one_hot_bool_chunk_2, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h1 : (step.is_or.eval * (step.is_or.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1] at h
  by_cases h2 : (step.is_cp.eval * (step.is_cp.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2] at h
  by_cases h3 : (step.is_inc.eval * (step.is_inc.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3] at h
  by_cases h4 : (step.is_dec.eval * (step.is_dec.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4] at h
  by_cases h5 : (step.is_rlc.eval * (step.is_rlc.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.is_rrc.eval * (step.is_rrc.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4, h5, h6] at h
  exact ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6⟩

set_option maxHeartbeats 3200000 in
theorem one_hot_bool_chunk_3_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (one_hot_bool_chunk_3 step) st).isSome →
    step.is_rl.eval * (step.is_rl.eval - 1) = 0 ∧
    step.is_rr.eval * (step.is_rr.eval - 1) = 0 ∧
    step.is_sla.eval * (step.is_sla.eval - 1) = 0 ∧
    step.is_sra.eval * (step.is_sra.eval - 1) = 0 ∧
    step.is_srl.eval * (step.is_srl.eval - 1) = 0 ∧
    step.is_swap.eval * (step.is_swap.eval - 1) = 0 := by
  simp only [one_hot_bool_chunk_3, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h1 : (step.is_rl.eval * (step.is_rl.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1] at h
  by_cases h2 : (step.is_rr.eval * (step.is_rr.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2] at h
  by_cases h3 : (step.is_sla.eval * (step.is_sla.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3] at h
  by_cases h4 : (step.is_sra.eval * (step.is_sra.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4] at h
  by_cases h5 : (step.is_srl.eval * (step.is_srl.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.is_swap.eval * (step.is_swap.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4, h5, h6] at h
  exact ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6⟩

set_option maxHeartbeats 3200000 in
theorem one_hot_bool_chunk_4_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (one_hot_bool_chunk_4 step) st).isSome →
    step.is_daa.eval * (step.is_daa.eval - 1) = 0 ∧
    step.is_cpl.eval * (step.is_cpl.eval - 1) = 0 ∧
    step.is_ccf.eval * (step.is_ccf.eval - 1) = 0 ∧
    step.is_scf.eval * (step.is_scf.eval - 1) = 0 := by
  simp only [one_hot_bool_chunk_4, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h1 : (step.is_daa.eval * (step.is_daa.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1] at h
  by_cases h2 : (step.is_cpl.eval * (step.is_cpl.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2] at h
  by_cases h3 : (step.is_ccf.eval * (step.is_ccf.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3] at h
  by_cases h4 : (step.is_scf.eval * (step.is_scf.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h1, h2, h3, h4] at h
  exact ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3, beq_iff_eq.mp h4⟩

set_option maxHeartbeats 800000 in
theorem one_hot_sum_constraint_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (one_hot_sum_constraint step) st).isSome →
    (step.is_add + step.is_adc + step.is_sub + step.is_sbc +
      step.is_and + step.is_xor + step.is_or + step.is_cp +
      step.is_inc + step.is_dec + step.is_rlc + step.is_rrc +
      step.is_rl + step.is_rr + step.is_sla + step.is_sra +
      step.is_srl + step.is_swap + step.is_daa + step.is_cpl +
      step.is_ccf + step.is_scf).eval = 1 := by
  simp only [one_hot_sum_constraint, runZKBuilder_constrainEq_eq]
  intro h
  split at h
  · next heq =>
    have := beq_iff_eq.mp heq
    simpa using this
  · contradiction

/-! ### Gap I derivation: sum of Booleans = 0 ⇒ all 0

Key lemma for Gap I's soundness: a list of Booleans in `ZMod p` with length
less than `p` summing to 0 must have all elements equal to 0.
-/

/-- `(x + y).val ≤ x.val + y.val` when `x.val + y.val < p`. -/
private theorem val_add_bool {p : ℕ} [hp : Fact p.Prime] {x : ZMod p}
    (hx : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases hx with rfl | rfl
  · simp
  · simp [ZMod.val_one]

/-- The val of a sum of Booleans is bounded by the list length. -/
theorem sum_bool_val_le {p : ℕ} [hp : Fact p.Prime]
    (xs : List (ZMod p)) (hlen : xs.length < p)
    (hb : ∀ x ∈ xs, x = 0 ∨ x = 1) :
    xs.sum.val ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hlen' : xs.length < p := by simp at hlen; omega
    have hb' : ∀ y ∈ xs, y = 0 ∨ y = 1 :=
      fun y hy => hb y (List.mem_cons_of_mem _ hy)
    have ih' := ih hlen' hb'
    have hx_val : x.val ≤ 1 := val_add_bool (hb x (List.mem_cons_self))
    have h_bound : x.val + xs.sum.val < p := by
      have : x.val + xs.sum.val ≤ 1 + xs.length := by omega
      calc x.val + xs.sum.val ≤ 1 + xs.length := this
        _ = xs.length + 1 := by omega
        _ = (x :: xs).length := by simp
        _ < p := hlen
    have h_sum : (x + xs.sum).val = x.val + xs.sum.val := ZMod.val_add_of_lt h_bound
    simp only [List.sum_cons, List.length_cons]
    rw [h_sum]
    omega

/-- Sum of Booleans = 0 in ZMod p (with length < p) implies each is 0. -/
theorem sum_bool_eq_zero_all_zero {p : ℕ} [hp : Fact p.Prime]
    (xs : List (ZMod p)) (hlen : xs.length < p)
    (hb : ∀ x ∈ xs, x = 0 ∨ x = 1) (hsum : xs.sum = 0) :
    ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => intro x hx; simp at hx
  | cons x xs ih =>
    have hlen' : xs.length < p := by simp at hlen; omega
    have hb' : ∀ y ∈ xs, y = 0 ∨ y = 1 :=
      fun y hy => hb y (List.mem_cons_of_mem _ hy)
    have hx : x = 0 ∨ x = 1 := hb x (List.mem_cons_self)
    -- Key claim: x = 0 (otherwise derive contradiction from hsum)
    have h_x_zero : x = 0 := by
      rcases hx with hx | hx
      · exact hx
      · -- x = 1: hsum says 1 + xs.sum = 0. But (1 + xs.sum).val = 1 + xs.sum.val
        -- (no wraparound since 1 + xs.length < p), and this is ≥ 1 > 0, so
        -- 1 + xs.sum ≠ 0 in ZMod p. Contradiction.
        exfalso
        have h_cons : (x :: xs).sum = 0 := hsum
        rw [List.sum_cons, hx] at h_cons
        have h_xs_val_le : xs.sum.val ≤ xs.length := sum_bool_val_le xs hlen' hb'
        have h_bound : (1 : ZMod p).val + xs.sum.val < p := by
          rw [ZMod.val_one]
          have : xs.length + 1 < p := by simp at hlen; omega
          omega
        have h_val_eq : (1 + xs.sum).val = (1 : ZMod p).val + xs.sum.val :=
          ZMod.val_add_of_lt h_bound
        rw [h_cons] at h_val_eq
        rw [ZMod.val_zero, ZMod.val_one] at h_val_eq
        omega
    -- With x = 0, xs.sum = 0, apply IH to xs
    have h_xs_sum_zero : xs.sum = 0 := by
      have := hsum
      rw [List.sum_cons, h_x_zero, zero_add] at this
      exact this
    have h_xs_all := ih hlen' hb' h_xs_sum_zero
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h_x_zero
    · exact h_xs_all y hy

/-- For ADD: derive `N = 0` from one-hot Boolean + sum constraints + `is_add = 1`.
    Uses `sum_bool_eq_zero_all_zero` to show all non-ADD flags are 0. -/
theorem add_N_derived_from_onehot
    {is_add is_adc is_sub is_sbc is_and is_xor is_or is_cp
     is_inc is_dec is_rlc is_rrc is_rl is_rr is_sla is_sra is_srl is_swap
     is_daa is_cpl is_ccf is_scf flag_n : ZMod p}
    (hp_big : 22 < p)
    (h_add : is_add = 1)
    (ha : is_add = 0 ∨ is_add = 1) (hb : is_adc = 0 ∨ is_adc = 1)
    (hc : is_sub = 0 ∨ is_sub = 1) (hd : is_sbc = 0 ∨ is_sbc = 1)
    (he : is_and = 0 ∨ is_and = 1) (hf : is_xor = 0 ∨ is_xor = 1)
    (hg : is_or = 0 ∨ is_or = 1) (hh : is_cp = 0 ∨ is_cp = 1)
    (hi : is_inc = 0 ∨ is_inc = 1) (hj : is_dec = 0 ∨ is_dec = 1)
    (hk : is_rlc = 0 ∨ is_rlc = 1) (hl : is_rrc = 0 ∨ is_rrc = 1)
    (hm : is_rl = 0 ∨ is_rl = 1) (hn : is_rr = 0 ∨ is_rr = 1)
    (ho : is_sla = 0 ∨ is_sla = 1) (hq : is_sra = 0 ∨ is_sra = 1)
    (hr : is_srl = 0 ∨ is_srl = 1) (hs : is_swap = 0 ∨ is_swap = 1)
    (ht : is_daa = 0 ∨ is_daa = 1) (hu : is_cpl = 0 ∨ is_cpl = 1)
    (hv : is_ccf = 0 ∨ is_ccf = 1) (hw : is_scf = 0 ∨ is_scf = 1)
    (h_sum : is_add + is_adc + is_sub + is_sbc + is_and + is_xor + is_or + is_cp +
             is_inc + is_dec + is_rlc + is_rrc + is_rl + is_rr + is_sla + is_sra +
             is_srl + is_swap + is_daa + is_cpl + is_ccf + is_scf = 1)
    (h_n_eq : flag_n = is_sub + is_sbc + is_cp + is_dec + is_cpl) :
    flag_n = 0 := by
  let others : List (ZMod p) := [is_adc, is_sub, is_sbc, is_and, is_xor, is_or,
    is_cp, is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
    is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have h_others_len_lt : others.length < p := by show 21 < p; omega
  have h_others_bool : ∀ x ∈ others, x = 0 ∨ x = 1 := by
    intro x hx
    simp [others, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  have h_others_sum : others.sum = 0 := by
    show is_adc + (is_sub + (is_sbc + (is_and + (is_xor + (is_or + (is_cp +
      (is_inc + (is_dec + (is_rlc + (is_rrc + (is_rl + (is_rr + (is_sla +
      (is_sra + (is_srl + (is_swap + (is_daa + (is_cpl + (is_ccf +
      (is_scf + 0)))))))))))))))))))) = 0
    linear_combination h_sum - h_add
  have h_all_zero := sum_bool_eq_zero_all_zero others h_others_len_lt h_others_bool h_others_sum
  have h_is_sub : is_sub = 0 := h_all_zero is_sub (by simp [others])
  have h_is_sbc : is_sbc = 0 := h_all_zero is_sbc (by simp [others])
  have h_is_cp : is_cp = 0 := h_all_zero is_cp (by simp [others])
  have h_is_dec : is_dec = 0 := h_all_zero is_dec (by simp [others])
  have h_is_cpl : is_cpl = 0 := h_all_zero is_cpl (by simp [others])
  rw [h_n_eq, h_is_sub, h_is_sbc, h_is_cp, h_is_dec, h_is_cpl]
  simp

/-! ### Gap I: Status

**Closed (constraints added, bridges proved):**
- `one_hot_constraints` in the generator emits 22 Boolean + 1 sum constraint.
- `one_hot_bool_chunk_{1-4}_bridge` extracts the 22 Boolean equations.
- `one_hot_sum_constraint_bridge` extracts the sum-to-1 equation.
- `sum_bool_val_le`: `xs.sum.val ≤ xs.length` for Boolean lists.
- `sum_bool_eq_zero_all_zero`: sum of 0 ⇒ all 0 (via Nat sum).

**Fully provable using `sum_bool_eq_zero_all_zero`:** the derivation
"one_hot + is_X = 1 ⇒ all other flags = 0" follows by subtracting to get
the other-flag sum equal to 0, then applying this lemma.
-/

/-! ### Gap H: Range bridges for `range_bool_{a,b,r}` and `range_sum_{a,b,r}`

Each range_bool chunk has 8 Boolean constraints. Each range_sum chunk has
1 equality constraint tying the value to its bit decomposition.
-/

set_option maxHeartbeats 3200000 in
theorem range_bool_a_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (range_bool_a step) st).isSome →
    step.a_bit_0.eval * (step.a_bit_0.eval - 1) = 0 ∧
    step.a_bit_1.eval * (step.a_bit_1.eval - 1) = 0 ∧
    step.a_bit_2.eval * (step.a_bit_2.eval - 1) = 0 ∧
    step.a_bit_3.eval * (step.a_bit_3.eval - 1) = 0 ∧
    step.a_bit_4.eval * (step.a_bit_4.eval - 1) = 0 ∧
    step.a_bit_5.eval * (step.a_bit_5.eval - 1) = 0 ∧
    step.a_bit_6.eval * (step.a_bit_6.eval - 1) = 0 ∧
    step.a_bit_7.eval * (step.a_bit_7.eval - 1) = 0 := by
  simp only [range_bool_a, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h0 : (step.a_bit_0.eval * (step.a_bit_0.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0] at h
  by_cases h1 : (step.a_bit_1.eval * (step.a_bit_1.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1] at h
  by_cases h2 : (step.a_bit_2.eval * (step.a_bit_2.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2] at h
  by_cases h3 : (step.a_bit_3.eval * (step.a_bit_3.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3] at h
  by_cases h4 : (step.a_bit_4.eval * (step.a_bit_4.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4] at h
  by_cases h5 : (step.a_bit_5.eval * (step.a_bit_5.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.a_bit_6.eval * (step.a_bit_6.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6] at h
  by_cases h7 : (step.a_bit_7.eval * (step.a_bit_7.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
  exact ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7⟩

set_option maxHeartbeats 3200000 in
theorem range_bool_b_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (range_bool_b step) st).isSome →
    step.b_bit_0.eval * (step.b_bit_0.eval - 1) = 0 ∧
    step.b_bit_1.eval * (step.b_bit_1.eval - 1) = 0 ∧
    step.b_bit_2.eval * (step.b_bit_2.eval - 1) = 0 ∧
    step.b_bit_3.eval * (step.b_bit_3.eval - 1) = 0 ∧
    step.b_bit_4.eval * (step.b_bit_4.eval - 1) = 0 ∧
    step.b_bit_5.eval * (step.b_bit_5.eval - 1) = 0 ∧
    step.b_bit_6.eval * (step.b_bit_6.eval - 1) = 0 ∧
    step.b_bit_7.eval * (step.b_bit_7.eval - 1) = 0 := by
  simp only [range_bool_b, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h0 : (step.b_bit_0.eval * (step.b_bit_0.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0] at h
  by_cases h1 : (step.b_bit_1.eval * (step.b_bit_1.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1] at h
  by_cases h2 : (step.b_bit_2.eval * (step.b_bit_2.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2] at h
  by_cases h3 : (step.b_bit_3.eval * (step.b_bit_3.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3] at h
  by_cases h4 : (step.b_bit_4.eval * (step.b_bit_4.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4] at h
  by_cases h5 : (step.b_bit_5.eval * (step.b_bit_5.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.b_bit_6.eval * (step.b_bit_6.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6] at h
  by_cases h7 : (step.b_bit_7.eval * (step.b_bit_7.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
  exact ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7⟩

set_option maxHeartbeats 3200000 in
theorem range_bool_r_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (range_bool_r step) st).isSome →
    step.r_bit_0.eval * (step.r_bit_0.eval - 1) = 0 ∧
    step.r_bit_1.eval * (step.r_bit_1.eval - 1) = 0 ∧
    step.r_bit_2.eval * (step.r_bit_2.eval - 1) = 0 ∧
    step.r_bit_3.eval * (step.r_bit_3.eval - 1) = 0 ∧
    step.r_bit_4.eval * (step.r_bit_4.eval - 1) = 0 ∧
    step.r_bit_5.eval * (step.r_bit_5.eval - 1) = 0 ∧
    step.r_bit_6.eval * (step.r_bit_6.eval - 1) = 0 ∧
    step.r_bit_7.eval * (step.r_bit_7.eval - 1) = 0 := by
  simp only [range_bool_r, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h0 : (step.r_bit_0.eval * (step.r_bit_0.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0] at h
  by_cases h1 : (step.r_bit_1.eval * (step.r_bit_1.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1] at h
  by_cases h2 : (step.r_bit_2.eval * (step.r_bit_2.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2] at h
  by_cases h3 : (step.r_bit_3.eval * (step.r_bit_3.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3] at h
  by_cases h4 : (step.r_bit_4.eval * (step.r_bit_4.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4] at h
  by_cases h5 : (step.r_bit_5.eval * (step.r_bit_5.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.r_bit_6.eval * (step.r_bit_6.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6] at h
  by_cases h7 : (step.r_bit_7.eval * (step.r_bit_7.eval - 1) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
  exact ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7⟩

set_option maxHeartbeats 800000 in
theorem range_sum_a_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (range_sum_a step) st).isSome →
    step.alu_operand_a.eval =
      step.a_bit_0.eval + step.a_bit_1.eval * 2 + step.a_bit_2.eval * 4 +
      step.a_bit_3.eval * 8 + step.a_bit_4.eval * 16 + step.a_bit_5.eval * 32 +
      step.a_bit_6.eval * 64 + step.a_bit_7.eval * 128 := by
  simp only [range_sum_a, runZKBuilder_constrainEq_eq]
  intro h
  split at h
  · next heq =>
    have := beq_iff_eq.mp heq
    simpa [ZKExpr.eval] using this
  · contradiction

set_option maxHeartbeats 800000 in
theorem range_sum_b_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (range_sum_b step) st).isSome →
    step.alu_operand_b.eval =
      step.b_bit_0.eval + step.b_bit_1.eval * 2 + step.b_bit_2.eval * 4 +
      step.b_bit_3.eval * 8 + step.b_bit_4.eval * 16 + step.b_bit_5.eval * 32 +
      step.b_bit_6.eval * 64 + step.b_bit_7.eval * 128 := by
  simp only [range_sum_b, runZKBuilder_constrainEq_eq]
  intro h
  split at h
  · next heq =>
    have := beq_iff_eq.mp heq
    simpa [ZKExpr.eval] using this
  · contradiction

set_option maxHeartbeats 800000 in
theorem range_sum_r_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (range_sum_r step) st).isSome →
    step.alu_result.eval =
      step.r_bit_0.eval + step.r_bit_1.eval * 2 + step.r_bit_2.eval * 4 +
      step.r_bit_3.eval * 8 + step.r_bit_4.eval * 16 + step.r_bit_5.eval * 32 +
      step.r_bit_6.eval * 64 + step.r_bit_7.eval * 128 := by
  simp only [range_sum_r, runZKBuilder_constrainEq_eq]
  intro h
  split at h
  · next heq =>
    have := beq_iff_eq.mp heq
    simpa [ZKExpr.eval] using this
  · contradiction

/-! ### Gap A: Table lookup bridge for bitwise ops

The `table_constraint_and` gadget emits 8 R1CS constraints of the form
`is_and * (r_bit_i - a_bit_i * b_bit_i) = 0`. When `is_and = 1` (one-hot),
this forces `r_bit_i = a_bit_i * b_bit_i` for each bit i, which IS the
closed-form polynomial for bitwise AND.

Combined with the range sum constraint (from Gap H), this implies
`alu_result = Σ (a_bit_i * b_bit_i) * 2^i = a AND b` (bitwise).
-/

set_option maxHeartbeats 3200000 in
theorem table_constraint_and_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (table_constraint_and step) st).isSome →
    step.is_and.eval * (step.r_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval) = 0 ∧
    step.is_and.eval * (step.r_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval) = 0 ∧
    step.is_and.eval * (step.r_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval) = 0 ∧
    step.is_and.eval * (step.r_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval) = 0 ∧
    step.is_and.eval * (step.r_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval) = 0 ∧
    step.is_and.eval * (step.r_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval) = 0 ∧
    step.is_and.eval * (step.r_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval) = 0 ∧
    step.is_and.eval * (step.r_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval) = 0 := by
  simp only [table_constraint_and, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h0 : (step.is_and.eval * (step.r_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0] at h
  by_cases h1 : (step.is_and.eval * (step.r_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1] at h
  by_cases h2 : (step.is_and.eval * (step.r_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2] at h
  by_cases h3 : (step.is_and.eval * (step.r_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3] at h
  by_cases h4 : (step.is_and.eval * (step.r_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4] at h
  by_cases h5 : (step.is_and.eval * (step.r_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.is_and.eval * (step.r_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6] at h
  by_cases h7 : (step.is_and.eval * (step.r_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
  exact ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7⟩

set_option maxHeartbeats 3200000 in
theorem table_constraint_xor_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (table_constraint_xor step) st).isSome →
    step.is_xor.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval * 2)) = 0 ∧
    step.is_xor.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval * 2)) = 0 ∧
    step.is_xor.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval * 2)) = 0 ∧
    step.is_xor.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval * 2)) = 0 ∧
    step.is_xor.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval * 2)) = 0 ∧
    step.is_xor.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval * 2)) = 0 ∧
    step.is_xor.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval * 2)) = 0 ∧
    step.is_xor.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval * 2)) = 0 := by
  simp only [table_constraint_xor, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h0 : (step.is_xor.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0] at h
  by_cases h1 : (step.is_xor.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1] at h
  by_cases h2 : (step.is_xor.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2] at h
  by_cases h3 : (step.is_xor.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3] at h
  by_cases h4 : (step.is_xor.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4] at h
  by_cases h5 : (step.is_xor.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.is_xor.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6] at h
  by_cases h7 : (step.is_xor.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval * 2)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
  exact ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7⟩

set_option maxHeartbeats 3200000 in
theorem table_constraint_or_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (table_constraint_or step) st).isSome →
    step.is_or.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval)) = 0 ∧
    step.is_or.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval)) = 0 ∧
    step.is_or.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval)) = 0 ∧
    step.is_or.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval)) = 0 ∧
    step.is_or.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval)) = 0 ∧
    step.is_or.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval)) = 0 ∧
    step.is_or.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval)) = 0 ∧
    step.is_or.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval)) = 0 := by
  simp only [table_constraint_or, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, ZKExpr.eval]
  intro h
  by_cases h0 : (step.is_or.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0] at h
  by_cases h1 : (step.is_or.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1] at h
  by_cases h2 : (step.is_or.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2] at h
  by_cases h3 : (step.is_or.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3] at h
  by_cases h4 : (step.is_or.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4] at h
  by_cases h5 : (step.is_or.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5] at h
  by_cases h6 : (step.is_or.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6] at h
  by_cases h7 : (step.is_or.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval)) == 0) = true
  on_goal 2 => exfalso; simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
  exact ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
         beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7⟩

/-- When `is_and = 1`, the bit-level AND constraint implies r_bit = a_bit * b_bit. -/
theorem and_constraint_activates {p : ℕ} [Fact p.Prime]
    {is_and r a b : ZMod p}
    (h_constr : is_and * (r - a * b) = 0)
    (h_one : is_and = 1) : r = a * b := by
  rw [h_one, one_mul] at h_constr
  exact sub_eq_zero.mp h_constr

/-! ### Gap H derivation: bit decomposition implies value ≤ 255

Key lemma: For 8 Booleans and a value equal to `Σ bᵢ * 2ⁱ`, the value
(interpreted as a natural via `ZMod.val`) is at most 255.

Proof strategy:
1. Each `bᵢ.val ≤ 1` (since Boolean).
2. `(bᵢ * (2^i : ZMod p)).val ≤ bᵢ.val * 2^i ≤ 2^i` by `ZMod.val_mul_le`
   and the bound on `(2^i : ZMod p).val` (which equals `2^i` when `2^i < p`).
3. The sum `(b₀ + 2*b₁ + 4*b₂ + ... + 128*b₇).val ≤ 1 + 2 + 4 + ... + 128 = 255`
   by iterated `ZMod.val_add_le`.
-/

/-- For natural `n < p`, `((n : ZMod p)).val = n`. -/
private theorem zmod_val_natcast_lt {p : ℕ} [Fact p.Prime] (n : ℕ) (h : n < p) :
    ((n : ZMod p)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

/-- For Boolean `b` and natural `n < p`, `(b * (n : ZMod p)).val ≤ n`. -/
private theorem val_mul_bool_le {p : ℕ} [Fact p.Prime] {b : ZMod p} {n : ℕ}
    (hb : b = 0 ∨ b = 1) (hn : n < p) :
    (b * (n : ZMod p)).val ≤ n := by
  rcases hb with rfl | rfl
  · simp
  · rw [one_mul, zmod_val_natcast_lt n hn]

/-- Range decomposition bound: 8 Boolean bits form a value ≤ 255. -/
theorem bit_decomposition_val_le {p : ℕ} [Fact p.Prime] (hp_big : 256 < p)
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    (h₀ : b₀ = 0 ∨ b₀ = 1) (h₁ : b₁ = 0 ∨ b₁ = 1) (h₂ : b₂ = 0 ∨ b₂ = 1)
    (h₃ : b₃ = 0 ∨ b₃ = 1) (h₄ : b₄ = 0 ∨ b₄ = 1) (h₅ : b₅ = 0 ∨ b₅ = 1)
    (h₆ : b₆ = 0 ∨ b₆ = 1) (h₇ : b₇ = 0 ∨ b₇ = 1) :
    (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64 + b₇ * 128).val ≤ 255 := by
  -- Each individual product has val ≤ 2^i
  have hb₀ : b₀.val ≤ 1 := val_add_bool h₀
  have hb₁ : (b₁ * (2 : ZMod p)).val ≤ 2 := by
    have : ((2 : ℕ) : ZMod p) = 2 := by norm_cast
    rw [← this]; exact val_mul_bool_le h₁ (by omega)
  have hb₂ : (b₂ * (4 : ZMod p)).val ≤ 4 := by
    have : ((4 : ℕ) : ZMod p) = 4 := by norm_cast
    rw [← this]; exact val_mul_bool_le h₂ (by omega)
  have hb₃ : (b₃ * (8 : ZMod p)).val ≤ 8 := by
    have : ((8 : ℕ) : ZMod p) = 8 := by norm_cast
    rw [← this]; exact val_mul_bool_le h₃ (by omega)
  have hb₄ : (b₄ * (16 : ZMod p)).val ≤ 16 := by
    have : ((16 : ℕ) : ZMod p) = 16 := by norm_cast
    rw [← this]; exact val_mul_bool_le h₄ (by omega)
  have hb₅ : (b₅ * (32 : ZMod p)).val ≤ 32 := by
    have : ((32 : ℕ) : ZMod p) = 32 := by norm_cast
    rw [← this]; exact val_mul_bool_le h₅ (by omega)
  have hb₆ : (b₆ * (64 : ZMod p)).val ≤ 64 := by
    have : ((64 : ℕ) : ZMod p) = 64 := by norm_cast
    rw [← this]; exact val_mul_bool_le h₆ (by omega)
  have hb₇ : (b₇ * (128 : ZMod p)).val ≤ 128 := by
    have : ((128 : ℕ) : ZMod p) = 128 := by norm_cast
    rw [← this]; exact val_mul_bool_le h₇ (by omega)
  -- Sum bounds via ZMod.val_add_le
  have s1 : (b₀ + b₁ * 2).val ≤ 1 + 2 :=
    le_trans (ZMod.val_add_le _ _) (by omega)
  have s2 : (b₀ + b₁ * 2 + b₂ * 4).val ≤ 1 + 2 + 4 :=
    le_trans (ZMod.val_add_le _ _) (by omega)
  have s3 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8).val ≤ 1 + 2 + 4 + 8 :=
    le_trans (ZMod.val_add_le _ _) (by omega)
  have s4 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16).val ≤ 1 + 2 + 4 + 8 + 16 :=
    le_trans (ZMod.val_add_le _ _) (by omega)
  have s5 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32).val ≤ 1 + 2 + 4 + 8 + 16 + 32 :=
    le_trans (ZMod.val_add_le _ _) (by omega)
  have s6 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64).val ≤
            1 + 2 + 4 + 8 + 16 + 32 + 64 :=
    le_trans (ZMod.val_add_le _ _) (by omega)
  calc (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64 + b₇ * 128).val
      ≤ (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64).val +
        (b₇ * 128).val := ZMod.val_add_le _ _
    _ ≤ (1 + 2 + 4 + 8 + 16 + 32 + 64) + 128 := by omega
    _ = 255 := by omega

/-! ### Gap A derivation: bit-level AND implies per-bit Nat multiplication

Key lemmas connecting the field-level AND bit constraint to Nat-level semantics:
1. For Boolean a, b in ZMod p, `(a * b).val = a.val * b.val` (the product of
   two {0,1} values never wraps around).
2. For the AND bit constraint `is_and * (r - a * b) = 0` with `is_and = 1`,
   we get `r = a * b` in the field, hence `r.val = a.val * b.val` as Nats.
3. Summing the per-bit products gives the value-level AND relation.
-/

/-- For Booleans a, b in ZMod p, (a * b).val = a.val * b.val. No wraparound
    since the product is itself in {0, 1}. -/
theorem val_bool_mul_bool {p : ℕ} [Fact p.Prime] {a b : ZMod p}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a * b).val = a.val * b.val := by
  rcases ha with rfl | rfl
  · simp
  · rcases hb with rfl | rfl
    · simp
    · simp [ZMod.val_one]

/-- Gap A per-bit soundness for AND: given the bit-level AND constraint
    and `is_and = 1`, the result bit equals the product of operand bits at
    the Nat level: `r_bit.val = a_bit.val * b_bit.val`. -/
theorem and_per_bit_nat_sound {p : ℕ} [Fact p.Prime]
    {is_and a_bit b_bit r_bit : ZMod p}
    (h_is_and : is_and = 1)
    (h_bit_constr : is_and * (r_bit - a_bit * b_bit) = 0)
    (ha : a_bit = 0 ∨ a_bit = 1)
    (hb : b_bit = 0 ∨ b_bit = 1) :
    r_bit.val = a_bit.val * b_bit.val := by
  have h_eq : r_bit = a_bit * b_bit := and_constraint_activates h_bit_constr h_is_and
  rw [h_eq]
  exact val_bool_mul_bool ha hb

/-- The value-level AND equality via bit decomposition. Given:
    - `is_and = 1` (one-hot for AND)
    - All 8 result bits satisfy the AND constraint
    - All 24 bits (a, b, r) are Boolean
    - `alu_result = Σ r_bit_i * 2^i` (from range sum)

    Then: `alu_result = Σ (a_bit_i * b_bit_i) * 2^i`. This is the value-level
    expression of bitwise AND via bit decomposition — the structural content
    of the AND lookup. -/
theorem and_value_sound {p : ℕ} [Fact p.Prime]
    {is_and alu_result : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    {r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ZMod p}
    (h_is_and : is_and = 1)
    -- Bit-level AND constraints (from table_constraint_and_bridge):
    (hbc₀ : is_and * (r₀ - a₀ * b₀) = 0)
    (hbc₁ : is_and * (r₁ - a₁ * b₁) = 0)
    (hbc₂ : is_and * (r₂ - a₂ * b₂) = 0)
    (hbc₃ : is_and * (r₃ - a₃ * b₃) = 0)
    (hbc₄ : is_and * (r₄ - a₄ * b₄) = 0)
    (hbc₅ : is_and * (r₅ - a₅ * b₅) = 0)
    (hbc₆ : is_and * (r₆ - a₆ * b₆) = 0)
    (hbc₇ : is_and * (r₇ - a₇ * b₇) = 0)
    -- Range sum for result (from range_sum_r_bridge):
    (h_r_sum : alu_result = r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 +
                            r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128) :
    alu_result = a₀ * b₀ + a₁ * b₁ * 2 + a₂ * b₂ * 4 + a₃ * b₃ * 8 +
                 a₄ * b₄ * 16 + a₅ * b₅ * 32 + a₆ * b₆ * 64 + a₇ * b₇ * 128 := by
  have e₀ : r₀ = a₀ * b₀ := and_constraint_activates hbc₀ h_is_and
  have e₁ : r₁ = a₁ * b₁ := and_constraint_activates hbc₁ h_is_and
  have e₂ : r₂ = a₂ * b₂ := and_constraint_activates hbc₂ h_is_and
  have e₃ : r₃ = a₃ * b₃ := and_constraint_activates hbc₃ h_is_and
  have e₄ : r₄ = a₄ * b₄ := and_constraint_activates hbc₄ h_is_and
  have e₅ : r₅ = a₅ * b₅ := and_constraint_activates hbc₅ h_is_and
  have e₆ : r₆ = a₆ * b₆ := and_constraint_activates hbc₆ h_is_and
  have e₇ : r₇ = a₇ * b₇ := and_constraint_activates hbc₇ h_is_and
  rw [h_r_sum, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇]

/-! ### Gap A derivations for XOR and OR

Analogous to the AND case. XOR uses `r = a + b - 2*a*b`; OR uses
`r = a + b - a*b`. Both are closed-form polynomials over {0,1}. -/

/-- When `is_xor = 1`, the bit-level XOR constraint implies
    `r = a + b - 2 * a * b`. -/
theorem xor_constraint_activates {p : ℕ} [Fact p.Prime]
    {is_xor r a b : ZMod p}
    (h_constr : is_xor * (r - (a + b - a * b * 2)) = 0)
    (h_one : is_xor = 1) : r = a + b - a * b * 2 := by
  rw [h_one, one_mul] at h_constr
  exact sub_eq_zero.mp h_constr

/-- When `is_or = 1`, the bit-level OR constraint implies `r = a + b - a*b`. -/
theorem or_constraint_activates {p : ℕ} [Fact p.Prime]
    {is_or r a b : ZMod p}
    (h_constr : is_or * (r - (a + b - a * b)) = 0)
    (h_one : is_or = 1) : r = a + b - a * b := by
  rw [h_one, one_mul] at h_constr
  exact sub_eq_zero.mp h_constr

/-- The value-level XOR equality via bit decomposition. -/
theorem xor_value_sound {p : ℕ} [Fact p.Prime]
    {is_xor alu_result : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    {r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ZMod p}
    (h_is_xor : is_xor = 1)
    (hbc₀ : is_xor * (r₀ - (a₀ + b₀ - a₀ * b₀ * 2)) = 0)
    (hbc₁ : is_xor * (r₁ - (a₁ + b₁ - a₁ * b₁ * 2)) = 0)
    (hbc₂ : is_xor * (r₂ - (a₂ + b₂ - a₂ * b₂ * 2)) = 0)
    (hbc₃ : is_xor * (r₃ - (a₃ + b₃ - a₃ * b₃ * 2)) = 0)
    (hbc₄ : is_xor * (r₄ - (a₄ + b₄ - a₄ * b₄ * 2)) = 0)
    (hbc₅ : is_xor * (r₅ - (a₅ + b₅ - a₅ * b₅ * 2)) = 0)
    (hbc₆ : is_xor * (r₆ - (a₆ + b₆ - a₆ * b₆ * 2)) = 0)
    (hbc₇ : is_xor * (r₇ - (a₇ + b₇ - a₇ * b₇ * 2)) = 0)
    (h_r_sum : alu_result = r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 +
                            r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128) :
    alu_result =
      (a₀ + b₀ - a₀ * b₀ * 2) + (a₁ + b₁ - a₁ * b₁ * 2) * 2 +
      (a₂ + b₂ - a₂ * b₂ * 2) * 4 + (a₃ + b₃ - a₃ * b₃ * 2) * 8 +
      (a₄ + b₄ - a₄ * b₄ * 2) * 16 + (a₅ + b₅ - a₅ * b₅ * 2) * 32 +
      (a₆ + b₆ - a₆ * b₆ * 2) * 64 + (a₇ + b₇ - a₇ * b₇ * 2) * 128 := by
  have e₀ : r₀ = a₀ + b₀ - a₀ * b₀ * 2 := xor_constraint_activates hbc₀ h_is_xor
  have e₁ : r₁ = a₁ + b₁ - a₁ * b₁ * 2 := xor_constraint_activates hbc₁ h_is_xor
  have e₂ : r₂ = a₂ + b₂ - a₂ * b₂ * 2 := xor_constraint_activates hbc₂ h_is_xor
  have e₃ : r₃ = a₃ + b₃ - a₃ * b₃ * 2 := xor_constraint_activates hbc₃ h_is_xor
  have e₄ : r₄ = a₄ + b₄ - a₄ * b₄ * 2 := xor_constraint_activates hbc₄ h_is_xor
  have e₅ : r₅ = a₅ + b₅ - a₅ * b₅ * 2 := xor_constraint_activates hbc₅ h_is_xor
  have e₆ : r₆ = a₆ + b₆ - a₆ * b₆ * 2 := xor_constraint_activates hbc₆ h_is_xor
  have e₇ : r₇ = a₇ + b₇ - a₇ * b₇ * 2 := xor_constraint_activates hbc₇ h_is_xor
  rw [h_r_sum, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇]

/-- The value-level OR equality via bit decomposition. -/
theorem or_value_sound {p : ℕ} [Fact p.Prime]
    {is_or alu_result : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    {r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ZMod p}
    (h_is_or : is_or = 1)
    (hbc₀ : is_or * (r₀ - (a₀ + b₀ - a₀ * b₀)) = 0)
    (hbc₁ : is_or * (r₁ - (a₁ + b₁ - a₁ * b₁)) = 0)
    (hbc₂ : is_or * (r₂ - (a₂ + b₂ - a₂ * b₂)) = 0)
    (hbc₃ : is_or * (r₃ - (a₃ + b₃ - a₃ * b₃)) = 0)
    (hbc₄ : is_or * (r₄ - (a₄ + b₄ - a₄ * b₄)) = 0)
    (hbc₅ : is_or * (r₅ - (a₅ + b₅ - a₅ * b₅)) = 0)
    (hbc₆ : is_or * (r₆ - (a₆ + b₆ - a₆ * b₆)) = 0)
    (hbc₇ : is_or * (r₇ - (a₇ + b₇ - a₇ * b₇)) = 0)
    (h_r_sum : alu_result = r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 +
                            r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128) :
    alu_result =
      (a₀ + b₀ - a₀ * b₀) + (a₁ + b₁ - a₁ * b₁) * 2 +
      (a₂ + b₂ - a₂ * b₂) * 4 + (a₃ + b₃ - a₃ * b₃) * 8 +
      (a₄ + b₄ - a₄ * b₄) * 16 + (a₅ + b₅ - a₅ * b₅) * 32 +
      (a₆ + b₆ - a₆ * b₆) * 64 + (a₇ + b₇ - a₇ * b₇) * 128 := by
  have e₀ : r₀ = a₀ + b₀ - a₀ * b₀ := or_constraint_activates hbc₀ h_is_or
  have e₁ : r₁ = a₁ + b₁ - a₁ * b₁ := or_constraint_activates hbc₁ h_is_or
  have e₂ : r₂ = a₂ + b₂ - a₂ * b₂ := or_constraint_activates hbc₂ h_is_or
  have e₃ : r₃ = a₃ + b₃ - a₃ * b₃ := or_constraint_activates hbc₃ h_is_or
  have e₄ : r₄ = a₄ + b₄ - a₄ * b₄ := or_constraint_activates hbc₄ h_is_or
  have e₅ : r₅ = a₅ + b₅ - a₅ * b₅ := or_constraint_activates hbc₅ h_is_or
  have e₆ : r₆ = a₆ + b₆ - a₆ * b₆ := or_constraint_activates hbc₆ h_is_or
  have e₇ : r₇ = a₇ + b₇ - a₇ * b₇ := or_constraint_activates hbc₇ h_is_or
  rw [h_r_sum, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇]

/-! ### Per-instruction one-hot flag determinations

For each of the 22 SM83 opcodes, we derive the complete 22-flag
configuration from the one-hot constraints plus `is_X = 1`: the selected
flag is 1, and the other 21 flags are 0.

The common pattern is factored into `onehot_others_zero_generic`; each
per-instruction helper supplies the specific `others` list (21 elements
in canonical order, minus the selected opcode) and a one-line
`linear_combination` witness. -/

/-- Generic "others sum to zero" helper: given a selected field element
    equal to 1 and a list of Booleans whose sum (with the selected)
    equals 1, every element of the list equals 0. -/
theorem onehot_others_zero_generic {p : ℕ} [Fact p.Prime]
    {selected : ZMod p} (h_sel : selected = 1)
    (others : List (ZMod p))
    (h_len_lt : others.length < p)
    (h_bool : ∀ x ∈ others, x = 0 ∨ x = 1)
    (h_total : selected + others.sum = 1) :
    ∀ x ∈ others, x = 0 := by
  have h_others_sum : others.sum = 0 := by linear_combination h_total - h_sel
  exact sum_bool_eq_zero_all_zero others h_len_lt h_bool h_others_sum

/-- Finset version of `sum_bool_eq_zero_all_zero`. Uses `Finset.sum_map_toList`
    to reduce to the List version. -/
theorem finset_sum_bool_eq_zero_all_zero {α : Type*} {p : ℕ} [Fact p.Prime]
    (s : Finset α) (f : α → ZMod p)
    (hlen : s.card < p)
    (hb : ∀ x ∈ s, f x = 0 ∨ f x = 1)
    (hsum : ∑ x ∈ s, f x = 0) :
    ∀ x ∈ s, f x = 0 := by
  intro x hx
  have hL_sum : (s.toList.map f).sum = 0 := by
    rw [Finset.sum_map_toList]; exact hsum
  have hL_len : (s.toList.map f).length < p := by
    simp [Finset.length_toList]; exact hlen
  have hL_bool : ∀ y ∈ s.toList.map f, y = 0 ∨ y = 1 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact hb z (Finset.mem_toList.mp hz)
  exact sum_bool_eq_zero_all_zero _ hL_len hL_bool hL_sum
    (f x) (List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx, rfl⟩)

/-- Generic one-hot uniqueness over `Fin n`: given `n` Boolean field elements
    (`n < p`) summing to 1, if position `i` has value 1, every other position
    has value 0. This is the single theorem that replaces the 22 per-instruction
    `onehot_flags_*` helpers. -/
theorem onehot_unique_fin {n : ℕ} {p : ℕ} [Fact p.Prime] (hp_big : n < p)
    (v : Fin n → ZMod p)
    (h_bool : ∀ i, v i = 0 ∨ v i = 1)
    (h_sum : ∑ i, v i = 1)
    (i : Fin n) (h_i : v i = 1) :
    ∀ j : Fin n, j ≠ i → v j = 0 := by
  -- Split the sum at `i`: ∑ = v i + ∑ (over erase i)
  have h_sum_split : (Finset.univ : Finset (Fin n)).sum v =
      v i + ((Finset.univ : Finset (Fin n)).erase i).sum v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  -- Derive that the "erase" sum is 0 via linear combination
  have h_erase_sum : ((Finset.univ : Finset (Fin n)).erase i).sum v = 0 := by
    linear_combination h_sum - h_sum_split - h_i
  -- The erased Finset has n-1 elements, all Boolean, summing to 0
  have h_erase_card : ((Finset.univ : Finset (Fin n)).erase i).card < p := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have h_erase_bool : ∀ x ∈ (Finset.univ : Finset (Fin n)).erase i, v x = 0 ∨ v x = 1 :=
    fun x _ => h_bool x
  have h_all_zero := finset_sum_bool_eq_zero_all_zero _ v h_erase_card h_erase_bool h_erase_sum
  intro j hji
  exact h_all_zero j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

section OneHotFlagsDetermined
set_option linter.unusedSectionVars false
variable {p : ℕ} [Fact p.Prime]
variable {is_add is_adc is_sub is_sbc is_and is_xor is_or is_cp
          is_inc is_dec is_rlc is_rrc is_rl is_rr is_sla is_sra is_srl is_swap
          is_daa is_cpl is_ccf is_scf : ZMod p}
variable (hp_big : 22 < p)
variable (ha : is_add = 0 ∨ is_add = 1) (hb : is_adc = 0 ∨ is_adc = 1)
variable (hc : is_sub = 0 ∨ is_sub = 1) (hd : is_sbc = 0 ∨ is_sbc = 1)
variable (he : is_and = 0 ∨ is_and = 1) (hf : is_xor = 0 ∨ is_xor = 1)
variable (hg : is_or = 0 ∨ is_or = 1) (hh : is_cp = 0 ∨ is_cp = 1)
variable (hi : is_inc = 0 ∨ is_inc = 1) (hj : is_dec = 0 ∨ is_dec = 1)
variable (hk : is_rlc = 0 ∨ is_rlc = 1) (hl : is_rrc = 0 ∨ is_rrc = 1)
variable (hm : is_rl = 0 ∨ is_rl = 1) (hn : is_rr = 0 ∨ is_rr = 1)
variable (ho : is_sla = 0 ∨ is_sla = 1) (hq : is_sra = 0 ∨ is_sra = 1)
variable (hr : is_srl = 0 ∨ is_srl = 1) (hs : is_swap = 0 ∨ is_swap = 1)
variable (ht : is_daa = 0 ∨ is_daa = 1) (hu : is_cpl = 0 ∨ is_cpl = 1)
variable (hv : is_ccf = 0 ∨ is_ccf = 1) (hw : is_scf = 0 ∨ is_scf = 1)
variable (h_sum : is_add + is_adc + is_sub + is_sbc + is_and + is_xor + is_or + is_cp +
                  is_inc + is_dec + is_rlc + is_rrc + is_rl + is_rr + is_sla + is_sra +
                  is_srl + is_swap + is_daa + is_cpl + is_ccf + is_scf = 1)

include hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum

/-- `is_add = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_add (h_add : is_add = 1) :
    is_add = 1 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 0
    (by simp [v]; exact h_add)
  exact ⟨h_add, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_adc = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_adc (h_adc : is_adc = 1) :
    is_add = 0 ∧ is_adc = 1 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 1
    (by simp [v]; exact h_adc)
  exact ⟨h 0 (by decide), h_adc, h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_sub = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_sub (h_sub : is_sub = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 1 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 2
    (by simp [v]; exact h_sub)
  exact ⟨h 0 (by decide), h 1 (by decide), h_sub, h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_sbc = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_sbc (h_sbc : is_sbc = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 1 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 3
    (by simp [v]; exact h_sbc)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h_sbc, h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_and = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_and (h_and : is_and = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 1 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 4
    (by simp [v]; exact h_and)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h_and,
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_xor = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_xor (h_xor : is_xor = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 1 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 5
    (by simp [v]; exact h_xor)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h_xor, h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_or = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_or (h_or : is_or = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 1 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 6
    (by simp [v]; exact h_or)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h_or, h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_cp = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_cp (h_cp : is_cp = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 1 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 7
    (by simp [v]; exact h_cp)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h_cp, h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_inc = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_inc (h_inc : is_inc = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 1 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 8
    (by simp [v]; exact h_inc)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h_inc, h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_dec = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_dec (h_dec : is_dec = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 1 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 9
    (by simp [v]; exact h_dec)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h_dec,
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_rlc = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_rlc (h_rlc : is_rlc = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 1 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 10
    (by simp [v]; exact h_rlc)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h_rlc, h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_rrc = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_rrc (h_rrc : is_rrc = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 1 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 11
    (by simp [v]; exact h_rrc)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h_rrc, h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_rl = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_rl (h_rl : is_rl = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 1 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 12
    (by simp [v]; exact h_rl)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h_rl, h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_rr = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_rr (h_rr : is_rr = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 1 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 13
    (by simp [v]; exact h_rr)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h_rr, h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_sla = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_sla (h_sla : is_sla = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 1 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 14
    (by simp [v]; exact h_sla)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h_sla,
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_sra = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_sra (h_sra : is_sra = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 1 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 15
    (by simp [v]; exact h_sra)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h_sra, h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_srl = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_srl (h_srl : is_srl = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 1 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 16
    (by simp [v]; exact h_srl)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h_srl, h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_swap = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_swap (h_swap : is_swap = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 1 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 17
    (by simp [v]; exact h_swap)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h_swap, h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_daa = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_daa (h_daa : is_daa = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 1 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 18
    (by simp [v]; exact h_daa)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h_daa, h 19 (by decide),
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_cpl = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_cpl (h_cpl : is_cpl = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 1 ∧
    is_ccf = 0 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 19
    (by simp [v]; exact h_cpl)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h_cpl,
         h 20 (by decide), h 21 (by decide)⟩

/-- `is_ccf = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_ccf (h_ccf : is_ccf = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 1 ∧ is_scf = 0 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 20
    (by simp [v]; exact h_ccf)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h_ccf, h 21 (by decide)⟩

/-- `is_scf = 1` uniquely determines all 22 one-hot flags. -/
theorem onehot_flags_scf (h_scf : is_scf = 1) :
    is_add = 0 ∧ is_adc = 0 ∧ is_sub = 0 ∧ is_sbc = 0 ∧ is_and = 0 ∧
    is_xor = 0 ∧ is_or = 0 ∧ is_cp = 0 ∧ is_inc = 0 ∧ is_dec = 0 ∧
    is_rlc = 0 ∧ is_rrc = 0 ∧ is_rl = 0 ∧ is_rr = 0 ∧ is_sla = 0 ∧
    is_sra = 0 ∧ is_srl = 0 ∧ is_swap = 0 ∧ is_daa = 0 ∧ is_cpl = 0 ∧
    is_ccf = 0 ∧ is_scf = 1 := by
  let v : Fin 22 → ZMod p :=
    ![is_add, is_adc, is_sub, is_sbc, is_and, is_xor, is_or, is_cp,
      is_inc, is_dec, is_rlc, is_rrc, is_rl, is_rr, is_sla, is_sra,
      is_srl, is_swap, is_daa, is_cpl, is_ccf, is_scf]
  have hb : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i; fin_cases i <;> simp [v] <;> assumption
  have hs : ∑ i, v i = 1 := by
    simp [v, Fin.sum_univ_succ]; linear_combination h_sum
  have h := onehot_unique_fin (by omega : (22 : ℕ) < p) v hb hs 21
    (by simp [v]; exact h_scf)
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
         h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
         h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
         h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
         h 20 (by decide), h_scf⟩

end OneHotFlagsDetermined

/-! ### Per-instruction N-flag derivations

Each of the 22 instructions determines `flag_n = 0` or `flag_n = 1` via
the master_constraints flag_n equation `flag_n = is_sub + is_sbc +
is_cp + is_dec + is_cpl`. N = 1 for {sub, sbc, cp, dec, cpl}; N = 0
otherwise. Proofs use the `onehot_flags_*` helpers. -/

section PerInstructionFlagN
variable {p : ℕ} [Fact p.Prime]
variable {is_add is_adc is_sub is_sbc is_and is_xor is_or is_cp
          is_inc is_dec is_rlc is_rrc is_rl is_rr is_sla is_sra is_srl is_swap
          is_daa is_cpl is_ccf is_scf flag_n : ZMod p}
variable (hp_big : 22 < p)
variable (ha : is_add = 0 ∨ is_add = 1) (hb : is_adc = 0 ∨ is_adc = 1)
variable (hc : is_sub = 0 ∨ is_sub = 1) (hd : is_sbc = 0 ∨ is_sbc = 1)
variable (he : is_and = 0 ∨ is_and = 1) (hf : is_xor = 0 ∨ is_xor = 1)
variable (hg : is_or = 0 ∨ is_or = 1) (hh : is_cp = 0 ∨ is_cp = 1)
variable (hi : is_inc = 0 ∨ is_inc = 1) (hj : is_dec = 0 ∨ is_dec = 1)
variable (hk : is_rlc = 0 ∨ is_rlc = 1) (hl : is_rrc = 0 ∨ is_rrc = 1)
variable (hm : is_rl = 0 ∨ is_rl = 1) (hn : is_rr = 0 ∨ is_rr = 1)
variable (ho : is_sla = 0 ∨ is_sla = 1) (hq : is_sra = 0 ∨ is_sra = 1)
variable (hr : is_srl = 0 ∨ is_srl = 1) (hs : is_swap = 0 ∨ is_swap = 1)
variable (ht : is_daa = 0 ∨ is_daa = 1) (hu : is_cpl = 0 ∨ is_cpl = 1)
variable (hv : is_ccf = 0 ∨ is_ccf = 1) (hw : is_scf = 0 ∨ is_scf = 1)
variable (h_sum : is_add + is_adc + is_sub + is_sbc + is_and + is_xor + is_or + is_cp +
                  is_inc + is_dec + is_rlc + is_rrc + is_rl + is_rr + is_sla + is_sra +
                  is_srl + is_swap + is_daa + is_cpl + is_ccf + is_scf = 1)
variable (h_n_eq : flag_n = is_sub + is_sbc + is_cp + is_dec + is_cpl)

include hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_n_eq

theorem add_N_derived (h_add : is_add = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_add hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_add
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem adc_N_derived (h_adc : is_adc = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_adc hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_adc
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem sub_N_derived (h_sub : is_sub = 1) : flag_n = 1 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_sub hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_sub
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem sbc_N_derived (h_sbc : is_sbc = 1) : flag_n = 1 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_sbc hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_sbc
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem and_N_derived (h_and : is_and = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_and hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_and
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem xor_N_derived (h_xor : is_xor = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_xor hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_xor
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem or_N_derived (h_or : is_or = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_or hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_or
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem cp_N_derived (h_cp : is_cp = 1) : flag_n = 1 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_cp hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_cp
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem inc_N_derived (h_inc : is_inc = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_inc hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_inc
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem dec_N_derived (h_dec : is_dec = 1) : flag_n = 1 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_dec hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_dec
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem rlc_N_derived (h_rlc : is_rlc = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_rlc hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rlc
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem rrc_N_derived (h_rrc : is_rrc = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_rrc hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rrc
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem rl_N_derived (h_rl : is_rl = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_rl hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rl
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem rr_N_derived (h_rr : is_rr = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_rr hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rr
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem sla_N_derived (h_sla : is_sla = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_sla hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_sla
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem sra_N_derived (h_sra : is_sra = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_sra hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_sra
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem srl_N_derived (h_srl : is_srl = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_srl hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_srl
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem swap_N_derived (h_swap : is_swap = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_swap hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_swap
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem daa_N_derived (h_daa : is_daa = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_daa hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_daa
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem cpl_N_derived (h_cpl : is_cpl = 1) : flag_n = 1 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_cpl hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_cpl
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem ccf_N_derived (h_ccf : is_ccf = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_ccf hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_ccf
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

theorem scf_N_derived (h_scf : is_scf = 1) : flag_n = 0 := by
  obtain ⟨_, _, n1, n2, _, _, _, n3, _, n4, _, _, _, _, _, _, _, _, _, n5, _, _⟩ :=
    onehot_flags_scf hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_scf
  rw [h_n_eq, n1, n2, n3, n4, n5]; ring

end PerInstructionFlagN

/-! ### Per-instruction H-flag MUX derivations

For 15 of the 22 instructions, the H flag is forced to a constant by
master_constraints' H-MUX: `(is_and + is_cpl) * (flag_h - 1) = 0`
(H = 1 for AND, CPL) and `(is_xor + is_or + ... + is_daa) * flag_h = 0`
(H = 0 for the rotates, shifts, SWAP, CCF, SCF, DAA).

ADD/ADC/SUB/SBC/CP/INC/DEC compute H via the half_carry sub-gadget, not
via master_constraints — those H derivations require additional
hypotheses and are not closed here. -/

section PerInstructionFlagH
variable {p : ℕ} [Fact p.Prime]
variable {is_add is_adc is_sub is_sbc is_and is_xor is_or is_cp
          is_inc is_dec is_rlc is_rrc is_rl is_rr is_sla is_sra is_srl is_swap
          is_daa is_cpl is_ccf is_scf flag_h : ZMod p}
variable (hp_big : 22 < p)
variable (ha : is_add = 0 ∨ is_add = 1) (hb : is_adc = 0 ∨ is_adc = 1)
variable (hc : is_sub = 0 ∨ is_sub = 1) (hd : is_sbc = 0 ∨ is_sbc = 1)
variable (he : is_and = 0 ∨ is_and = 1) (hf : is_xor = 0 ∨ is_xor = 1)
variable (hg : is_or = 0 ∨ is_or = 1) (hh : is_cp = 0 ∨ is_cp = 1)
variable (hi : is_inc = 0 ∨ is_inc = 1) (hj : is_dec = 0 ∨ is_dec = 1)
variable (hk : is_rlc = 0 ∨ is_rlc = 1) (hl : is_rrc = 0 ∨ is_rrc = 1)
variable (hm : is_rl = 0 ∨ is_rl = 1) (hn : is_rr = 0 ∨ is_rr = 1)
variable (ho : is_sla = 0 ∨ is_sla = 1) (hq : is_sra = 0 ∨ is_sra = 1)
variable (hr : is_srl = 0 ∨ is_srl = 1) (hs : is_swap = 0 ∨ is_swap = 1)
variable (ht : is_daa = 0 ∨ is_daa = 1) (hu : is_cpl = 0 ∨ is_cpl = 1)
variable (hv : is_ccf = 0 ∨ is_ccf = 1) (hw : is_scf = 0 ∨ is_scf = 1)
variable (h_sum : is_add + is_adc + is_sub + is_sbc + is_and + is_xor + is_or + is_cp +
                  is_inc + is_dec + is_rlc + is_rrc + is_rl + is_rr + is_sla + is_sra +
                  is_srl + is_swap + is_daa + is_cpl + is_ccf + is_scf = 1)
variable (h_h_one : (is_and + is_cpl) * (flag_h - 1) = 0)
variable (h_h_zero : (is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl +
                       is_rr + is_sla + is_sra + is_srl + is_ccf + is_scf +
                       is_daa) * flag_h = 0)

include hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_h_one h_h_zero

set_option linter.unusedSectionVars false

-- H = 1 derivations (via h_h_one MUX)

theorem and_H_derived (h_and : is_and = 1) : flag_h = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, z_cpl, _, _⟩ :=
    onehot_flags_and hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_and
  have h_sel_ne : is_and + is_cpl ≠ (0 : ZMod p) := by
    rw [h_and, z_cpl]; simp
  exact SM83.ConstraintProofs.mux_forces_value h_h_one h_sel_ne

theorem cpl_H_derived (h_cpl : is_cpl = 1) : flag_h = 1 := by
  obtain ⟨_, _, _, _, z_and, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    onehot_flags_cpl hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_cpl
  have h_sel_ne : is_and + is_cpl ≠ (0 : ZMod p) := by
    rw [z_and, h_cpl]; simp
  exact SM83.ConstraintProofs.mux_forces_value h_h_one h_sel_ne

-- H = 0 derivations (via h_h_zero MUX) for xor/or/swap/rlc/rrc/rl/rr/sla/sra/srl/ccf/scf/daa

theorem xor_H_derived (h_xor : is_xor = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, _, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_xor hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_xor
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [h_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem or_H_derived (h_or : is_or = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, _, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_or hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_or
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, h_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem swap_H_derived (h_swap : is_swap = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, _, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_swap hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_swap
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, h_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem rlc_H_derived (h_rlc : is_rlc = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, _, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_rlc hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rlc
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, h_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem rrc_H_derived (h_rrc : is_rrc = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, _, z_rl, z_rr, z_sla, z_sra, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_rrc hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rrc
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, h_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem rl_H_derived (h_rl : is_rl = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, _, z_rr, z_sla, z_sra, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_rl hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rl
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, h_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem rr_H_derived (h_rr : is_rr = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, _, z_sla, z_sra, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_rr hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_rr
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, h_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem sla_H_derived (h_sla : is_sla = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, _, z_sra, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_sla hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_sla
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, h_sla, z_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem sra_H_derived (h_sra : is_sra = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, _, z_srl, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_sra hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_sra
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, h_sra, z_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem srl_H_derived (h_srl : is_srl = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, _, z_swap, z_daa, _, z_ccf, z_scf⟩ :=
    onehot_flags_srl hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_srl
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, h_srl, z_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem ccf_H_derived (h_ccf : is_ccf = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_swap, z_daa, _, _, z_scf⟩ :=
    onehot_flags_ccf hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_ccf
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, h_ccf, z_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem scf_H_derived (h_scf : is_scf = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_swap, z_daa, _, z_ccf, _⟩ :=
    onehot_flags_scf hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_scf
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, h_scf, z_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

theorem daa_H_derived (h_daa : is_daa = 1) : flag_h = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_swap, _, _, z_ccf, z_scf⟩ :=
    onehot_flags_daa hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_daa
  have h_sel_ne :
      is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl + is_rr +
        is_sla + is_sra + is_srl + is_ccf + is_scf + is_daa ≠ (0 : ZMod p) := by
    rw [z_xor, z_or, z_swap, z_rlc, z_rrc, z_rl, z_rr, z_sla, z_sra, z_srl, z_ccf, z_scf, h_daa]
    simp
  exact SM83.ConstraintProofs.mux_forces_zero h_h_zero h_sel_ne

end PerInstructionFlagH

/-! ### Per-instruction C-flag MUX derivations

Only 4 of the 22 instructions have their C flag determined by the
master_constraints C-MUX: AND/XOR/OR (C = 0 via c_must_be_zero) and
SCF (C = 1 via c_must_be_one).

For ADD/ADC/SUB/SBC/CP/INC/DEC and the rotates/shifts, C is computed by
sub-gadgets; DAA and CCF have instruction-specific logic. Those are not
closed here. -/

section PerInstructionFlagC
variable {p : ℕ} [Fact p.Prime]
variable {is_add is_adc is_sub is_sbc is_and is_xor is_or is_cp
          is_inc is_dec is_rlc is_rrc is_rl is_rr is_sla is_sra is_srl is_swap
          is_daa is_cpl is_ccf is_scf flag_c : ZMod p}
variable (hp_big : 22 < p)
variable (ha : is_add = 0 ∨ is_add = 1) (hb : is_adc = 0 ∨ is_adc = 1)
variable (hc : is_sub = 0 ∨ is_sub = 1) (hd : is_sbc = 0 ∨ is_sbc = 1)
variable (he : is_and = 0 ∨ is_and = 1) (hf : is_xor = 0 ∨ is_xor = 1)
variable (hg : is_or = 0 ∨ is_or = 1) (hh : is_cp = 0 ∨ is_cp = 1)
variable (hi : is_inc = 0 ∨ is_inc = 1) (hj : is_dec = 0 ∨ is_dec = 1)
variable (hk : is_rlc = 0 ∨ is_rlc = 1) (hl : is_rrc = 0 ∨ is_rrc = 1)
variable (hm : is_rl = 0 ∨ is_rl = 1) (hn : is_rr = 0 ∨ is_rr = 1)
variable (ho : is_sla = 0 ∨ is_sla = 1) (hq : is_sra = 0 ∨ is_sra = 1)
variable (hr : is_srl = 0 ∨ is_srl = 1) (hs : is_swap = 0 ∨ is_swap = 1)
variable (ht : is_daa = 0 ∨ is_daa = 1) (hu : is_cpl = 0 ∨ is_cpl = 1)
variable (hv : is_ccf = 0 ∨ is_ccf = 1) (hw : is_scf = 0 ∨ is_scf = 1)
variable (h_sum : is_add + is_adc + is_sub + is_sbc + is_and + is_xor + is_or + is_cp +
                  is_inc + is_dec + is_rlc + is_rrc + is_rl + is_rr + is_sla + is_sra +
                  is_srl + is_swap + is_daa + is_cpl + is_ccf + is_scf = 1)
variable (h_c_zero : (is_and + is_xor + is_or) * flag_c = 0)
variable (h_c_one : is_scf * (flag_c - 1) = 0)

include hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_c_zero h_c_one

set_option linter.unusedSectionVars false

-- C = 0 derivations (via h_c_zero MUX) for AND, XOR, OR

theorem and_C_derived (h_and : is_and = 1) : flag_c = 0 := by
  obtain ⟨_, _, _, _, _, z_xor, z_or, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    onehot_flags_and hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_and
  have h_sel_ne : is_and + is_xor + is_or ≠ (0 : ZMod p) := by
    rw [h_and, z_xor, z_or]; simp
  exact SM83.ConstraintProofs.mux_forces_zero h_c_zero h_sel_ne

theorem xor_C_derived (h_xor : is_xor = 1) : flag_c = 0 := by
  obtain ⟨_, _, _, _, z_and, _, z_or, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    onehot_flags_xor hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_xor
  have h_sel_ne : is_and + is_xor + is_or ≠ (0 : ZMod p) := by
    rw [z_and, h_xor, z_or]; simp
  exact SM83.ConstraintProofs.mux_forces_zero h_c_zero h_sel_ne

theorem or_C_derived (h_or : is_or = 1) : flag_c = 0 := by
  obtain ⟨_, _, _, _, z_and, z_xor, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    onehot_flags_or hp_big ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hq hr hs ht hu hv hw h_sum h_or
  have h_sel_ne : is_and + is_xor + is_or ≠ (0 : ZMod p) := by
    rw [z_and, z_xor, h_or]; simp
  exact SM83.ConstraintProofs.mux_forces_zero h_c_zero h_sel_ne

-- C = 1 derivation (via h_c_one MUX) for SCF

theorem scf_C_derived (h_scf : is_scf = 1) : flag_c = 1 := by
  have h_sel_ne : is_scf ≠ (0 : ZMod p) := by rw [h_scf]; exact one_ne_zero
  exact SM83.ConstraintProofs.mux_forces_value h_c_one h_sel_ne

end PerInstructionFlagC

/-! ### Gap K: Unified `master_constraints` bridge

Provides a single theorem — `master_constraints_bridge` — that extracts
every primitive equation emitted by `master_constraints` from its
success. Per-instruction proofs can invoke this one bridge and read off
named fields of `MasterConstraintFacts`, rather than composing each
sub-bridge manually.

Strategy: use `runZKBuilder_seq_isSome_split` (already defined above) to
peel one `>>=` layer at a time, dispatching each peeled `isSome` to the
relevant sub-bridge. The inline flag-MUX primitives use the sound
primitives from `SM83.SemanticBridge`.
-/

-- Compositional bridge for `one_hot_constraints`: extracts all 22 opcode
-- Booleans plus the sum-to-1 constraint.
set_option maxHeartbeats 1600000 in
theorem one_hot_constraints_bridge (step : SM83StepInputs g) (st : ZKState g)
    (h : (runZKBuilder (one_hot_constraints step) st).isSome) :
    step.is_add.eval * (step.is_add.eval - 1) = 0 ∧
    step.is_adc.eval * (step.is_adc.eval - 1) = 0 ∧
    step.is_sub.eval * (step.is_sub.eval - 1) = 0 ∧
    step.is_sbc.eval * (step.is_sbc.eval - 1) = 0 ∧
    step.is_and.eval * (step.is_and.eval - 1) = 0 ∧
    step.is_xor.eval * (step.is_xor.eval - 1) = 0 ∧
    step.is_or.eval * (step.is_or.eval - 1) = 0 ∧
    step.is_cp.eval * (step.is_cp.eval - 1) = 0 ∧
    step.is_inc.eval * (step.is_inc.eval - 1) = 0 ∧
    step.is_dec.eval * (step.is_dec.eval - 1) = 0 ∧
    step.is_rlc.eval * (step.is_rlc.eval - 1) = 0 ∧
    step.is_rrc.eval * (step.is_rrc.eval - 1) = 0 ∧
    step.is_rl.eval * (step.is_rl.eval - 1) = 0 ∧
    step.is_rr.eval * (step.is_rr.eval - 1) = 0 ∧
    step.is_sla.eval * (step.is_sla.eval - 1) = 0 ∧
    step.is_sra.eval * (step.is_sra.eval - 1) = 0 ∧
    step.is_srl.eval * (step.is_srl.eval - 1) = 0 ∧
    step.is_swap.eval * (step.is_swap.eval - 1) = 0 ∧
    step.is_daa.eval * (step.is_daa.eval - 1) = 0 ∧
    step.is_cpl.eval * (step.is_cpl.eval - 1) = 0 ∧
    step.is_ccf.eval * (step.is_ccf.eval - 1) = 0 ∧
    step.is_scf.eval * (step.is_scf.eval - 1) = 0 ∧
    (step.is_add + step.is_adc + step.is_sub + step.is_sbc +
      step.is_and + step.is_xor + step.is_or + step.is_cp +
      step.is_inc + step.is_dec + step.is_rlc + step.is_rrc +
      step.is_rl + step.is_rr + step.is_sla + step.is_sra +
      step.is_srl + step.is_swap + step.is_daa + step.is_cpl +
      step.is_ccf + step.is_scf).eval = 1 := by
  unfold one_hot_constraints at h
  obtain ⟨h_c1, st1, h1⟩ := runZKBuilder_seq_isSome_split h
  obtain ⟨h_c2, st2, h2⟩ := runZKBuilder_seq_isSome_split h1
  obtain ⟨h_c3, st3, h3⟩ := runZKBuilder_seq_isSome_split h2
  obtain ⟨h_c4, st4, h_sum⟩ := runZKBuilder_seq_isSome_split h3
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := one_hot_bool_chunk_1_bridge step st h_c1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := one_hot_bool_chunk_2_bridge step st1 h_c2
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := one_hot_bool_chunk_3_bridge step st2 h_c3
  obtain ⟨d1, d2, d3, d4⟩ := one_hot_bool_chunk_4_bridge step st3 h_c4
  have e := one_hot_sum_constraint_bridge step st4 h_sum
  exact ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6,
         c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, e⟩

-- Compositional bridge for `range_check_constraints`: extracts all 24
-- bit Boolean constraints plus the 3 decomposition equalities.
set_option maxHeartbeats 1600000 in
theorem range_check_constraints_bridge (step : SM83StepInputs g) (st : ZKState g)
    (h : (runZKBuilder (range_check_constraints step) st).isSome) :
    (step.a_bit_0.eval * (step.a_bit_0.eval - 1) = 0 ∧
     step.a_bit_1.eval * (step.a_bit_1.eval - 1) = 0 ∧
     step.a_bit_2.eval * (step.a_bit_2.eval - 1) = 0 ∧
     step.a_bit_3.eval * (step.a_bit_3.eval - 1) = 0 ∧
     step.a_bit_4.eval * (step.a_bit_4.eval - 1) = 0 ∧
     step.a_bit_5.eval * (step.a_bit_5.eval - 1) = 0 ∧
     step.a_bit_6.eval * (step.a_bit_6.eval - 1) = 0 ∧
     step.a_bit_7.eval * (step.a_bit_7.eval - 1) = 0) ∧
    (step.alu_operand_a.eval =
      step.a_bit_0.eval + step.a_bit_1.eval * 2 + step.a_bit_2.eval * 4 +
      step.a_bit_3.eval * 8 + step.a_bit_4.eval * 16 + step.a_bit_5.eval * 32 +
      step.a_bit_6.eval * 64 + step.a_bit_7.eval * 128) ∧
    (step.b_bit_0.eval * (step.b_bit_0.eval - 1) = 0 ∧
     step.b_bit_1.eval * (step.b_bit_1.eval - 1) = 0 ∧
     step.b_bit_2.eval * (step.b_bit_2.eval - 1) = 0 ∧
     step.b_bit_3.eval * (step.b_bit_3.eval - 1) = 0 ∧
     step.b_bit_4.eval * (step.b_bit_4.eval - 1) = 0 ∧
     step.b_bit_5.eval * (step.b_bit_5.eval - 1) = 0 ∧
     step.b_bit_6.eval * (step.b_bit_6.eval - 1) = 0 ∧
     step.b_bit_7.eval * (step.b_bit_7.eval - 1) = 0) ∧
    (step.alu_operand_b.eval =
      step.b_bit_0.eval + step.b_bit_1.eval * 2 + step.b_bit_2.eval * 4 +
      step.b_bit_3.eval * 8 + step.b_bit_4.eval * 16 + step.b_bit_5.eval * 32 +
      step.b_bit_6.eval * 64 + step.b_bit_7.eval * 128) ∧
    (step.r_bit_0.eval * (step.r_bit_0.eval - 1) = 0 ∧
     step.r_bit_1.eval * (step.r_bit_1.eval - 1) = 0 ∧
     step.r_bit_2.eval * (step.r_bit_2.eval - 1) = 0 ∧
     step.r_bit_3.eval * (step.r_bit_3.eval - 1) = 0 ∧
     step.r_bit_4.eval * (step.r_bit_4.eval - 1) = 0 ∧
     step.r_bit_5.eval * (step.r_bit_5.eval - 1) = 0 ∧
     step.r_bit_6.eval * (step.r_bit_6.eval - 1) = 0 ∧
     step.r_bit_7.eval * (step.r_bit_7.eval - 1) = 0) ∧
    (step.alu_result.eval =
      step.r_bit_0.eval + step.r_bit_1.eval * 2 + step.r_bit_2.eval * 4 +
      step.r_bit_3.eval * 8 + step.r_bit_4.eval * 16 + step.r_bit_5.eval * 32 +
      step.r_bit_6.eval * 64 + step.r_bit_7.eval * 128) := by
  unfold range_check_constraints at h
  obtain ⟨h_ba, st1, h1⟩ := runZKBuilder_seq_isSome_split h
  obtain ⟨h_sa, st2, h2⟩ := runZKBuilder_seq_isSome_split h1
  obtain ⟨h_bb, st3, h3⟩ := runZKBuilder_seq_isSome_split h2
  obtain ⟨h_sb, st4, h4⟩ := runZKBuilder_seq_isSome_split h3
  obtain ⟨h_br, st5, h_sr⟩ := runZKBuilder_seq_isSome_split h4
  have ba := range_bool_a_bridge step st h_ba
  have sa := range_sum_a_bridge step st1 h_sa
  have bb := range_bool_b_bridge step st2 h_bb
  have sb := range_sum_b_bridge step st3 h_sb
  have br := range_bool_r_bridge step st4 h_br
  have sr := range_sum_r_bridge step st5 h_sr
  exact ⟨ba, sa, bb, sb, br, sr⟩

-- Compositional bridge for `table_lookup_constraints`: extracts all 24
-- bit-level lookup constraints for AND, XOR, OR.
set_option maxHeartbeats 1600000 in
theorem table_lookup_constraints_bridge (step : SM83StepInputs g) (st : ZKState g)
    (h : (runZKBuilder (table_lookup_constraints step) st).isSome) :
    (step.is_and.eval * (step.r_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval) = 0) ∧
    (step.is_xor.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval * 2)) = 0) ∧
    (step.is_or.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval)) = 0) := by
  unfold table_lookup_constraints at h
  obtain ⟨h_and, st1, h1⟩ := runZKBuilder_seq_isSome_split h
  obtain ⟨h_xor, st2, h_or⟩ := runZKBuilder_seq_isSome_split h1
  have a := table_constraint_and_bridge step st h_and
  have x := table_constraint_xor_bridge step st1 h_xor
  have o := table_constraint_or_bridge step st2 h_or
  exact ⟨a, x, o⟩

-- Compositional bridge for `register_coupling_constraints`: extracts the
-- 7 source-selector Boolean facts, the sum-to-1 fact, and the two
-- coupling equations linking `alu_operand_a` / `alu_operand_b` to the
-- register file columns.
set_option maxHeartbeats 1600000 in
theorem register_coupling_constraints_bridge (step : SM83StepInputs g) (st : ZKState g)
    (h : (runZKBuilder (register_coupling_constraints step) st).isSome) :
    step.is_src_a.eval * (step.is_src_a.eval - 1) = 0 ∧
    step.is_src_b.eval * (step.is_src_b.eval - 1) = 0 ∧
    step.is_src_c.eval * (step.is_src_c.eval - 1) = 0 ∧
    step.is_src_d.eval * (step.is_src_d.eval - 1) = 0 ∧
    step.is_src_e.eval * (step.is_src_e.eval - 1) = 0 ∧
    step.is_src_h.eval * (step.is_src_h.eval - 1) = 0 ∧
    step.is_src_l.eval * (step.is_src_l.eval - 1) = 0 ∧
    (step.is_src_a + step.is_src_b + step.is_src_c + step.is_src_d +
      step.is_src_e + step.is_src_h + step.is_src_l).eval = 1 ∧
    step.alu_operand_a.eval = step.reg_a.eval ∧
    step.alu_operand_b.eval =
      (step.is_src_a * step.reg_a + step.is_src_b * step.reg_b +
        step.is_src_c * step.reg_c + step.is_src_d * step.reg_d +
        step.is_src_e * step.reg_e + step.is_src_h * step.reg_h +
        step.is_src_l * step.reg_l).eval := by
  unfold register_coupling_constraints at h
  obtain ⟨h_a, st1, h1⟩ := runZKBuilder_seq_isSome_split h
  obtain ⟨h_b, st2, h2⟩ := runZKBuilder_seq_isSome_split h1
  obtain ⟨h_c, st3, h3⟩ := runZKBuilder_seq_isSome_split h2
  obtain ⟨h_d, st4, h4⟩ := runZKBuilder_seq_isSome_split h3
  obtain ⟨h_e, st5, h5⟩ := runZKBuilder_seq_isSome_split h4
  obtain ⟨h_hh, st6, h6⟩ := runZKBuilder_seq_isSome_split h5
  obtain ⟨h_ll, st7, h7⟩ := runZKBuilder_seq_isSome_split h6
  obtain ⟨h_sum, st8, h8⟩ := runZKBuilder_seq_isSome_split h7
  obtain ⟨h_acoup, st9, h_bcoup⟩ := runZKBuilder_seq_isSome_split h8
  have e_a := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st h_a
  have e_b := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st1 h_b
  have e_c := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st2 h_c
  have e_d := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st3 h_d
  have e_e := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st4 h_e
  have e_hh := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st5 h_hh
  have e_ll := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st6 h_ll
  have e_sum := SM83.SemanticBridge.constrainEq_sound _ _ st7 h_sum
  have e_acoup := SM83.SemanticBridge.constrainEq_sound _ _ st8 h_acoup
  have e_bcoup := SM83.SemanticBridge.constrainEq_sound _ _ st9 h_bcoup
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ZKExpr.eval] using e_a
  · simpa only [ZKExpr.eval] using e_b
  · simpa only [ZKExpr.eval] using e_c
  · simpa only [ZKExpr.eval] using e_d
  · simpa only [ZKExpr.eval] using e_e
  · simpa only [ZKExpr.eval] using e_hh
  · simpa only [ZKExpr.eval] using e_ll
  · simpa only [ZKExpr.eval] using e_sum
  · simpa only [ZKExpr.eval] using e_acoup
  · simpa only [ZKExpr.eval] using e_bcoup

/-- Structured output of `master_constraints_bridge`: every primitive
    equation emitted by the `master_constraints` generator, grouped by
    subsystem. Per-instruction proofs can name the field they need
    instead of destructuring a deep conjunction. -/
structure MasterConstraintFacts (step : SM83StepInputs g) : Prop where
  /-- 22 opcode Booleans + sum-to-1 constraint (Gap I). -/
  one_hot :
    step.is_add.eval * (step.is_add.eval - 1) = 0 ∧
    step.is_adc.eval * (step.is_adc.eval - 1) = 0 ∧
    step.is_sub.eval * (step.is_sub.eval - 1) = 0 ∧
    step.is_sbc.eval * (step.is_sbc.eval - 1) = 0 ∧
    step.is_and.eval * (step.is_and.eval - 1) = 0 ∧
    step.is_xor.eval * (step.is_xor.eval - 1) = 0 ∧
    step.is_or.eval * (step.is_or.eval - 1) = 0 ∧
    step.is_cp.eval * (step.is_cp.eval - 1) = 0 ∧
    step.is_inc.eval * (step.is_inc.eval - 1) = 0 ∧
    step.is_dec.eval * (step.is_dec.eval - 1) = 0 ∧
    step.is_rlc.eval * (step.is_rlc.eval - 1) = 0 ∧
    step.is_rrc.eval * (step.is_rrc.eval - 1) = 0 ∧
    step.is_rl.eval * (step.is_rl.eval - 1) = 0 ∧
    step.is_rr.eval * (step.is_rr.eval - 1) = 0 ∧
    step.is_sla.eval * (step.is_sla.eval - 1) = 0 ∧
    step.is_sra.eval * (step.is_sra.eval - 1) = 0 ∧
    step.is_srl.eval * (step.is_srl.eval - 1) = 0 ∧
    step.is_swap.eval * (step.is_swap.eval - 1) = 0 ∧
    step.is_daa.eval * (step.is_daa.eval - 1) = 0 ∧
    step.is_cpl.eval * (step.is_cpl.eval - 1) = 0 ∧
    step.is_ccf.eval * (step.is_ccf.eval - 1) = 0 ∧
    step.is_scf.eval * (step.is_scf.eval - 1) = 0 ∧
    (step.is_add + step.is_adc + step.is_sub + step.is_sbc +
      step.is_and + step.is_xor + step.is_or + step.is_cp +
      step.is_inc + step.is_dec + step.is_rlc + step.is_rrc +
      step.is_rl + step.is_rr + step.is_sla + step.is_sra +
      step.is_srl + step.is_swap + step.is_daa + step.is_cpl +
      step.is_ccf + step.is_scf).eval = 1
  /-- 24 bit Booleans + 3 decomposition equalities for alu_operand_a,
      alu_operand_b, alu_result (Gap H). -/
  range_check :
    (step.a_bit_0.eval * (step.a_bit_0.eval - 1) = 0 ∧
     step.a_bit_1.eval * (step.a_bit_1.eval - 1) = 0 ∧
     step.a_bit_2.eval * (step.a_bit_2.eval - 1) = 0 ∧
     step.a_bit_3.eval * (step.a_bit_3.eval - 1) = 0 ∧
     step.a_bit_4.eval * (step.a_bit_4.eval - 1) = 0 ∧
     step.a_bit_5.eval * (step.a_bit_5.eval - 1) = 0 ∧
     step.a_bit_6.eval * (step.a_bit_6.eval - 1) = 0 ∧
     step.a_bit_7.eval * (step.a_bit_7.eval - 1) = 0) ∧
    (step.alu_operand_a.eval =
      step.a_bit_0.eval + step.a_bit_1.eval * 2 + step.a_bit_2.eval * 4 +
      step.a_bit_3.eval * 8 + step.a_bit_4.eval * 16 + step.a_bit_5.eval * 32 +
      step.a_bit_6.eval * 64 + step.a_bit_7.eval * 128) ∧
    (step.b_bit_0.eval * (step.b_bit_0.eval - 1) = 0 ∧
     step.b_bit_1.eval * (step.b_bit_1.eval - 1) = 0 ∧
     step.b_bit_2.eval * (step.b_bit_2.eval - 1) = 0 ∧
     step.b_bit_3.eval * (step.b_bit_3.eval - 1) = 0 ∧
     step.b_bit_4.eval * (step.b_bit_4.eval - 1) = 0 ∧
     step.b_bit_5.eval * (step.b_bit_5.eval - 1) = 0 ∧
     step.b_bit_6.eval * (step.b_bit_6.eval - 1) = 0 ∧
     step.b_bit_7.eval * (step.b_bit_7.eval - 1) = 0) ∧
    (step.alu_operand_b.eval =
      step.b_bit_0.eval + step.b_bit_1.eval * 2 + step.b_bit_2.eval * 4 +
      step.b_bit_3.eval * 8 + step.b_bit_4.eval * 16 + step.b_bit_5.eval * 32 +
      step.b_bit_6.eval * 64 + step.b_bit_7.eval * 128) ∧
    (step.r_bit_0.eval * (step.r_bit_0.eval - 1) = 0 ∧
     step.r_bit_1.eval * (step.r_bit_1.eval - 1) = 0 ∧
     step.r_bit_2.eval * (step.r_bit_2.eval - 1) = 0 ∧
     step.r_bit_3.eval * (step.r_bit_3.eval - 1) = 0 ∧
     step.r_bit_4.eval * (step.r_bit_4.eval - 1) = 0 ∧
     step.r_bit_5.eval * (step.r_bit_5.eval - 1) = 0 ∧
     step.r_bit_6.eval * (step.r_bit_6.eval - 1) = 0 ∧
     step.r_bit_7.eval * (step.r_bit_7.eval - 1) = 0) ∧
    (step.alu_result.eval =
      step.r_bit_0.eval + step.r_bit_1.eval * 2 + step.r_bit_2.eval * 4 +
      step.r_bit_3.eval * 8 + step.r_bit_4.eval * 16 + step.r_bit_5.eval * 32 +
      step.r_bit_6.eval * 64 + step.r_bit_7.eval * 128)
  /-- 8 per-bit lookup constraints each for AND, XOR, OR (Gap A). -/
  table_lookup :
    (step.is_and.eval * (step.r_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval) = 0 ∧
     step.is_and.eval * (step.r_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval) = 0) ∧
    (step.is_xor.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval * 2)) = 0 ∧
     step.is_xor.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval * 2)) = 0) ∧
    (step.is_or.eval * (step.r_bit_0.eval - (step.a_bit_0.eval + step.b_bit_0.eval - step.a_bit_0.eval * step.b_bit_0.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_1.eval - (step.a_bit_1.eval + step.b_bit_1.eval - step.a_bit_1.eval * step.b_bit_1.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_2.eval - (step.a_bit_2.eval + step.b_bit_2.eval - step.a_bit_2.eval * step.b_bit_2.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_3.eval - (step.a_bit_3.eval + step.b_bit_3.eval - step.a_bit_3.eval * step.b_bit_3.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_4.eval - (step.a_bit_4.eval + step.b_bit_4.eval - step.a_bit_4.eval * step.b_bit_4.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_5.eval - (step.a_bit_5.eval + step.b_bit_5.eval - step.a_bit_5.eval * step.b_bit_5.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_6.eval - (step.a_bit_6.eval + step.b_bit_6.eval - step.a_bit_6.eval * step.b_bit_6.eval)) = 0 ∧
     step.is_or.eval * (step.r_bit_7.eval - (step.a_bit_7.eval + step.b_bit_7.eval - step.a_bit_7.eval * step.b_bit_7.eval)) = 0)
  /-- Zero-flag witness + pinning constraints. -/
  is_zero :
    step.alu_result.eval * step.result_inv.eval = 1 - step.flag_z.eval ∧
    step.flag_z.eval * step.alu_result.eval = 0
  /-- N-flag value: equal to `is_sub + is_sbc + is_cp + is_dec + is_cpl`. -/
  flag_n :
    step.flag_n.eval =
      step.is_sub.eval + step.is_sbc.eval + step.is_cp.eval +
      step.is_dec.eval + step.is_cpl.eval
  /-- H-flag "must-be-1" MUX (forces H=1 when AND or CPL). -/
  h_must_be_one :
    (step.is_and.eval + step.is_cpl.eval) * (step.flag_h.eval - 1) = 0
  /-- H-flag "must-be-0" MUX (forces H=0 for the listed ops). -/
  h_must_be_zero :
    (step.is_xor.eval + step.is_or.eval + step.is_swap.eval +
      step.is_rlc.eval + step.is_rrc.eval + step.is_rl.eval +
      step.is_rr.eval + step.is_sla.eval + step.is_sra.eval +
      step.is_srl.eval + step.is_ccf.eval + step.is_scf.eval +
      step.is_daa.eval) * step.flag_h.eval = 0
  /-- C-flag "must-be-0" MUX (forces C=0 for AND/XOR/OR). -/
  c_must_be_zero :
    (step.is_and.eval + step.is_xor.eval + step.is_or.eval) * step.flag_c.eval = 0
  /-- C-flag "must-be-1" MUX (forces C=1 for SCF). -/
  c_must_be_one :
    step.is_scf.eval * (step.flag_c.eval - 1) = 0
  /-- Register-coupling facts: 7 source-selector booleans, sum-to-1, and
      the two equations linking the abstract ALU operands to the concrete
      register file columns. Closes the coupling caveat for the
      single-step refinement theorem. -/
  register_coupling :
    step.is_src_a.eval * (step.is_src_a.eval - 1) = 0 ∧
    step.is_src_b.eval * (step.is_src_b.eval - 1) = 0 ∧
    step.is_src_c.eval * (step.is_src_c.eval - 1) = 0 ∧
    step.is_src_d.eval * (step.is_src_d.eval - 1) = 0 ∧
    step.is_src_e.eval * (step.is_src_e.eval - 1) = 0 ∧
    step.is_src_h.eval * (step.is_src_h.eval - 1) = 0 ∧
    step.is_src_l.eval * (step.is_src_l.eval - 1) = 0 ∧
    (step.is_src_a + step.is_src_b + step.is_src_c + step.is_src_d +
      step.is_src_e + step.is_src_h + step.is_src_l).eval = 1 ∧
    step.alu_operand_a.eval = step.reg_a.eval ∧
    step.alu_operand_b.eval =
      (step.is_src_a * step.reg_a + step.is_src_b * step.reg_b +
        step.is_src_c * step.reg_c + step.is_src_d * step.reg_d +
        step.is_src_e * step.reg_e + step.is_src_h * step.reg_h +
        step.is_src_l * step.reg_l).eval
  /-- ADD lookup constraint: when `is_add = 1`, `alu_operand_a + alu_operand_b = alu_result + flag_c * 256`.
      Closes Gap A for ADD via the carry decomposition. -/
  table_constraint_add :
    step.is_add.eval *
      (step.alu_operand_a.eval + step.alu_operand_b.eval -
        step.alu_result.eval - step.flag_c.eval * 256) = 0
  /-- SUB lookup constraint: when `is_sub = 1`, `alu_operand_a + flag_c * 256 = alu_result + alu_operand_b`.
      Closes Gap A for SUB via the borrow decomposition. -/
  table_constraint_sub :
    step.is_sub.eval *
      (step.alu_operand_a.eval + step.flag_c.eval * 256 -
        step.alu_result.eval - step.alu_operand_b.eval) = 0
  /-- INC lookup constraint: when `is_inc = 1`, `alu_operand_a + 1 = alu_result + inc_overflow * 256`. -/
  table_constraint_inc :
    step.is_inc.eval *
      (step.alu_operand_a.eval + 1 - step.alu_result.eval -
        step.inc_overflow.eval * 256) = 0
  /-- DEC lookup constraint: when `is_dec = 1`, `alu_operand_a + inc_overflow * 256 = alu_result + 1`. -/
  table_constraint_dec :
    step.is_dec.eval *
      (step.alu_operand_a.eval + step.inc_overflow.eval * 256 -
        step.alu_result.eval - 1) = 0
  /-- Global Boolean constraint on `flag_c`: required by `table_constraint_add` and `table_constraint_sub`. -/
  flag_c_boolean :
    step.flag_c.eval * (step.flag_c.eval - 1) = 0
  /-- Global Boolean constraint on `inc_overflow`: required by INC/DEC tables. -/
  inc_overflow_boolean :
    step.inc_overflow.eval * (step.inc_overflow.eval - 1) = 0
  /-- SLA: `is_sla * (a*2 - r - flag_c*256) = 0`. -/
  table_constraint_sla :
    step.is_sla.eval *
      (step.alu_operand_a.eval * 2 - step.alu_result.eval - step.flag_c.eval * 256) = 0
  /-- SRL: `is_srl * (a - r*2 - flag_c) = 0`. -/
  table_constraint_srl :
    step.is_srl.eval *
      (step.alu_operand_a.eval - step.alu_result.eval * 2 - step.flag_c.eval) = 0
  /-- RLC: two facts — flag_c = a_bit_7, and the rotate equation. -/
  table_constraint_rlc :
    step.is_rlc.eval * (step.flag_c.eval - step.a_bit_7.eval) = 0 ∧
    step.is_rlc.eval *
      (step.alu_operand_a.eval * 2 + step.a_bit_7.eval -
        step.alu_result.eval - step.a_bit_7.eval * 256) = 0
  /-- RRC: two facts — flag_c = a_bit_0, and the rotate equation. -/
  table_constraint_rrc :
    step.is_rrc.eval * (step.flag_c.eval - step.a_bit_0.eval) = 0 ∧
    step.is_rrc.eval *
      (step.alu_operand_a.eval + step.a_bit_0.eval * 256 -
        step.alu_result.eval * 2 - step.a_bit_0.eval) = 0
  /-- SRA: two facts — flag_c = a_bit_0, and the sign-extending shift equation. -/
  table_constraint_sra :
    step.is_sra.eval * (step.flag_c.eval - step.a_bit_0.eval) = 0 ∧
    step.is_sra.eval *
      (step.alu_operand_a.eval + step.a_bit_7.eval * 256 -
        step.alu_result.eval * 2 - step.flag_c.eval) = 0
  /-- SWAP: 8 per-bit constraints, `r_bit_i = a_bit_(i ⊕ 4)`. -/
  table_constraint_swap :
    step.is_swap.eval * (step.r_bit_0.eval - step.a_bit_4.eval) = 0 ∧
    step.is_swap.eval * (step.r_bit_1.eval - step.a_bit_5.eval) = 0 ∧
    step.is_swap.eval * (step.r_bit_2.eval - step.a_bit_6.eval) = 0 ∧
    step.is_swap.eval * (step.r_bit_3.eval - step.a_bit_7.eval) = 0 ∧
    step.is_swap.eval * (step.r_bit_4.eval - step.a_bit_0.eval) = 0 ∧
    step.is_swap.eval * (step.r_bit_5.eval - step.a_bit_1.eval) = 0 ∧
    step.is_swap.eval * (step.r_bit_6.eval - step.a_bit_2.eval) = 0 ∧
    step.is_swap.eval * (step.r_bit_7.eval - step.a_bit_3.eval) = 0
  /-- Global Boolean constraint on `carry_in`: required by ADC/SBC/RL/RR. -/
  carry_in_boolean :
    step.carry_in.eval * (step.carry_in.eval - 1) = 0
  /-- ADC: `is_adc * (a + b + carry_in - r - flag_c * 256) = 0`. -/
  table_constraint_adc :
    step.is_adc.eval *
      (step.alu_operand_a.eval + step.alu_operand_b.eval + step.carry_in.eval -
        step.alu_result.eval - step.flag_c.eval * 256) = 0
  /-- SBC: `is_sbc * (a + flag_c * 256 - r - b - carry_in) = 0`. -/
  table_constraint_sbc :
    step.is_sbc.eval *
      (step.alu_operand_a.eval + step.flag_c.eval * 256 -
        step.alu_result.eval - step.alu_operand_b.eval - step.carry_in.eval) = 0
  /-- CP: `is_cp * (a + flag_c * 256 - r - b) = 0`. Same shape as SUB. -/
  table_constraint_cp :
    step.is_cp.eval *
      (step.alu_operand_a.eval + step.flag_c.eval * 256 -
        step.alu_result.eval - step.alu_operand_b.eval) = 0
  /-- RL: two facts — flag_c = a_bit_7, and the through-carry rotate equation. -/
  table_constraint_rl :
    step.is_rl.eval * (step.flag_c.eval - step.a_bit_7.eval) = 0 ∧
    step.is_rl.eval *
      (step.alu_operand_a.eval * 2 + step.carry_in.eval -
        step.alu_result.eval - step.a_bit_7.eval * 256) = 0
  /-- RR: two facts — flag_c = a_bit_0, and the through-carry rotate equation. -/
  table_constraint_rr :
    step.is_rr.eval * (step.flag_c.eval - step.a_bit_0.eval) = 0 ∧
    step.is_rr.eval *
      (step.alu_operand_a.eval + step.carry_in.eval * 256 -
        step.alu_result.eval * 2 - step.a_bit_0.eval) = 0
  /-- CPL: `is_cpl * (a + r - 255) = 0`. -/
  table_constraint_cpl :
    step.is_cpl.eval * (step.alu_operand_a.eval + step.alu_result.eval - 255) = 0
  /-- CCF: accumulator unchanged. -/
  table_constraint_ccf :
    step.is_ccf.eval * (step.alu_result.eval - step.alu_operand_a.eval) = 0
  /-- SCF: accumulator unchanged. -/
  table_constraint_scf :
    step.is_scf.eval * (step.alu_result.eval - step.alu_operand_a.eval) = 0
  /-- DAA pre-op N flag input is Boolean. -/
  daa_n_in_boolean :
    step.daa_n_in.eval * (step.daa_n_in.eval - 1) = 0
  /-- DAA pre-op H flag input is Boolean. -/
  daa_h_in_boolean :
    step.daa_h_in.eval * (step.daa_h_in.eval - 1) = 0
  /-- DAA pre-op C flag input is Boolean. -/
  daa_c_in_boolean :
    step.daa_c_in.eval * (step.daa_c_in.eval - 1) = 0
  /-- DAA polynomial lookup: alu_result equals `daa_poly_from_step step` when
      `is_daa = 1`. -/
  table_constraint_daa :
    step.is_daa.eval *
      (step.alu_result.eval - (daa_poly_from_step step).eval) = 0

-- Unified `master_constraints` bridge: from a single `isSome` hypothesis
-- on `master_constraints`, extract every primitive equation as a named
-- field of `MasterConstraintFacts`. Closes Gap K.
set_option maxHeartbeats 6400000 in
theorem master_constraints_bridge (step : SM83StepInputs g) (st : ZKState g)
    (h : (runZKBuilder (master_constraints step) st).isSome) :
    MasterConstraintFacts step := by
  unfold master_constraints at h
  obtain ⟨h_oh, st1, h1⟩ := runZKBuilder_seq_isSome_split h
  obtain ⟨h_rc, st2, h2⟩ := runZKBuilder_seq_isSome_split h1
  obtain ⟨h_tl, st3, h3⟩ := runZKBuilder_seq_isSome_split h2
  obtain ⟨h_iz, st4, h4⟩ := runZKBuilder_seq_isSome_split h3
  obtain ⟨h_n, st5, h5⟩ := runZKBuilder_seq_isSome_split h4
  obtain ⟨h_h1, st6, h6⟩ := runZKBuilder_seq_isSome_split h5
  obtain ⟨h_h0, st7, h7⟩ := runZKBuilder_seq_isSome_split h6
  obtain ⟨h_c0, st8, h8⟩ := runZKBuilder_seq_isSome_split h7
  obtain ⟨h_c1, st9, h9⟩ := runZKBuilder_seq_isSome_split h8
  obtain ⟨h_rc_couple, st10, h10⟩ := runZKBuilder_seq_isSome_split h9
  obtain ⟨h_table_add, st11, h11⟩ := runZKBuilder_seq_isSome_split h10
  obtain ⟨h_table_sub, st12, h12⟩ := runZKBuilder_seq_isSome_split h11
  obtain ⟨h_table_inc, st13, h13⟩ := runZKBuilder_seq_isSome_split h12
  obtain ⟨h_table_dec, st14, h14⟩ := runZKBuilder_seq_isSome_split h13
  obtain ⟨h_flag_c_bool, st15, h15⟩ := runZKBuilder_seq_isSome_split h14
  obtain ⟨h_inc_ov_bool, st16, h16⟩ := runZKBuilder_seq_isSome_split h15
  obtain ⟨h_sla, st17, h17⟩ := runZKBuilder_seq_isSome_split h16
  obtain ⟨h_srl, st18, h18⟩ := runZKBuilder_seq_isSome_split h17
  obtain ⟨h_rlc1, st19, h19⟩ := runZKBuilder_seq_isSome_split h18
  obtain ⟨h_rlc2, st20, h20⟩ := runZKBuilder_seq_isSome_split h19
  obtain ⟨h_rrc1, st21, h21⟩ := runZKBuilder_seq_isSome_split h20
  obtain ⟨h_rrc2, st22, h22⟩ := runZKBuilder_seq_isSome_split h21
  obtain ⟨h_sra1, st23, h23⟩ := runZKBuilder_seq_isSome_split h22
  obtain ⟨h_sra2, st24, h24⟩ := runZKBuilder_seq_isSome_split h23
  obtain ⟨h_sw0, st25, h25⟩ := runZKBuilder_seq_isSome_split h24
  obtain ⟨h_sw1, st26, h26⟩ := runZKBuilder_seq_isSome_split h25
  obtain ⟨h_sw2, st27, h27⟩ := runZKBuilder_seq_isSome_split h26
  obtain ⟨h_sw3, st28, h28⟩ := runZKBuilder_seq_isSome_split h27
  obtain ⟨h_sw4, st29, h29⟩ := runZKBuilder_seq_isSome_split h28
  obtain ⟨h_sw5, st30, h30⟩ := runZKBuilder_seq_isSome_split h29
  obtain ⟨h_sw6, st31, h31⟩ := runZKBuilder_seq_isSome_split h30
  obtain ⟨h_sw7, st32, h32⟩ := runZKBuilder_seq_isSome_split h31
  obtain ⟨h_carry_in_bool, st33, h33⟩ := runZKBuilder_seq_isSome_split h32
  obtain ⟨h_adc, st34, h34⟩ := runZKBuilder_seq_isSome_split h33
  obtain ⟨h_sbc, st35, h35⟩ := runZKBuilder_seq_isSome_split h34
  obtain ⟨h_cp, st36, h36⟩ := runZKBuilder_seq_isSome_split h35
  obtain ⟨h_rl1, st37, h37⟩ := runZKBuilder_seq_isSome_split h36
  obtain ⟨h_rl2, st38, h38⟩ := runZKBuilder_seq_isSome_split h37
  obtain ⟨h_rr1, st39, h39⟩ := runZKBuilder_seq_isSome_split h38
  obtain ⟨h_rr2, st40, h40⟩ := runZKBuilder_seq_isSome_split h39
  obtain ⟨h_cpl, st41, h41⟩ := runZKBuilder_seq_isSome_split h40
  obtain ⟨h_ccf, st42, h42⟩ := runZKBuilder_seq_isSome_split h41
  obtain ⟨h_scf, st43, h43⟩ := runZKBuilder_seq_isSome_split h42
  obtain ⟨h_daa_n_bool, st44, h44⟩ := runZKBuilder_seq_isSome_split h43
  obtain ⟨h_daa_h_bool, st45, h45⟩ := runZKBuilder_seq_isSome_split h44
  obtain ⟨h_daa_c_bool, st46, h_daa_table⟩ := runZKBuilder_seq_isSome_split h45
  refine {
    one_hot := one_hot_constraints_bridge step st h_oh
    range_check := range_check_constraints_bridge step st1 h_rc
    table_lookup := table_lookup_constraints_bridge step st2 h_tl
    is_zero := SM83.SemanticBridge.is_zero_bridge step st3 h_iz
    flag_n := ?_
    h_must_be_one := ?_
    h_must_be_zero := ?_
    c_must_be_zero := ?_
    c_must_be_one := ?_
    register_coupling := register_coupling_constraints_bridge step st9 h_rc_couple
    table_constraint_add := ?_
    table_constraint_sub := ?_
    table_constraint_inc := ?_
    table_constraint_dec := ?_
    flag_c_boolean := ?_
    inc_overflow_boolean := ?_
    table_constraint_sla := ?_
    table_constraint_srl := ?_
    table_constraint_rlc := ?_
    table_constraint_rrc := ?_
    table_constraint_sra := ?_
    table_constraint_swap := ?_
    carry_in_boolean := ?_
    table_constraint_adc := ?_
    table_constraint_sbc := ?_
    table_constraint_cp := ?_
    table_constraint_rl := ?_
    table_constraint_rr := ?_
    table_constraint_cpl := ?_
    table_constraint_ccf := ?_
    table_constraint_scf := ?_
    daa_n_in_boolean := ?_
    daa_h_in_boolean := ?_
    daa_c_in_boolean := ?_
    table_constraint_daa := ?_
  }
  · have := SM83.SemanticBridge.constrainEq_sound _ _ st4 h_n
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st5 h_h1
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st6 h_h0
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st7 h_c0
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st8 h_c1
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st10 h_table_add
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st11 h_table_sub
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st12 h_table_inc
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st13 h_table_dec
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st14 h_flag_c_bool
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st15 h_inc_ov_bool
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st16 h_sla
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st17 h_srl
    simpa only [ZKExpr.eval] using this
  · refine ⟨?_, ?_⟩
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st18 h_rlc1
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st19 h_rlc2
      simpa only [ZKExpr.eval] using this
  · refine ⟨?_, ?_⟩
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st20 h_rrc1
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st21 h_rrc2
      simpa only [ZKExpr.eval] using this
  · refine ⟨?_, ?_⟩
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st22 h_sra1
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st23 h_sra2
      simpa only [ZKExpr.eval] using this
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st24 h_sw0
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st25 h_sw1
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st26 h_sw2
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st27 h_sw3
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st28 h_sw4
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st29 h_sw5
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st30 h_sw6
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st31 h_sw7
      simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st32 h_carry_in_bool
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st33 h_adc
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st34 h_sbc
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st35 h_cp
    simpa only [ZKExpr.eval] using this
  · refine ⟨?_, ?_⟩
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st36 h_rl1
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st37 h_rl2
      simpa only [ZKExpr.eval] using this
  · refine ⟨?_, ?_⟩
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st38 h_rr1
      simpa only [ZKExpr.eval] using this
    · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st39 h_rr2
      simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st40 h_cpl
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st41 h_ccf
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st42 h_scf
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st43 h_daa_n_bool
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st44 h_daa_h_bool
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st45 h_daa_c_bool
    simpa only [ZKExpr.eval] using this
  · have := SM83.SemanticBridge.constrainR1CS_sound _ _ _ st46 h_daa_table
    simpa only [ZKExpr.eval] using this

end SM83.FullSoundness
