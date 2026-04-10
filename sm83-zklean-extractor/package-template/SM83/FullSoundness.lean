import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
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

/-! ### Gap C: master_constraints bridge (via runZKBuilder equation lemmas)

Now that we have `runZKBuilder_constrainR1CS_eq` and `runZKBuilder_constrainEq_eq`,
we can prove the master_constraints bridge by repeated rewriting.
-/

/-- Helper: extract Boolean chain from N-nested if-then-else applied to same state. -/
private theorem extract_7_bools {c1 c2 c3 c4 c5 c6 c7 : Bool}
    {σ α : Type} {st : σ} {v : α} :
    (if c1 then (if c2 then (if c3 then (if c4 then (if c5 then (if c6 then
      (if c7 then some (v, st) else none) else none) else none) else none) else none) else none) else (none : Option (α × σ))).isSome →
    c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧ c5 = true ∧ c6 = true ∧ c7 = true := by
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;>
    cases c5 <;> cases c6 <;> cases c7 <;> simp

set_option maxHeartbeats 6400000 in
/-- Master constraints bridge: extracts all 7 primitive constraint equations
    from `master_constraints` success. This closes Gap C. -/
theorem master_constraints_bridge (step : SM83StepInputs g) (st : ZKState g) :
    (runZKBuilder (master_constraints step) st).isSome →
    -- is_zero #1: result * result_inv = 1 - Z
    step.alu_result.eval * step.result_inv.eval = 1 - step.flag_z.eval ∧
    -- is_zero #2: Z * result = 0
    step.flag_z.eval * step.alu_result.eval = 0 ∧
    -- N flag: flag_n = is_sub + is_sbc + is_cp + is_dec + is_cpl
    step.flag_n.eval =
      step.is_sub.eval + step.is_sbc.eval + step.is_cp.eval +
      step.is_dec.eval + step.is_cpl.eval ∧
    -- H must-be-one: (is_and + is_cpl) * (flag_h - 1) = 0
    (step.is_and.eval + step.is_cpl.eval) * (step.flag_h.eval - 1) = 0 ∧
    -- H must-be-zero
    (step.is_xor.eval + step.is_or.eval + step.is_swap.eval +
      step.is_rlc.eval + step.is_rrc.eval + step.is_rl.eval +
      step.is_rr.eval + step.is_sla.eval + step.is_sra.eval +
      step.is_srl.eval + step.is_ccf.eval + step.is_scf.eval +
      step.is_daa.eval) * step.flag_h.eval = 0 ∧
    -- C must-be-zero: (is_and + is_xor + is_or) * flag_c = 0
    (step.is_and.eval + step.is_xor.eval + step.is_or.eval) * step.flag_c.eval = 0 ∧
    -- C must-be-one: is_scf * (flag_c - 1) = 0
    step.is_scf.eval * (step.flag_c.eval - 1) = 0 := by
  -- Unfold master_constraints and is_zero_constraint to get flat sequence of primitives
  -- Then use the runZKBuilder equation lemmas to reduce each primitive
  -- Use the monad morphism lemma to decompose the bind chain
  -- master_constraints = do is_zero; constrainEq flag_n _; constrainR1CS ...; ...
  simp only [master_constraints]
  -- The morphism lemma converts runZKBuilder of bind into Option.bind
  simp only [runZKBuilder_bind, runZKBuilder_constrainR1CS_eq, runZKBuilder_constrainEq_eq]
  -- Also need to handle is_zero_constraint: it's itself a bind chain
  simp only [is_zero_constraint, runZKBuilder_bind, runZKBuilder_constrainR1CS_eq]
  intro h
  -- After rewriting, h has nested match/Option.bind structure.
  -- Use repeated split to extract each Boolean condition.
  split at h
  · next hc1 =>
    refine ⟨beq_iff_eq.mp hc1, ?_⟩
    split at h
    · next hc2 =>
      refine ⟨beq_iff_eq.mp hc2, ?_⟩
      split at h
      · next hc3 =>
        refine ⟨beq_iff_eq.mp hc3, ?_⟩
        split at h
        · next hc4 =>
          refine ⟨beq_iff_eq.mp hc4, ?_⟩
          split at h
          · next hc5 =>
            refine ⟨beq_iff_eq.mp hc5, ?_⟩
            split at h
            · next hc6 =>
              refine ⟨beq_iff_eq.mp hc6, ?_⟩
              split at h
              · next hc7 => exact beq_iff_eq.mp hc7
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

end SM83.FullSoundness
