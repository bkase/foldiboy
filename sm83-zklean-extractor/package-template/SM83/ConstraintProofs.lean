import Mathlib.Algebra.Field.ZMod

/-! # SM83 Constraint Soundness Proofs

Pure algebraic proofs over `ZMod p` that the constraint gadgets in
`SM83/Constraints.lean` are sound. These do NOT reason about the
`ZKBuilder` monad — they work directly with field elements.

Matches the constraint forms:
- `constrainR1CS a b c` enforces `a * b = c`
- `constrainEq a b` enforces `a = b`

## Gadgets proved
- **is_zero**: `result * result_inv = 1 - Z`, `Z * result = 0`
- **boolean**: `x * (x - 1) = 0`
- **mux**: `selector * (flag - target) = 0`
- **half_carry_add/sub**: nibble decomposition with Boolean flag
- **carry_add/sub**: 8-bit decomposition with Boolean flag
-/

namespace SM83.ConstraintProofs

variable {p : ℕ} [Fact p.Prime]

/-! ### Boolean from R1CS -/

/-- `x * (x - 1) = 0` implies `x ∈ {0, 1}` in a prime field. -/
theorem boolean_of_r1cs {x : ZMod p} (h : x * (x - 1) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-! ### IsZero sub-constraint -/

/-- The is_zero gadget is sound: `result = 0 ↔ Z = 1`.
    From `Constraints.lean`:
    - `constrainR1CS result result_inv (1 - Z)` i.e. `result * result_inv = 1 - Z`
    - `constrainR1CS Z result 0` i.e. `Z * result = 0` -/
theorem is_zero_sound {result Z result_inv : ZMod p}
    (h1 : result * result_inv = 1 - Z)
    (h2 : Z * result = 0) :
    result = 0 ↔ Z = 1 := by
  constructor
  · intro hr
    subst hr
    simp [zero_mul] at h1
    exact (sub_eq_zero.mp h1.symm).symm
  · intro hz
    subst hz
    simpa [one_mul] using h2

/-- Z is Boolean: follows from the is_zero constraints alone (no separate `hZ` needed). -/
theorem is_zero_z_boolean {result Z result_inv : ZMod p}
    (h1 : result * result_inv = 1 - Z)
    (h2 : Z * result = 0) :
    Z = 0 ∨ Z = 1 := by
  have hZZ : Z * (1 - Z) = 0 := by
    have h3 : Z * result * result_inv = 0 := by rw [h2, zero_mul]
    rwa [mul_assoc, h1] at h3
  rcases mul_eq_zero.mp hZZ with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

/-! ### MUX dispatch -/

/-- If `selector ≠ 0` and `selector * (flag - target) = 0`, then `flag = target`.
    Used for `constrainR1CS h_must_be_one (H - 1) 0` etc. -/
theorem mux_forces_value {selector flag target : ZMod p}
    (h : selector * (flag - target) = 0) (hs : selector ≠ 0) :
    flag = target :=
  sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs)

/-- If `selector ≠ 0` and `selector * flag = 0`, then `flag = 0`.
    Used for `constrainR1CS h_must_be_zero H 0`. -/
theorem mux_forces_zero {selector flag : ZMod p}
    (h : selector * flag = 0) (hs : selector ≠ 0) :
    flag = 0 :=
  (mul_eq_zero.mp h).resolve_left hs

/-! ### Half-carry add

From `Constraints.lean`:
- `constrainEq (nibble_a + nibble_b) (nibble_result + H * 16)`
- `constrainR1CS H (H - 1) 0` -/

theorem half_carry_add_h_boolean {nibble_a nibble_b nibble_result H : ZMod p}
    (_h_eq : nibble_a + nibble_b = nibble_result + H * 16)
    (h_bool : H * (H - 1) = 0) :
    H = 0 ∨ H = 1 :=
  boolean_of_r1cs h_bool

/-- When H = 0, nibbles add directly (no half-carry). -/
theorem half_carry_add_no_carry {nibble_a nibble_b nibble_result H : ZMod p}
    (h_eq : nibble_a + nibble_b = nibble_result + H * 16)
    (hH : H = 0) :
    nibble_a + nibble_b = nibble_result := by
  rw [hH, zero_mul, add_zero] at h_eq; exact h_eq

/-- When H = 1, nibbles overflow by 16 (half-carry occurred). -/
theorem half_carry_add_with_carry {nibble_a nibble_b nibble_result H : ZMod p}
    (h_eq : nibble_a + nibble_b = nibble_result + H * 16)
    (hH : H = 1) :
    nibble_a + nibble_b = nibble_result + 16 := by
  rw [hH, one_mul] at h_eq; exact h_eq

/-! ### Half-carry sub

From `Constraints.lean`:
- `constrainEq (nibble_a + H * 16) (nibble_result + nibble_b)`
- `constrainR1CS H (H - 1) 0` -/

theorem half_carry_sub_h_boolean {nibble_a nibble_b nibble_result H : ZMod p}
    (_h_eq : nibble_a + H * 16 = nibble_result + nibble_b)
    (h_bool : H * (H - 1) = 0) :
    H = 0 ∨ H = 1 :=
  boolean_of_r1cs h_bool

/-- When H = 0, no borrow: `nibble_a = nibble_result + nibble_b`. -/
theorem half_carry_sub_no_borrow {nibble_a nibble_b nibble_result H : ZMod p}
    (h_eq : nibble_a + H * 16 = nibble_result + nibble_b)
    (hH : H = 0) :
    nibble_a = nibble_result + nibble_b := by
  rw [hH, zero_mul, add_zero] at h_eq; exact h_eq

/-- When H = 1, borrow: `nibble_a + 16 = nibble_result + nibble_b`. -/
theorem half_carry_sub_with_borrow {nibble_a nibble_b nibble_result H : ZMod p}
    (h_eq : nibble_a + H * 16 = nibble_result + nibble_b)
    (hH : H = 1) :
    nibble_a + 16 = nibble_result + nibble_b := by
  rw [hH, one_mul] at h_eq; exact h_eq

/-! ### Carry add

From `Constraints.lean`:
- `constrainEq (a + b) (result + C * 256)`
- `constrainR1CS C (C - 1) 0` -/

theorem carry_add_c_boolean {a b result C : ZMod p}
    (_h_eq : a + b = result + C * 256)
    (h_bool : C * (C - 1) = 0) :
    C = 0 ∨ C = 1 :=
  boolean_of_r1cs h_bool

/-- When C = 0, no carry: `a + b = result`. -/
theorem carry_add_no_carry {a b result C : ZMod p}
    (h_eq : a + b = result + C * 256)
    (hC : C = 0) :
    a + b = result := by
  rw [hC, zero_mul, add_zero] at h_eq; exact h_eq

/-- When C = 1, carry: `a + b = result + 256`. -/
theorem carry_add_with_carry {a b result C : ZMod p}
    (h_eq : a + b = result + C * 256)
    (hC : C = 1) :
    a + b = result + 256 := by
  rw [hC, one_mul] at h_eq; exact h_eq

/-! ### Carry sub

From `Constraints.lean`:
- `constrainEq (a + C * 256) (result + b)`
- `constrainR1CS C (C - 1) 0` -/

theorem carry_sub_c_boolean {a b result C : ZMod p}
    (_h_eq : a + C * 256 = result + b)
    (h_bool : C * (C - 1) = 0) :
    C = 0 ∨ C = 1 :=
  boolean_of_r1cs h_bool

/-- When C = 0, no borrow: `a = result + b`. -/
theorem carry_sub_no_borrow {a b result C : ZMod p}
    (h_eq : a + C * 256 = result + b)
    (hC : C = 0) :
    a = result + b := by
  rw [hC, zero_mul, add_zero] at h_eq; exact h_eq

/-- When C = 1, borrow: `a + 256 = result + b`. -/
theorem carry_sub_with_borrow {a b result C : ZMod p}
    (h_eq : a + C * 256 = result + b)
    (hC : C = 1) :
    a + 256 = result + b := by
  rw [hC, one_mul] at h_eq; exact h_eq

/-! ### Composed: full ADD/SUB instruction flags -/

/-- For a full ADD step: is_zero determines Z, carry determines C, both Boolean. -/
theorem add_flags_sound {result result_inv Z C a b : ZMod p}
    (h_iz1 : result * result_inv = 1 - Z)
    (h_iz2 : Z * result = 0)
    (_h_carry_eq : a + b = result + C * 256)
    (h_cbool : C * (C - 1) = 0) :
    (result = 0 ↔ Z = 1) ∧ (C = 0 ∨ C = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, boolean_of_r1cs h_cbool⟩

/-- For a full SUB step: is_zero determines Z, borrow determines C, both Boolean. -/
theorem sub_flags_sound {result result_inv Z C a b : ZMod p}
    (h_iz1 : result * result_inv = 1 - Z)
    (h_iz2 : Z * result = 0)
    (_h_borrow_eq : a + C * 256 = result + b)
    (h_cbool : C * (C - 1) = 0) :
    (result = 0 ↔ Z = 1) ∧ (C = 0 ∨ C = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, boolean_of_r1cs h_cbool⟩

end SM83.ConstraintProofs
