import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import SM83.Spec

/-! # ZMod ↔ BitVec 8 Bridge (Gap T)

Closes Gap T: bridges the constraint-system `ZMod p` values (bit-decomposed
via Gap H) to spec-level `BitVec 8` operands, so that the `h_table` hypothesis
in the compositional end-to-end theorems can be *derived* from the underlying
constraint equations rather than assumed.

## Contents

- `zmodToBitVec8`: the canonical conversion `ZMod p → BitVec 8`.
- `zmodToBitVec8_cast_bounded`: when `x.val ≤ 255`, round-tripping through
  `BitVec 8` and back to `ZMod p` is the identity.
- `bit_decomp_val_eq`: For 8 Boolean bits, the `ZMod.val` of their weighted
  sum equals the Nat sum of their individual `.val`s (no wraparound).
- `land_eight_bits`: Bit-level `Nat.land` equation — the 8-bit `Nat.land`
  of two bit-decomposed naturals equals the bit-decomposed product.
- `and_bv_bridge`: The headline theorem. Given the Gap H bit-decomposition
  constraints for `alu_operand_a`, `alu_operand_b`, `alu_result`, plus the
  Gap A per-bit `is_and * (r_bit_i - a_bit_i * b_bit_i) = 0` constraints
  activated by `is_and = 1`, derives
  `alu_result = ((spec_and (zmodToBitVec8 alu_operand_a) (zmodToBitVec8 alu_operand_b)).toNat : ZMod p)`.

This theorem's conclusion is exactly the `h_table` hypothesis required by
`and_compositional_algebraic` in `EndToEnd.lean`, turning that hypothesis
into something *provable* from the constraint equations.
-/

namespace SM83.ZmodBitVecBridge

variable {p : ℕ} [Fact p.Prime]

/-! ### Definitions -/

/-- Canonical conversion from a field element to `BitVec 8` via its natural
    representative `ZMod.val`. For values `≤ 255` this is the natural
    embedding and is faithful. -/
def zmodToBitVec8 (x : ZMod p) : BitVec 8 := BitVec.ofNat 8 x.val

/-! ### Round-trip -/

/-- Round-trip through `BitVec 8` is the identity when the value fits. -/
theorem zmodToBitVec8_cast_bounded {x : ZMod p} (h : x.val ≤ 255) :
    ((zmodToBitVec8 x).toNat : ZMod p) = x := by
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have hmod : x.val % 2^8 = x.val := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  exact ZMod.natCast_zmod_val x

/-! ### Value-level bit decomposition

Key lemma: the `ZMod.val` of a Boolean-weighted sum equals the Nat sum of
the individual `.val`s. This is the same identity that `bit_decomposition_val_le`
in `FullSoundness.lean` proves as an inequality — here we sharpen it to
equality, which requires all partial sums to fit in `p`.
-/

private theorem bool_val_le_one {x : ZMod p} (hx : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases hx with rfl | rfl
  · simp
  · simp [ZMod.val_one]

/-- For a Boolean `x : ZMod p` and natural `n < p`,
    `(x * (n : ZMod p)).val = x.val * n`. -/
private theorem val_bool_mul_nat_const {x : ZMod p} {n : ℕ}
    (hx : x = 0 ∨ x = 1) (hn : n < p) :
    (x * (n : ZMod p)).val = x.val * n := by
  rcases hx with rfl | rfl
  · simp
  · rw [one_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hn, ZMod.val_one, one_mul]

/-- The `val` of a Boolean-bit-decomposed sum equals the Nat sum of the
    individual `.val`s. Requires `256 < p` so partial sums never wrap. -/
theorem bit_decomp_val_eq (hp_big : 256 < p)
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    (h₀ : b₀ = 0 ∨ b₀ = 1) (h₁ : b₁ = 0 ∨ b₁ = 1) (h₂ : b₂ = 0 ∨ b₂ = 1)
    (h₃ : b₃ = 0 ∨ b₃ = 1) (h₄ : b₄ = 0 ∨ b₄ = 1) (h₅ : b₅ = 0 ∨ b₅ = 1)
    (h₆ : b₆ = 0 ∨ b₆ = 1) (h₇ : b₇ = 0 ∨ b₇ = 1) :
    (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64 + b₇ * 128).val =
    b₀.val + 2 * b₁.val + 4 * b₂.val + 8 * b₃.val +
      16 * b₄.val + 32 * b₅.val + 64 * b₆.val + 128 * b₇.val := by
  have e2 : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_cast
  have e4 : (4 : ZMod p) = ((4 : ℕ) : ZMod p) := by norm_cast
  have e8 : (8 : ZMod p) = ((8 : ℕ) : ZMod p) := by norm_cast
  have e16 : (16 : ZMod p) = ((16 : ℕ) : ZMod p) := by norm_cast
  have e32 : (32 : ZMod p) = ((32 : ℕ) : ZMod p) := by norm_cast
  have e64 : (64 : ZMod p) = ((64 : ℕ) : ZMod p) := by norm_cast
  have e128 : (128 : ZMod p) = ((128 : ℕ) : ZMod p) := by norm_cast
  have v0 : b₀.val ≤ 1 := bool_val_le_one h₀
  have v1 : b₁.val ≤ 1 := bool_val_le_one h₁
  have v2 : b₂.val ≤ 1 := bool_val_le_one h₂
  have v3 : b₃.val ≤ 1 := bool_val_le_one h₃
  have v4 : b₄.val ≤ 1 := bool_val_le_one h₄
  have v5 : b₅.val ≤ 1 := bool_val_le_one h₅
  have v6 : b₆.val ≤ 1 := bool_val_le_one h₆
  have v7 : b₇.val ≤ 1 := bool_val_le_one h₇
  have p2 : (b₁ * 2).val = 2 * b₁.val := by
    rw [e2, val_bool_mul_nat_const h₁ (by omega)]; ring
  have p4 : (b₂ * 4).val = 4 * b₂.val := by
    rw [e4, val_bool_mul_nat_const h₂ (by omega)]; ring
  have p8 : (b₃ * 8).val = 8 * b₃.val := by
    rw [e8, val_bool_mul_nat_const h₃ (by omega)]; ring
  have p16 : (b₄ * 16).val = 16 * b₄.val := by
    rw [e16, val_bool_mul_nat_const h₄ (by omega)]; ring
  have p32 : (b₅ * 32).val = 32 * b₅.val := by
    rw [e32, val_bool_mul_nat_const h₅ (by omega)]; ring
  have p64 : (b₆ * 64).val = 64 * b₆.val := by
    rw [e64, val_bool_mul_nat_const h₆ (by omega)]; ring
  have p128 : (b₇ * 128).val = 128 * b₇.val := by
    rw [e128, val_bool_mul_nat_const h₇ (by omega)]; ring
  have s1 : (b₀ + b₁ * 2).val = b₀.val + (b₁ * 2).val := by
    apply ZMod.val_add_of_lt; rw [p2]; omega
  have s2 : (b₀ + b₁ * 2 + b₂ * 4).val =
      (b₀ + b₁ * 2).val + (b₂ * 4).val := by
    apply ZMod.val_add_of_lt; rw [s1, p2, p4]; omega
  have s3 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8).val =
      (b₀ + b₁ * 2 + b₂ * 4).val + (b₃ * 8).val := by
    apply ZMod.val_add_of_lt; rw [s2, s1, p2, p4, p8]; omega
  have s4 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16).val =
      (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8).val + (b₄ * 16).val := by
    apply ZMod.val_add_of_lt; rw [s3, s2, s1, p2, p4, p8, p16]; omega
  have s5 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32).val =
      (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16).val + (b₅ * 32).val := by
    apply ZMod.val_add_of_lt; rw [s4, s3, s2, s1, p2, p4, p8, p16, p32]; omega
  have s6 : (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64).val =
      (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32).val + (b₆ * 64).val := by
    apply ZMod.val_add_of_lt; rw [s5, s4, s3, s2, s1, p2, p4, p8, p16, p32, p64]; omega
  have s7 :
      (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64 + b₇ * 128).val =
      (b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64).val + (b₇ * 128).val := by
    apply ZMod.val_add_of_lt
    rw [s6, s5, s4, s3, s2, s1, p2, p4, p8, p16, p32, p64, p128]; omega
  rw [s7, s6, s5, s4, s3, s2, s1, p2, p4, p8, p16, p32, p64, p128]

/-! ### Value-level XOR / OR of Boolean operands

For Boolean `a, b : ZMod p`, the polynomial representations
`a + b - 2*a*b` (XOR) and `a + b - a*b` (OR) have the correct `.val`:
equal to the Nat-level bitwise XOR / OR of the `.val`s. Proved by case
analysis on the four Boolean combinations. -/

private theorem val_xor_bool {a b : ZMod p}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a + b - a * b * 2).val = a.val ^^^ b.val := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  · rcases hb with rfl | rfl
    · simp [ZMod.val_one]
    · have h1 : (1 : ZMod p) + 1 - 1 * 1 * 2 = 0 := by ring
      rw [h1]; simp

private theorem val_or_bool {a b : ZMod p}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a + b - a * b).val = a.val ||| b.val := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  · rcases hb with rfl | rfl
    · simp [ZMod.val_one]
    · have h1 : (1 : ZMod p) + 1 - 1 * 1 = 1 := by ring
      rw [h1]; simp [ZMod.val_one]

/-! ### Nat-level bit-wise AND

Closed form for `Nat.land` of two 8-bit bit-decomposed naturals: it equals
the bit-decomposed product. Proven by iterating a single-bit step lemma.
-/

/-- Single-bit step: `Nat.land (a₀ + 2*ra) (b₀ + 2*rb) = a₀*b₀ + 2*Nat.land ra rb`
    for Boolean `a₀`, `b₀`. Proven by `Nat.testBit_ext`. -/
private theorem land_step (a₀ b₀ ra rb : ℕ) (ha : a₀ < 2) (hb : b₀ < 2) :
    Nat.land (a₀ + 2 * ra) (b₀ + 2 * rb) = a₀ * b₀ + 2 * Nat.land ra rb := by
  have ha' : a₀ < 2 ^ 1 := by simpa using ha
  have hb' : b₀ < 2 ^ 1 := by simpa using hb
  apply Nat.eq_of_testBit_eq
  intro k
  show ((a₀ + 2 * ra) &&& (b₀ + 2 * rb)).testBit k = _
  rw [Nat.testBit_land]
  have ea : a₀ + 2 * ra = 2 ^ 1 * ra + a₀ := by ring
  have eb : b₀ + 2 * rb = 2 ^ 1 * rb + b₀ := by ring
  rw [ea, eb]
  rw [Nat.testBit_two_pow_mul_add _ ha', Nat.testBit_two_pow_mul_add _ hb']
  have hab : a₀ * b₀ < 2 ^ 1 := by
    simp only [pow_one]
    interval_cases a₀ <;> interval_cases b₀ <;> decide
  have erhs : a₀ * b₀ + 2 * Nat.land ra rb = 2 ^ 1 * Nat.land ra rb + a₀ * b₀ := by ring
  rw [erhs, Nat.testBit_two_pow_mul_add _ hab]
  split
  · have hk : k = 0 := by omega
    subst hk
    interval_cases a₀ <;> interval_cases b₀ <;> decide
  · show (ra.testBit (k - 1) && rb.testBit (k - 1)) = (Nat.land ra rb).testBit (k - 1)
    rw [← Nat.testBit_land]
    rfl

/-- 8-bit Nat-level bit decomposition of `Nat.land`. -/
theorem land_eight_bits
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℕ}
    (ha₀ : a₀ < 2) (ha₁ : a₁ < 2) (ha₂ : a₂ < 2) (ha₃ : a₃ < 2)
    (ha₄ : a₄ < 2) (ha₅ : a₅ < 2) (ha₆ : a₆ < 2) (ha₇ : a₇ < 2)
    (hb₀ : b₀ < 2) (hb₁ : b₁ < 2) (hb₂ : b₂ < 2) (hb₃ : b₃ < 2)
    (hb₄ : b₄ < 2) (hb₅ : b₅ < 2) (hb₆ : b₆ < 2) (hb₇ : b₇ < 2) :
    Nat.land (a₀ + 2 * a₁ + 4 * a₂ + 8 * a₃ + 16 * a₄ + 32 * a₅ + 64 * a₆ + 128 * a₇)
             (b₀ + 2 * b₁ + 4 * b₂ + 8 * b₃ + 16 * b₄ + 32 * b₅ + 64 * b₆ + 128 * b₇) =
    a₀ * b₀ + 2 * (a₁ * b₁) + 4 * (a₂ * b₂) + 8 * (a₃ * b₃) +
      16 * (a₄ * b₄) + 32 * (a₅ * b₅) + 64 * (a₆ * b₆) + 128 * (a₇ * b₇) := by
  have nested_a :
      a₀ + 2 * a₁ + 4 * a₂ + 8 * a₃ + 16 * a₄ + 32 * a₅ + 64 * a₆ + 128 * a₇ =
      a₀ + 2 * (a₁ + 2 * (a₂ + 2 * (a₃ + 2 * (a₄ + 2 * (a₅ + 2 * (a₆ + 2 * a₇)))))) := by ring
  have nested_b :
      b₀ + 2 * b₁ + 4 * b₂ + 8 * b₃ + 16 * b₄ + 32 * b₅ + 64 * b₆ + 128 * b₇ =
      b₀ + 2 * (b₁ + 2 * (b₂ + 2 * (b₃ + 2 * (b₄ + 2 * (b₅ + 2 * (b₆ + 2 * b₇)))))) := by ring
  rw [nested_a, nested_b]
  rw [land_step _ _ _ _ ha₀ hb₀]
  rw [land_step _ _ _ _ ha₁ hb₁]
  rw [land_step _ _ _ _ ha₂ hb₂]
  rw [land_step _ _ _ _ ha₃ hb₃]
  rw [land_step _ _ _ _ ha₄ hb₄]
  rw [land_step _ _ _ _ ha₅ hb₅]
  rw [land_step _ _ _ _ ha₆ hb₆]
  have last : Nat.land a₇ b₇ = a₇ * b₇ := by
    interval_cases a₇ <;> interval_cases b₇ <;> rfl
  rw [last]
  ring

/-! ### Nat-level bit-wise XOR

Closed form for `Nat.xor` (`^^^`) of two 8-bit bit-decomposed naturals:
it equals the bit-decomposed XOR. Proven by iterating a single-bit
step lemma — analogous to `land_step` / `land_eight_bits`. -/

/-- Single-bit step for XOR: `(a₀ + 2*ra) ^^^ (b₀ + 2*rb) = (a₀ ^^^ b₀) + 2*(ra ^^^ rb)`
    for Boolean `a₀`, `b₀`. -/
private theorem lxor_step (a₀ b₀ ra rb : ℕ) (ha : a₀ < 2) (hb : b₀ < 2) :
    (a₀ + 2 * ra) ^^^ (b₀ + 2 * rb) = (a₀ ^^^ b₀) + 2 * (ra ^^^ rb) := by
  have ha' : a₀ < 2 ^ 1 := by simpa using ha
  have hb' : b₀ < 2 ^ 1 := by simpa using hb
  apply Nat.eq_of_testBit_eq
  intro k
  show ((a₀ + 2 * ra) ^^^ (b₀ + 2 * rb)).testBit k = _
  rw [Nat.testBit_xor]
  have ea : a₀ + 2 * ra = 2 ^ 1 * ra + a₀ := by ring
  have eb : b₀ + 2 * rb = 2 ^ 1 * rb + b₀ := by ring
  rw [ea, eb]
  rw [Nat.testBit_two_pow_mul_add _ ha', Nat.testBit_two_pow_mul_add _ hb']
  have hab : (a₀ ^^^ b₀) < 2 ^ 1 := by
    simp only [pow_one]
    interval_cases a₀ <;> interval_cases b₀ <;> decide
  have erhs : (a₀ ^^^ b₀) + 2 * (ra ^^^ rb) = 2 ^ 1 * (ra ^^^ rb) + (a₀ ^^^ b₀) := by ring
  rw [erhs, Nat.testBit_two_pow_mul_add _ hab]
  split
  · have hk : k = 0 := by omega
    subst hk
    interval_cases a₀ <;> interval_cases b₀ <;> decide
  · show (ra.testBit (k - 1) ^^ rb.testBit (k - 1)) = (ra ^^^ rb).testBit (k - 1)
    rw [← Nat.testBit_xor]

/-- 8-bit Nat-level bit decomposition of `Nat.xor`. -/
theorem lxor_eight_bits
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℕ}
    (ha₀ : a₀ < 2) (ha₁ : a₁ < 2) (ha₂ : a₂ < 2) (ha₃ : a₃ < 2)
    (ha₄ : a₄ < 2) (ha₅ : a₅ < 2) (ha₆ : a₆ < 2) (_ha₇ : a₇ < 2)
    (hb₀ : b₀ < 2) (hb₁ : b₁ < 2) (hb₂ : b₂ < 2) (hb₃ : b₃ < 2)
    (hb₄ : b₄ < 2) (hb₅ : b₅ < 2) (hb₆ : b₆ < 2) (_hb₇ : b₇ < 2) :
    (a₀ + 2 * a₁ + 4 * a₂ + 8 * a₃ + 16 * a₄ + 32 * a₅ + 64 * a₆ + 128 * a₇) ^^^
    (b₀ + 2 * b₁ + 4 * b₂ + 8 * b₃ + 16 * b₄ + 32 * b₅ + 64 * b₆ + 128 * b₇) =
    (a₀ ^^^ b₀) + 2 * (a₁ ^^^ b₁) + 4 * (a₂ ^^^ b₂) + 8 * (a₃ ^^^ b₃) +
      16 * (a₄ ^^^ b₄) + 32 * (a₅ ^^^ b₅) + 64 * (a₆ ^^^ b₆) + 128 * (a₇ ^^^ b₇) := by
  have nested_a :
      a₀ + 2 * a₁ + 4 * a₂ + 8 * a₃ + 16 * a₄ + 32 * a₅ + 64 * a₆ + 128 * a₇ =
      a₀ + 2 * (a₁ + 2 * (a₂ + 2 * (a₃ + 2 * (a₄ + 2 * (a₅ + 2 * (a₆ + 2 * a₇)))))) := by ring
  have nested_b :
      b₀ + 2 * b₁ + 4 * b₂ + 8 * b₃ + 16 * b₄ + 32 * b₅ + 64 * b₆ + 128 * b₇ =
      b₀ + 2 * (b₁ + 2 * (b₂ + 2 * (b₃ + 2 * (b₄ + 2 * (b₅ + 2 * (b₆ + 2 * b₇)))))) := by ring
  rw [nested_a, nested_b]
  rw [lxor_step _ _ _ _ ha₀ hb₀]
  rw [lxor_step _ _ _ _ ha₁ hb₁]
  rw [lxor_step _ _ _ _ ha₂ hb₂]
  rw [lxor_step _ _ _ _ ha₃ hb₃]
  rw [lxor_step _ _ _ _ ha₄ hb₄]
  rw [lxor_step _ _ _ _ ha₅ hb₅]
  rw [lxor_step _ _ _ _ ha₆ hb₆]
  ring

/-! ### Nat-level bit-wise OR

Closed form for `Nat.lor` (`|||`) of two 8-bit bit-decomposed naturals. -/

/-- Single-bit step for OR: `(a₀ + 2*ra) ||| (b₀ + 2*rb) = (a₀ ||| b₀) + 2*(ra ||| rb)`
    for Boolean `a₀`, `b₀`. -/
private theorem lor_step (a₀ b₀ ra rb : ℕ) (ha : a₀ < 2) (hb : b₀ < 2) :
    (a₀ + 2 * ra) ||| (b₀ + 2 * rb) = (a₀ ||| b₀) + 2 * (ra ||| rb) := by
  have ha' : a₀ < 2 ^ 1 := by simpa using ha
  have hb' : b₀ < 2 ^ 1 := by simpa using hb
  apply Nat.eq_of_testBit_eq
  intro k
  show ((a₀ + 2 * ra) ||| (b₀ + 2 * rb)).testBit k = _
  rw [Nat.testBit_or]
  have ea : a₀ + 2 * ra = 2 ^ 1 * ra + a₀ := by ring
  have eb : b₀ + 2 * rb = 2 ^ 1 * rb + b₀ := by ring
  rw [ea, eb]
  rw [Nat.testBit_two_pow_mul_add _ ha', Nat.testBit_two_pow_mul_add _ hb']
  have hab : (a₀ ||| b₀) < 2 ^ 1 := by
    simp only [pow_one]
    interval_cases a₀ <;> interval_cases b₀ <;> decide
  have erhs : (a₀ ||| b₀) + 2 * (ra ||| rb) = 2 ^ 1 * (ra ||| rb) + (a₀ ||| b₀) := by ring
  rw [erhs, Nat.testBit_two_pow_mul_add _ hab]
  split
  · have hk : k = 0 := by omega
    subst hk
    interval_cases a₀ <;> interval_cases b₀ <;> decide
  · show (ra.testBit (k - 1) || rb.testBit (k - 1)) = (ra ||| rb).testBit (k - 1)
    rw [← Nat.testBit_or]

/-- 8-bit Nat-level bit decomposition of `Nat.lor`. -/
theorem lor_eight_bits
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℕ}
    (ha₀ : a₀ < 2) (ha₁ : a₁ < 2) (ha₂ : a₂ < 2) (ha₃ : a₃ < 2)
    (ha₄ : a₄ < 2) (ha₅ : a₅ < 2) (ha₆ : a₆ < 2) (_ha₇ : a₇ < 2)
    (hb₀ : b₀ < 2) (hb₁ : b₁ < 2) (hb₂ : b₂ < 2) (hb₃ : b₃ < 2)
    (hb₄ : b₄ < 2) (hb₅ : b₅ < 2) (hb₆ : b₆ < 2) (_hb₇ : b₇ < 2) :
    (a₀ + 2 * a₁ + 4 * a₂ + 8 * a₃ + 16 * a₄ + 32 * a₅ + 64 * a₆ + 128 * a₇) |||
    (b₀ + 2 * b₁ + 4 * b₂ + 8 * b₃ + 16 * b₄ + 32 * b₅ + 64 * b₆ + 128 * b₇) =
    (a₀ ||| b₀) + 2 * (a₁ ||| b₁) + 4 * (a₂ ||| b₂) + 8 * (a₃ ||| b₃) +
      16 * (a₄ ||| b₄) + 32 * (a₅ ||| b₅) + 64 * (a₆ ||| b₆) + 128 * (a₇ ||| b₇) := by
  have nested_a :
      a₀ + 2 * a₁ + 4 * a₂ + 8 * a₃ + 16 * a₄ + 32 * a₅ + 64 * a₆ + 128 * a₇ =
      a₀ + 2 * (a₁ + 2 * (a₂ + 2 * (a₃ + 2 * (a₄ + 2 * (a₅ + 2 * (a₆ + 2 * a₇)))))) := by ring
  have nested_b :
      b₀ + 2 * b₁ + 4 * b₂ + 8 * b₃ + 16 * b₄ + 32 * b₅ + 64 * b₆ + 128 * b₇ =
      b₀ + 2 * (b₁ + 2 * (b₂ + 2 * (b₃ + 2 * (b₄ + 2 * (b₅ + 2 * (b₆ + 2 * b₇)))))) := by ring
  rw [nested_a, nested_b]
  rw [lor_step _ _ _ _ ha₀ hb₀]
  rw [lor_step _ _ _ _ ha₁ hb₁]
  rw [lor_step _ _ _ _ ha₂ hb₂]
  rw [lor_step _ _ _ _ ha₃ hb₃]
  rw [lor_step _ _ _ _ ha₄ hb₄]
  rw [lor_step _ _ _ _ ha₅ hb₅]
  rw [lor_step _ _ _ _ ha₆ hb₆]
  ring

/-! ### Bound propagation: product of Booleans is < 2 -/

private theorem bool_mul_val_lt {a b : ZMod p} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a * b).val < 2 := by
  rcases ha with rfl | rfl
  · simp
  · rcases hb with rfl | rfl
    · simp
    · simp [ZMod.val_one]

/-! ### Headline: AND bridge `ZMod → BitVec 8` -/

/-- **Gap T closure for AND.** Given the Gap H bit decomposition constraints
    plus the Gap A per-bit AND constraint activated by `is_and = 1`, the
    Gap 2 `h_table` hypothesis is *derivable*:

      `alu_result = ((spec_and (zmodToBitVec8 alu_operand_a) (zmodToBitVec8 alu_operand_b)).toNat : ZMod p)`.

    All hypotheses are the same equations that `range_*_bridge` and
    `table_constraint_and_bridge` (in `FullSoundness.lean`) extract from
    the `ZKBuilder` monad. -/
theorem and_bv_bridge (hp_big : 256 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_and : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    {r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ZMod p}
    (h_is_and : is_and = 1)
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (hb₀ : b₀ = 0 ∨ b₀ = 1) (hb₁ : b₁ = 0 ∨ b₁ = 1)
    (hb₂ : b₂ = 0 ∨ b₂ = 1) (hb₃ : b₃ = 0 ∨ b₃ = 1)
    (hb₄ : b₄ = 0 ∨ b₄ = 1) (hb₅ : b₅ = 0 ∨ b₅ = 1)
    (hb₆ : b₆ = 0 ∨ b₆ = 1) (hb₇ : b₇ = 0 ∨ b₇ = 1)
    (hr₀ : r₀ = 0 ∨ r₀ = 1) (hr₁ : r₁ = 0 ∨ r₁ = 1)
    (hr₂ : r₂ = 0 ∨ r₂ = 1) (hr₃ : r₃ = 0 ∨ r₃ = 1)
    (hr₄ : r₄ = 0 ∨ r₄ = 1) (hr₅ : r₅ = 0 ∨ r₅ = 1)
    (hr₆ : r₆ = 0 ∨ r₆ = 1) (hr₇ : r₇ = 0 ∨ r₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (hb_sum : alu_operand_b =
      b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64 + b₇ * 128)
    (hr_sum : alu_result =
      r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 + r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128)
    (hbc₀ : is_and * (r₀ - a₀ * b₀) = 0)
    (hbc₁ : is_and * (r₁ - a₁ * b₁) = 0)
    (hbc₂ : is_and * (r₂ - a₂ * b₂) = 0)
    (hbc₃ : is_and * (r₃ - a₃ * b₃) = 0)
    (hbc₄ : is_and * (r₄ - a₄ * b₄) = 0)
    (hbc₅ : is_and * (r₅ - a₅ * b₅) = 0)
    (hbc₆ : is_and * (r₆ - a₆ * b₆) = 0)
    (hbc₇ : is_and * (r₇ - a₇ * b₇) = 0) :
    alu_result = ((spec_and (zmodToBitVec8 alu_operand_a)
                             (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) := by
  -- Step 1: extract r_i = a_i * b_i from the AND constraints (Gap A).
  have e₀ : r₀ = a₀ * b₀ := by
    have := hbc₀; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  have e₁ : r₁ = a₁ * b₁ := by
    have := hbc₁; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  have e₂ : r₂ = a₂ * b₂ := by
    have := hbc₂; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  have e₃ : r₃ = a₃ * b₃ := by
    have := hbc₃; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  have e₄ : r₄ = a₄ * b₄ := by
    have := hbc₄; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  have e₅ : r₅ = a₅ * b₅ := by
    have := hbc₅; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  have e₆ : r₆ = a₆ * b₆ := by
    have := hbc₆; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  have e₇ : r₇ = a₇ * b₇ := by
    have := hbc₇; rw [h_is_and, one_mul] at this; exact sub_eq_zero.mp this
  -- Step 2: transport to Nat via bit_decomp_val_eq.
  have hav := bit_decomp_val_eq hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have hbv := bit_decomp_val_eq hp_big hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have hrv := bit_decomp_val_eq hp_big hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  -- val bounds (≤ 255 since sum of 1+2+4+...+128 = 255).
  have bound : ∀ {x : ZMod p} (hx : x = 0 ∨ x = 1), x.val ≤ 1 := fun hx => bool_val_le_one hx
  have ha_val_le : alu_operand_a.val ≤ 255 := by
    rw [ha_sum, hav]
    have := bound ha₀
    have := bound ha₁; have := bound ha₂; have := bound ha₃; have := bound ha₄
    have := bound ha₅; have := bound ha₆; have := bound ha₇
    omega
  have hb_val_le : alu_operand_b.val ≤ 255 := by
    rw [hb_sum, hbv]
    have := bound hb₀
    have := bound hb₁; have := bound hb₂; have := bound hb₃; have := bound hb₄
    have := bound hb₅; have := bound hb₆; have := bound hb₇
    omega
  -- Step 3: express alu_result.val via Nat.land of alu_operand_a.val and alu_operand_b.val.
  -- From e₀..e₇ and hrv, alu_result.val = a₀*b₀ + 2*a₁*b₁ + ... + 128*a₇*b₇ (in Nat).
  have hr_val_eq : alu_result.val =
      a₀.val * b₀.val + 2 * (a₁.val * b₁.val) + 4 * (a₂.val * b₂.val) +
      8 * (a₃.val * b₃.val) + 16 * (a₄.val * b₄.val) + 32 * (a₅.val * b₅.val) +
      64 * (a₆.val * b₆.val) + 128 * (a₇.val * b₇.val) := by
    rw [hr_sum, hrv, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇]
    -- Need: (a_i * b_i).val = a_i.val * b_i.val
    have bm : ∀ {x y : ZMod p} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1),
        (x * y).val = x.val * y.val := by
      intro x y hx hy
      rcases hx with rfl | rfl
      · simp
      · rcases hy with rfl | rfl
        · simp
        · simp [ZMod.val_one]
    rw [bm ha₀ hb₀, bm ha₁ hb₁, bm ha₂ hb₂, bm ha₃ hb₃,
        bm ha₄ hb₄, bm ha₅ hb₅, bm ha₆ hb₆, bm ha₇ hb₇]
  -- Step 4: Nat.land of the two bit-decomposed sums equals the bit-decomposed product.
  have hland : Nat.land alu_operand_a.val alu_operand_b.val = alu_result.val := by
    rw [hr_val_eq, ha_sum, hav, hb_sum, hbv]
    have l := land_eight_bits
      (a₀ := a₀.val) (a₁ := a₁.val) (a₂ := a₂.val) (a₃ := a₃.val)
      (a₄ := a₄.val) (a₅ := a₅.val) (a₆ := a₆.val) (a₇ := a₇.val)
      (b₀ := b₀.val) (b₁ := b₁.val) (b₂ := b₂.val) (b₃ := b₃.val)
      (b₄ := b₄.val) (b₅ := b₅.val) (b₆ := b₆.val) (b₇ := b₇.val)
      (by have := bound ha₀; omega) (by have := bound ha₁; omega)
      (by have := bound ha₂; omega) (by have := bound ha₃; omega)
      (by have := bound ha₄; omega) (by have := bound ha₅; omega)
      (by have := bound ha₆; omega) (by have := bound ha₇; omega)
      (by have := bound hb₀; omega) (by have := bound hb₁; omega)
      (by have := bound hb₂; omega) (by have := bound hb₃; omega)
      (by have := bound hb₄; omega) (by have := bound hb₅; omega)
      (by have := bound hb₆; omega) (by have := bound hb₇; omega)
    exact l
  -- Step 5: rewrite the RHS using zmodToBitVec8 and BitVec.toNat_and.
  unfold spec_and zmodToBitVec8
  rw [BitVec.toNat_and]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hmod_a : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have hmod_b : alu_operand_b.val % 2 ^ 8 = alu_operand_b.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod_a, hmod_b]
  -- Now: alu_result = ((alu_operand_a.val &&& alu_operand_b.val : ℕ) : ZMod p)
  -- `x &&& y` on Nat is `Nat.land x y`.
  have hbridge : ((alu_operand_a.val &&& alu_operand_b.val : ℕ) : ZMod p) = alu_result := by
    show ((Nat.land alu_operand_a.val alu_operand_b.val : ℕ) : ZMod p) = alu_result
    rw [hland]
    exact ZMod.natCast_zmod_val alu_result
  exact hbridge.symm

/-! ### Headline: XOR bridge `ZMod → BitVec 8` -/

/-- **Gap T closure for XOR.** Given the Gap H bit decomposition constraints
    plus the Gap A per-bit XOR constraint activated by `is_xor = 1`, the
    Gap 2 `h_table` hypothesis is *derivable*:

      `alu_result = ((spec_xor (zmodToBitVec8 alu_operand_a) (zmodToBitVec8 alu_operand_b)).toNat : ZMod p)`.
-/
theorem xor_bv_bridge (hp_big : 256 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_xor : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    {r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ZMod p}
    (h_is_xor : is_xor = 1)
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (hb₀ : b₀ = 0 ∨ b₀ = 1) (hb₁ : b₁ = 0 ∨ b₁ = 1)
    (hb₂ : b₂ = 0 ∨ b₂ = 1) (hb₃ : b₃ = 0 ∨ b₃ = 1)
    (hb₄ : b₄ = 0 ∨ b₄ = 1) (hb₅ : b₅ = 0 ∨ b₅ = 1)
    (hb₆ : b₆ = 0 ∨ b₆ = 1) (hb₇ : b₇ = 0 ∨ b₇ = 1)
    (hr₀ : r₀ = 0 ∨ r₀ = 1) (hr₁ : r₁ = 0 ∨ r₁ = 1)
    (hr₂ : r₂ = 0 ∨ r₂ = 1) (hr₃ : r₃ = 0 ∨ r₃ = 1)
    (hr₄ : r₄ = 0 ∨ r₄ = 1) (hr₅ : r₅ = 0 ∨ r₅ = 1)
    (hr₆ : r₆ = 0 ∨ r₆ = 1) (hr₇ : r₇ = 0 ∨ r₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (hb_sum : alu_operand_b =
      b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64 + b₇ * 128)
    (hr_sum : alu_result =
      r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 + r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128)
    (hbc₀ : is_xor * (r₀ - (a₀ + b₀ - a₀ * b₀ * 2)) = 0)
    (hbc₁ : is_xor * (r₁ - (a₁ + b₁ - a₁ * b₁ * 2)) = 0)
    (hbc₂ : is_xor * (r₂ - (a₂ + b₂ - a₂ * b₂ * 2)) = 0)
    (hbc₃ : is_xor * (r₃ - (a₃ + b₃ - a₃ * b₃ * 2)) = 0)
    (hbc₄ : is_xor * (r₄ - (a₄ + b₄ - a₄ * b₄ * 2)) = 0)
    (hbc₅ : is_xor * (r₅ - (a₅ + b₅ - a₅ * b₅ * 2)) = 0)
    (hbc₆ : is_xor * (r₆ - (a₆ + b₆ - a₆ * b₆ * 2)) = 0)
    (hbc₇ : is_xor * (r₇ - (a₇ + b₇ - a₇ * b₇ * 2)) = 0) :
    alu_result = ((spec_xor (zmodToBitVec8 alu_operand_a)
                             (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) := by
  -- Step 1: extract r_i = a_i + b_i - a_i * b_i * 2 (Gap A).
  have e₀ : r₀ = a₀ + b₀ - a₀ * b₀ * 2 := by
    have := hbc₀; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  have e₁ : r₁ = a₁ + b₁ - a₁ * b₁ * 2 := by
    have := hbc₁; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  have e₂ : r₂ = a₂ + b₂ - a₂ * b₂ * 2 := by
    have := hbc₂; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  have e₃ : r₃ = a₃ + b₃ - a₃ * b₃ * 2 := by
    have := hbc₃; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  have e₄ : r₄ = a₄ + b₄ - a₄ * b₄ * 2 := by
    have := hbc₄; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  have e₅ : r₅ = a₅ + b₅ - a₅ * b₅ * 2 := by
    have := hbc₅; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  have e₆ : r₆ = a₆ + b₆ - a₆ * b₆ * 2 := by
    have := hbc₆; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  have e₇ : r₇ = a₇ + b₇ - a₇ * b₇ * 2 := by
    have := hbc₇; rw [h_is_xor, one_mul] at this; exact sub_eq_zero.mp this
  -- Step 2: bit decomposition val equations.
  have hav := bit_decomp_val_eq hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have hbv := bit_decomp_val_eq hp_big hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have hrv := bit_decomp_val_eq hp_big hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  -- val bounds (≤ 255).
  have bound : ∀ {x : ZMod p} (hx : x = 0 ∨ x = 1), x.val ≤ 1 := fun hx => bool_val_le_one hx
  have ha_val_le : alu_operand_a.val ≤ 255 := by
    rw [ha_sum, hav]
    have := bound ha₀
    have := bound ha₁; have := bound ha₂; have := bound ha₃; have := bound ha₄
    have := bound ha₅; have := bound ha₆; have := bound ha₇
    omega
  have hb_val_le : alu_operand_b.val ≤ 255 := by
    rw [hb_sum, hbv]
    have := bound hb₀
    have := bound hb₁; have := bound hb₂; have := bound hb₃; have := bound hb₄
    have := bound hb₅; have := bound hb₆; have := bound hb₇
    omega
  -- Step 3: express alu_result.val as bit-decomposed XOR.
  have hr_val_eq : alu_result.val =
      (a₀.val ^^^ b₀.val) + 2 * (a₁.val ^^^ b₁.val) + 4 * (a₂.val ^^^ b₂.val) +
      8 * (a₃.val ^^^ b₃.val) + 16 * (a₄.val ^^^ b₄.val) + 32 * (a₅.val ^^^ b₅.val) +
      64 * (a₆.val ^^^ b₆.val) + 128 * (a₇.val ^^^ b₇.val) := by
    rw [hr_sum, hrv, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇]
    rw [val_xor_bool ha₀ hb₀, val_xor_bool ha₁ hb₁, val_xor_bool ha₂ hb₂,
        val_xor_bool ha₃ hb₃, val_xor_bool ha₄ hb₄, val_xor_bool ha₅ hb₅,
        val_xor_bool ha₆ hb₆, val_xor_bool ha₇ hb₇]
  -- Step 4: Nat.xor of the two bit-decomposed sums equals the result val.
  have hlxor : alu_operand_a.val ^^^ alu_operand_b.val = alu_result.val := by
    rw [hr_val_eq, ha_sum, hav, hb_sum, hbv]
    exact lxor_eight_bits
      (by have := bound ha₀; omega) (by have := bound ha₁; omega)
      (by have := bound ha₂; omega) (by have := bound ha₃; omega)
      (by have := bound ha₄; omega) (by have := bound ha₅; omega)
      (by have := bound ha₆; omega) (by have := bound ha₇; omega)
      (by have := bound hb₀; omega) (by have := bound hb₁; omega)
      (by have := bound hb₂; omega) (by have := bound hb₃; omega)
      (by have := bound hb₄; omega) (by have := bound hb₅; omega)
      (by have := bound hb₆; omega) (by have := bound hb₇; omega)
  -- Step 5: rewrite RHS using zmodToBitVec8 and BitVec.toNat_xor.
  unfold spec_xor zmodToBitVec8
  rw [BitVec.toNat_xor]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hmod_a : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have hmod_b : alu_operand_b.val % 2 ^ 8 = alu_operand_b.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod_a, hmod_b]
  have hbridge : ((alu_operand_a.val ^^^ alu_operand_b.val : ℕ) : ZMod p) = alu_result := by
    rw [hlxor]
    exact ZMod.natCast_zmod_val alu_result
  exact hbridge.symm

/-! ### Headline: OR bridge `ZMod → BitVec 8` -/

/-- **Gap T closure for OR.** Given the Gap H bit decomposition constraints
    plus the Gap A per-bit OR constraint activated by `is_or = 1`, the
    Gap 2 `h_table` hypothesis is *derivable*:

      `alu_result = ((spec_or (zmodToBitVec8 alu_operand_a) (zmodToBitVec8 alu_operand_b)).toNat : ZMod p)`.
-/
theorem or_bv_bridge (hp_big : 256 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_or : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    {b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ZMod p}
    {r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ZMod p}
    (h_is_or : is_or = 1)
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (hb₀ : b₀ = 0 ∨ b₀ = 1) (hb₁ : b₁ = 0 ∨ b₁ = 1)
    (hb₂ : b₂ = 0 ∨ b₂ = 1) (hb₃ : b₃ = 0 ∨ b₃ = 1)
    (hb₄ : b₄ = 0 ∨ b₄ = 1) (hb₅ : b₅ = 0 ∨ b₅ = 1)
    (hb₆ : b₆ = 0 ∨ b₆ = 1) (hb₇ : b₇ = 0 ∨ b₇ = 1)
    (hr₀ : r₀ = 0 ∨ r₀ = 1) (hr₁ : r₁ = 0 ∨ r₁ = 1)
    (hr₂ : r₂ = 0 ∨ r₂ = 1) (hr₃ : r₃ = 0 ∨ r₃ = 1)
    (hr₄ : r₄ = 0 ∨ r₄ = 1) (hr₅ : r₅ = 0 ∨ r₅ = 1)
    (hr₆ : r₆ = 0 ∨ r₆ = 1) (hr₇ : r₇ = 0 ∨ r₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (hb_sum : alu_operand_b =
      b₀ + b₁ * 2 + b₂ * 4 + b₃ * 8 + b₄ * 16 + b₅ * 32 + b₆ * 64 + b₇ * 128)
    (hr_sum : alu_result =
      r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 + r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128)
    (hbc₀ : is_or * (r₀ - (a₀ + b₀ - a₀ * b₀)) = 0)
    (hbc₁ : is_or * (r₁ - (a₁ + b₁ - a₁ * b₁)) = 0)
    (hbc₂ : is_or * (r₂ - (a₂ + b₂ - a₂ * b₂)) = 0)
    (hbc₃ : is_or * (r₃ - (a₃ + b₃ - a₃ * b₃)) = 0)
    (hbc₄ : is_or * (r₄ - (a₄ + b₄ - a₄ * b₄)) = 0)
    (hbc₅ : is_or * (r₅ - (a₅ + b₅ - a₅ * b₅)) = 0)
    (hbc₆ : is_or * (r₆ - (a₆ + b₆ - a₆ * b₆)) = 0)
    (hbc₇ : is_or * (r₇ - (a₇ + b₇ - a₇ * b₇)) = 0) :
    alu_result = ((spec_or (zmodToBitVec8 alu_operand_a)
                            (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) := by
  -- Step 1: extract r_i = a_i + b_i - a_i * b_i (Gap A).
  have e₀ : r₀ = a₀ + b₀ - a₀ * b₀ := by
    have := hbc₀; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  have e₁ : r₁ = a₁ + b₁ - a₁ * b₁ := by
    have := hbc₁; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  have e₂ : r₂ = a₂ + b₂ - a₂ * b₂ := by
    have := hbc₂; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  have e₃ : r₃ = a₃ + b₃ - a₃ * b₃ := by
    have := hbc₃; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  have e₄ : r₄ = a₄ + b₄ - a₄ * b₄ := by
    have := hbc₄; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  have e₅ : r₅ = a₅ + b₅ - a₅ * b₅ := by
    have := hbc₅; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  have e₆ : r₆ = a₆ + b₆ - a₆ * b₆ := by
    have := hbc₆; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  have e₇ : r₇ = a₇ + b₇ - a₇ * b₇ := by
    have := hbc₇; rw [h_is_or, one_mul] at this; exact sub_eq_zero.mp this
  -- Step 2: bit decomposition val equations.
  have hav := bit_decomp_val_eq hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have hbv := bit_decomp_val_eq hp_big hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
  have hrv := bit_decomp_val_eq hp_big hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have bound : ∀ {x : ZMod p} (hx : x = 0 ∨ x = 1), x.val ≤ 1 := fun hx => bool_val_le_one hx
  have ha_val_le : alu_operand_a.val ≤ 255 := by
    rw [ha_sum, hav]
    have := bound ha₀
    have := bound ha₁; have := bound ha₂; have := bound ha₃; have := bound ha₄
    have := bound ha₅; have := bound ha₆; have := bound ha₇
    omega
  have hb_val_le : alu_operand_b.val ≤ 255 := by
    rw [hb_sum, hbv]
    have := bound hb₀
    have := bound hb₁; have := bound hb₂; have := bound hb₃; have := bound hb₄
    have := bound hb₅; have := bound hb₆; have := bound hb₇
    omega
  -- Step 3: express alu_result.val as bit-decomposed OR.
  have hr_val_eq : alu_result.val =
      (a₀.val ||| b₀.val) + 2 * (a₁.val ||| b₁.val) + 4 * (a₂.val ||| b₂.val) +
      8 * (a₃.val ||| b₃.val) + 16 * (a₄.val ||| b₄.val) + 32 * (a₅.val ||| b₅.val) +
      64 * (a₆.val ||| b₆.val) + 128 * (a₇.val ||| b₇.val) := by
    rw [hr_sum, hrv, e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇]
    rw [val_or_bool ha₀ hb₀, val_or_bool ha₁ hb₁, val_or_bool ha₂ hb₂,
        val_or_bool ha₃ hb₃, val_or_bool ha₄ hb₄, val_or_bool ha₅ hb₅,
        val_or_bool ha₆ hb₆, val_or_bool ha₇ hb₇]
  -- Step 4: Nat.lor of the two bit-decomposed sums equals the result val.
  have hlor : alu_operand_a.val ||| alu_operand_b.val = alu_result.val := by
    rw [hr_val_eq, ha_sum, hav, hb_sum, hbv]
    exact lor_eight_bits
      (by have := bound ha₀; omega) (by have := bound ha₁; omega)
      (by have := bound ha₂; omega) (by have := bound ha₃; omega)
      (by have := bound ha₄; omega) (by have := bound ha₅; omega)
      (by have := bound ha₆; omega) (by have := bound ha₇; omega)
      (by have := bound hb₀; omega) (by have := bound hb₁; omega)
      (by have := bound hb₂; omega) (by have := bound hb₃; omega)
      (by have := bound hb₄; omega) (by have := bound hb₅; omega)
      (by have := bound hb₆; omega) (by have := bound hb₇; omega)
  -- Step 5: rewrite RHS using zmodToBitVec8 and BitVec.toNat_or.
  unfold spec_or zmodToBitVec8
  rw [BitVec.toNat_or]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hmod_a : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have hmod_b : alu_operand_b.val % 2 ^ 8 = alu_operand_b.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod_a, hmod_b]
  have hbridge : ((alu_operand_a.val ||| alu_operand_b.val : ℕ) : ZMod p) = alu_result := by
    rw [hlor]
    exact ZMod.natCast_zmod_val alu_result
  exact hbridge.symm

/-! ### Headline: ADD bridge `ZMod → BitVec 8`

Closes Gap A for ADD via the value-level carry decomposition. Unlike
the bit-level AND/XOR/OR bridges, this one works directly on the ZMod
operands and the carry flag, requiring only the field-level carry
equation `is_add * (a + b - r - c * 256) = 0` plus a Boolean
constraint on `flag_c` and the range bounds (which the caller obtains
from the existing Gap H bit decomposition). -/

/-- Pure-Nat helper: from `a + b = r + c * 256` with all four bounded,
    derive `r = (a + b) % 256`. -/
private theorem add_carry_decomp_nat
    (a b r c : ℕ) (h_a : a ≤ 255) (h_b : b ≤ 255) (h_r : r ≤ 255)
    (h_c : c ≤ 1) (h_eq : a + b = r + c * 256) :
    r = (a + b) % 256 := by
  interval_cases c
  all_goals omega

/-- **Gap T closure for ADD.** Given the value-level carry equation
    activated by `is_add = 1`, a Boolean witness for `flag_c`, and the
    Gap H range bounds on `alu_operand_a` / `alu_operand_b` /
    `alu_result`, the Gap 2 `h_table` hypothesis is *derivable*:

      `alu_result = ((spec_add (zmodToBitVec8 alu_operand_a) (zmodToBitVec8 alu_operand_b)).toNat : ZMod p)`.

    Requires `512 < p` (one bit larger than AND/XOR/OR's `256 < p`)
    because the Nat lift of `alu_operand_a.val + alu_operand_b.val`
    can reach 510. -/
theorem add_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_add flag_c : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_b_le : alu_operand_b.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_add : is_add = 1)
    (h_carry : is_add *
      (alu_operand_a + alu_operand_b - alu_result - flag_c * 256) = 0)
    (h_c_bool : flag_c * (flag_c - 1) = 0) :
    alu_result = ((spec_add (zmodToBitVec8 alu_operand_a)
                             (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) := by
  -- Activate the conditional carry equation.
  rw [h_is_add, one_mul] at h_carry
  have h_eq : alu_operand_a + alu_operand_b = alu_result + flag_c * 256 := by
    linear_combination h_carry
  -- Boolean fact for flag_c.
  have hc : flag_c = 0 ∨ flag_c = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : flag_c.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  -- (256 : ZMod p).val = 256 (using p > 256).
  have h_256_val : ((256 : ZMod p)).val = 256 := by
    have heq : (256 : ZMod p) = ((256 : ℕ) : ZMod p) := by norm_cast
    rw [heq, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  -- Lift the LHS of h_eq to Nat.
  have h_lhs_val : (alu_operand_a + alu_operand_b).val =
      alu_operand_a.val + alu_operand_b.val := by
    apply ZMod.val_add_of_lt
    omega
  -- Lift `flag_c * 256` to Nat.
  have h_c256_val : (flag_c * 256).val = flag_c.val * 256 := by
    rcases hc with rfl | rfl
    · simp
    · rw [one_mul, ZMod.val_one]
      simpa using h_256_val
  -- Lift the RHS of h_eq to Nat.
  have h_rhs_val : (alu_result + flag_c * 256).val =
      alu_result.val + flag_c.val * 256 := by
    rw [ZMod.val_add_of_lt, h_c256_val]
    rw [h_c256_val]
    omega
  -- Combine: a.val + b.val = r.val + c.val * 256 (Nat equation).
  have h_nat : alu_operand_a.val + alu_operand_b.val =
      alu_result.val + flag_c.val * 256 := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  -- Apply the Nat-level decomposition lemma.
  have h_r_mod : alu_result.val =
      (alu_operand_a.val + alu_operand_b.val) % 256 :=
    add_carry_decomp_nat _ _ _ _ h_a_le h_b_le h_r_le hc_val h_nat
  -- Convert to the BitVec spec.
  unfold spec_add zmodToBitVec8
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_b_mod : alu_operand_b.val % 2 ^ 8 = alu_operand_b.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod, h_b_mod]
  show alu_result =
      ((((alu_operand_a.val + alu_operand_b.val) % 2 ^ 8 : ℕ)) : ZMod p)
  rw [show (2 : ℕ) ^ 8 = 256 from rfl, ← h_r_mod]
  exact (ZMod.natCast_zmod_val _).symm

/-! ### Headline: SUB bridge `ZMod → BitVec 8`

Closes Gap A for SUB via the borrow-decomposition equation, mirroring
`add_bv_bridge`. The constraint shape comes from the existing
`carry_sub` sub-gadget pattern:

  `is_sub * (alu_operand_a + flag_c * 256 - alu_result - alu_operand_b) = 0`

where `flag_c = 1` indicates a borrow occurred. -/

/-- Pure-Nat helper: from `a + c * 256 = r + b` with bounded operands,
    derive `r = (a + 256 - b) % 256`. -/
private theorem sub_carry_decomp_nat
    (a b r c : ℕ) (h_a : a ≤ 255) (h_b : b ≤ 255) (h_r : r ≤ 255)
    (h_c : c ≤ 1) (h_eq : a + c * 256 = r + b) :
    r = (a + 256 - b) % 256 := by
  interval_cases c
  all_goals omega

/-- **Gap T closure for SUB.** Mirror of `add_bv_bridge`. -/
theorem sub_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_sub flag_c : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_b_le : alu_operand_b.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_sub : is_sub = 1)
    (h_borrow : is_sub *
      (alu_operand_a + flag_c * 256 - alu_result - alu_operand_b) = 0)
    (h_c_bool : flag_c * (flag_c - 1) = 0) :
    alu_result = ((spec_sub (zmodToBitVec8 alu_operand_a)
                             (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) := by
  -- Activate the borrow equation.
  rw [h_is_sub, one_mul] at h_borrow
  have h_eq : alu_operand_a + flag_c * 256 = alu_result + alu_operand_b := by
    linear_combination h_borrow
  -- Boolean fact for flag_c.
  have hc : flag_c = 0 ∨ flag_c = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : flag_c.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  -- (256 : ZMod p).val = 256.
  have h_256_val : ((256 : ZMod p)).val = 256 := by
    have heq : (256 : ZMod p) = ((256 : ℕ) : ZMod p) := by norm_cast
    rw [heq, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  -- (flag_c * 256).val = flag_c.val * 256.
  have h_c256_val : (flag_c * 256).val = flag_c.val * 256 := by
    rcases hc with rfl | rfl
    · simp
    · rw [one_mul, ZMod.val_one]
      simpa using h_256_val
  -- LHS lift: (alu_operand_a + flag_c * 256).val = alu_operand_a.val + flag_c.val * 256.
  have h_lhs_val : (alu_operand_a + flag_c * 256).val =
      alu_operand_a.val + flag_c.val * 256 := by
    rw [ZMod.val_add_of_lt, h_c256_val]
    rw [h_c256_val]
    omega
  -- RHS lift: (alu_result + alu_operand_b).val = alu_result.val + alu_operand_b.val.
  have h_rhs_val : (alu_result + alu_operand_b).val =
      alu_result.val + alu_operand_b.val := by
    apply ZMod.val_add_of_lt
    omega
  -- Combine: a.val + c.val * 256 = r.val + b.val (Nat).
  have h_nat : alu_operand_a.val + flag_c.val * 256 =
      alu_result.val + alu_operand_b.val := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  -- Apply the Nat-level decomposition.
  have h_r_mod : alu_result.val =
      (alu_operand_a.val + 256 - alu_operand_b.val) % 256 :=
    sub_carry_decomp_nat _ _ _ _ h_a_le h_b_le h_r_le hc_val h_nat
  -- Convert to BitVec spec.
  unfold spec_sub zmodToBitVec8
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_b_mod : alu_operand_b.val % 2 ^ 8 = alu_operand_b.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod, h_b_mod]
  -- Goal: alu_result = ((2^8 - alu_operand_b.val + alu_operand_a.val) % 2^8 : ZMod p)
  rw [show (2 : ℕ) ^ 8 = 256 from rfl]
  -- Rewrite to a form matching `h_r_mod` (Nat operations are commutative).
  rw [show 256 - alu_operand_b.val + alu_operand_a.val =
       alu_operand_a.val + 256 - alu_operand_b.val by omega]
  rw [← h_r_mod]
  exact (ZMod.natCast_zmod_val _).symm

/-! ### Headline: INC and DEC bridges -/

private theorem inc_carry_decomp_nat
    (a r c : ℕ) (h_a : a ≤ 255) (h_r : r ≤ 255) (h_c : c ≤ 1)
    (h_eq : a + 1 = r + c * 256) :
    r = (a + 1) % 256 := by
  interval_cases c
  all_goals omega

/-- **Gap T closure for INC.** Mirror of `add_bv_bridge` with `b = 1`. -/
theorem inc_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_inc inc_overflow : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_inc : is_inc = 1)
    (h_inc : is_inc * (alu_operand_a + 1 - alu_result - inc_overflow * 256) = 0)
    (h_c_bool : inc_overflow * (inc_overflow - 1) = 0) :
    alu_result = ((spec_inc (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_inc, one_mul] at h_inc
  have h_eq : alu_operand_a + 1 = alu_result + inc_overflow * 256 := by
    linear_combination h_inc
  have hc : inc_overflow = 0 ∨ inc_overflow = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : inc_overflow.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have h_256_val : ((256 : ZMod p)).val = 256 := by
    have heq : (256 : ZMod p) = ((256 : ℕ) : ZMod p) := by norm_cast
    rw [heq, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have h_1_val : ((1 : ZMod p)).val = 1 := ZMod.val_one p
  -- LHS: (alu_operand_a + 1).val = alu_operand_a.val + 1.
  have h_lhs_val : (alu_operand_a + 1).val = alu_operand_a.val + 1 := by
    rw [ZMod.val_add_of_lt, h_1_val]
    rw [h_1_val]; omega
  -- inc_overflow * 256 lift.
  have h_c256_val : (inc_overflow * 256).val = inc_overflow.val * 256 := by
    rcases hc with rfl | rfl
    · simp
    · rw [one_mul, ZMod.val_one]
      simpa using h_256_val
  -- RHS lift.
  have h_rhs_val : (alu_result + inc_overflow * 256).val =
      alu_result.val + inc_overflow.val * 256 := by
    rw [ZMod.val_add_of_lt, h_c256_val]
    rw [h_c256_val]
    omega
  have h_nat : alu_operand_a.val + 1 =
      alu_result.val + inc_overflow.val * 256 := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val = (alu_operand_a.val + 1) % 256 :=
    inc_carry_decomp_nat _ _ _ h_a_le h_r_le hc_val h_nat
  -- Convert to BitVec spec.
  unfold spec_inc zmodToBitVec8
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h_one_toNat : (1 : BitVec 8).toNat = 1 := by decide
  rw [h_one_toNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl]
  rw [← h_r_mod]
  exact (ZMod.natCast_zmod_val _).symm

private theorem dec_carry_decomp_nat
    (a r c : ℕ) (h_a : a ≤ 255) (h_r : r ≤ 255) (h_c : c ≤ 1)
    (h_eq : a + c * 256 = r + 1) :
    r = (a + 256 - 1) % 256 := by
  interval_cases c
  all_goals omega

/-- **Gap T closure for DEC.** Mirror of `sub_bv_bridge` with `b = 1`. -/
theorem dec_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_dec inc_overflow : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_dec : is_dec = 1)
    (h_dec : is_dec * (alu_operand_a + inc_overflow * 256 - alu_result - 1) = 0)
    (h_c_bool : inc_overflow * (inc_overflow - 1) = 0) :
    alu_result = ((spec_dec (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_dec, one_mul] at h_dec
  have h_eq : alu_operand_a + inc_overflow * 256 = alu_result + 1 := by
    linear_combination h_dec
  have hc : inc_overflow = 0 ∨ inc_overflow = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : inc_overflow.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have h_256_val : ((256 : ZMod p)).val = 256 := by
    have heq : (256 : ZMod p) = ((256 : ℕ) : ZMod p) := by norm_cast
    rw [heq, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have h_1_val : ((1 : ZMod p)).val = 1 := ZMod.val_one p
  have h_c256_val : (inc_overflow * 256).val = inc_overflow.val * 256 := by
    rcases hc with rfl | rfl
    · simp
    · rw [one_mul, ZMod.val_one]
      simpa using h_256_val
  have h_lhs_val : (alu_operand_a + inc_overflow * 256).val =
      alu_operand_a.val + inc_overflow.val * 256 := by
    rw [ZMod.val_add_of_lt, h_c256_val]
    rw [h_c256_val]
    omega
  have h_rhs_val : (alu_result + 1).val = alu_result.val + 1 := by
    rw [ZMod.val_add_of_lt, h_1_val]
    rw [h_1_val]; omega
  have h_nat : alu_operand_a.val + inc_overflow.val * 256 =
      alu_result.val + 1 := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val = (alu_operand_a.val + 256 - 1) % 256 :=
    dec_carry_decomp_nat _ _ _ h_a_le h_r_le hc_val h_nat
  -- Convert to BitVec spec. spec_dec a = a - 1, and BitVec.toNat_sub gives
  -- (a - 1).toNat = (a.toNat + (2^8 - 1)) % 2^8 = (a.toNat + 255) % 256.
  unfold spec_dec zmodToBitVec8
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h_one_toNat : (1 : BitVec 8).toNat = 1 := by decide
  rw [h_one_toNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl]
  -- Goal: alu_result = ((256 - 1 + alu_operand_a.val) % 256 : ZMod p)
  rw [show 256 - 1 + alu_operand_a.val = alu_operand_a.val + 256 - 1 by omega]
  rw [← h_r_mod]
  exact (ZMod.natCast_zmod_val _).symm

/-! ### Shifts, rotates, and SWAP

The next batch of bridges closes Gap T for the unary shift/rotate ops
in the binary-ALU block: SLA, SRL, RLC, RRC, SRA, SWAP. They all share
the same skeleton:
1. Activate the value-level constraint via `is_<op> = 1`.
2. Lift the ZMod equation to a Nat equation using `ZMod.val_*` lemmas.
3. Use `interval_cases` or `omega` to derive `alu_result.val = <Nat formula>`.
4. Convert the Nat formula to the BitVec spec via the relevant
   `BitVec.toNat_*` lemma.

Each requires `512 < p` so the Nat lift is well-defined. -/

/-- (256 : ZMod p).val = 256 helper, used by all shift bridges. -/
private theorem zmod_256_val_eq {p : ℕ} [Fact p.Prime] (hp_big : 512 < p) :
    ((256 : ZMod p)).val = 256 := by
  have heq : (256 : ZMod p) = ((256 : ℕ) : ZMod p) := by norm_cast
  rw [heq, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

/-- (a * 2).val = a.val * 2 when 2*a fits, used by SLA and rotates. -/
private theorem zmod_mul_two_val {p : ℕ} [Fact p.Prime] (hp_big : 512 < p)
    {a : ZMod p} (h_a_le : a.val ≤ 255) :
    (a * 2).val = a.val * 2 := by
  have heq : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_cast
  rw [heq, ZMod.val_mul, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (show 2 < p by omega)]
  apply Nat.mod_eq_of_lt
  omega

/-! ### Standalone BitVec spec lemmas

These connect the `spec_*` BitVec functions to their pure-Nat formulas.
Each is a single rewrite chain. Used by the corresponding `*_bv_bridge`. -/

private theorem spec_sla_toNat (bv : BitVec 8) :
    (spec_sla bv).toNat = (bv.toNat * 2) % 256 := by
  unfold spec_sla
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_one]

private theorem spec_srl_toNat (bv : BitVec 8) :
    (spec_srl bv).toNat = bv.toNat / 2 := by
  unfold spec_srl
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, pow_one]

/-! ### Spec lemmas for RLC, RRC, SRA, SWAP via BitVec addition

The trick: each of these spec functions is defined using `|||` over
non-overlapping bit ranges. Since the bits don't overlap, `OR = ADD`
at the BitVec level, and `bv_decide` can prove the BitVec equality. -/

private theorem spec_rlc_eq_add (bv : BitVec 8) :
    spec_rlc bv = bv * 2#8 + bv >>> 7 := by
  unfold spec_rlc
  bv_decide

private theorem spec_rrc_eq_add (bv : BitVec 8) :
    spec_rrc bv = bv >>> 1 + bv <<< 7 := by
  unfold spec_rrc
  bv_decide

private theorem spec_sra_eq_add (bv : BitVec 8) :
    spec_sra bv = bv >>> 1 + (bv >>> 7) * 128#8 := by
  unfold spec_sra
  bv_decide

private theorem spec_swap_eq_add (bv : BitVec 8) :
    spec_swap bv = bv >>> 4 + bv <<< 4 := by
  unfold spec_swap
  bv_decide

/-- `(spec_rlc bv).toNat = (bv.toNat * 2 + bv.toNat / 128) % 256` — derived
    from the BitVec addition form via `BitVec.toNat_add` etc. -/
private theorem spec_rlc_toNat (bv : BitVec 8) :
    (spec_rlc bv).toNat = (bv.toNat * 2 + bv.toNat / 128) % 256 := by
  rw [spec_rlc_eq_add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight]
  rw [show (2#8 : BitVec 8).toNat = 2 from rfl]
  rw [Nat.shiftRight_eq_div_pow]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 7 = 128 from rfl]
  -- ((bv.toNat * 2) % 256 + bv.toNat / 128) % 256 = (bv.toNat * 2 + bv.toNat / 128) % 256
  omega

private theorem spec_rrc_toNat (bv : BitVec 8) :
    (spec_rrc bv).toNat = (bv.toNat / 2 + (bv.toNat % 2) * 128) % 256 := by
  rw [spec_rrc_eq_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, pow_one]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 7 = 128 from rfl]
  have h_bv : bv.toNat < 256 := bv.isLt
  have h_par : bv.toNat * 128 % 256 = (bv.toNat % 2) * 128 := by omega
  rw [h_par]

private theorem spec_sra_toNat (bv : BitVec 8) :
    (spec_sra bv).toNat = (bv.toNat / 2 + (bv.toNat / 128) * 128) % 256 := by
  rw [spec_sra_eq_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_mul, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 7 = 128 from rfl,
      show (2 : ℕ) ^ 1 = 2 from rfl]
  rw [show (128#8 : BitVec 8).toNat = 128 from rfl]
  have h_bv : bv.toNat < 256 := bv.isLt
  have h_div : bv.toNat / 128 ≤ 1 := by omega
  have h_mul_lt : bv.toNat / 128 * 128 < 256 := by
    have : bv.toNat / 128 * 128 ≤ 128 := by
      calc bv.toNat / 128 * 128 ≤ 1 * 128 := Nat.mul_le_mul_right _ h_div
        _ = 128 := by ring
    omega
  rw [Nat.mod_eq_of_lt h_mul_lt]

private theorem spec_swap_toNat (bv : BitVec 8) :
    (spec_swap bv).toNat = (bv.toNat / 16 + (bv.toNat % 16) * 16) % 256 := by
  rw [spec_swap_eq_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 4 = 16 from rfl]
  -- (bv.toNat / 16 + bv.toNat * 16 % 256) % 256 = (bv.toNat / 16 + bv.toNat % 16 * 16) % 256
  have h : bv.toNat * 16 % 256 = (bv.toNat % 16) * 16 := by omega
  rw [h]

/-! ### SLA bridge -/

private theorem sla_decomp_nat (a r c : ℕ) (_h_a : a ≤ 255) (_h_r : r ≤ 255) (h_c : c ≤ 1)
    (h_eq : a * 2 = r + c * 256) : r = a * 2 % 256 := by
  interval_cases c
  all_goals omega

/-- **Gap T closure for SLA.** -/
theorem sla_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_sla flag_c : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_sla : is_sla = 1)
    (h_carry : is_sla *
      (alu_operand_a * 2 - alu_result - flag_c * 256) = 0)
    (h_c_bool : flag_c * (flag_c - 1) = 0) :
    alu_result = ((spec_sla (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_sla, one_mul] at h_carry
  have h_eq : alu_operand_a * 2 = alu_result + flag_c * 256 := by
    linear_combination h_carry
  have hc : flag_c = 0 ∨ flag_c = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : flag_c.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  have h_a2_val := zmod_mul_two_val hp_big h_a_le
  have h_c256_val : (flag_c * 256).val = flag_c.val * 256 := by
    rcases hc with rfl | rfl
    · simp
    · rw [one_mul, ZMod.val_one]; simpa using h_256_val
  have h_rhs_val : (alu_result + flag_c * 256).val =
      alu_result.val + flag_c.val * 256 := by
    rw [ZMod.val_add_of_lt, h_c256_val]
    rw [h_c256_val]; omega
  have h_nat : alu_operand_a.val * 2 = alu_result.val + flag_c.val * 256 := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_a2_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val = alu_operand_a.val * 2 % 256 :=
    sla_decomp_nat _ _ _ h_a_le h_r_le hc_val h_nat
  -- BitVec spec: spec_sla a = a <<< 1, (a <<< 1).toNat = (a.toNat * 2) % 256
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_sla_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]

/-! ### SRL bridge -/

private theorem srl_decomp_nat (a r c : ℕ) (_h_a : a ≤ 255) (_h_r : r ≤ 255) (_h_c : c ≤ 1)
    (h_eq : a = r * 2 + c) : r = a / 2 := by
  omega

/-- **Gap T closure for SRL.** -/
theorem srl_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_srl flag_c : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_srl : is_srl = 1)
    (h_eq_constr : is_srl *
      (alu_operand_a - alu_result * 2 - flag_c) = 0)
    (h_c_bool : flag_c * (flag_c - 1) = 0) :
    alu_result = ((spec_srl (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_srl, one_mul] at h_eq_constr
  have h_eq : alu_operand_a = alu_result * 2 + flag_c := by
    linear_combination h_eq_constr
  have hc : flag_c = 0 ∨ flag_c = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : flag_c.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have h_r2_val := zmod_mul_two_val hp_big h_r_le
  have h_rhs_val : (alu_result * 2 + flag_c).val = alu_result.val * 2 + flag_c.val := by
    rw [ZMod.val_add_of_lt, h_r2_val]
    rw [h_r2_val]; omega
  have h_nat : alu_operand_a.val = alu_result.val * 2 + flag_c.val := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_rhs_val] at hcong
    exact hcong
  have h_r_eq : alu_result.val = alu_operand_a.val / 2 :=
    srl_decomp_nat _ _ _ h_a_le h_r_le hc_val h_nat
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_eq]
  congr 1
  rw [spec_srl_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]

/-! ### Helpers: bit values from full bit decomposition -/

private theorem bit7_eq_div_128 {p : ℕ} [Fact p.Prime] (hp_big : 256 < p)
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1) :
    (a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128).val / 128 = a₇.val := by
  rw [bit_decomp_val_eq hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇]
  have h0 := bool_val_le_one ha₀
  have h1 := bool_val_le_one ha₁
  have h2 := bool_val_le_one ha₂
  have h3 := bool_val_le_one ha₃
  have h4 := bool_val_le_one ha₄
  have h5 := bool_val_le_one ha₅
  have h6 := bool_val_le_one ha₆
  have h7 := bool_val_le_one ha₇
  omega

private theorem bit0_eq_mod_2 {p : ℕ} [Fact p.Prime] (hp_big : 256 < p)
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1) :
    (a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128).val % 2 = a₀.val := by
  rw [bit_decomp_val_eq hp_big ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇]
  have h0 := bool_val_le_one ha₀
  have h1 := bool_val_le_one ha₁
  have h2 := bool_val_le_one ha₂
  have h3 := bool_val_le_one ha₃
  have h4 := bool_val_le_one ha₄
  have h5 := bool_val_le_one ha₅
  have h6 := bool_val_le_one ha₆
  have h7 := bool_val_le_one ha₇
  omega

/-! ### CCF bv_bridge (identity on accumulator) -/

theorem ccf_bv_bridge {p : ℕ} [Fact p.Prime] (_hp_big : 256 < p)
    {alu_operand_a alu_result : ZMod p} {is_ccf : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_is_ccf : is_ccf = 1)
    (h_eq : is_ccf * (alu_result - alu_operand_a) = 0) :
    alu_result = ((spec_ccf (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_ccf, one_mul] at h_eq
  have h_ar : alu_result = alu_operand_a := sub_eq_zero.mp h_eq
  rw [h_ar]
  unfold spec_ccf
  exact (zmodToBitVec8_cast_bounded h_a_le).symm

/-! ### SCF bv_bridge (identity on accumulator) -/

theorem scf_bv_bridge {p : ℕ} [Fact p.Prime] (_hp_big : 256 < p)
    {alu_operand_a alu_result : ZMod p} {is_scf : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_is_scf : is_scf = 1)
    (h_eq : is_scf * (alu_result - alu_operand_a) = 0) :
    alu_result = ((spec_scf (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_scf, one_mul] at h_eq
  have h_ar : alu_result = alu_operand_a := sub_eq_zero.mp h_eq
  rw [h_ar]
  unfold spec_scf
  exact (zmodToBitVec8_cast_bounded h_a_le).symm

/-! ### CPL bv_bridge -/

private theorem spec_cpl_eq_sub (bv : BitVec 8) : spec_cpl bv = 255#8 - bv := by
  unfold spec_cpl
  bv_decide

private theorem spec_cpl_toNat (bv : BitVec 8) :
    (spec_cpl bv).toNat = 255 - bv.toNat := by
  rw [spec_cpl_eq_sub, BitVec.toNat_sub]
  rw [show (255#8 : BitVec 8).toNat = 255 from rfl]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl]
  have h : bv.toNat < 256 := bv.isLt
  omega

theorem cpl_bv_bridge {p : ℕ} [Fact p.Prime] (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p} {is_cpl : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_cpl : is_cpl = 1)
    (h_eq : is_cpl * (alu_operand_a + alu_result - 255) = 0) :
    alu_result = ((spec_cpl (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_cpl, one_mul] at h_eq
  have h_sum : alu_operand_a + alu_result = 255 := by linear_combination h_eq
  -- Lift to Nat
  have h_lhs_val : (alu_operand_a + alu_result).val =
      alu_operand_a.val + alu_result.val := by
    apply ZMod.val_add_of_lt; omega
  have h_255_val : ((255 : ZMod p)).val = 255 := by
    have heq : (255 : ZMod p) = ((255 : ℕ) : ZMod p) := by norm_cast
    rw [heq, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have h_nat : alu_operand_a.val + alu_result.val = 255 := by
    have hcong := congrArg ZMod.val h_sum
    rw [h_lhs_val, h_255_val] at hcong
    exact hcong
  have h_r_eq : alu_result.val = 255 - alu_operand_a.val := by omega
  -- Convert to spec
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_eq]
  congr 1
  rw [spec_cpl_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]

/-! ### CP bv_bridge (alias for SUB) -/

theorem cp_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_cp flag_c : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_b_le : alu_operand_b.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_cp : is_cp = 1)
    (h_borrow : is_cp *
      (alu_operand_a + flag_c * 256 - alu_result - alu_operand_b) = 0)
    (h_c_bool : flag_c * (flag_c - 1) = 0) :
    alu_result = ((spec_cp (zmodToBitVec8 alu_operand_a)
                            (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) := by
  -- spec_cp = spec_sub, so reuse sub_bv_bridge
  unfold spec_cp
  exact sub_bv_bridge hp_big h_a_le h_b_le h_r_le h_is_cp h_borrow h_c_bool

/-! ### ADC bv_bridge -/

private theorem adc_decomp_nat (a b r c_in c_out : ℕ)
    (_h_a : a ≤ 255) (_h_b : b ≤ 255) (_h_r : r ≤ 255)
    (_h_c_in : c_in ≤ 1) (_h_c_out : c_out ≤ 1)
    (h_eq : a + b + c_in = r + c_out * 256) : r = (a + b + c_in) % 256 := by
  interval_cases c_out
  all_goals omega

private theorem spec_adc_toNat_local (a b c : BitVec 8) :
    (spec_adc a b c).toNat = (a.toNat + b.toNat + c.toNat) % 256 := by
  unfold spec_adc
  rw [BitVec.toNat_add, BitVec.toNat_add]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl]
  have h_a : a.toNat < 256 := a.isLt
  have h_b : b.toNat < 256 := b.isLt
  have h_c : c.toNat < 256 := c.isLt
  omega

private theorem spec_sbc_toNat_local (a b c : BitVec 8) :
    (spec_sbc a b c).toNat = (a.toNat + 512 - b.toNat - c.toNat) % 256 := by
  unfold spec_sbc
  rw [BitVec.toNat_sub, BitVec.toNat_sub]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl]
  have h_a : a.toNat < 256 := a.isLt
  have h_b : b.toNat < 256 := b.isLt
  have h_c : c.toNat < 256 := c.isLt
  omega

theorem adc_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_adc carry_in flag_c : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_b_le : alu_operand_b.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_adc : is_adc = 1)
    (h_carry : is_adc *
      (alu_operand_a + alu_operand_b + carry_in - alu_result - flag_c * 256) = 0)
    (h_cin_bool : carry_in * (carry_in - 1) = 0)
    (h_c_bool : flag_c * (flag_c - 1) = 0) :
    alu_result = ((spec_adc (zmodToBitVec8 alu_operand_a)
                             (zmodToBitVec8 alu_operand_b)
                             (zmodToBitVec8 carry_in)).toNat : ZMod p) := by
  rw [h_is_adc, one_mul] at h_carry
  have h_eq : alu_operand_a + alu_operand_b + carry_in = alu_result + flag_c * 256 := by
    linear_combination h_carry
  have hc_in : carry_in = 0 ∨ carry_in = 1 := by
    rcases mul_eq_zero.mp h_cin_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hcin_val : carry_in.val ≤ 1 := by
    rcases hc_in with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have hc : flag_c = 0 ∨ flag_c = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : flag_c.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  -- Lift each side to Nat
  have h_ab_val : (alu_operand_a + alu_operand_b).val =
      alu_operand_a.val + alu_operand_b.val := by
    apply ZMod.val_add_of_lt; omega
  have h_lhs_val : (alu_operand_a + alu_operand_b + carry_in).val =
      alu_operand_a.val + alu_operand_b.val + carry_in.val := by
    rw [ZMod.val_add_of_lt, h_ab_val]
    rw [h_ab_val]; omega
  have h_c256_val : (flag_c * 256).val = flag_c.val * 256 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]; exact h_256_val
  have h_rhs_val : (alu_result + flag_c * 256).val =
      alu_result.val + flag_c.val * 256 := by
    rw [ZMod.val_add_of_lt, h_c256_val]
    rw [h_c256_val]; omega
  have h_nat : alu_operand_a.val + alu_operand_b.val + carry_in.val =
      alu_result.val + flag_c.val * 256 := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val =
      (alu_operand_a.val + alu_operand_b.val + carry_in.val) % 256 :=
    adc_decomp_nat _ _ _ _ _ h_a_le h_b_le h_r_le hcin_val hc_val h_nat
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_adc_toNat_local]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_b_mod : alu_operand_b.val % 2 ^ 8 = alu_operand_b.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_cin_mod : carry_in.val % 2 ^ 8 = carry_in.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod, h_b_mod, h_cin_mod]

/-! ### SBC bv_bridge -/

private theorem sbc_decomp_nat (a b r c_in c_out : ℕ)
    (_h_a : a ≤ 255) (_h_b : b ≤ 255) (_h_r : r ≤ 255)
    (_h_c_in : c_in ≤ 1) (_h_c_out : c_out ≤ 1)
    (h_eq : a + c_out * 256 = r + b + c_in) :
    r = (a + 512 - b - c_in) % 256 := by
  interval_cases c_out
  all_goals omega

theorem sbc_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_operand_b alu_result : ZMod p}
    {is_sbc carry_in flag_c : ZMod p}
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_b_le : alu_operand_b.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_sbc : is_sbc = 1)
    (h_borrow : is_sbc *
      (alu_operand_a + flag_c * 256 - alu_result - alu_operand_b - carry_in) = 0)
    (h_cin_bool : carry_in * (carry_in - 1) = 0)
    (h_c_bool : flag_c * (flag_c - 1) = 0) :
    alu_result = ((spec_sbc (zmodToBitVec8 alu_operand_a)
                             (zmodToBitVec8 alu_operand_b)
                             (zmodToBitVec8 carry_in)).toNat : ZMod p) := by
  rw [h_is_sbc, one_mul] at h_borrow
  have h_eq : alu_operand_a + flag_c * 256 = alu_result + alu_operand_b + carry_in := by
    linear_combination h_borrow
  have hc_in : carry_in = 0 ∨ carry_in = 1 := by
    rcases mul_eq_zero.mp h_cin_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hcin_val : carry_in.val ≤ 1 := by
    rcases hc_in with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have hc : flag_c = 0 ∨ flag_c = 1 := by
    rcases mul_eq_zero.mp h_c_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hc_val : flag_c.val ≤ 1 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  have h_c256_val : (flag_c * 256).val = flag_c.val * 256 := by
    rcases hc with rfl | rfl
    · simp
    · simp [ZMod.val_one]; exact h_256_val
  have h_lhs_val : (alu_operand_a + flag_c * 256).val =
      alu_operand_a.val + flag_c.val * 256 := by
    rw [ZMod.val_add_of_lt, h_c256_val]
    rw [h_c256_val]; omega
  have h_rb_val : (alu_result + alu_operand_b).val =
      alu_result.val + alu_operand_b.val := by
    apply ZMod.val_add_of_lt; omega
  have h_rhs_val : (alu_result + alu_operand_b + carry_in).val =
      alu_result.val + alu_operand_b.val + carry_in.val := by
    rw [ZMod.val_add_of_lt, h_rb_val]
    rw [h_rb_val]; omega
  have h_nat : alu_operand_a.val + flag_c.val * 256 =
      alu_result.val + alu_operand_b.val + carry_in.val := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val =
      (alu_operand_a.val + 512 - alu_operand_b.val - carry_in.val) % 256 :=
    sbc_decomp_nat _ _ _ _ _ h_a_le h_b_le h_r_le hcin_val hc_val (by omega)
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_sbc_toNat_local]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_b_mod : alu_operand_b.val % 2 ^ 8 = alu_operand_b.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_cin_mod : carry_in.val % 2 ^ 8 = carry_in.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod, h_b_mod, h_cin_mod]

/-! ### RL bv_bridge -/

private theorem spec_rl_eq_add (bv c : BitVec 8) :
    spec_rl bv c = bv * 2#8 + (c &&& 1#8) := by
  unfold spec_rl
  bv_decide

private theorem spec_rl_toNat (bv c : BitVec 8) :
    (spec_rl bv c).toNat = (bv.toNat * 2 + c.toNat % 2) % 256 := by
  rw [spec_rl_eq_add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_and]
  rw [show (2#8 : BitVec 8).toNat = 2 from rfl, show (1#8 : BitVec 8).toNat = 1 from rfl]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl]
  have h_bv : bv.toNat < 256 := bv.isLt
  have h_c : c.toNat < 256 := c.isLt
  -- Need: (bv.toNat * 2 % 256 + bv.toNat &&& 1) % 256 = (bv.toNat * 2 + c.toNat % 2) % 256
  -- Wait that's wrong, the &&& is on c
  have h_and : c.toNat &&& 1 = c.toNat % 2 := by
    rcases Nat.mod_two_eq_zero_or_one c.toNat with h0 | h1
    · -- c.toNat is even
      have : c.toNat &&& 1 = 0 := by
        have : c.toNat = 2 * (c.toNat / 2) := by omega
        rw [this]
        simp [Nat.and_one_is_mod]
      rw [this, h0]
    · -- c.toNat is odd
      have : c.toNat &&& 1 = 1 := by
        simp [Nat.and_one_is_mod]
        omega
      rw [this, h1]
  rw [h_and]
  omega

private theorem rl_decomp_nat (a r b7 c_in : ℕ)
    (_h_a : a ≤ 255) (_h_r : r ≤ 255) (_h_b7 : b7 ≤ 1) (_h_c_in : c_in ≤ 1)
    (h_eq : a * 2 + c_in = r + b7 * 256) :
    r = (a * 2 + c_in) % 256 := by
  interval_cases b7
  all_goals omega

theorem rl_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_rl carry_in flag_c : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_rl : is_rl = 1)
    (h_flag_eq : is_rl * (flag_c - a₇) = 0)
    (h_rot : is_rl * (alu_operand_a * 2 + carry_in - alu_result - a₇ * 256) = 0)
    (h_cin_bool : carry_in * (carry_in - 1) = 0) :
    alu_result = ((spec_rl (zmodToBitVec8 alu_operand_a)
                            (zmodToBitVec8 carry_in)).toNat : ZMod p) := by
  rw [h_is_rl, one_mul] at h_flag_eq h_rot
  have h_eq : alu_operand_a * 2 + carry_in = alu_result + a₇ * 256 := by
    linear_combination h_rot
  have h7_val : a₇.val ≤ 1 := bool_val_le_one ha₇
  have hc_in : carry_in = 0 ∨ carry_in = 1 := by
    rcases mul_eq_zero.mp h_cin_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hcin_val : carry_in.val ≤ 1 := by
    rcases hc_in with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have hp_256 : 256 < p := by omega
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  have h_a2_val := zmod_mul_two_val hp_big h_a_le
  have h_a7_256_val : (a₇ * 256).val = a₇.val * 256 := by
    rcases ha₇ with rfl | rfl
    · simp
    · simp [ZMod.val_one]; exact h_256_val
  have h_lhs_val : (alu_operand_a * 2 + carry_in).val =
      alu_operand_a.val * 2 + carry_in.val := by
    rw [ZMod.val_add_of_lt, h_a2_val]
    rw [h_a2_val]; omega
  have h_rhs_val : (alu_result + a₇ * 256).val = alu_result.val + a₇.val * 256 := by
    rw [ZMod.val_add_of_lt, h_a7_256_val]
    rw [h_a7_256_val]; omega
  have h_nat : alu_operand_a.val * 2 + carry_in.val = alu_result.val + a₇.val * 256 := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val = (alu_operand_a.val * 2 + carry_in.val) % 256 :=
    rl_decomp_nat _ _ _ _ h_a_le h_r_le h7_val hcin_val h_nat
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_rl_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_cin_mod : carry_in.val % 2 ^ 8 = carry_in.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod, h_cin_mod]
  -- Goal: (alu_operand_a.val * 2 + carry_in.val) % 256 = (alu_operand_a.val * 2 + carry_in.val % 2) % 256
  have h_cin_mod2 : carry_in.val % 2 = carry_in.val := by omega
  rw [h_cin_mod2]

/-! ### RR bv_bridge -/

private theorem spec_rr_eq_add (bv c : BitVec 8) :
    spec_rr bv c = bv >>> 1 + (c &&& 1#8) <<< 7 := by
  unfold spec_rr
  bv_decide

private theorem spec_rr_toNat (bv c : BitVec 8) :
    (spec_rr bv c).toNat = (bv.toNat / 2 + (c.toNat % 2) * 128) % 256 := by
  rw [spec_rr_eq_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_and]
  rw [show (1#8 : BitVec 8).toNat = 1 from rfl]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, pow_one]
  rw [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 7 = 128 from rfl]
  have h_bv : bv.toNat < 256 := bv.isLt
  have h_c : c.toNat < 256 := c.isLt
  have h_and : c.toNat &&& 1 = c.toNat % 2 := by
    rcases Nat.mod_two_eq_zero_or_one c.toNat with h0 | h1
    · have : c.toNat &&& 1 = 0 := by
        have : c.toNat = 2 * (c.toNat / 2) := by omega
        rw [this]
        simp [Nat.and_one_is_mod]
      rw [this, h0]
    · have : c.toNat &&& 1 = 1 := by
        simp [Nat.and_one_is_mod]; omega
      rw [this, h1]
  rw [h_and]
  have h_par : c.toNat % 2 * 128 % 256 = (c.toNat % 2) * 128 := by
    have : c.toNat % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  rw [h_par]

private theorem rr_decomp_nat (a r b0 c_in : ℕ)
    (_h_a : a ≤ 255) (_h_r : r ≤ 255) (_h_b0 : b0 ≤ 1) (_h_c_in : c_in ≤ 1)
    (h_eq : a + c_in * 256 = r * 2 + b0) :
    r = (a / 2 + c_in * 128) % 256 := by
  interval_cases c_in
  all_goals omega

theorem rr_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_rr carry_in flag_c : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_rr : is_rr = 1)
    (h_flag_eq : is_rr * (flag_c - a₀) = 0)
    (h_rot : is_rr * (alu_operand_a + carry_in * 256 - alu_result * 2 - a₀) = 0)
    (h_cin_bool : carry_in * (carry_in - 1) = 0) :
    alu_result = ((spec_rr (zmodToBitVec8 alu_operand_a)
                            (zmodToBitVec8 carry_in)).toNat : ZMod p) := by
  rw [h_is_rr, one_mul] at h_flag_eq h_rot
  have h_eq : alu_operand_a + carry_in * 256 = alu_result * 2 + a₀ := by
    linear_combination h_rot
  have h0_val : a₀.val ≤ 1 := bool_val_le_one ha₀
  have hc_in : carry_in = 0 ∨ carry_in = 1 := by
    rcases mul_eq_zero.mp h_cin_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hcin_val : carry_in.val ≤ 1 := by
    rcases hc_in with rfl | rfl
    · simp
    · simp [ZMod.val_one]
  have hp_256 : 256 < p := by omega
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  have h_r2_val := zmod_mul_two_val hp_big h_r_le
  have h_cin_256_val : (carry_in * 256).val = carry_in.val * 256 := by
    rcases hc_in with rfl | rfl
    · simp
    · simp [ZMod.val_one]; exact h_256_val
  have h_lhs_val : (alu_operand_a + carry_in * 256).val =
      alu_operand_a.val + carry_in.val * 256 := by
    rw [ZMod.val_add_of_lt, h_cin_256_val]
    rw [h_cin_256_val]; omega
  have h_rhs_val : (alu_result * 2 + a₀).val = alu_result.val * 2 + a₀.val := by
    rw [ZMod.val_add_of_lt, h_r2_val]
    rw [h_r2_val]; omega
  have h_nat : alu_operand_a.val + carry_in.val * 256 = alu_result.val * 2 + a₀.val := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val = (alu_operand_a.val / 2 + carry_in.val * 128) % 256 :=
    rr_decomp_nat _ _ _ _ h_a_le h_r_le h0_val hcin_val h_nat
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_rr_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  have h_cin_mod : carry_in.val % 2 ^ 8 = carry_in.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod, h_cin_mod]
  -- Goal: (a/2 + cin*128) % 256 = (a/2 + (cin%2)*128) % 256
  have h_cin_mod2 : carry_in.val % 2 = carry_in.val := by omega
  rw [h_cin_mod2]

/-! ### RLC bv_bridge -/

private theorem rlc_decomp_nat (a r b7 : ℕ) (_h_a : a ≤ 255) (_h_r : r ≤ 255) (_h_b7 : b7 ≤ 1)
    (h_eq : a * 2 + b7 = r + b7 * 256) : r = (a * 2 + b7) % 256 := by
  interval_cases b7
  all_goals omega

/-- **Gap T closure for RLC.** -/
theorem rlc_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_rlc flag_c : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_rlc : is_rlc = 1)
    (h_flag_eq : is_rlc * (flag_c - a₇) = 0)
    (h_rot : is_rlc * (alu_operand_a * 2 + a₇ - alu_result - a₇ * 256) = 0) :
    alu_result = ((spec_rlc (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_rlc, one_mul] at h_flag_eq h_rot
  have h_eq : alu_operand_a * 2 + a₇ = alu_result + a₇ * 256 := by
    linear_combination h_rot
  have h7_val : a₇.val ≤ 1 := bool_val_le_one ha₇
  have hp_256 : 256 < p := by omega
  have h_a7_eq : alu_operand_a.val / 128 = a₇.val := by
    rw [ha_sum]
    exact bit7_eq_div_128 hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  have h_a2_val := zmod_mul_two_val hp_big h_a_le
  have h_a7_256_val : (a₇ * 256).val = a₇.val * 256 := by
    rcases ha₇ with rfl | rfl
    · simp
    · simp [ZMod.val_one]; exact h_256_val
  have h_lhs_val : (alu_operand_a * 2 + a₇).val = alu_operand_a.val * 2 + a₇.val := by
    rw [ZMod.val_add_of_lt, h_a2_val]
    rw [h_a2_val]; omega
  have h_rhs_val : (alu_result + a₇ * 256).val = alu_result.val + a₇.val * 256 := by
    rw [ZMod.val_add_of_lt, h_a7_256_val]
    rw [h_a7_256_val]; omega
  have h_nat : alu_operand_a.val * 2 + a₇.val = alu_result.val + a₇.val * 256 := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val = (alu_operand_a.val * 2 + a₇.val) % 256 :=
    rlc_decomp_nat _ _ _ h_a_le h_r_le h7_val h_nat
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_rlc_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod, h_a7_eq]

/-! ### RRC bv_bridge -/

private theorem rrc_decomp_nat (a r b0 : ℕ) (_h_a : a ≤ 255) (_h_r : r ≤ 255) (_h_b0 : b0 ≤ 1)
    (h_eq : a + b0 * 256 = r * 2 + b0) : r = (a / 2 + (a % 2) * 128) % 256 := by
  interval_cases b0
  all_goals omega

/-- **Gap T closure for RRC.** -/
theorem rrc_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_rrc flag_c : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_rrc : is_rrc = 1)
    (h_flag_eq : is_rrc * (flag_c - a₀) = 0)
    (h_rot : is_rrc * (alu_operand_a + a₀ * 256 - alu_result * 2 - a₀) = 0) :
    alu_result = ((spec_rrc (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_rrc, one_mul] at h_flag_eq h_rot
  have h_eq : alu_operand_a + a₀ * 256 = alu_result * 2 + a₀ := by
    linear_combination h_rot
  have h0_val : a₀.val ≤ 1 := bool_val_le_one ha₀
  have hp_256 : 256 < p := by omega
  have h_a0_eq : alu_operand_a.val % 2 = a₀.val := by
    rw [ha_sum]
    exact bit0_eq_mod_2 hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  have h_r2_val := zmod_mul_two_val hp_big h_r_le
  have h_a0_256_val : (a₀ * 256).val = a₀.val * 256 := by
    rcases ha₀ with rfl | rfl
    · simp
    · simp [ZMod.val_one]; exact h_256_val
  have h_lhs_val : (alu_operand_a + a₀ * 256).val = alu_operand_a.val + a₀.val * 256 := by
    rw [ZMod.val_add_of_lt, h_a0_256_val]
    rw [h_a0_256_val]; omega
  have h_rhs_val : (alu_result * 2 + a₀).val = alu_result.val * 2 + a₀.val := by
    rw [ZMod.val_add_of_lt, h_r2_val]
    rw [h_r2_val]; omega
  have h_nat : alu_operand_a.val + a₀.val * 256 = alu_result.val * 2 + a₀.val := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val = (alu_operand_a.val / 2 + (alu_operand_a.val % 2) * 128) % 256 :=
    rrc_decomp_nat _ _ _ h_a_le h_r_le h0_val h_nat
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_rrc_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]

/-! ### SRA bv_bridge -/

private theorem sra_decomp_nat (a r b7 b0 : ℕ) (_h_a : a ≤ 255) (_h_r : r ≤ 255)
    (_h_b7 : b7 ≤ 1) (_h_b0 : b0 ≤ 1) (h_a_high : a / 128 = b7) (h_a_low : a % 2 = b0)
    (h_eq : a + b7 * 256 = r * 2 + b0) :
    r = (a / 2 + (a / 128) * 128) % 256 := by
  subst h_a_high
  subst h_a_low
  omega

/-- **Gap T closure for SRA.** -/
theorem sra_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_sra flag_c : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (h_a_le : alu_operand_a.val ≤ 255)
    (h_r_le : alu_result.val ≤ 255)
    (h_is_sra : is_sra = 1)
    (h_flag_eq : is_sra * (flag_c - a₀) = 0)
    (h_shift : is_sra * (alu_operand_a + a₇ * 256 - alu_result * 2 - flag_c) = 0) :
    alu_result = ((spec_sra (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  rw [h_is_sra, one_mul] at h_flag_eq h_shift
  have h_flag : flag_c = a₀ := by linear_combination h_flag_eq
  rw [h_flag] at h_shift
  have h_eq : alu_operand_a + a₇ * 256 = alu_result * 2 + a₀ := by
    linear_combination h_shift
  have h0_val : a₀.val ≤ 1 := bool_val_le_one ha₀
  have h7_val : a₇.val ≤ 1 := bool_val_le_one ha₇
  have hp_256 : 256 < p := by omega
  have h_a7_eq : alu_operand_a.val / 128 = a₇.val := by
    rw [ha_sum]
    exact bit7_eq_div_128 hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_a0_eq : alu_operand_a.val % 2 = a₀.val := by
    rw [ha_sum]
    exact bit0_eq_mod_2 hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_256_val := zmod_256_val_eq (p := p) hp_big
  have h_r2_val := zmod_mul_two_val hp_big h_r_le
  have h_a7_256_val : (a₇ * 256).val = a₇.val * 256 := by
    rcases ha₇ with rfl | rfl
    · simp
    · simp [ZMod.val_one]; exact h_256_val
  have h_lhs_val : (alu_operand_a + a₇ * 256).val = alu_operand_a.val + a₇.val * 256 := by
    rw [ZMod.val_add_of_lt, h_a7_256_val]
    rw [h_a7_256_val]; omega
  have h_rhs_val : (alu_result * 2 + a₀).val = alu_result.val * 2 + a₀.val := by
    rw [ZMod.val_add_of_lt, h_r2_val]
    rw [h_r2_val]; omega
  have h_nat : alu_operand_a.val + a₇.val * 256 = alu_result.val * 2 + a₀.val := by
    have hcong := congrArg ZMod.val h_eq
    rw [h_lhs_val, h_rhs_val] at hcong
    exact hcong
  have h_r_mod : alu_result.val =
      (alu_operand_a.val / 2 + (alu_operand_a.val / 128) * 128) % 256 :=
    sra_decomp_nat _ _ _ _ h_a_le h_r_le h7_val h0_val h_a7_eq h_a0_eq h_nat
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_r_mod]
  congr 1
  rw [spec_sra_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]

/-! ### SWAP bv_bridge -/

private theorem swap_decomp_nat
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℕ)
    (ha₀ : a₀ ≤ 1) (ha₁ : a₁ ≤ 1) (ha₂ : a₂ ≤ 1) (ha₃ : a₃ ≤ 1)
    (ha₄ : a₄ ≤ 1) (ha₅ : a₅ ≤ 1) (ha₆ : a₆ ≤ 1) (ha₇ : a₇ ≤ 1) :
    a₄ + 2 * a₅ + 4 * a₆ + 8 * a₇ + 16 * a₀ + 32 * a₁ + 64 * a₂ + 128 * a₃ =
    ((a₀ + 2*a₁ + 4*a₂ + 8*a₃ + 16*a₄ + 32*a₅ + 64*a₆ + 128*a₇) / 16 +
     ((a₀ + 2*a₁ + 4*a₂ + 8*a₃ + 16*a₄ + 32*a₅ + 64*a₆ + 128*a₇) % 16) * 16) % 256 := by
  set lo := a₀ + 2*a₁ + 4*a₂ + 8*a₃ with hlo
  set hi := a₄ + 2*a₅ + 4*a₆ + 8*a₇ with hhi
  have h_eq : a₀ + 2*a₁ + 4*a₂ + 8*a₃ + 16*a₄ + 32*a₅ + 64*a₆ + 128*a₇ = lo + 16*hi := by
    simp [lo, hi]; ring
  rw [h_eq]
  have h_lo_lt : lo < 16 := by simp [lo]; omega
  have h_hi_lt : hi < 16 := by simp [hi]; omega
  have h_div : (lo + 16*hi) / 16 = hi := by omega
  have h_mod : (lo + 16*hi) % 16 = lo := by omega
  rw [h_div, h_mod]
  show a₄ + 2 * a₅ + 4 * a₆ + 8 * a₇ + 16 * a₀ + 32 * a₁ + 64 * a₂ + 128 * a₃ = (hi + lo * 16) % 256
  have h_total_lt : hi + lo * 16 < 256 := by omega
  rw [Nat.mod_eq_of_lt h_total_lt]
  simp [hi, lo]
  ring

/-- **Gap T closure for SWAP.** -/
theorem swap_bv_bridge (hp_big : 512 < p)
    {alu_operand_a alu_result : ZMod p}
    {is_swap : ZMod p}
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ZMod p}
    {r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ZMod p}
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (hr₀ : r₀ = 0 ∨ r₀ = 1) (hr₁ : r₁ = 0 ∨ r₁ = 1)
    (hr₂ : r₂ = 0 ∨ r₂ = 1) (hr₃ : r₃ = 0 ∨ r₃ = 1)
    (hr₄ : r₄ = 0 ∨ r₄ = 1) (hr₅ : r₅ = 0 ∨ r₅ = 1)
    (hr₆ : r₆ = 0 ∨ r₆ = 1) (hr₇ : r₇ = 0 ∨ r₇ = 1)
    (ha_sum : alu_operand_a =
      a₀ + a₁ * 2 + a₂ * 4 + a₃ * 8 + a₄ * 16 + a₅ * 32 + a₆ * 64 + a₇ * 128)
    (hr_sum : alu_result =
      r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 + r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128)
    (h_is_swap : is_swap = 1)
    (hbc₀ : is_swap * (r₀ - a₄) = 0) (hbc₁ : is_swap * (r₁ - a₅) = 0)
    (hbc₂ : is_swap * (r₂ - a₆) = 0) (hbc₃ : is_swap * (r₃ - a₇) = 0)
    (hbc₄ : is_swap * (r₄ - a₀) = 0) (hbc₅ : is_swap * (r₅ - a₁) = 0)
    (hbc₆ : is_swap * (r₆ - a₂) = 0) (hbc₇ : is_swap * (r₇ - a₃) = 0) :
    alu_result = ((spec_swap (zmodToBitVec8 alu_operand_a)).toNat : ZMod p) := by
  -- Activate constraints, get r_i = a_(i⊕4) in ZMod
  have e₀ : r₀ = a₄ := by
    have := hbc₀; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  have e₁ : r₁ = a₅ := by
    have := hbc₁; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  have e₂ : r₂ = a₆ := by
    have := hbc₂; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  have e₃ : r₃ = a₇ := by
    have := hbc₃; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  have e₄ : r₄ = a₀ := by
    have := hbc₄; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  have e₅ : r₅ = a₁ := by
    have := hbc₅; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  have e₆ : r₆ = a₂ := by
    have := hbc₆; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  have e₇ : r₇ = a₃ := by
    have := hbc₇; rw [h_is_swap, one_mul] at this; exact sub_eq_zero.mp this
  -- Lift to .val
  have hp_256 : 256 < p := by omega
  have h_r_val : alu_result.val =
      r₀.val + 2 * r₁.val + 4 * r₂.val + 8 * r₃.val +
      16 * r₄.val + 32 * r₅.val + 64 * r₆.val + 128 * r₇.val := by
    rw [hr_sum]
    exact bit_decomp_val_eq hp_256 hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
  have h_a_val : alu_operand_a.val =
      a₀.val + 2 * a₁.val + 4 * a₂.val + 8 * a₃.val +
      16 * a₄.val + 32 * a₅.val + 64 * a₆.val + 128 * a₇.val := by
    rw [ha_sum]
    exact bit_decomp_val_eq hp_256 ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
  have h_a_le : alu_operand_a.val ≤ 255 := by
    rw [h_a_val]
    have h0 := bool_val_le_one ha₀
    have h1 := bool_val_le_one ha₁
    have h2 := bool_val_le_one ha₂
    have h3 := bool_val_le_one ha₃
    have h4 := bool_val_le_one ha₄
    have h5 := bool_val_le_one ha₅
    have h6 := bool_val_le_one ha₆
    have h7 := bool_val_le_one ha₇
    omega
  -- Substitute the bit equalities (.val)
  have e₀' : r₀.val = a₄.val := by rw [e₀]
  have e₁' : r₁.val = a₅.val := by rw [e₁]
  have e₂' : r₂.val = a₆.val := by rw [e₂]
  have e₃' : r₃.val = a₇.val := by rw [e₃]
  have e₄' : r₄.val = a₀.val := by rw [e₄]
  have e₅' : r₅.val = a₁.val := by rw [e₅]
  have e₆' : r₆.val = a₂.val := by rw [e₆]
  have e₇' : r₇.val = a₃.val := by rw [e₇]
  -- Now apply the Nat-level decomposition
  have h_nat_eq : alu_result.val =
      (alu_operand_a.val / 16 + (alu_operand_a.val % 16) * 16) % 256 := by
    rw [h_r_val, h_a_val]
    rw [e₀', e₁', e₂', e₃', e₄', e₅', e₆', e₇']
    exact swap_decomp_nat _ _ _ _ _ _ _ _
      (bool_val_le_one ha₀) (bool_val_le_one ha₁) (bool_val_le_one ha₂) (bool_val_le_one ha₃)
      (bool_val_le_one ha₄) (bool_val_le_one ha₅) (bool_val_le_one ha₆) (bool_val_le_one ha₇)
  have h_target : ((alu_result.val : ℕ) : ZMod p) = alu_result :=
    ZMod.natCast_zmod_val alu_result
  rw [← h_target, h_nat_eq]
  congr 1
  rw [spec_swap_toNat]
  unfold zmodToBitVec8
  rw [BitVec.toNat_ofNat]
  have h_a_mod : alu_operand_a.val % 2 ^ 8 = alu_operand_a.val :=
    Nat.mod_eq_of_lt (by omega)
  rw [h_a_mod]

/-! ### DAA polynomial bridge

DAA is the single unary opcode whose output depends not only on the operand
but also on three Boolean input flags (`N`, `H`, `C`) from the previous op.
Its spec `spec_daa` uses nested conditional logic; the constraint system
encodes the same logic as a closed-form polynomial over 11 Boolean inputs
(8 operand bits + 3 flag witnesses).
-/

/-- The DAA polynomial, specialized to `ZMod p`. Mirrors `daa_poly_from_step`
    from `Constraints.lean` but operates on 11 explicit `ZMod p` values. -/
def daa_poly_val (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ N H C : ZMod p) : ZMod p :=
  let notN := 1 - N
  let lo_gt9 := a₃ * (a₂ + a₁ - a₂ * a₁)
  let adj_lo_cond := notN * lo_gt9
  let adj_lo := adj_lo_cond + H - adj_lo_cond * H
  let hi_ge10 := a₇ * (a₆ + a₅ - a₆ * a₅)
  let hi_eq9 := a₄ * (1 - a₅) * (1 - a₆) * a₇
  let a_gt99 := hi_ge10 + hi_eq9 * lo_gt9 - hi_ge10 * hi_eq9 * lo_gt9
  let adj_hi_cond := notN * a_gt99
  let adj_hi := adj_hi_cond + C - adj_hi_cond * C
  let off0 : ZMod p := 0
  let off1 := adj_lo
  let off2 := adj_lo
  let off3 : ZMod p := 0
  let off4 : ZMod p := 0
  let off5 := adj_hi
  let off6 := adj_hi
  let off7 : ZMod p := 0
  let b0 := off0 + N - 2 * off0 * N
  let b1 := off1 + N - 2 * off1 * N
  let b2 := off2 + N - 2 * off2 * N
  let b3 := off3 + N - 2 * off3 * N
  let b4 := off4 + N - 2 * off4 * N
  let b5 := off5 + N - 2 * off5 * N
  let b6 := off6 + N - 2 * off6 * N
  let b7 := off7 + N - 2 * off7 * N
  let cin : ZMod p := N
  let rc_c0 := cin
  let rc_ab0 := a₀ * b0
  let rc_ac0 := a₀ * rc_c0
  let rc_bc0 := b0 * rc_c0
  let rc_abc0 := rc_ab0 * rc_c0
  let rc_s0 := a₀ + b0 + rc_c0 - 2 * (rc_ab0 + rc_ac0 + rc_bc0) + 4 * rc_abc0
  let rc_c1 := rc_ab0 + rc_ac0 + rc_bc0 - 2 * rc_abc0
  let rc_ab1 := a₁ * b1
  let rc_ac1 := a₁ * rc_c1
  let rc_bc1 := b1 * rc_c1
  let rc_abc1 := rc_ab1 * rc_c1
  let rc_s1 := a₁ + b1 + rc_c1 - 2 * (rc_ab1 + rc_ac1 + rc_bc1) + 4 * rc_abc1
  let rc_c2 := rc_ab1 + rc_ac1 + rc_bc1 - 2 * rc_abc1
  let rc_ab2 := a₂ * b2
  let rc_ac2 := a₂ * rc_c2
  let rc_bc2 := b2 * rc_c2
  let rc_abc2 := rc_ab2 * rc_c2
  let rc_s2 := a₂ + b2 + rc_c2 - 2 * (rc_ab2 + rc_ac2 + rc_bc2) + 4 * rc_abc2
  let rc_c3 := rc_ab2 + rc_ac2 + rc_bc2 - 2 * rc_abc2
  let rc_ab3 := a₃ * b3
  let rc_ac3 := a₃ * rc_c3
  let rc_bc3 := b3 * rc_c3
  let rc_abc3 := rc_ab3 * rc_c3
  let rc_s3 := a₃ + b3 + rc_c3 - 2 * (rc_ab3 + rc_ac3 + rc_bc3) + 4 * rc_abc3
  let rc_c4 := rc_ab3 + rc_ac3 + rc_bc3 - 2 * rc_abc3
  let rc_ab4 := a₄ * b4
  let rc_ac4 := a₄ * rc_c4
  let rc_bc4 := b4 * rc_c4
  let rc_abc4 := rc_ab4 * rc_c4
  let rc_s4 := a₄ + b4 + rc_c4 - 2 * (rc_ab4 + rc_ac4 + rc_bc4) + 4 * rc_abc4
  let rc_c5 := rc_ab4 + rc_ac4 + rc_bc4 - 2 * rc_abc4
  let rc_ab5 := a₅ * b5
  let rc_ac5 := a₅ * rc_c5
  let rc_bc5 := b5 * rc_c5
  let rc_abc5 := rc_ab5 * rc_c5
  let rc_s5 := a₅ + b5 + rc_c5 - 2 * (rc_ab5 + rc_ac5 + rc_bc5) + 4 * rc_abc5
  let rc_c6 := rc_ab5 + rc_ac5 + rc_bc5 - 2 * rc_abc5
  let rc_ab6 := a₆ * b6
  let rc_ac6 := a₆ * rc_c6
  let rc_bc6 := b6 * rc_c6
  let rc_abc6 := rc_ab6 * rc_c6
  let rc_s6 := a₆ + b6 + rc_c6 - 2 * (rc_ab6 + rc_ac6 + rc_bc6) + 4 * rc_abc6
  let rc_c7 := rc_ab6 + rc_ac6 + rc_bc6 - 2 * rc_abc6
  let rc_ab7 := a₇ * b7
  let rc_ac7 := a₇ * rc_c7
  let rc_bc7 := b7 * rc_c7
  let rc_abc7 := rc_ab7 * rc_c7
  let rc_s7 := a₇ + b7 + rc_c7 - 2 * (rc_ab7 + rc_ac7 + rc_bc7) + 4 * rc_abc7
  rc_s0 + 2 * rc_s1 + 4 * rc_s2 + 8 * rc_s3 + 16 * rc_s4 + 32 * rc_s5 + 64 * rc_s6 + 128 * rc_s7

/-- Pack 11 ZMod p Booleans into a single BitVec 11. Used to connect the field
    polynomial to `daa_11_mle_bv` / `spec_daa_bv`. -/
private def pack11 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ N H C : ZMod p) : BitVec 11 :=
  BitVec.ofNat 11
    (a₀.val + 2 * a₁.val + 4 * a₂.val + 8 * a₃.val + 16 * a₄.val + 32 * a₅.val +
     64 * a₆.val + 128 * a₇.val + 256 * N.val + 512 * H.val + 1024 * C.val)

/-- Case-split helper: for 8 flag combinations (N, H, C), the polynomial value
    equals `(spec_daa ...).toNat` cast to `ZMod p`. This is the crux lemma;
    proved by `rcases` on 11 booleans + `decide` in each of 2048 concrete cases. -/
set_option maxHeartbeats 4000000 in
private theorem daa_poly_val_eq_spec_toNat (hp : 1536 < p)
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ N H C : ZMod p)
    (ha₀ : a₀ = 0 ∨ a₀ = 1) (ha₁ : a₁ = 0 ∨ a₁ = 1)
    (ha₂ : a₂ = 0 ∨ a₂ = 1) (ha₃ : a₃ = 0 ∨ a₃ = 1)
    (ha₄ : a₄ = 0 ∨ a₄ = 1) (ha₅ : a₅ = 0 ∨ a₅ = 1)
    (ha₆ : a₆ = 0 ∨ a₆ = 1) (ha₇ : a₇ = 0 ∨ a₇ = 1)
    (hN : N = 0 ∨ N = 1) (hH : H = 0 ∨ H = 1) (hC : C = 0 ∨ C = 1) :
    daa_poly_val a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ N H C =
      ((spec_daa_bv (pack11 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ N H C)).toNat : ZMod p) := by
  rcases ha₀ with rfl | rfl <;>
  rcases ha₁ with rfl | rfl <;>
  rcases ha₂ with rfl | rfl <;>
  rcases ha₃ with rfl | rfl <;>
  rcases ha₄ with rfl | rfl <;>
  rcases ha₅ with rfl | rfl <;>
  rcases ha₆ with rfl | rfl <;>
  rcases ha₇ with rfl | rfl <;>
  rcases hN with rfl | rfl <;>
  rcases hH with rfl | rfl <;>
  rcases hC with rfl | rfl <;>
  (unfold daa_poly_val pack11
   simp only [ZMod.val_zero, ZMod.val_one, Nat.zero_mul, Nat.mul_zero, Nat.add_zero,
              Nat.zero_add, Nat.mul_one, Nat.one_mul]
   -- LHS: polynomial in 0s and 1s in ZMod p — ring_nf to a literal
   -- RHS: spec_daa_bv of a concrete BitVec 11 — decide to a literal
   ring_nf
   -- After ring_nf, LHS is a `ZMod p` numeric literal. RHS is `(BitVec.toNat of concrete BitVec : ZMod p)`.
   -- Both should be equal as `ZMod p` values since each concrete BitVec has toNat < 256 < p.
   rfl)

end SM83.ZmodBitVecBridge
