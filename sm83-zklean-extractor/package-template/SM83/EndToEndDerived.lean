import SM83.EndToEnd
import SM83.FullSoundness

/-! # End-to-End theorems with derived N/H/C flags (Gap F wiring)

The 8 `*_end_to_end` theorems in `SM83.EndToEnd` take the N flag value
(and, for AND/XOR/OR, the H and C flag values) as *opaque* hypotheses
(`h_n : N = 0`, `h_h : H = 1`, etc.). This file provides
`*_end_to_end_flags_derived` variants that *derive* those flag
equalities from the master-constraint MUX equations (`h_n_eq`,
`h_h_one`, `h_h_zero`, `h_c_zero`, `h_c_one`) plus the opcode one-hot
Booleans, using the per-instruction `*_N_derived`, `*_H_derived`, and
`*_C_derived` theorems proved in `SM83.FullSoundness`.

For AND, the fully-derived version additionally uses
`SM83.ZmodBitVecBridge.and_bv_bridge` (Gap T) to *derive* the table
equality from the Gap H bit decomposition plus the Gap A per-bit AND
constraints, producing a single theorem that consumes only
constraint-level equations.

For ADD/SUB/INC/DEC, only the N flag is derived here; H and C still
come from the half_carry / carry sub-gadgets and are passed in as
`h_hbool`, `h_hc_eq`, `h_cbool` (unchanged from the original
`*_end_to_end` statements).
-/

namespace SM83.EndToEnd

open SM83.ConstraintProofs
open SM83.ZmodBitVecBridge

variable {p : ℕ} [Fact p.Prime]

section FlagsDerived

variable {is_add is_adc is_sub is_sbc is_and is_xor is_or is_cp
          is_inc is_dec is_rlc is_rrc is_rl is_rr is_sla is_sra is_srl is_swap
          is_daa is_cpl is_ccf is_scf : ZMod p}
variable {flag_z flag_n flag_h flag_c : ZMod p}
variable (hp_big : 22 < p)
variable (h_add_b : is_add = 0 ∨ is_add = 1) (h_adc_b : is_adc = 0 ∨ is_adc = 1)
variable (h_sub_b : is_sub = 0 ∨ is_sub = 1) (h_sbc_b : is_sbc = 0 ∨ is_sbc = 1)
variable (h_and_b : is_and = 0 ∨ is_and = 1) (h_xor_b : is_xor = 0 ∨ is_xor = 1)
variable (h_or_b : is_or = 0 ∨ is_or = 1) (h_cp_b : is_cp = 0 ∨ is_cp = 1)
variable (h_inc_b : is_inc = 0 ∨ is_inc = 1) (h_dec_b : is_dec = 0 ∨ is_dec = 1)
variable (h_rlc_b : is_rlc = 0 ∨ is_rlc = 1) (h_rrc_b : is_rrc = 0 ∨ is_rrc = 1)
variable (h_rl_b : is_rl = 0 ∨ is_rl = 1) (h_rr_b : is_rr = 0 ∨ is_rr = 1)
variable (h_sla_b : is_sla = 0 ∨ is_sla = 1) (h_sra_b : is_sra = 0 ∨ is_sra = 1)
variable (h_srl_b : is_srl = 0 ∨ is_srl = 1) (h_swap_b : is_swap = 0 ∨ is_swap = 1)
variable (h_daa_b : is_daa = 0 ∨ is_daa = 1) (h_cpl_b : is_cpl = 0 ∨ is_cpl = 1)
variable (h_ccf_b : is_ccf = 0 ∨ is_ccf = 1) (h_scf_b : is_scf = 0 ∨ is_scf = 1)
variable (h_sum : is_add + is_adc + is_sub + is_sbc + is_and + is_xor + is_or + is_cp +
                  is_inc + is_dec + is_rlc + is_rrc + is_rl + is_rr + is_sla + is_sra +
                  is_srl + is_swap + is_daa + is_cpl + is_ccf + is_scf = 1)
-- N-flag MUX equation (master_constraints).
variable (h_n_eq : flag_n = is_sub + is_sbc + is_cp + is_dec + is_cpl)
-- H-flag MUX equations (master_constraints).
variable (h_h_one : (is_and + is_cpl) * (flag_h - 1) = 0)
variable (h_h_zero : (is_xor + is_or + is_swap + is_rlc + is_rrc + is_rl +
                      is_rr + is_sla + is_sra + is_srl + is_ccf + is_scf +
                      is_daa) * flag_h = 0)
-- C-flag MUX equations (master_constraints).
variable (h_c_zero : (is_and + is_xor + is_or) * flag_c = 0)
variable (h_c_one : is_scf * (flag_c - 1) = 0)

include hp_big h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
        h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
        h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum
        h_n_eq h_h_one h_h_zero h_c_zero h_c_one

set_option linter.unusedSectionVars false

/-! ### ADD: N-flag derived from one-hot -/

theorem add_end_to_end_flags_derived
    {a_bv b_bv : BitVec 8}
    {result result_inv nibble_a nibble_b nibble_result : ZMod p}
    (h_is_add : is_add = 1)
    (h_table : result = ((spec_add a_bv b_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (_h_hc_eq : nibble_a + nibble_b = nibble_result + flag_h * 16)
    (h_hbool : flag_h * (flag_h - 1) = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_add a_bv b_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ (flag_h = 0 ∨ flag_h = 1) ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.add_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_add,
   boolean_of_r1cs h_hbool, boolean_of_r1cs h_cbool⟩

/-! ### SUB: N-flag derived from one-hot -/

theorem sub_end_to_end_flags_derived
    {a_bv b_bv : BitVec 8}
    {result result_inv nibble_a nibble_b nibble_result : ZMod p}
    (h_is_sub : is_sub = 1)
    (h_table : result = ((spec_sub a_bv b_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (_h_hc_eq : nibble_a + flag_h * 16 = nibble_result + nibble_b)
    (h_hbool : flag_h * (flag_h - 1) = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_sub a_bv b_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 1 ∧ (flag_h = 0 ∨ flag_h = 1) ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.sub_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_sub,
   boolean_of_r1cs h_hbool, boolean_of_r1cs h_cbool⟩

/-! ### AND: all three flags + table equality derived

Combines Gap T (`and_bv_bridge`) with the N/H/C derivations. No opaque
flag hypotheses remain: the conclusion follows from the bit-level
constraint equations + one-hot equations alone. -/

theorem and_end_to_end_flags_derived
    (hp_big_p : 256 < p)
    {alu_operand_a alu_operand_b result result_inv : ZMod p}
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
    (hr_sum : result =
      r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 + r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128)
    (hbc₀ : is_and * (r₀ - a₀ * b₀) = 0)
    (hbc₁ : is_and * (r₁ - a₁ * b₁) = 0)
    (hbc₂ : is_and * (r₂ - a₂ * b₂) = 0)
    (hbc₃ : is_and * (r₃ - a₃ * b₃) = 0)
    (hbc₄ : is_and * (r₄ - a₄ * b₄) = 0)
    (hbc₅ : is_and * (r₅ - a₅ * b₅) = 0)
    (hbc₆ : is_and * (r₆ - a₆ * b₆) = 0)
    (hbc₇ : is_and * (r₇ - a₇ * b₇) = 0)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0) :
    result = ((spec_and (zmodToBitVec8 alu_operand_a)
                        (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 1 ∧ flag_c = 0 :=
  ⟨and_bv_bridge hp_big_p h_is_and
     ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
     hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
     hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
     ha_sum hb_sum hr_sum
     hbc₀ hbc₁ hbc₂ hbc₃ hbc₄ hbc₅ hbc₆ hbc₇,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.and_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_and,
   SM83.FullSoundness.and_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_and,
   SM83.FullSoundness.and_C_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_c_zero h_c_one h_is_and⟩

/-! ### XOR: all three flags + table equality derived

Combines Gap T (`xor_bv_bridge`) with the N/H/C derivations. Mirrors
`and_end_to_end_flags_derived`. No opaque flag hypotheses remain. -/

theorem xor_end_to_end_flags_derived
    (hp_big_p : 256 < p)
    {alu_operand_a alu_operand_b result result_inv : ZMod p}
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
    (hr_sum : result =
      r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 + r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128)
    (hbc₀ : is_xor * (r₀ - (a₀ + b₀ - a₀ * b₀ * 2)) = 0)
    (hbc₁ : is_xor * (r₁ - (a₁ + b₁ - a₁ * b₁ * 2)) = 0)
    (hbc₂ : is_xor * (r₂ - (a₂ + b₂ - a₂ * b₂ * 2)) = 0)
    (hbc₃ : is_xor * (r₃ - (a₃ + b₃ - a₃ * b₃ * 2)) = 0)
    (hbc₄ : is_xor * (r₄ - (a₄ + b₄ - a₄ * b₄ * 2)) = 0)
    (hbc₅ : is_xor * (r₅ - (a₅ + b₅ - a₅ * b₅ * 2)) = 0)
    (hbc₆ : is_xor * (r₆ - (a₆ + b₆ - a₆ * b₆ * 2)) = 0)
    (hbc₇ : is_xor * (r₇ - (a₇ + b₇ - a₇ * b₇ * 2)) = 0)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0) :
    result = ((spec_xor (zmodToBitVec8 alu_operand_a)
                        (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ flag_c = 0 :=
  ⟨xor_bv_bridge hp_big_p h_is_xor
     ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
     hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
     hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
     ha_sum hb_sum hr_sum
     hbc₀ hbc₁ hbc₂ hbc₃ hbc₄ hbc₅ hbc₆ hbc₇,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.xor_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_xor,
   SM83.FullSoundness.xor_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_xor,
   SM83.FullSoundness.xor_C_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_c_zero h_c_one h_is_xor⟩

/-! ### OR: all three flags + table equality derived

Combines Gap T (`or_bv_bridge`) with the N/H/C derivations. Mirrors
`and_end_to_end_flags_derived`. No opaque flag hypotheses remain. -/

theorem or_end_to_end_flags_derived
    (hp_big_p : 256 < p)
    {alu_operand_a alu_operand_b result result_inv : ZMod p}
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
    (hr_sum : result =
      r₀ + r₁ * 2 + r₂ * 4 + r₃ * 8 + r₄ * 16 + r₅ * 32 + r₆ * 64 + r₇ * 128)
    (hbc₀ : is_or * (r₀ - (a₀ + b₀ - a₀ * b₀)) = 0)
    (hbc₁ : is_or * (r₁ - (a₁ + b₁ - a₁ * b₁)) = 0)
    (hbc₂ : is_or * (r₂ - (a₂ + b₂ - a₂ * b₂)) = 0)
    (hbc₃ : is_or * (r₃ - (a₃ + b₃ - a₃ * b₃)) = 0)
    (hbc₄ : is_or * (r₄ - (a₄ + b₄ - a₄ * b₄)) = 0)
    (hbc₅ : is_or * (r₅ - (a₅ + b₅ - a₅ * b₅)) = 0)
    (hbc₆ : is_or * (r₆ - (a₆ + b₆ - a₆ * b₆)) = 0)
    (hbc₇ : is_or * (r₇ - (a₇ + b₇ - a₇ * b₇)) = 0)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0) :
    result = ((spec_or (zmodToBitVec8 alu_operand_a)
                       (zmodToBitVec8 alu_operand_b)).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ flag_c = 0 :=
  ⟨or_bv_bridge hp_big_p h_is_or
     ha₀ ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ ha₇
     hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇
     hr₀ hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇
     ha_sum hb_sum hr_sum
     hbc₀ hbc₁ hbc₂ hbc₃ hbc₄ hbc₅ hbc₆ hbc₇,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.or_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_or,
   SM83.FullSoundness.or_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_or,
   SM83.FullSoundness.or_C_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_c_zero h_c_one h_is_or⟩

/-! ### INC: N-flag derived from one-hot -/

theorem inc_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv nibble_a nibble_b nibble_result : ZMod p}
    (h_is_inc : is_inc = 1)
    (h_table : result = ((spec_inc a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (_h_hc_eq : nibble_a + nibble_b = nibble_result + flag_h * 16)
    (h_hbool : flag_h * (flag_h - 1) = 0) :
    result = ((spec_inc a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ (flag_h = 0 ∨ flag_h = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.inc_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_inc,
   boolean_of_r1cs h_hbool⟩

/-! ### DEC: N-flag derived from one-hot -/

theorem dec_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv nibble_a nibble_b nibble_result : ZMod p}
    (h_is_dec : is_dec = 1)
    (h_table : result = ((spec_dec a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (_h_hc_eq : nibble_a + flag_h * 16 = nibble_result + nibble_b)
    (h_hbool : flag_h * (flag_h - 1) = 0) :
    result = ((spec_dec a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 1 ∧ (flag_h = 0 ∨ flag_h = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.dec_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_dec,
   boolean_of_r1cs h_hbool⟩

/-! ### Unary shifts / rotates / SWAP

Six instructions (`RLC`, `RRC`, `SLA`, `SRA`, `SRL`, `SWAP`) all share
the same flag structure:
- `flag_n = 0` (derived from master_constraints N-MUX)
- `flag_h = 0` (derived from master_constraints H-MUX via `h_h_zero`)
- `flag_c ∈ {0, 1}` (taken as Boolean hypothesis — C is computed by
  instruction-specific carry logic not captured by master_constraints)
- `h_table` taken as hypothesis (Gap T / Gap A lookup wiring not closed
  for these — item #3 in the remaining-gaps list).
-/

theorem rlc_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv : ZMod p}
    (h_is_rlc : is_rlc = 1)
    (h_table : result = ((spec_rlc a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_rlc a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.rlc_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_rlc,
   SM83.FullSoundness.rlc_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_rlc,
   boolean_of_r1cs h_cbool⟩

theorem rrc_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv : ZMod p}
    (h_is_rrc : is_rrc = 1)
    (h_table : result = ((spec_rrc a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_rrc a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.rrc_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_rrc,
   SM83.FullSoundness.rrc_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_rrc,
   boolean_of_r1cs h_cbool⟩

theorem sla_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv : ZMod p}
    (h_is_sla : is_sla = 1)
    (h_table : result = ((spec_sla a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_sla a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.sla_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_sla,
   SM83.FullSoundness.sla_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_sla,
   boolean_of_r1cs h_cbool⟩

theorem sra_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv : ZMod p}
    (h_is_sra : is_sra = 1)
    (h_table : result = ((spec_sra a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_sra a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.sra_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_sra,
   SM83.FullSoundness.sra_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_sra,
   boolean_of_r1cs h_cbool⟩

theorem srl_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv : ZMod p}
    (h_is_srl : is_srl = 1)
    (h_table : result = ((spec_srl a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_srl a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.srl_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_srl,
   SM83.FullSoundness.srl_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_srl,
   boolean_of_r1cs h_cbool⟩

theorem swap_end_to_end_flags_derived
    {a_bv : BitVec 8}
    {result result_inv : ZMod p}
    (h_is_swap : is_swap = 1)
    (h_table : result = ((spec_swap a_bv).toNat : ZMod p))
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    result = ((spec_swap a_bv).toNat : ZMod p) ∧
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨h_table,
   is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.swap_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_swap,
   SM83.FullSoundness.swap_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_swap,
   boolean_of_r1cs h_cbool⟩

/-! ### Flag-only end-to-end theorems

For the 9 remaining opcodes (`ADC`, `SBC`, `CP`, `CPL`, `CCF`, `SCF`,
`DAA`, `RL`, `RR`), either no `spec_<instr>` exists in `SM83.Spec`
(ADC/SBC/CP/CPL/CCF/SCF/RL/RR — semantics handled elsewhere) or the
spec takes input flags (`spec_daa`). For those cases we provide
*flag-only* end-to-end theorems that conclude the flag values only,
without claiming anything about `alu_result`.

The `is_zero` sub-gadget is always emitted by `master_constraints`, so
`flag_z` soundness is included for consistency with the other theorems.

Together with the 14 instruction-with-result theorems above, this
gives a flag_derived theorem for every one of the 22 opcodes. -/

/-- **SCF**: set carry flag. All three flags are tight from master_constraints
    MUX (N=0 via `flag_n`, H=0 via `h_h_zero`, C=1 via `h_c_one`). -/
theorem scf_flags_derived
    {result result_inv : ZMod p}
    (h_is_scf : is_scf = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ flag_c = 1 :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.scf_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_scf,
   SM83.FullSoundness.scf_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_scf,
   SM83.FullSoundness.scf_C_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_c_zero h_c_one h_is_scf⟩

/-- **CPL**: complement A. N=1 and H=1 tight from master_constraints MUX
    (via `flag_n` and `h_h_one`). C is not determined by master_constraints
    and is taken as a Boolean hypothesis. -/
theorem cpl_flags_derived
    {result result_inv : ZMod p}
    (h_is_cpl : is_cpl = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 1 ∧ flag_h = 1 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.cpl_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_cpl,
   SM83.FullSoundness.cpl_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_cpl,
   boolean_of_r1cs h_cbool⟩

/-- **CCF**: complement carry flag. N=0 and H=0 tight via MUX; C is toggled
    by instruction-specific logic (not captured in master_constraints) and
    is taken as a Boolean hypothesis. -/
theorem ccf_flags_derived
    {result result_inv : ZMod p}
    (h_is_ccf : is_ccf = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.ccf_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_ccf,
   SM83.FullSoundness.ccf_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_ccf,
   boolean_of_r1cs h_cbool⟩

/-- **DAA**: decimal adjust. N=0 and H=0 tight via MUX; C is instruction-specific. -/
theorem daa_flags_derived
    {result result_inv : ZMod p}
    (h_is_daa : is_daa = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.daa_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_daa,
   SM83.FullSoundness.daa_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_daa,
   boolean_of_r1cs h_cbool⟩

/-- **RL**: rotate left through carry. N=0 and H=0 tight via MUX. -/
theorem rl_flags_derived
    {result result_inv : ZMod p}
    (h_is_rl : is_rl = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.rl_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_rl,
   SM83.FullSoundness.rl_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_rl,
   boolean_of_r1cs h_cbool⟩

/-- **RR**: rotate right through carry. N=0 and H=0 tight via MUX. -/
theorem rr_flags_derived
    {result result_inv : ZMod p}
    (h_is_rr : is_rr = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ flag_h = 0 ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.rr_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_rr,
   SM83.FullSoundness.rr_H_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_h_one h_h_zero h_is_rr,
   boolean_of_r1cs h_cbool⟩

/-- **ADC**: add with carry. Only N=0 is tight via MUX (H and C are computed
    by half_carry_add / carry_add sub-gadgets when invoked); both are passed
    in as Boolean hypotheses. -/
theorem adc_flags_derived
    {result result_inv : ZMod p}
    (h_is_adc : is_adc = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_hbool : flag_h * (flag_h - 1) = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 0 ∧ (flag_h = 0 ∨ flag_h = 1) ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.adc_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_adc,
   boolean_of_r1cs h_hbool, boolean_of_r1cs h_cbool⟩

/-- **SBC**: subtract with carry. Only N=1 is tight via MUX. -/
theorem sbc_flags_derived
    {result result_inv : ZMod p}
    (h_is_sbc : is_sbc = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_hbool : flag_h * (flag_h - 1) = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 1 ∧ (flag_h = 0 ∨ flag_h = 1) ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.sbc_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_sbc,
   boolean_of_r1cs h_hbool, boolean_of_r1cs h_cbool⟩

/-- **CP**: compare (subtract without storing result). Only N=1 is tight via MUX. -/
theorem cp_flags_derived
    {result result_inv : ZMod p}
    (h_is_cp : is_cp = 1)
    (h_iz1 : result * result_inv = 1 - flag_z) (h_iz2 : flag_z * result = 0)
    (h_hbool : flag_h * (flag_h - 1) = 0)
    (h_cbool : flag_c * (flag_c - 1) = 0) :
    (result = 0 ↔ flag_z = 1) ∧ (flag_z = 0 ∨ flag_z = 1) ∧
    flag_n = 1 ∧ (flag_h = 0 ∨ flag_h = 1) ∧ (flag_c = 0 ∨ flag_c = 1) :=
  ⟨is_zero_sound h_iz1 h_iz2, is_zero_z_boolean h_iz1 h_iz2,
   SM83.FullSoundness.cp_N_derived hp_big
     h_add_b h_adc_b h_sub_b h_sbc_b h_and_b h_xor_b h_or_b h_cp_b
     h_inc_b h_dec_b h_rlc_b h_rrc_b h_rl_b h_rr_b h_sla_b h_sra_b
     h_srl_b h_swap_b h_daa_b h_cpl_b h_ccf_b h_scf_b h_sum h_n_eq h_is_cp,
   boolean_of_r1cs h_hbool, boolean_of_r1cs h_cbool⟩

end FlagsDerived

end SM83.EndToEnd
