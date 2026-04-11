//! Generates SM83/StepInputs.lean and SM83/Constraints.lean modules.

use crate::modules::{AsModule, Module};

// ---------------------------------------------------------------------------
// StepInputs module
// ---------------------------------------------------------------------------

pub struct Sm83StepInputs;

impl Sm83StepInputs {
    pub fn extract() -> Self {
        Self
    }
}

const STEP_FIELDS: &[(&str, &str)] = &[
    ("alu_operand_a", "ALU input A"),
    ("alu_operand_b", "ALU input B"),
    ("alu_result", "Lookup table output"),
    ("flag_z", "Zero flag"),
    ("flag_n", "Subtract flag"),
    ("flag_h", "Half-carry flag"),
    ("flag_c", "Carry flag"),
    ("result_inv", "Witness for is_zero sub-constraint"),
    ("nibble_a", "LOWER_NIBBLE(a) lookup result"),
    ("nibble_b", "LOWER_NIBBLE(b) lookup result"),
    ("nibble_result", "LOWER_NIBBLE(result) lookup result"),
    ("carry_in", "Carry flag input (for ADC/SBC/RL/RR)"),
    ("daa_n_in", "Pre-op N flag input (for DAA)"),
    ("daa_h_in", "Pre-op H flag input (for DAA)"),
    ("daa_c_in", "Pre-op C flag input (for DAA)"),
    ("add_carry", "Carry chain witness"),
    ("inc_overflow", "Increment overflow witness"),
    // Opcode flags (one-hot)
    ("is_add", "ADD opcode flag"),
    ("is_adc", "ADC opcode flag"),
    ("is_sub", "SUB opcode flag"),
    ("is_sbc", "SBC opcode flag"),
    ("is_and", "AND opcode flag"),
    ("is_xor", "XOR opcode flag"),
    ("is_or", "OR opcode flag"),
    ("is_cp", "CP opcode flag"),
    ("is_inc", "INC opcode flag"),
    ("is_dec", "DEC opcode flag"),
    ("is_rlc", "RLC opcode flag"),
    ("is_rrc", "RRC opcode flag"),
    ("is_rl", "RL opcode flag"),
    ("is_rr", "RR opcode flag"),
    ("is_sla", "SLA opcode flag"),
    ("is_sra", "SRA opcode flag"),
    ("is_srl", "SRL opcode flag"),
    ("is_swap", "SWAP opcode flag"),
    ("is_daa", "DAA opcode flag"),
    ("is_cpl", "CPL opcode flag"),
    ("is_ccf", "CCF opcode flag"),
    ("is_scf", "SCF opcode flag"),
    // Range-check bit decomposition witnesses (Gap H)
    // 8 bits for alu_operand_a
    ("a_bit_0", "Bit 0 of alu_operand_a"),
    ("a_bit_1", "Bit 1 of alu_operand_a"),
    ("a_bit_2", "Bit 2 of alu_operand_a"),
    ("a_bit_3", "Bit 3 of alu_operand_a"),
    ("a_bit_4", "Bit 4 of alu_operand_a"),
    ("a_bit_5", "Bit 5 of alu_operand_a"),
    ("a_bit_6", "Bit 6 of alu_operand_a"),
    ("a_bit_7", "Bit 7 of alu_operand_a"),
    // 8 bits for alu_operand_b
    ("b_bit_0", "Bit 0 of alu_operand_b"),
    ("b_bit_1", "Bit 1 of alu_operand_b"),
    ("b_bit_2", "Bit 2 of alu_operand_b"),
    ("b_bit_3", "Bit 3 of alu_operand_b"),
    ("b_bit_4", "Bit 4 of alu_operand_b"),
    ("b_bit_5", "Bit 5 of alu_operand_b"),
    ("b_bit_6", "Bit 6 of alu_operand_b"),
    ("b_bit_7", "Bit 7 of alu_operand_b"),
    // 8 bits for alu_result
    ("r_bit_0", "Bit 0 of alu_result"),
    ("r_bit_1", "Bit 1 of alu_result"),
    ("r_bit_2", "Bit 2 of alu_result"),
    ("r_bit_3", "Bit 3 of alu_result"),
    ("r_bit_4", "Bit 4 of alu_result"),
    ("r_bit_5", "Bit 5 of alu_result"),
    ("r_bit_6", "Bit 6 of alu_result"),
    ("r_bit_7", "Bit 7 of alu_result"),
    // Register file columns for the binary-ALU block (Reg8 minus F and (HL)).
    // These let `master_constraints` *enforce* the coupling between the ZK
    // operands and a CPU register file, removing the need for callers to
    // supply external `h_couple_*` hypotheses to the refinement theorems.
    ("reg_a", "Register A value (the ALU accumulator / dest)"),
    ("reg_b", "Register B value"),
    ("reg_c", "Register C value"),
    ("reg_d", "Register D value"),
    ("reg_e", "Register E value"),
    ("reg_h", "Register H value"),
    ("reg_l", "Register L value"),
    // Source-register one-hot selector for the binary-ALU block.
    // Exactly one of these is 1; that register provides `alu_operand_b`.
    // (The (HL) variant is excluded — it requires memory modeling.)
    ("is_src_a", "Source-register selector: A"),
    ("is_src_b", "Source-register selector: B"),
    ("is_src_c", "Source-register selector: C"),
    ("is_src_d", "Source-register selector: D"),
    ("is_src_e", "Source-register selector: E"),
    ("is_src_h", "Source-register selector: H"),
    ("is_src_l", "Source-register selector: L"),
];

impl AsModule for Sm83StepInputs {
    fn as_module(&self) -> std::io::Result<Module> {
        let mut out = String::new();

        // Structure definition
        out.push_str("structure SM83StepInputs (f : Type) : Type where\n");
        for (name, comment) in STEP_FIELDS {
            out.push_str(&format!("  {} : ZKExpr f  -- {}\n", name, comment));
        }
        out.push('\n');

        // Witnessable instance
        out.push_str("instance : Witnessable f (SM83StepInputs f) where\n");
        out.push_str("  witness := do\n");
        for (name, _) in STEP_FIELDS {
            out.push_str(&format!("    let {} <- Witnessable.witness\n", name));
        }
        out.push_str("    pure {\n");
        for (name, _) in STEP_FIELDS {
            out.push_str(&format!("      {name} := {name}\n"));
        }
        out.push_str("    }\n");

        Ok(Module {
            name: "StepInputs".into(),
            imports: vec!["zkLean".into()],
            contents: out.into_bytes(),
        })
    }
}

// ---------------------------------------------------------------------------
// Constraints module
// ---------------------------------------------------------------------------

pub struct Sm83Constraints;

impl Sm83Constraints {
    pub fn extract() -> Self {
        Self
    }
}

impl AsModule for Sm83Constraints {
    fn as_module(&self) -> std::io::Result<Module> {
        let mut out = String::new();

        // -- Sub-constraint: is_zero --
        out.push_str("-- | Zero-flag sub-constraint: Z=1 iff result=0.\n");
        out.push_str("-- | Requires witness result_inv = if result=0 then 0 else result⁻¹.\n");
        out.push_str("def is_zero_constraint [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  -- result * result_inv = 1 - Z\n");
        out.push_str("  ZKBuilder.constrainR1CS step.alu_result step.result_inv (1 - step.flag_z)\n");
        out.push_str("  -- Z * result = 0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.flag_z step.alu_result 0\n\n");

        // -- Sub-constraint: half_carry_add --
        out.push_str("-- | Half-carry sub-constraint for addition: nibble_a + nibble_b = nibble_result + H * 16\n");
        out.push_str("def half_carry_add [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainEq\n");
        out.push_str("    (step.nibble_a + step.nibble_b)\n");
        out.push_str("    (step.nibble_result + step.flag_h * 16)\n");
        out.push_str("  -- H is boolean\n");
        out.push_str("  ZKBuilder.constrainR1CS step.flag_h (step.flag_h - 1) 0\n\n");

        // -- Sub-constraint: half_carry_sub --
        out.push_str("-- | Half-carry sub-constraint for subtraction: nibble_a - nibble_b + H * 16 = nibble_result\n");
        out.push_str("def half_carry_sub [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainEq\n");
        out.push_str("    (step.nibble_a + step.flag_h * 16)\n");
        out.push_str("    (step.nibble_result + step.nibble_b)\n");
        out.push_str("  -- H is boolean\n");
        out.push_str("  ZKBuilder.constrainR1CS step.flag_h (step.flag_h - 1) 0\n\n");

        // -- Sub-constraint: carry_add --
        out.push_str("-- | Carry sub-constraint for 8-bit addition: a + b = result + C * 256\n");
        out.push_str("def carry_add [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainEq\n");
        out.push_str("    (step.alu_operand_a + step.alu_operand_b)\n");
        out.push_str("    (step.alu_result + step.flag_c * 256)\n");
        out.push_str("  -- C is boolean\n");
        out.push_str("  ZKBuilder.constrainR1CS step.flag_c (step.flag_c - 1) 0\n\n");

        // -- Sub-constraint: carry_sub --
        out.push_str("-- | Carry sub-constraint for 8-bit subtraction: a = result + b - C * 256\n");
        out.push_str("def carry_sub [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainEq\n");
        out.push_str("    (step.alu_operand_a + step.flag_c * 256)\n");
        out.push_str("    (step.alu_result + step.alu_operand_b)\n");
        out.push_str("  -- C is boolean\n");
        out.push_str("  ZKBuilder.constrainR1CS step.flag_c (step.flag_c - 1) 0\n\n");

        // -- Sub-constraint: one_hot_constraints (Gap I) --
        // Enforces: each is_* flag is Boolean AND exactly one is 1.
        // Split into 4 small chunks so each chunk's bridge has ≤ 6 nested
        // splits — keeps Lean's `split at h` internal simp within step limits.
        let opcode_flags = [
            "is_add", "is_adc", "is_sub", "is_sbc",
            "is_and", "is_xor", "is_or", "is_cp",
            "is_inc", "is_dec",
            "is_rlc", "is_rrc", "is_rl", "is_rr",
            "is_sla", "is_sra", "is_srl", "is_swap",
            "is_daa", "is_cpl", "is_ccf", "is_scf",
        ];
        // Boolean chunk: 6 or fewer booleans per chunk
        let chunks: Vec<&[&str]> = vec![
            &opcode_flags[0..6],
            &opcode_flags[6..12],
            &opcode_flags[12..18],
            &opcode_flags[18..22],
        ];
        for (i, chunk) in chunks.iter().enumerate() {
            out.push_str(&format!(
                "-- | One-hot boolean chunk {}: {} Boolean constraints.\n",
                i + 1, chunk.len()
            ));
            out.push_str(&format!(
                "def one_hot_bool_chunk_{} [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n",
                i + 1
            ));
            for flag in chunk.iter() {
                out.push_str(&format!(
                    "  ZKBuilder.constrainR1CS step.{flag} (step.{flag} - 1) 0\n"
                ));
            }
            out.push_str("\n");
        }
        // Sum-to-1 constraint
        out.push_str("-- | One-hot sum constraint: sum of all opcode flags = 1.\n");
        out.push_str("def one_hot_sum_constraint [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        let sum_expr = opcode_flags
            .iter()
            .map(|f| format!("step.{f}"))
            .collect::<Vec<_>>()
            .join(" + ");
        out.push_str(&format!("  ZKBuilder.constrainEq ({sum_expr}) 1\n\n"));

        // Composed one_hot_constraints
        out.push_str("-- | One-hot constraint: each opcode flag is Boolean AND sum = 1.\n");
        out.push_str("-- | Closes Gap I (one-hot enforcement).\n");
        out.push_str("def one_hot_constraints [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  one_hot_bool_chunk_1 step\n");
        out.push_str("  one_hot_bool_chunk_2 step\n");
        out.push_str("  one_hot_bool_chunk_3 step\n");
        out.push_str("  one_hot_bool_chunk_4 step\n");
        out.push_str("  one_hot_sum_constraint step\n\n");

        // -- Sub-constraint: range_check_constraints (Gap H) --
        // For each of alu_operand_a, alu_operand_b, alu_result:
        //   - Each of the 8 bits is Boolean (is 0 or 1)
        //   - The value equals the sum of bits * powers of 2
        // Together these enforce that the value is in [0, 255] (assuming
        // field characteristic > 256).
        let value_prefixes = [
            ("alu_operand_a", "a"),
            ("alu_operand_b", "b"),
            ("alu_result", "r"),
        ];
        for (value, prefix) in &value_prefixes {
            // Boolean chunk (8 constraints)
            out.push_str(&format!(
                "-- | Range-check bit Boolean constraints for {value}.\n"
            ));
            out.push_str(&format!(
                "def range_bool_{prefix} [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n"
            ));
            for i in 0..8 {
                out.push_str(&format!(
                    "  ZKBuilder.constrainR1CS step.{prefix}_bit_{i} (step.{prefix}_bit_{i} - 1) 0\n"
                ));
            }
            out.push_str("\n");
            // Sum constraint: value = sum of bits * 2^i
            out.push_str(&format!(
                "-- | Range-check sum constraint: {value} = Σ bit_i * 2^i.\n"
            ));
            out.push_str(&format!(
                "def range_sum_{prefix} [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n"
            ));
            let sum_expr = (0..8)
                .map(|i| {
                    if i == 0 {
                        format!("step.{prefix}_bit_{i}")
                    } else {
                        format!("step.{prefix}_bit_{i} * {}", 1u32 << i)
                    }
                })
                .collect::<Vec<_>>()
                .join(" + ");
            out.push_str(&format!("  ZKBuilder.constrainEq step.{value} ({sum_expr})\n\n"));
        }
        // Composed range_check_constraints
        out.push_str("-- | Range check: enforces alu_operand_a, alu_operand_b, alu_result ∈ [0, 255].\n");
        out.push_str("-- | Closes Gap H (range constraints).\n");
        out.push_str("def range_check_constraints [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        for (_, prefix) in &value_prefixes {
            out.push_str(&format!("  range_bool_{prefix} step\n"));
            out.push_str(&format!("  range_sum_{prefix} step\n"));
        }
        out.push_str("\n");

        // -- Sub-constraint: table_lookup_constraints (Gap A) --
        // Uses the bit decomposition (from Gap H) to express bitwise operations
        // as closed-form polynomials. For each bitwise op, the constraint is
        // guarded by `is_X * (r_bit_i - expected_r_bit_i) = 0` so it only fires
        // for that specific opcode (via one-hot from Gap I).
        //
        // Bitwise operations (closed form):
        //   AND: r_bit_i = a_bit_i * b_bit_i
        //   XOR: r_bit_i = a_bit_i + b_bit_i - 2 * a_bit_i * b_bit_i
        //   OR:  r_bit_i = a_bit_i + b_bit_i - a_bit_i * b_bit_i
        //
        // Non-bitwise ops (ADD, SUB, INC, DEC, shifts, etc.) are handled via
        // their sub-gadgets (carry_add, half_carry_add, etc.) combined with
        // the result-bit decomposition from Gap H. The AND/XOR/OR closed-form
        // constraints here demonstrate how the lookup is effectively encoded
        // structurally without needing zkLean's lookup table API.
        out.push_str("-- | Bitwise lookup constraint: for AND opcode, r_bit_i = a_bit_i * b_bit_i.\n");
        out.push_str("def table_constraint_and [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        for i in 0..8 {
            out.push_str(&format!(
                "  ZKBuilder.constrainR1CS step.is_and (step.r_bit_{i} - step.a_bit_{i} * step.b_bit_{i}) 0\n"
            ));
        }
        out.push_str("\n");
        out.push_str("-- | Bitwise lookup constraint: for XOR opcode, r_bit_i = a_bit_i + b_bit_i - 2*a_bit_i*b_bit_i.\n");
        out.push_str("def table_constraint_xor [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        for i in 0..8 {
            out.push_str(&format!(
                "  ZKBuilder.constrainR1CS step.is_xor (step.r_bit_{i} - (step.a_bit_{i} + step.b_bit_{i} - step.a_bit_{i} * step.b_bit_{i} * 2)) 0\n"
            ));
        }
        out.push_str("\n");
        out.push_str("-- | Bitwise lookup constraint: for OR opcode, r_bit_i = a_bit_i + b_bit_i - a_bit_i*b_bit_i.\n");
        out.push_str("def table_constraint_or [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        for i in 0..8 {
            out.push_str(&format!(
                "  ZKBuilder.constrainR1CS step.is_or (step.r_bit_{i} - (step.a_bit_{i} + step.b_bit_{i} - step.a_bit_{i} * step.b_bit_{i})) 0\n"
            ));
        }
        out.push_str("\n");

        // -- table_constraint_add --
        // Closes Gap A for ADD via the carry-decomposition equation, conditional
        // on `is_add = 1`. Combined with the global `flag_c` boolean constraint
        // (emitted below) and the Gap H range checks, this is sufficient to
        // derive `alu_result = (alu_operand_a + alu_operand_b) mod 256` — the
        // BitVec spec for ADD — entirely from the constraint system.
        out.push_str("-- | ADD lookup constraint: when is_add = 1, alu_operand_a + alu_operand_b = alu_result + flag_c * 256.\n");
        out.push_str("def table_constraint_add [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_add\n");
        out.push_str("    (step.alu_operand_a + step.alu_operand_b - step.alu_result - step.flag_c * 256) 0\n\n");

        // -- table_constraint_sub --
        // Closes Gap A for SUB via the borrow-decomposition equation, conditional
        // on `is_sub = 1`. The form mirrors `carry_sub`:
        //   alu_operand_a + flag_c * 256 = alu_result + alu_operand_b
        // i.e. when there's no borrow (flag_c = 0), `alu_operand_a = alu_result + alu_operand_b`,
        // and when there's a borrow (flag_c = 1), `alu_operand_a + 256 = alu_result + alu_operand_b`.
        out.push_str("-- | SUB lookup constraint: when is_sub = 1, alu_operand_a + flag_c * 256 = alu_result + alu_operand_b.\n");
        out.push_str("def table_constraint_sub [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_sub\n");
        out.push_str("    (step.alu_operand_a + step.flag_c * 256 - step.alu_result - step.alu_operand_b) 0\n\n");

        // -- table_constraint_inc / table_constraint_dec --
        // Unary INC/DEC operations. Reuse the existing `inc_overflow` witness as
        // a single-bit carry/borrow flag. For INC: when alu_operand_a = 0xFF, the
        // overflow is 1 and alu_result wraps to 0. For DEC: when alu_operand_a = 0,
        // the borrow is 1 and alu_result wraps to 0xFF.
        out.push_str("-- | INC lookup constraint: when is_inc = 1, alu_operand_a + 1 = alu_result + inc_overflow * 256.\n");
        out.push_str("def table_constraint_inc [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_inc\n");
        out.push_str("    (step.alu_operand_a + 1 - step.alu_result - step.inc_overflow * 256) 0\n\n");
        out.push_str("-- | DEC lookup constraint: when is_dec = 1, alu_operand_a + inc_overflow * 256 = alu_result + 1.\n");
        out.push_str("def table_constraint_dec [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_dec\n");
        out.push_str("    (step.alu_operand_a + step.inc_overflow * 256 - step.alu_result - 1) 0\n\n");
        out.push_str("-- | Global Boolean constraint on inc_overflow: required by table_constraint_inc / dec.\n");
        out.push_str("def inc_overflow_boolean_constraint [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainR1CS step.inc_overflow (step.inc_overflow - 1) 0\n\n");

        // -- flag_c_boolean_constraint --
        // Always-on Boolean constraint on `flag_c`. Required by `table_constraint_add`
        // to make the carry decomposition correct (the prover can't put a non-Boolean
        // value in `flag_c`). Consistent with both `c_must_be_zero` and `c_must_be_one`
        // master MUX equations: 0 and 1 are both Boolean.
        out.push_str("-- | Global Boolean constraint on flag_c. Required by table_constraint_add.\n");
        out.push_str("def flag_c_boolean_constraint [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  ZKBuilder.constrainR1CS step.flag_c (step.flag_c - 1) 0\n\n");

        // -- DAA polynomial helper --
        // Mirrors `daa_11_lookup_table` in LookupTables.lean, but specialized to
        // `SM83StepInputs f` and `ZKExpr f` so it only needs the Add/Sub/Mul/OfNat
        // instances on `ZKExpr f` (no `Field` required). This is the polynomial
        // used by `table_constraint_daa` below.
        out.push_str("-- | DAA polynomial over the step's bit witnesses and input flag witnesses.\n");
        out.push_str("-- | Mirrors `daa_11_lookup_table` from LookupTables.lean but operates on\n");
        out.push_str("-- | `ZKExpr f` directly (Add/Sub/Mul/OfNat only).\n");
        out.push_str("def daa_poly_from_step [ZKField f] (step : SM83StepInputs f) : ZKExpr f :=\n");
        out.push_str("  let a0 := step.a_bit_0\n");
        out.push_str("  let a1 := step.a_bit_1\n");
        out.push_str("  let a2 := step.a_bit_2\n");
        out.push_str("  let a3 := step.a_bit_3\n");
        out.push_str("  let a4 := step.a_bit_4\n");
        out.push_str("  let a5 := step.a_bit_5\n");
        out.push_str("  let a6 := step.a_bit_6\n");
        out.push_str("  let a7 := step.a_bit_7\n");
        out.push_str("  let N := step.daa_n_in\n");
        out.push_str("  let H := step.daa_h_in\n");
        out.push_str("  let C := step.daa_c_in\n");
        out.push_str("  let notN := 1 - N\n");
        out.push_str("  let lo_gt9 := a3 * (a2 + a1 - a2 * a1)\n");
        out.push_str("  let adj_lo_cond := notN * lo_gt9\n");
        out.push_str("  let adj_lo := adj_lo_cond + H - adj_lo_cond * H\n");
        out.push_str("  let hi_ge10 := a7 * (a6 + a5 - a6 * a5)\n");
        out.push_str("  let hi_eq9 := a4 * (1 - a5) * (1 - a6) * a7\n");
        out.push_str("  let a_gt99 := hi_ge10 + hi_eq9 * lo_gt9 - hi_ge10 * hi_eq9 * lo_gt9\n");
        out.push_str("  let adj_hi_cond := notN * a_gt99\n");
        out.push_str("  let adj_hi := adj_hi_cond + C - adj_hi_cond * C\n");
        out.push_str("  let off0 : ZKExpr f := 0\n");
        out.push_str("  let off1 := adj_lo\n");
        out.push_str("  let off2 := adj_lo\n");
        out.push_str("  let off3 : ZKExpr f := 0\n");
        out.push_str("  let off4 : ZKExpr f := 0\n");
        out.push_str("  let off5 := adj_hi\n");
        out.push_str("  let off6 := adj_hi\n");
        out.push_str("  let off7 : ZKExpr f := 0\n");
        out.push_str("  let b0 := off0 + N - 2 * off0 * N\n");
        out.push_str("  let b1 := off1 + N - 2 * off1 * N\n");
        out.push_str("  let b2 := off2 + N - 2 * off2 * N\n");
        out.push_str("  let b3 := off3 + N - 2 * off3 * N\n");
        out.push_str("  let b4 := off4 + N - 2 * off4 * N\n");
        out.push_str("  let b5 := off5 + N - 2 * off5 * N\n");
        out.push_str("  let b6 := off6 + N - 2 * off6 * N\n");
        out.push_str("  let b7 := off7 + N - 2 * off7 * N\n");
        out.push_str("  let cin : ZKExpr f := N\n");
        out.push_str("  let rc_c0 := cin\n");
        out.push_str("  let rc_ab0 := a0 * b0\n");
        out.push_str("  let rc_ac0 := a0 * rc_c0\n");
        out.push_str("  let rc_bc0 := b0 * rc_c0\n");
        out.push_str("  let rc_abc0 := rc_ab0 * rc_c0\n");
        out.push_str("  let rc_s0 := a0 + b0 + rc_c0 - 2 * (rc_ab0 + rc_ac0 + rc_bc0) + 4 * rc_abc0\n");
        out.push_str("  let rc_c1 := rc_ab0 + rc_ac0 + rc_bc0 - 2 * rc_abc0\n");
        out.push_str("  let rc_ab1 := a1 * b1\n");
        out.push_str("  let rc_ac1 := a1 * rc_c1\n");
        out.push_str("  let rc_bc1 := b1 * rc_c1\n");
        out.push_str("  let rc_abc1 := rc_ab1 * rc_c1\n");
        out.push_str("  let rc_s1 := a1 + b1 + rc_c1 - 2 * (rc_ab1 + rc_ac1 + rc_bc1) + 4 * rc_abc1\n");
        out.push_str("  let rc_c2 := rc_ab1 + rc_ac1 + rc_bc1 - 2 * rc_abc1\n");
        out.push_str("  let rc_ab2 := a2 * b2\n");
        out.push_str("  let rc_ac2 := a2 * rc_c2\n");
        out.push_str("  let rc_bc2 := b2 * rc_c2\n");
        out.push_str("  let rc_abc2 := rc_ab2 * rc_c2\n");
        out.push_str("  let rc_s2 := a2 + b2 + rc_c2 - 2 * (rc_ab2 + rc_ac2 + rc_bc2) + 4 * rc_abc2\n");
        out.push_str("  let rc_c3 := rc_ab2 + rc_ac2 + rc_bc2 - 2 * rc_abc2\n");
        out.push_str("  let rc_ab3 := a3 * b3\n");
        out.push_str("  let rc_ac3 := a3 * rc_c3\n");
        out.push_str("  let rc_bc3 := b3 * rc_c3\n");
        out.push_str("  let rc_abc3 := rc_ab3 * rc_c3\n");
        out.push_str("  let rc_s3 := a3 + b3 + rc_c3 - 2 * (rc_ab3 + rc_ac3 + rc_bc3) + 4 * rc_abc3\n");
        out.push_str("  let rc_c4 := rc_ab3 + rc_ac3 + rc_bc3 - 2 * rc_abc3\n");
        out.push_str("  let rc_ab4 := a4 * b4\n");
        out.push_str("  let rc_ac4 := a4 * rc_c4\n");
        out.push_str("  let rc_bc4 := b4 * rc_c4\n");
        out.push_str("  let rc_abc4 := rc_ab4 * rc_c4\n");
        out.push_str("  let rc_s4 := a4 + b4 + rc_c4 - 2 * (rc_ab4 + rc_ac4 + rc_bc4) + 4 * rc_abc4\n");
        out.push_str("  let rc_c5 := rc_ab4 + rc_ac4 + rc_bc4 - 2 * rc_abc4\n");
        out.push_str("  let rc_ab5 := a5 * b5\n");
        out.push_str("  let rc_ac5 := a5 * rc_c5\n");
        out.push_str("  let rc_bc5 := b5 * rc_c5\n");
        out.push_str("  let rc_abc5 := rc_ab5 * rc_c5\n");
        out.push_str("  let rc_s5 := a5 + b5 + rc_c5 - 2 * (rc_ab5 + rc_ac5 + rc_bc5) + 4 * rc_abc5\n");
        out.push_str("  let rc_c6 := rc_ab5 + rc_ac5 + rc_bc5 - 2 * rc_abc5\n");
        out.push_str("  let rc_ab6 := a6 * b6\n");
        out.push_str("  let rc_ac6 := a6 * rc_c6\n");
        out.push_str("  let rc_bc6 := b6 * rc_c6\n");
        out.push_str("  let rc_abc6 := rc_ab6 * rc_c6\n");
        out.push_str("  let rc_s6 := a6 + b6 + rc_c6 - 2 * (rc_ab6 + rc_ac6 + rc_bc6) + 4 * rc_abc6\n");
        out.push_str("  let rc_c7 := rc_ab6 + rc_ac6 + rc_bc6 - 2 * rc_abc6\n");
        out.push_str("  let rc_ab7 := a7 * b7\n");
        out.push_str("  let rc_ac7 := a7 * rc_c7\n");
        out.push_str("  let rc_bc7 := b7 * rc_c7\n");
        out.push_str("  let rc_abc7 := rc_ab7 * rc_c7\n");
        out.push_str("  let rc_s7 := a7 + b7 + rc_c7 - 2 * (rc_ab7 + rc_ac7 + rc_bc7) + 4 * rc_abc7\n");
        out.push_str("  rc_s0 + 2 * rc_s1 + 4 * rc_s2 + 8 * rc_s3 + 16 * rc_s4 + 32 * rc_s5 + 64 * rc_s6 + 128 * rc_s7\n\n");
        // Composed table_lookup_constraints
        out.push_str("-- | Table lookup constraints: enforces alu_result matches the opcode's spec.\n");
        out.push_str("-- | Closes Gap A (lookup invocation) structurally for bitwise ops via bit\n");
        out.push_str("-- | decomposition. Non-bitwise ops are handled by carry/half-carry sub-gadgets.\n");
        out.push_str("def table_lookup_constraints [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  table_constraint_and step\n");
        out.push_str("  table_constraint_xor step\n");
        out.push_str("  table_constraint_or step\n\n");

        // -- Sub-constraint: register_coupling_constraints --
        // Couples the abstract `alu_operand_a` / `alu_operand_b` wires to a
        // concrete CPU register file column set, indexed by a one-hot
        // source-register selector. This is what makes the *single-step
        // refinement theorem* close without external coupling hypotheses:
        // the prover commits to a register file (via `reg_*`) and a source
        // selector (via `is_src_*`), and the constraint system enforces that
        // `alu_operand_a = reg_a` and `alu_operand_b = reg[selected]`.
        //
        // Scope: the binary-ALU block (`0x80..=0xBF`), register-to-register
        // variants only — the (HL) memory variant is excluded because memory
        // modeling is out of scope for this single-step refinement.
        let src_flags = ["is_src_a", "is_src_b", "is_src_c", "is_src_d", "is_src_e", "is_src_h", "is_src_l"];
        let src_pairs = [
            ("is_src_a", "reg_a"),
            ("is_src_b", "reg_b"),
            ("is_src_c", "reg_c"),
            ("is_src_d", "reg_d"),
            ("is_src_e", "reg_e"),
            ("is_src_h", "reg_h"),
            ("is_src_l", "reg_l"),
        ];
        out.push_str("-- | Register-coupling sub-constraint: ties the abstract ALU operands\n");
        out.push_str("-- | to a concrete register file via a one-hot source selector.\n");
        out.push_str("-- |   * each `is_src_*` is Boolean, and exactly one is 1\n");
        out.push_str("-- |   * `alu_operand_a = reg_a` (the accumulator / dest is always A)\n");
        out.push_str("-- |   * `alu_operand_b = Σ is_src_X * reg_X` (the source register MUX)\n");
        out.push_str("def register_coupling_constraints [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        for flag in &src_flags {
            out.push_str(&format!(
                "  ZKBuilder.constrainR1CS step.{flag} (step.{flag} - 1) 0\n"
            ));
        }
        let src_sum_expr = src_flags
            .iter()
            .map(|f| format!("step.{f}"))
            .collect::<Vec<_>>()
            .join(" + ");
        out.push_str(&format!(
            "  ZKBuilder.constrainEq ({src_sum_expr}) 1\n"
        ));
        out.push_str("  ZKBuilder.constrainEq step.alu_operand_a step.reg_a\n");
        let mux_expr = src_pairs
            .iter()
            .map(|(sel, reg)| format!("step.{sel} * step.{reg}"))
            .collect::<Vec<_>>()
            .join(" + ");
        out.push_str(&format!(
            "  ZKBuilder.constrainEq step.alu_operand_b ({mux_expr})\n\n"
        ));

        // -- Master constraint: Z flag --
        // is_zero_constraint is ALWAYS applied. It forces:
        //   result * result_inv = 1 - Z  and  Z * result = 0
        // This is always satisfiable: the prover sets result_inv = result⁻¹ (or 0).
        // For opcodes that don't update Z (LD, JP, etc.), the execution trace layer
        // handles flag carry-through — at the step level, Z is always well-defined.
        out.push_str("-- | Master constraints: enforce all flag relationships for one ALU step.\n");
        out.push_str("def master_constraints [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
        out.push_str("  -- One-hot encoding: ensures exactly one opcode flag is set (Gap I)\n");
        out.push_str("  one_hot_constraints step\n");
        out.push_str("  -- Range check: ensures operands and result are in [0, 255] (Gap H)\n");
        out.push_str("  range_check_constraints step\n");
        out.push_str("  -- Lookup table constraints: ties alu_result to the correct spec (Gap A, bitwise ops)\n");
        out.push_str("  table_lookup_constraints step\n");
        out.push_str("  -- Z flag: always enforce is_zero relationship\n");
        out.push_str("  is_zero_constraint step\n");
        out.push_str("  -- N flag: must equal 1 for SUB/SBC/CP/DEC/CPL, 0 otherwise\n");
        out.push_str("  let n_should_be := step.is_sub + step.is_sbc + step.is_cp + step.is_dec + step.is_cpl\n");
        out.push_str("  ZKBuilder.constrainEq step.flag_n n_should_be\n");
        out.push_str("  -- H flag MUX: dispatch based on opcode flag pattern\n");
        out.push_str("  -- Pattern z0hc (ADD/ADC): H from half_carry_add\n");
        out.push_str("  -- Pattern z1hc (SUB/SBC/CP): H from half_carry_sub\n");
        out.push_str("  -- Pattern z0h- (INC): H from half_carry_add (b=1)\n");
        out.push_str("  -- Pattern z1h- (DEC): H from half_carry_sub (b=1)\n");
        out.push_str("  -- Pattern z010 (AND), -11- (CPL): H = 1\n");
        out.push_str("  -- All others that set H: H = 0\n");
        out.push_str("  let h_must_be_one := step.is_and + step.is_cpl\n");
        out.push_str("  let h_must_be_zero := step.is_xor + step.is_or + step.is_swap + step.is_rlc + step.is_rrc + step.is_rl + step.is_rr + step.is_sla + step.is_sra + step.is_srl + step.is_ccf + step.is_scf + step.is_daa\n");
        out.push_str("  -- Constrain: h_must_be_one * (H - 1) = 0  (forces H=1 when flagged)\n");
        out.push_str("  ZKBuilder.constrainR1CS h_must_be_one (step.flag_h - 1) 0\n");
        out.push_str("  -- Constrain: h_must_be_zero * H = 0  (forces H=0 when flagged)\n");
        out.push_str("  ZKBuilder.constrainR1CS h_must_be_zero step.flag_h 0\n");
        out.push_str("  -- For computed H (ADD/ADC/INC use half_carry_add, SUB/SBC/CP/DEC use half_carry_sub),\n");
        out.push_str("  -- the caller must invoke the appropriate sub-constraint separately.\n");
        out.push_str("  -- C flag MUX: dispatch based on opcode flag pattern\n");
        out.push_str("  -- Pattern z0hc/z1hc (ADD/SUB): C from carry_add/carry_sub\n");
        out.push_str("  -- Pattern z00c (shifts): C from shift-specific identity\n");
        out.push_str("  -- Pattern -001 (SCF): C = 1\n");
        out.push_str("  -- Pattern -00c (CCF): C = 1 - C_prev (complement)\n");
        out.push_str("  -- Pattern z000/z010 (XOR/OR/AND): C = 0\n");
        out.push_str("  let c_must_be_zero := step.is_and + step.is_xor + step.is_or\n");
        out.push_str("  ZKBuilder.constrainR1CS c_must_be_zero step.flag_c 0\n");
        out.push_str("  let c_must_be_one := step.is_scf\n");
        out.push_str("  ZKBuilder.constrainR1CS c_must_be_one (step.flag_c - 1) 0\n");
        out.push_str("  -- Register coupling: ties alu_operand_a/b to a concrete register file\n");
        out.push_str("  -- via one-hot source selectors. Closes the coupling caveat for the\n");
        out.push_str("  -- single-step refinement theorem.\n");
        out.push_str("  register_coupling_constraints step\n");
        out.push_str("  -- ADD value-level lookup: alu_operand_a + alu_operand_b = alu_result + flag_c * 256\n");
        out.push_str("  -- (closes Gap A for ADD when is_add = 1)\n");
        out.push_str("  table_constraint_add step\n");
        out.push_str("  -- SUB value-level lookup: alu_operand_a + flag_c * 256 = alu_result + alu_operand_b\n");
        out.push_str("  -- (closes Gap A for SUB when is_sub = 1)\n");
        out.push_str("  table_constraint_sub step\n");
        out.push_str("  -- INC value-level lookup: alu_operand_a + 1 = alu_result + inc_overflow * 256\n");
        out.push_str("  table_constraint_inc step\n");
        out.push_str("  -- DEC value-level lookup: alu_operand_a + inc_overflow * 256 = alu_result + 1\n");
        out.push_str("  table_constraint_dec step\n");
        out.push_str("  -- Global flag_c boolean (required by table_constraint_add / table_constraint_sub)\n");
        out.push_str("  flag_c_boolean_constraint step\n");
        out.push_str("  -- Global inc_overflow boolean (required by table_constraint_inc / table_constraint_dec)\n");
        out.push_str("  inc_overflow_boolean_constraint step\n");
        // ----- Shifts / rotates / SWAP value-level constraints -----
        // SLA: alu_operand_a * 2 = alu_result + flag_c * 256 (when is_sla = 1)
        out.push_str("  -- SLA: alu_operand_a * 2 = alu_result + flag_c * 256\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_sla\n");
        out.push_str("    (step.alu_operand_a * 2 - step.alu_result - step.flag_c * 256) 0\n");
        // SRL: alu_operand_a = alu_result * 2 + flag_c (when is_srl = 1)
        out.push_str("  -- SRL: alu_operand_a = alu_result * 2 + flag_c\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_srl\n");
        out.push_str("    (step.alu_operand_a - step.alu_result * 2 - step.flag_c) 0\n");
        // RLC: flag_c = a_bit_7 AND alu_operand_a * 2 + a_bit_7 = alu_result + a_bit_7 * 256
        out.push_str("  -- RLC: flag_c = a_bit_7 (carry-out is bit 7)\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rlc (step.flag_c - step.a_bit_7) 0\n");
        out.push_str("  -- RLC: alu_operand_a * 2 + a_bit_7 = alu_result + a_bit_7 * 256\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rlc\n");
        out.push_str("    (step.alu_operand_a * 2 + step.a_bit_7 - step.alu_result - step.a_bit_7 * 256) 0\n");
        // RRC: flag_c = a_bit_0 AND alu_operand_a + a_bit_0 * 256 = alu_result * 2 + a_bit_0
        out.push_str("  -- RRC: flag_c = a_bit_0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rrc (step.flag_c - step.a_bit_0) 0\n");
        out.push_str("  -- RRC: alu_operand_a + a_bit_0 * 256 = alu_result * 2 + a_bit_0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rrc\n");
        out.push_str("    (step.alu_operand_a + step.a_bit_0 * 256 - step.alu_result * 2 - step.a_bit_0) 0\n");
        // SRA: flag_c = a_bit_0 AND alu_operand_a + a_bit_7 * 256 = alu_result * 2 + flag_c
        out.push_str("  -- SRA: flag_c = a_bit_0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_sra (step.flag_c - step.a_bit_0) 0\n");
        out.push_str("  -- SRA: alu_operand_a + a_bit_7 * 256 = alu_result * 2 + flag_c (sign-extending shift)\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_sra\n");
        out.push_str("    (step.alu_operand_a + step.a_bit_7 * 256 - step.alu_result * 2 - step.flag_c) 0\n");
        // SWAP: 8 per-bit constraints (bit-permutation)
        out.push_str("  -- SWAP: r_bit_i = a_bit_(perm i) where perm swaps the high and low nibbles\n");
        for i in 0..8 {
            // Permutation: nibble swap maps bit i ↔ bit i⊕4
            let src = i ^ 4;
            out.push_str(&format!(
                "  ZKBuilder.constrainR1CS step.is_swap (step.r_bit_{i} - step.a_bit_{src}) 0\n"
            ));
        }
        // Global Boolean constraint on `carry_in` (used by ADC/SBC/RL/RR).
        out.push_str("  -- Global carry_in boolean (required by ADC/SBC/RL/RR)\n");
        out.push_str("  ZKBuilder.constrainR1CS step.carry_in (step.carry_in - 1) 0\n");
        // ADC: alu_operand_a + alu_operand_b + carry_in = alu_result + flag_c * 256
        out.push_str("  -- ADC: a + b + carry_in = result + flag_c * 256\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_adc\n");
        out.push_str("    (step.alu_operand_a + step.alu_operand_b + step.carry_in - step.alu_result - step.flag_c * 256) 0\n");
        // SBC: alu_operand_a + flag_c * 256 = alu_result + alu_operand_b + carry_in
        out.push_str("  -- SBC: a + flag_c * 256 = result + b + carry_in\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_sbc\n");
        out.push_str("    (step.alu_operand_a + step.flag_c * 256 - step.alu_result - step.alu_operand_b - step.carry_in) 0\n");
        // CP: same shape as SUB (CP doesn't write back, but the constraint
        // system stores `a - b` in alu_result for soundness)
        out.push_str("  -- CP: a + flag_c * 256 = result + b (same as SUB)\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_cp\n");
        out.push_str("    (step.alu_operand_a + step.flag_c * 256 - step.alu_result - step.alu_operand_b) 0\n");
        // RL: rotate left through carry. flag_c becomes a_bit_7, result = (a*2) | carry_in.
        out.push_str("  -- RL: flag_c = a_bit_7\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rl (step.flag_c - step.a_bit_7) 0\n");
        out.push_str("  -- RL: a*2 + carry_in = result + a_bit_7 * 256\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rl\n");
        out.push_str("    (step.alu_operand_a * 2 + step.carry_in - step.alu_result - step.a_bit_7 * 256) 0\n");
        // RR: rotate right through carry. flag_c becomes a_bit_0, result = (a/2) | (carry_in << 7).
        out.push_str("  -- RR: flag_c = a_bit_0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rr (step.flag_c - step.a_bit_0) 0\n");
        out.push_str("  -- RR: a + carry_in * 256 = result * 2 + a_bit_0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_rr\n");
        out.push_str("    (step.alu_operand_a + step.carry_in * 256 - step.alu_result * 2 - step.a_bit_0) 0\n");
        // CPL: result = 255 - a (i.e., bitwise NOT in 8 bits).
        out.push_str("  -- CPL: a + result = 255\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_cpl (step.alu_operand_a + step.alu_result - 255) 0\n");
        // CCF: accumulator unchanged.
        out.push_str("  -- CCF: result = a (accumulator unchanged)\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_ccf (step.alu_result - step.alu_operand_a) 0\n");
        // SCF: accumulator unchanged.
        out.push_str("  -- SCF: result = a (accumulator unchanged)\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_scf (step.alu_result - step.alu_operand_a) 0\n");
        // ----- DAA: input flag Boolean constraints + polynomial lookup -----
        // DAA is a unary op that consumes the pre-op N/H/C flags. We witness
        // them via `daa_n_in / daa_h_in / daa_c_in` (Boolean) and enforce the
        // value-level constraint `alu_result = daa_poly_from_step(step)`
        // when `is_daa = 1`. `daa_poly_from_step` mirrors `daa_11_lookup_table`
        // from LookupTables.lean but is specialized to `SM83StepInputs f` +
        // `ZKExpr f`, so it only needs Add/Sub/Mul/OfNat (no Field).
        out.push_str("  -- DAA: pre-op flag inputs are Boolean\n");
        out.push_str("  ZKBuilder.constrainR1CS step.daa_n_in (step.daa_n_in - 1) 0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.daa_h_in (step.daa_h_in - 1) 0\n");
        out.push_str("  ZKBuilder.constrainR1CS step.daa_c_in (step.daa_c_in - 1) 0\n");
        // DAA polynomial constraint: alu_result = daa_poly_from_step step
        out.push_str("  -- DAA polynomial lookup: alu_result = daa_poly_from_step step when is_daa = 1\n");
        out.push_str("  ZKBuilder.constrainR1CS step.is_daa (step.alu_result - daa_poly_from_step step) 0\n");

        Ok(Module {
            name: "Constraints".into(),
            imports: vec!["zkLean".into(), "SM83.StepInputs".into()],
            contents: out.into_bytes(),
        })
    }
}
