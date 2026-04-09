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

        // -- Master constraint: Z flag --
        // is_zero_constraint is ALWAYS applied. It forces:
        //   result * result_inv = 1 - Z  and  Z * result = 0
        // This is always satisfiable: the prover sets result_inv = result⁻¹ (or 0).
        // For opcodes that don't update Z (LD, JP, etc.), the execution trace layer
        // handles flag carry-through — at the step level, Z is always well-defined.
        out.push_str("-- | Master constraints: enforce all flag relationships for one ALU step.\n");
        out.push_str("def master_constraints [ZKField f] (step : SM83StepInputs f) : ZKBuilder f PUnit := do\n");
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
        out.push_str("  pure ()\n");

        Ok(Module {
            name: "Constraints".into(),
            imports: vec!["zkLean".into(), "SM83.StepInputs".into()],
            contents: out.into_bytes(),
        })
    }
}
