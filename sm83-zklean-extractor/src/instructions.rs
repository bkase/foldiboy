//! Generates the SM83/Instructions.lean module — maps instructions to lookup tables.

use crate::modules::{AsModule, Module};

/// Represents how operands are combined for a lookup.
#[derive(Debug, Clone, Copy)]
pub enum Interleaving {
    Concatenated,
    Interleaved,
}

impl std::fmt::Display for Interleaving {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Concatenated => write!(f, "Concatenated"),
            Self::Interleaved => write!(f, "Interleaved"),
        }
    }
}

struct InstructionDef {
    name: &'static str,
    table: &'static str,
    interleaving: Interleaving,
    num_vars: usize,
    flag_pattern: &'static str,
}

fn all_instructions() -> Vec<InstructionDef> {
    vec![
        // Binary ALU (16 vars)
        InstructionDef { name: "sm83_add", table: "add_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 16, flag_pattern: "z0hc" },
        InstructionDef { name: "sm83_sub", table: "sub_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 16, flag_pattern: "z1hc" },
        InstructionDef { name: "sm83_and", table: "and_8_lookup_table", interleaving: Interleaving::Interleaved, num_vars: 16, flag_pattern: "z010" },
        InstructionDef { name: "sm83_xor", table: "xor_8_lookup_table", interleaving: Interleaving::Interleaved, num_vars: 16, flag_pattern: "z000" },
        InstructionDef { name: "sm83_or", table: "or_8_lookup_table", interleaving: Interleaving::Interleaved, num_vars: 16, flag_pattern: "z000" },
        // Unary ALU (8 vars)
        InstructionDef { name: "sm83_inc", table: "inc_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z0h-" },
        InstructionDef { name: "sm83_dec", table: "dec_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z1h-" },
        InstructionDef { name: "sm83_rlc", table: "rlc_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z00c" },
        InstructionDef { name: "sm83_rrc", table: "rrc_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z00c" },
        InstructionDef { name: "sm83_sla", table: "sla_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z00c" },
        InstructionDef { name: "sm83_sra", table: "sra_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z00c" },
        InstructionDef { name: "sm83_srl", table: "srl_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z00c" },
        InstructionDef { name: "sm83_swap", table: "swap_8_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 8, flag_pattern: "z000" },
        // DAA (11 vars)
        InstructionDef { name: "sm83_daa", table: "daa_11_lookup_table", interleaving: Interleaving::Concatenated, num_vars: 11, flag_pattern: "z-0c" },
    ]
}

pub struct Sm83Instructions;

impl Sm83Instructions {
    pub fn extract() -> Self {
        Self
    }
}

impl AsModule for Sm83Instructions {
    fn as_module(&self) -> std::io::Result<Module> {
        let mut contents = Vec::new();

        for instr in all_instructions() {
            let line = format!(
                "noncomputable def {} [Field f] : LookupTableMLE f {} :=\n  -- Flag pattern: {}\n  LookupTableMLE.mk Interleaving.{} ({} : Vector f {} -> f)\n\n",
                instr.name,
                instr.num_vars,
                instr.flag_pattern,
                instr.interleaving,
                instr.table,
                instr.num_vars,
            );
            contents.extend_from_slice(line.as_bytes());
        }

        // Bit-variant instructions
        for bit in 0..8u8 {
            for (prefix, table_prefix, pattern) in [
                ("bit", "bit", "z01-"),
                ("res", "res", "----"),
                ("set", "set", "----"),
            ] {
                let line = format!(
                    "noncomputable def sm83_{prefix}_{bit} [Field f] : LookupTableMLE f 8 :=\n  -- Flag pattern: {pattern}\n  LookupTableMLE.mk Interleaving.Concatenated ({table_prefix}_{bit}_8_lookup_table : Vector f 8 -> f)\n\n",
                );
                contents.extend_from_slice(line.as_bytes());
            }
        }

        Ok(Module {
            name: "Instructions".into(),
            imports: vec!["zkLean".into(), "SM83.LookupTables".into()],
            contents,
        })
    }
}
