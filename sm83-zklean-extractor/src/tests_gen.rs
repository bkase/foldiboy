//! Generates SM83/Tests.lean with #guard tests for each lookup table.

use crate::modules::{AsModule, Module};
use crate::tables::Sm83Table;

pub struct Sm83Tests;

impl Sm83Tests {
    pub fn extract() -> Self {
        Self
    }
}

/// Convert a u8 value to its bit decomposition as a Lean Vector literal over F.
/// Bits are in LSB-first order: `(#v[(b0 : F), ..., (b7 : F)])`
fn byte_to_lean_vec(val: u8) -> String {
    let bits: Vec<String> = (0..8)
        .map(|i| if val & (1 << i) != 0 { "(1 : F)" } else { "(0 : F)" })
        .map(String::from)
        .collect();
    format!("#v[{}]", bits.join(", "))
}

/// Convert a binary (a, b) input to a Lean Vector literal over 16 variables.
fn binary_input_to_lean_vec(a: u8, b: u8) -> String {
    let mut bits = Vec::with_capacity(16);
    for i in 0..8 {
        bits.push(if a & (1 << i) != 0 { "(1 : F)" } else { "(0 : F)" });
    }
    for i in 0..8 {
        bits.push(if b & (1 << i) != 0 { "(1 : F)" } else { "(0 : F)" });
    }
    format!("#v[{}]", bits.join(", "))
}

impl AsModule for Sm83Tests {
    fn as_module(&self) -> std::io::Result<Module> {
        let mut out = String::new();

        out.push_str("-- Auto-generated tests: verify MLE at Boolean points matches ALU.\n");
        out.push_str("-- Uses ProofField (= ZMod 257) as the concrete field for evaluation.\n\n");
        out.push_str("private abbrev F := ProofField\n\n");

        // Test a selection of unary tables exhaustively (they're small)
        for table in [Sm83Table::Inc, Sm83Table::Dec, Sm83Table::Swap] {
            let tt = table.truth_table();
            let name = format!("{}_lookup_table", table.name());
            out.push_str(&format!("-- Tests for {name}\n"));
            // Test all 256 inputs
            for input in 0..=255u8 {
                let expected = tt[input as usize];
                let vec_lit = byte_to_lean_vec(input);
                out.push_str(&format!(
                    "#guard (@{name} F _ {vec_lit}) = ({expected} : F)\n"
                ));
            }
            out.push('\n');
        }

        // Test closed-form tables at corners
        for table in [Sm83Table::And, Sm83Table::Xor, Sm83Table::Or] {
            let tt = table.truth_table();
            let name = format!("{}_lookup_table", table.name());
            out.push_str(&format!("-- Corner tests for {name}\n"));
            let test_cases: Vec<(u8, u8)> = vec![
                (0, 0),
                (0xFF, 0xFF),
                (0xFF, 0),
                (0, 0xFF),
                (0x55, 0xAA),
                (0xAA, 0x55),
                (1, 1),
                (0x0F, 0xF0),
            ];
            for (a, b) in test_cases {
                let expected = tt[a as usize + ((b as usize) << 8)];
                let vec_lit = binary_input_to_lean_vec(a, b);
                out.push_str(&format!(
                    "#guard (@{name} F _ {vec_lit}) = ({expected} : F)\n"
                ));
            }
            out.push('\n');
        }

        // BIT test
        for bit in [0u8, 4, 7] {
            let table = Sm83Table::Bit(bit);
            let tt = table.truth_table();
            let name = format!("{}_lookup_table", table.name());
            out.push_str(&format!("-- Tests for {name}\n"));
            for input in [0u8, 1 << bit, 0xFF, 0] {
                let expected = tt[input as usize];
                let vec_lit = byte_to_lean_vec(input);
                out.push_str(&format!(
                    "#guard (@{name} F _ {vec_lit}) = ({expected} : F)\n"
                ));
            }
            out.push('\n');
        }

        Ok(Module {
            name: "Tests".into(),
            imports: vec!["SM83.LookupTables".into(), "SM83.BitVecBridge".into()],
            contents: out.into_bytes(),
        })
    }
}
