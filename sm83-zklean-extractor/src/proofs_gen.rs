//! Generates SM83/Proofs.lean — correctness proofs for lookup tables.
//!
//! Phase 2A: `decide` proofs for all 33 eight-variable tables.
//! Proves each MLE lookup table matches the BitVec spec at all Boolean inputs.
//!
//! Uses ZMod 257 as the concrete proof field (prime, > 255, fast kernel arithmetic).
//! `dec` uses `native_decide` due to deep CSE chain nesting.

use crate::modules::{AsModule, Module};
use crate::spec_gen::{spec_application, spec_fn_name};
use crate::tables::{Sm83Table, TableKind};

/// Proof strategy for a lookup table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofStrategy {
    /// `∀ (n : Fin N), ...` proved by `decide`
    Decide,
    /// `∀ (n : Fin N), ...` proved by `native_decide` (deep CSE chains)
    NativeDecide,
    /// `bv_decide` via SAT solver (for DAA, 11-var)
    BvDecide,
    /// `solveMLE` or `bv_decide` (for binary 16-var tables)
    SolveMLE,
}

impl Sm83Table {
    /// Determine the proof strategy for this table.
    pub fn proof_strategy(self) -> ProofStrategy {
        match self {
            // Dec has 25+ CSE helper defs — needs native_decide
            Self::Dec => ProofStrategy::NativeDecide,
            // All other 8-var tables: simple polynomials, decide handles them
            _ if self.kind() == TableKind::Unary => ProofStrategy::Decide,
            // DAA: 11-var, use bv_decide (Phase 2B)
            Self::Daa => ProofStrategy::BvDecide,
            // Binary 16-var: solveMLE or bv_decide (Phase 2C/2D)
            _ => ProofStrategy::SolveMLE,
        }
    }
}

pub struct Sm83Proofs;

impl Sm83Proofs {
    pub fn extract() -> Self {
        Self
    }
}

/// Generate a proof for a single 8-variable table.
fn proof_for_unary_table(table: Sm83Table) -> String {
    assert_eq!(table.kind(), TableKind::Unary);

    let table_name = format!("{}_lookup_table", table.name());
    let theorem_name = format!("{}_correct", table.name());
    let spec_app = spec_application(table);

    let tactic = match table.proof_strategy() {
        ProofStrategy::Decide => "decide",
        ProofStrategy::NativeDecide => "native_decide",
        _ => unreachable!("unary table with non-decide strategy"),
    };

    format!(
        concat!(
            "theorem {theorem} : ∀ (n : Fin 256),\n",
            "    @{table} F _ (@bitsOf8 F _ n) =\n",
            "    (({spec}) : F) := by\n",
            "  {tactic}\n",
        ),
        theorem = theorem_name,
        table = table_name,
        spec = spec_app,
        tactic = tactic,
    )
}

impl AsModule for Sm83Proofs {
    fn as_module(&self) -> std::io::Result<Module> {
        let mut out = String::new();
        out.push_str("/-! # Lookup Table Correctness Proofs\n");
        out.push_str("\n");
        out.push_str("Each theorem proves that the MLE lookup table, evaluated at Boolean\n");
        out.push_str("field points, equals the BitVec spec applied to the same input.\n");
        out.push_str("\n");
        out.push_str("Phase 2A: 33 eight-variable tables proved by `decide`.\n");
        out.push_str("Uses ZMod 257 as the concrete proof field.\n");
        out.push_str("-/\n\n");

        // ZMod 257 field alias
        out.push_str("set_option maxRecDepth 1024\n\n");
        out.push_str("private abbrev F := ProofField\n\n");

        // Phase 2A: all 8-variable tables
        let unary_tables: Vec<Sm83Table> = Sm83Table::all()
            .into_iter()
            .filter(|t| t.kind() == TableKind::Unary)
            .collect();

        for table in unary_tables {
            let fn_name = spec_fn_name(table);
            out.push_str(&format!("-- {} matches {}\n", table.name(), fn_name));
            out.push_str(&proof_for_unary_table(table));
            out.push('\n');
        }

        // Placeholders for future phases
        out.push_str("-- Phase 2B: DAA (11-var) — TODO: bv_decide\n");
        out.push_str("-- Phase 2C: AND/XOR/OR (16-var, closed-form) — TODO: solveMLE\n");
        out.push_str("-- Phase 2D: ADD/SUB (16-var, ripple-carry) — TODO: bv_decide\n");

        Ok(Module {
            name: "Proofs".into(),
            imports: vec![
                "SM83.LookupTables".into(),
                "SM83.Spec".into(),
                "SM83.BitVecBridge".into(),
            ],
            contents: out.into_bytes(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_unary_tables_have_proofs() {
        let proofs = Sm83Proofs::extract();
        let module = proofs.as_module().unwrap();
        let contents = String::from_utf8(module.contents).unwrap();

        for table in Sm83Table::all() {
            if table.kind() != TableKind::Unary {
                continue;
            }
            let theorem_name = format!("{}_correct", table.name());
            assert!(
                contents.contains(&theorem_name),
                "missing proof for {:?} (expected theorem {})",
                table,
                theorem_name
            );
        }
    }

    #[test]
    fn proof_count_is_33() {
        let proofs = Sm83Proofs::extract();
        let module = proofs.as_module().unwrap();
        let contents = String::from_utf8(module.contents).unwrap();
        let count = contents.matches("\ntheorem ").count();
        assert_eq!(count, 33, "expected 33 theorems for 8-var tables");
    }

    #[test]
    fn dec_uses_native_decide() {
        assert_eq!(Sm83Table::Dec.proof_strategy(), ProofStrategy::NativeDecide);
    }

    #[test]
    fn inc_uses_decide() {
        assert_eq!(Sm83Table::Inc.proof_strategy(), ProofStrategy::Decide);
    }

    #[test]
    fn only_dec_uses_native_decide() {
        for table in Sm83Table::all() {
            if table.kind() != TableKind::Unary {
                continue;
            }
            if table == Sm83Table::Dec {
                assert_eq!(table.proof_strategy(), ProofStrategy::NativeDecide);
            } else {
                assert_eq!(
                    table.proof_strategy(),
                    ProofStrategy::Decide,
                    "{:?} should use Decide",
                    table
                );
            }
        }
    }
}
