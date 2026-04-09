//! Generates SM83/BitVecBridge.lean — bridge between MLE (Field) and BitVec spec domains.

use crate::modules::{AsModule, Module};

pub struct Sm83BitVecBridge;

impl Sm83BitVecBridge {
    pub fn extract() -> Self {
        Self
    }
}

impl AsModule for Sm83BitVecBridge {
    fn as_module(&self) -> std::io::Result<Module> {
        let contents = concat!(
            "/-! # BitVec Bridge\n",
            "\n",
            "Bridge between MLE domain (`Vector f N` with Boolean entries) and\n",
            "spec domain (`BitVec 8`). Used by correctness proofs.\n",
            "-/\n",
            "\n",
            "/-- Convert a natural number to its LSB-first bit decomposition as a field vector.\n",
            "    At Boolean points, the MLE evaluates to the same natural number as the spec. -/\n",
            "def bitsOf8 [Field f] (n : Fin 256) : Vector f 8 :=\n",
            "  Vector.ofFn fun (i : Fin 8) =>\n",
            "    if (n.val / 2 ^ i.val) % 2 = 1 then (1 : f) else (0 : f)\n",
            "\n",
            "/-- 11-variable version for DAA (a[0..7], N, H, C). -/\n",
            "def bitsOf11 [Field f] (n : Fin 2048) : Vector f 11 :=\n",
            "  Vector.ofFn fun (i : Fin 11) =>\n",
            "    if (n.val / 2 ^ i.val) % 2 = 1 then (1 : f) else (0 : f)\n",
            "\n",
            "/-- 16-variable version for binary tables (a[0..7], b[0..7]). -/\n",
            "def bitsOf16 [Field f] (n : Fin 65536) : Vector f 16 :=\n",
            "  Vector.ofFn fun (i : Fin 16) =>\n",
            "    if (n.val / 2 ^ i.val) % 2 = 1 then (1 : f) else (0 : f)\n",
            "\n",
            "-- Concrete field for decidable proofs: ZMod 257 (prime, > 255)\n",
            "instance : Fact (Nat.Prime 257) := ⟨by native_decide⟩\n",
            "abbrev ProofField := ZMod 257\n",
        );

        Ok(Module {
            name: "BitVecBridge".into(),
            imports: vec![
                "zkLean".into(),
                "Mathlib.Data.ZMod.Defs".into(),
                "Mathlib.Algebra.Field.ZMod".into(),
                "Mathlib.Data.Nat.Prime.Defs".into(),
            ],
            contents: contents.as_bytes().to_vec(),
        })
    }
}
