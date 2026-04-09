/-
  SM83 ZK utilities: MLE evaluation from truth tables stored as ByteArrays.
-/
import Mathlib.Algebra.Field.Defs

/-- Evaluate a multilinear extension from a truth table stored as a ByteArray.

  Given a truth table `data` of length `2^n` (mapping each Boolean input to a `UInt8` value),
  and a point `x : Vector f n`, compute the standard streaming MLE evaluation.
-/
noncomputable def evalMleFromByteArray {f : Type*} [Field f]
    (data : ByteArray) (n : Nat) (x : Vector f n) : f :=
  -- Convert truth table to field elements
  let init : Array f := data.data.map fun b => (b.toNat : f)
  -- Fold over each variable: interpolate pairs
  let result := (List.range n).foldl (fun (arr : Array f) (i : Nat) =>
    let halfLen := arr.size / 2
    let xi := x.getD i 0
    Array.ofFn fun (j : Fin halfLen) =>
      let lo := arr.getD (2 * j.val) 0
      let hi := arr.getD (2 * j.val + 1) 0
      lo * (1 - xi) + hi * xi
  ) init
  result.getD 0 0
