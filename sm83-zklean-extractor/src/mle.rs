//! MLE (Multilinear Extension) construction from truth tables and closed-form expressions.
//!
//! Two strategies:
//! 1. **Closed-form**: For AND, OR, XOR, SWAP, etc. — compact polynomial expressions.
//! 2. **Interpolation**: For ADD, SUB, shifts, DAA — compute MLE coefficients from truth table.
//! 3. **Flat array**: For binary tables (ADD, SUB) where interpolation yields too many terms
//!    for Lean to handle — output as a hex-encoded ByteArray with a Lean evaluator.

use crate::tables::{Sm83Table, TableKind};

/// Generate the Lean definition for a lookup table's MLE.
pub fn table_to_lean(table: Sm83Table) -> String {
    let name = format!("{}_lookup_table", table.name());
    let n = table.num_vars();

    if table.has_closed_form() {
        closed_form_lean(table, &name, n)
    } else if matches!(table, Sm83Table::Add | Sm83Table::Sub) {
        ripple_carry_lean(table, &name)
    } else if table.kind() == TableKind::Daa {
        daa_lean(&name)
    } else {
        // Unary tables: interpolate (at most 256 terms)
        interpolated_lean(table, &name, n)
    }
}

// ---------------------------------------------------------------------------
// Closed-form MLEs
// ---------------------------------------------------------------------------

fn closed_form_lean(table: Sm83Table, name: &str, n: usize) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "def {name} [Field f] (x : Vector f {n}) : f :=\n"
    ));

    match table {
        Sm83Table::And => {
            // AND(a, b) bit i = a_i * b_i
            // MLE = sum_{i=0}^{7} 2^i * x[i] * x[i+8]
            let terms: Vec<String> = (0..8)
                .map(|i| format!("{} * x[{}] * x[{}]", 1u32 << i, i, i + 8))
                .collect();
            out.push_str(&format!("  {}\n", terms.join(" + ")));
        }
        Sm83Table::Or => {
            // OR(a, b) bit i = a_i + b_i - a_i * b_i
            let terms: Vec<String> = (0..8)
                .map(|i| {
                    format!(
                        "{} * (x[{}] + x[{}] - x[{}] * x[{}])",
                        1u32 << i,
                        i,
                        i + 8,
                        i,
                        i + 8
                    )
                })
                .collect();
            out.push_str(&format!("  {}\n", terms.join(" + ")));
        }
        Sm83Table::Xor => {
            // XOR(a, b) bit i = a_i + b_i - 2 * a_i * b_i
            let terms: Vec<String> = (0..8)
                .map(|i| {
                    format!(
                        "{} * (x[{}] + x[{}] - 2 * x[{}] * x[{}])",
                        1u32 << i,
                        i,
                        i + 8,
                        i,
                        i + 8
                    )
                })
                .collect();
            out.push_str(&format!("  {}\n", terms.join(" + ")));
        }
        Sm83Table::LowerNibble => {
            // x & 0x0F = sum_{i=0}^{3} 2^i * x[i]
            let terms: Vec<String> = (0..4)
                .map(|i| format!("{} * x[{}]", 1u32 << i, i))
                .collect();
            out.push_str(&format!("  {}\n", terms.join(" + ")));
        }
        Sm83Table::Swap => {
            // SWAP(x) = (x >> 4) | (x << 4)
            // bit i of result: if i < 4 then x[i+4], else x[i-4]
            let terms: Vec<String> = (0..8)
                .map(|i| {
                    let src = if i < 4 { i + 4 } else { i - 4 };
                    format!("{} * x[{}]", 1u32 << i, src)
                })
                .collect();
            out.push_str(&format!("  {}\n", terms.join(" + ")));
        }
        Sm83Table::Set(bit) => {
            // SET n: result bit i = x[i] if i != n, else 1
            let terms: Vec<String> = (0..8)
                .map(|i| {
                    if i == bit {
                        format!("{}", 1u32 << i)
                    } else {
                        format!("{} * x[{}]", 1u32 << i, i)
                    }
                })
                .collect();
            out.push_str(&format!("  {}\n", terms.join(" + ")));
        }
        Sm83Table::Res(bit) => {
            // RES n: result bit i = x[i] if i != n, else 0
            let terms: Vec<String> = (0..8)
                .filter(|&i| i != bit)
                .map(|i| format!("{} * x[{}]", 1u32 << i, i))
                .collect();
            if terms.is_empty() {
                out.push_str("  0\n");
            } else {
                out.push_str(&format!("  {}\n", terms.join(" + ")));
            }
        }
        Sm83Table::Bit(bit) => {
            // BIT n: returns flags byte.
            // If x[n]=0: Z=1,H=1 → 0xA0. If x[n]=1: Z=0,H=1 → 0x20.
            // MLE: 0xA0 - 0x80 * x[n]  (corrected per review)
            // Use (160 + (0 - 128) * x[n]) to avoid negative literal
            out.push_str(&format!("  160 - 128 * x[{}]\n", bit));
            // Note: In Lean [Field f], `160 - 128 * x[n]` is fine because
            // Sub on f is defined. The issue is only with bare negative Int literals.
        }
        _ => unreachable!("not a closed-form table"),
    }

    out
}

// ---------------------------------------------------------------------------
// Ripple-carry adder/subtractor for ADD, SUB
// ---------------------------------------------------------------------------

/// Generate a ripple-carry adder in Lean.
///
/// For ADD: carry_0 = 0, a_i = x[i], b_i = x[i+8]
/// For SUB: carry_0 = 1, a_i = x[i], b_i = (1 - x[i+8])  (two's complement: NOT + 1)
///
/// At each bit:
///   sum_i  = XOR3(a_i, b_i, c_i) = a_i + b_i + c_i - 2*(a_i*b_i + a_i*c_i + b_i*c_i) + 4*a_i*b_i*c_i
///   c_{i+1} = MAJ(a_i, b_i, c_i) = a_i*b_i + a_i*c_i + b_i*c_i - 2*a_i*b_i*c_i
///
/// result = Σ 2^i * sum_i
fn ripple_carry_lean(table: Sm83Table, name: &str) -> String {
    let is_sub = matches!(table, Sm83Table::Sub);
    let mut out = String::new();

    out.push_str(&format!(
        "/-- {} via 8-bit ripple-carry {}. --/\n",
        name,
        if is_sub { "subtractor (two's complement)" } else { "adder" }
    ));
    out.push_str(&format!(
        "def {name} [Field f] (x : Vector f 16) : f :=\n"
    ));

    // Bind input bits
    for i in 0..8 {
        out.push_str(&format!("  let a{i} := x[{i}]\n"));
    }
    if is_sub {
        // SUB: b_i = 1 - x[i+8] (bitwise NOT), carry_0 = 1 (add 1 for two's complement)
        for i in 0..8 {
            out.push_str(&format!("  let b{i} := 1 - x[{}]\n", i + 8));
        }
        out.push_str("  let c0 : f := 1\n");
    } else {
        for i in 0..8 {
            out.push_str(&format!("  let b{i} := x[{}]\n", i + 8));
        }
        out.push_str("  let c0 : f := 0\n");
    }

    // Ripple-carry chain
    for i in 0..8 {
        // MAJ(a, b, c) = a*b + a*c + b*c - 2*a*b*c
        // XOR3(a, b, c) = a + b + c - 2*(a*b + a*c + b*c) + 4*a*b*c
        out.push_str(&format!(
            "  let ab{i} := a{i} * b{i}\n"
        ));
        out.push_str(&format!(
            "  let ac{i} := a{i} * c{i}\n"
        ));
        out.push_str(&format!(
            "  let bc{i} := b{i} * c{i}\n"
        ));
        out.push_str(&format!(
            "  let abc{i} := ab{i} * c{i}\n"
        ));
        out.push_str(&format!(
            "  let s{i} := a{i} + b{i} + c{i} - 2 * (ab{i} + ac{i} + bc{i}) + 4 * abc{i}\n"
        ));
        if i < 7 {
            out.push_str(&format!(
                "  let c{} := ab{i} + ac{i} + bc{i} - 2 * abc{i}\n",
                i + 1
            ));
        }
    }

    // Result = Σ 2^i * s_i
    let result_terms: Vec<String> = (0..8)
        .map(|i| {
            if i == 0 {
                format!("s{i}")
            } else {
                format!("{} * s{i}", 1u32 << i)
            }
        })
        .collect();
    out.push_str(&format!("  {}\n", result_terms.join(" + ")));

    out
}

// ---------------------------------------------------------------------------
// DAA — sorry for now, needs conditional logic
// ---------------------------------------------------------------------------

/// Generate the DAA (Decimal Adjust Accumulator) as field polynomials.
///
/// Inputs: x[0..7] = A bits (LSB first), x[8] = N, x[9] = H, x[10] = C
///
/// Logic:
///   low_nibble_gt_9 = a3 * (a2 + a1 - a2*a1)  // nibble in {10..15}
///   adj_lo = (!N * low_nibble_gt_9) + H - (!N * low_nibble_gt_9) * H  // OR
///   high_nibble_ge_10 = a7 * (a6 + a5 - a6*a5)
///   low_ge_10 = low_nibble_gt_9  (reuse)
///   high_eq_9 = a7_bar * a6_bar * a5_bar * a4  // exactly 1001 = 9
///     where a7_bar = 1-a7 etc. but actually high nibble=9 means a7=1,a6=0,a5=0,a4=1
///     Wait: 9 = 1001 in binary so a4=1, a5=0, a6=0, a7=1. No:
///     nibble = a4 + 2*a5 + 4*a6 + 8*a7. So 9 = a4=1, a5=0, a6=0, a7=1.
///   a_gt_0x99 = high_nibble_ge_10 + high_eq_9 * low_ge_10
///               - high_nibble_ge_10 * high_eq_9 * low_ge_10  // OR
///   adj_hi = (!N * a_gt_0x99) + C - (!N * a_gt_0x99) * C  // OR
///
///   offset = adj_lo * 6 + adj_hi * 96  (0x06 + 0x60)
///   result = if N: A - offset else: A + offset
///          = A + offset * (1 - 2*N)  // N=0 → +offset, N=1 → -offset
///   But we need mod 256, so use ripple-carry for A ± offset.
fn daa_lean(name: &str) -> String {
    let mut out = String::new();

    out.push_str(&format!(
        "/-- DAA (Decimal Adjust Accumulator) via field polynomial.\n"
    ));
    out.push_str("   Inputs: x[0..7] = A bits (LSB first), x[8] = N, x[9] = H, x[10] = C. --/\n");
    out.push_str(&format!(
        "def {name} [Field f] (x : Vector f 11) : f :=\n"
    ));

    // Bind inputs
    for i in 0..8 {
        out.push_str(&format!("  let a{i} := x[{i}]\n"));
    }
    out.push_str("  let N := x[8]\n");
    out.push_str("  let H := x[9]\n");
    out.push_str("  let C := x[10]\n");
    out.push_str("  let notN := 1 - N\n");

    // low_nibble > 9: nibble = a0 + 2*a1 + 4*a2 + 8*a3, values 10-15
    // = a3 AND (a2 OR a1)
    out.push_str("  let lo_gt9 := a3 * (a2 + a1 - a2 * a1)\n");

    // adj_lo = (notN * lo_gt9) OR H
    out.push_str("  let adj_lo_cond := notN * lo_gt9\n");
    out.push_str("  let adj_lo := adj_lo_cond + H - adj_lo_cond * H\n");

    // high_nibble >= 10: nibble = a4 + 2*a5 + 4*a6 + 8*a7, values 10-15
    // = a7 AND (a6 OR a5)
    out.push_str("  let hi_ge10 := a7 * (a6 + a5 - a6 * a5)\n");

    // high_nibble == 9: a4=1, a5=0, a6=0, a7=1
    // = a4 * (1-a5) * (1-a6) * a7
    out.push_str("  let hi_eq9 := a4 * (1 - a5) * (1 - a6) * a7\n");

    // A > 0x99: high >= 10, OR (high == 9 AND low >= 10)
    out.push_str("  let a_gt99 := hi_ge10 + hi_eq9 * lo_gt9 - hi_ge10 * hi_eq9 * lo_gt9\n");

    // adj_hi = (notN * a_gt99) OR C
    out.push_str("  let adj_hi_cond := notN * a_gt99\n");
    out.push_str("  let adj_hi := adj_hi_cond + C - adj_hi_cond * C\n");

    // offset bits: adj_lo * 0x06 + adj_hi * 0x60
    // 0x06 = 0b00000110, 0x60 = 0b01100000
    // Combined offset bits: b0=0, b1=adj_lo, b2=adj_lo, b3=0, b4=0, b5=adj_hi, b6=adj_hi, b7=0
    for i in 0..8 {
        let bit = match i {
            1 | 2 => "adj_lo",
            5 | 6 => "adj_hi",
            _ => "zero",
        };
        if bit == "zero" {
            out.push_str(&format!("  let off{i} : f := 0\n"));
        } else {
            out.push_str(&format!("  let off{i} := {bit}\n"));
        }
    }

    // sign: +1 if N=0, -1 if N=1 → (1 - 2*N)
    // For SUB case (N=1): result = A - offset
    // For ADD case (N=0): result = A + offset
    // Use ripple-carry: result = A + signed_offset mod 256
    // where signed_offset bits = if N then NOT(off) else off, carry_in = N
    // (two's complement: -offset = NOT(offset) + 1)

    // b_i = off_i XOR N = off_i + N - 2*off_i*N
    for i in 0..8 {
        out.push_str(&format!(
            "  let b{i} := off{i} + N - 2 * off{i} * N\n"
        ));
    }
    out.push_str("  -- Ripple-carry: A + (offset XOR N_mask) + N\n");
    out.push_str("  let cin : f := N\n");

    // Now do the same ripple-carry as ADD, but with a_i and b_i and cin
    // Reuse variable names with rc_ prefix
    out.push_str("  let rc_c0 := cin\n");
    for i in 0..8 {
        let c = format!("rc_c{i}");
        out.push_str(&format!("  let rc_ab{i} := a{i} * b{i}\n"));
        out.push_str(&format!("  let rc_ac{i} := a{i} * {c}\n"));
        out.push_str(&format!("  let rc_bc{i} := b{i} * {c}\n"));
        out.push_str(&format!("  let rc_abc{i} := rc_ab{i} * {c}\n"));
        out.push_str(&format!(
            "  let rc_s{i} := a{i} + b{i} + {c} - 2 * (rc_ab{i} + rc_ac{i} + rc_bc{i}) + 4 * rc_abc{i}\n"
        ));
        if i < 7 {
            out.push_str(&format!(
                "  let rc_c{} := rc_ab{i} + rc_ac{i} + rc_bc{i} - 2 * rc_abc{i}\n",
                i + 1
            ));
        }
    }

    let result_terms: Vec<String> = (0..8)
        .map(|i| {
            if i == 0 {
                format!("rc_s{i}")
            } else {
                format!("{} * rc_s{i}", 1u32 << i)
            }
        })
        .collect();
    out.push_str(&format!("  {}\n", result_terms.join(" + ")));

    out
}

// ---------------------------------------------------------------------------
// (removed: flat_array_lean — replaced by ripple_carry_lean + daa_lean)
// ---------------------------------------------------------------------------


// ---------------------------------------------------------------------------
// Interpolated MLE for small tables (unary, DAA)
// ---------------------------------------------------------------------------

fn interpolated_lean(table: Sm83Table, name: &str, n: usize) -> String {
    let tt = table.truth_table();
    let coeffs = interpolate_mle(&tt, n);

    let mut out = String::new();

    // Collect nonzero monomial terms, separating positive and negative.
    // Negative coefficients are emitted using subtraction to avoid Lean Int coercion issues.
    // Each term is (sign, lean_expr) where sign is true for positive.
    let mut signed_terms: Vec<(bool, String)> = Vec::new();
    for (mask, coeff) in coeffs.iter().enumerate() {
        if *coeff == 0i64 {
            continue;
        }
        let positive = *coeff > 0;
        let abs_coeff = coeff.unsigned_abs();
        let vars: Vec<String> = (0..n)
            .filter(|&i| mask & (1 << i) != 0)
            .map(|i| format!("x[{}]", i))
            .collect();
        let term = if vars.is_empty() {
            format!("{abs_coeff}")
        } else {
            let var_prod = vars.join(" * ");
            if abs_coeff == 1 {
                var_prod
            } else {
                format!("{abs_coeff} * {var_prod}")
            }
        };
        signed_terms.push((positive, term));
    }

    if signed_terms.is_empty() {
        signed_terms.push((true, "0".into()));
    }

    // Format as "pos + pos - neg - neg + pos ..."
    let terms: Vec<String> = signed_terms
        .iter()
        .enumerate()
        .map(|(i, (positive, term))| {
            if i == 0 {
                if *positive {
                    term.clone()
                } else {
                    // First term is negative — need explicit negation
                    format!("(0 - {term})")
                }
            } else if *positive {
                format!("+ {term}")
            } else {
                format!("- {term}")
            }
        })
        .collect();

    // For small tables, emit directly. For larger ones, use CSE-style chaining.
    if terms.len() <= 20 {
        out.push_str(&format!(
            "def {name} [Field f] (x : Vector f {n}) : f :=\n"
        ));
        out.push_str(&format!("  {}\n", terms.join(" ")));
    } else {
        // Chain CSE definitions, ~10 terms each
        let chunk_size = 10;
        let chunks: Vec<&[String]> = terms.chunks(chunk_size).collect();
        for (i, chunk) in chunks.iter().enumerate() {
            let cse_name = format!("{name}_cse_{i}");
            out.push_str(&format!(
                "def {cse_name} [Field f] (x : Vector f {n}) : f := "
            ));
            if i > 0 {
                out.push_str(&format!("{name}_cse_{} x ", i - 1));
            }
            out.push_str(&chunk.join(" "));
            out.push('\n');
        }
        let last = chunks.len() - 1;
        out.push_str(&format!(
            "def {name} [Field f] (x : Vector f {n}) : f := {name}_cse_{last} x\n"
        ));
    }

    out
}

/// Standard bottom-up multilinear interpolation.
///
/// Given truth table T[0..2^n], compute coefficients c[S] for each subset S ⊆ {0..n-1}
/// such that MLE(x) = Σ_S c[S] · Π_{i∈S} x[i].
///
/// Returns coefficients indexed by bitmask (bit i set means x[i] is in the monomial).
fn interpolate_mle(truth_table: &[u8], n: usize) -> Vec<i64> {
    let size = 1 << n;
    assert_eq!(truth_table.len(), size);

    let mut coeffs: Vec<i64> = truth_table.iter().map(|&v| v as i64).collect();

    for i in 0..n {
        let stride = 1 << i;
        for j in (0..size).step_by(stride * 2) {
            for k in 0..stride {
                let lo = coeffs[j + k];
                let hi = coeffs[j + k + stride];
                // lo stays as the coefficient for the monomial without x[i]
                // hi - lo becomes the coefficient for the monomial with x[i]
                coeffs[j + k + stride] = hi - lo;
            }
        }
    }

    coeffs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpolate_identity() {
        // f(x0, x1) on {0,1}^2: f(0,0)=0, f(1,0)=1, f(0,1)=2, f(1,1)=3
        // = 0 + 1*x0 + 2*x1 + 0*x0*x1
        let tt = vec![0u8, 1, 2, 3];
        let coeffs = interpolate_mle(&tt, 2);
        assert_eq!(coeffs, vec![0, 1, 2, 0]); // [const, x0, x1, x0*x1]
    }

    #[test]
    fn interpolate_and_2bit() {
        // AND on 2 bits: f(a, b) = a*b
        // f(0,0)=0, f(1,0)=0, f(0,1)=0, f(1,1)=1
        let tt = vec![0u8, 0, 0, 1];
        let coeffs = interpolate_mle(&tt, 2);
        assert_eq!(coeffs, vec![0, 0, 0, 1]); // only x0*x1 term
    }

    #[test]
    fn interpolate_inc_roundtrip() {
        // Verify MLE evaluation at Boolean points matches truth table
        let table = Sm83Table::Inc;
        let tt = table.truth_table();
        let coeffs = interpolate_mle(&tt, 8);

        // Spot check a few points
        for input in [0u8, 1, 127, 128, 255] {
            let expected = tt[input as usize] as i64;
            let mut val = 0i64;
            for (mask, &c) in coeffs.iter().enumerate() {
                if c == 0 {
                    continue;
                }
                let all_bits_set = (0..8).all(|i| {
                    if mask & (1 << i) != 0 {
                        input & (1 << i) != 0
                    } else {
                        true
                    }
                });
                if all_bits_set {
                    val += c;
                }
            }
            assert_eq!(val, expected, "MLE mismatch at input {input}");
        }
    }

    #[test]
    fn closed_form_and_generates_lean() {
        let lean = table_to_lean(Sm83Table::And);
        assert!(lean.contains("x[0] * x[8]"));
        assert!(lean.contains("128 * x[7] * x[15]"));
    }

    #[test]
    fn closed_form_bit_corrected() {
        let lean = table_to_lean(Sm83Table::Bit(4));
        // Should be 0xA0 - 0x80 * x[4] = 160 - 128 * x[4]
        assert!(lean.contains("160 - 128 * x[4]"));
    }

    #[test]
    fn ripple_carry_add() {
        let lean = table_to_lean(Sm83Table::Add);
        assert!(lean.contains("ripple-carry adder"));
        assert!(lean.contains("let c0 : f := 0"));
        assert!(lean.contains("let s7"));
    }

    #[test]
    fn ripple_carry_sub() {
        let lean = table_to_lean(Sm83Table::Sub);
        assert!(lean.contains("two's complement"));
        assert!(lean.contains("let c0 : f := 1"));
        assert!(lean.contains("1 - x["));
    }

    // -----------------------------------------------------------------------
    // Exhaustive evaluation tests: verify formulas match truth tables at ALL
    // Boolean inputs. This is the primary correctness guarantee.
    // -----------------------------------------------------------------------

    /// Evaluate a ripple-carry add/sub formula at a Boolean point.
    /// `bits` is the bit vector (LSB first), `is_sub` selects subtraction.
    fn eval_ripple_carry(bits: &[i64], is_sub: bool) -> i64 {
        assert_eq!(bits.len(), 16);
        let a: Vec<i64> = bits[0..8].to_vec();
        let b: Vec<i64> = if is_sub {
            bits[8..16].iter().map(|&x| 1 - x).collect()
        } else {
            bits[8..16].to_vec()
        };
        let mut carry: i64 = if is_sub { 1 } else { 0 };
        let mut result = 0i64;
        for i in 0..8 {
            let ab = a[i] * b[i];
            let ac = a[i] * carry;
            let bc = b[i] * carry;
            let abc = ab * carry;
            let s = a[i] + b[i] + carry - 2 * (ab + ac + bc) + 4 * abc;
            carry = ab + ac + bc - 2 * abc;
            result += (1i64 << i) * s;
        }
        result
    }

    /// Evaluate a closed-form formula at a Boolean point.
    fn eval_closed_form(table: Sm83Table, bits: &[i64]) -> i64 {
        match table {
            Sm83Table::And => {
                (0..8).map(|i| (1i64 << i) * bits[i] * bits[i + 8]).sum()
            }
            Sm83Table::Or => {
                (0..8).map(|i| (1i64 << i) * (bits[i] + bits[i + 8] - bits[i] * bits[i + 8])).sum()
            }
            Sm83Table::Xor => {
                (0..8).map(|i| (1i64 << i) * (bits[i] + bits[i + 8] - 2 * bits[i] * bits[i + 8])).sum()
            }
            Sm83Table::LowerNibble => {
                (0..4).map(|i| (1i64 << i) * bits[i]).sum()
            }
            Sm83Table::Swap => {
                (0..8).map(|i| {
                    let src = if i < 4 { i + 4 } else { i - 4 };
                    (1i64 << i) * bits[src]
                }).sum()
            }
            Sm83Table::Set(n) => {
                (0..8usize).map(|i| {
                    if i == n as usize { 1i64 << i } else { (1i64 << i) * bits[i] }
                }).sum()
            }
            Sm83Table::Res(n) => {
                (0..8usize).filter(|&i| i != n as usize).map(|i| (1i64 << i) * bits[i]).sum()
            }
            Sm83Table::Bit(n) => {
                160 - 128 * bits[n as usize]
            }
            _ => panic!("no closed form for {:?}", table),
        }
    }

    /// Evaluate the DAA formula at a Boolean point.
    fn eval_daa(bits: &[i64]) -> i64 {
        assert_eq!(bits.len(), 11);
        let a: Vec<i64> = bits[0..8].to_vec();
        let n_flag = bits[8];
        let h_flag = bits[9];
        let c_flag = bits[10];
        let not_n = 1 - n_flag;

        // lo_gt9 = a3 * (a2 + a1 - a2 * a1)
        let lo_gt9 = a[3] * (a[2] + a[1] - a[2] * a[1]);
        let adj_lo_cond = not_n * lo_gt9;
        let adj_lo = adj_lo_cond + h_flag - adj_lo_cond * h_flag;

        let hi_ge10 = a[7] * (a[6] + a[5] - a[6] * a[5]);
        let hi_eq9 = a[4] * (1 - a[5]) * (1 - a[6]) * a[7];
        let a_gt99 = hi_ge10 + hi_eq9 * lo_gt9 - hi_ge10 * hi_eq9 * lo_gt9;
        let adj_hi_cond = not_n * a_gt99;
        let adj_hi = adj_hi_cond + c_flag - adj_hi_cond * c_flag;

        // offset bits
        let off = [0i64, adj_lo, adj_lo, 0, 0, adj_hi, adj_hi, 0];

        // b_i = off_i XOR N
        let b: Vec<i64> = off.iter().map(|&o| o + n_flag - 2 * o * n_flag).collect();

        // Ripple-carry: A + b + cin where cin = N
        let mut carry = n_flag;
        let mut result = 0i64;
        for i in 0..8 {
            let ab = a[i] * b[i];
            let ac = a[i] * carry;
            let bc = b[i] * carry;
            let abc = ab * carry;
            let s = a[i] + b[i] + carry - 2 * (ab + ac + bc) + 4 * abc;
            carry = ab + ac + bc - 2 * abc;
            result += (1i64 << i) * s;
        }
        result
    }

    /// Convert a usize to a Boolean bit vector (LSB first).
    fn to_bits(val: usize, n: usize) -> Vec<i64> {
        (0..n).map(|i| if val & (1 << i) != 0 { 1 } else { 0 }).collect()
    }

    #[test]
    fn exhaustive_add_formula_matches_truth_table() {
        let tt = Sm83Table::Add.truth_table();
        for idx in 0..65536usize {
            let bits = to_bits(idx, 16);
            let formula = eval_ripple_carry(&bits, false);
            let expected = tt[idx] as i64;
            assert_eq!(formula, expected, "ADD mismatch at idx={idx} (a={}, b={})", idx & 0xFF, idx >> 8);
        }
    }

    #[test]
    fn exhaustive_sub_formula_matches_truth_table() {
        let tt = Sm83Table::Sub.truth_table();
        for idx in 0..65536usize {
            let bits = to_bits(idx, 16);
            let formula = eval_ripple_carry(&bits, true);
            let expected = tt[idx] as i64;
            assert_eq!(formula, expected, "SUB mismatch at idx={idx} (a={}, b={})", idx & 0xFF, idx >> 8);
        }
    }

    #[test]
    fn exhaustive_and_formula_matches_truth_table() {
        let tt = Sm83Table::And.truth_table();
        for idx in 0..65536usize {
            let bits = to_bits(idx, 16);
            let formula = eval_closed_form(Sm83Table::And, &bits);
            assert_eq!(formula, tt[idx] as i64, "AND mismatch at idx={idx}");
        }
    }

    #[test]
    fn exhaustive_xor_formula_matches_truth_table() {
        let tt = Sm83Table::Xor.truth_table();
        for idx in 0..65536usize {
            let bits = to_bits(idx, 16);
            let formula = eval_closed_form(Sm83Table::Xor, &bits);
            assert_eq!(formula, tt[idx] as i64, "XOR mismatch at idx={idx}");
        }
    }

    #[test]
    fn exhaustive_or_formula_matches_truth_table() {
        let tt = Sm83Table::Or.truth_table();
        for idx in 0..65536usize {
            let bits = to_bits(idx, 16);
            let formula = eval_closed_form(Sm83Table::Or, &bits);
            assert_eq!(formula, tt[idx] as i64, "OR mismatch at idx={idx}");
        }
    }

    #[test]
    fn exhaustive_daa_formula_matches_truth_table() {
        let tt = Sm83Table::Daa.truth_table();
        for idx in 0..2048usize {
            let bits = to_bits(idx, 11);
            let formula = eval_daa(&bits);
            let expected = tt[idx] as i64;
            assert_eq!(formula, expected,
                "DAA mismatch at idx={idx} (a={}, n={}, h={}, c={})",
                idx & 0xFF, bits[8], bits[9], bits[10]);
        }
    }

    #[test]
    fn exhaustive_all_unary_interpolated_tables() {
        // Verify interpolated MLEs match truth tables at ALL Boolean points
        for table in [Sm83Table::Inc, Sm83Table::Dec, Sm83Table::Rlc, Sm83Table::Rrc,
                      Sm83Table::Sla, Sm83Table::Sra, Sm83Table::Srl, Sm83Table::Swap] {
            let tt = table.truth_table();
            let coeffs = interpolate_mle(&tt, 8);
            for input in 0..256usize {
                let bits = to_bits(input, 8);
                let mut val = 0i64;
                for (mask, &c) in coeffs.iter().enumerate() {
                    if c == 0 { continue; }
                    let active = (0..8).all(|i| mask & (1 << i) == 0 || bits[i] == 1);
                    if active { val += c; }
                }
                assert_eq!(val, tt[input] as i64,
                    "{:?} mismatch at input={input}", table);
            }
        }
    }

    #[test]
    fn exhaustive_bit_res_set_formulas() {
        for bit in 0..8u8 {
            for table in [Sm83Table::Bit(bit), Sm83Table::Res(bit), Sm83Table::Set(bit)] {
                let tt = table.truth_table();
                for input in 0..256usize {
                    let bits = to_bits(input, 8);
                    let formula = eval_closed_form(table, &bits);
                    assert_eq!(formula, tt[input] as i64,
                        "{:?} mismatch at input={input}", table);
                }
            }
        }
    }
}
