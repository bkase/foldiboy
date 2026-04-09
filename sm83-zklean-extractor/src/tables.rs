//! SM83 lookup table enumeration and truth table generation.
//!
//! Each table variant maps to one or more calls to foldiboy's pure ALU functions,
//! producing a complete truth table as `Vec<u8>`.

use cpu::alu::*;

/// All SM83 lookup tables as described in `docs/constraints.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sm83Table {
    // -- Unary (u8 -> u8): 256 entries, MLE over 8 variables --
    Inc,
    Dec,
    Rlc,
    Rrc,
    Sla,
    Sra,
    Srl,
    Swap,
    LowerNibble,

    // -- Bit-variant (u8 -> u8): 256 entries per bit, MLE over 8 variables --
    Bit(u8),
    Res(u8),
    Set(u8),

    // -- DAA: single 11-variable table (2048 entries) --
    // Inputs: (a[0..7], N, H, C) → result byte
    Daa,

    // -- Binary (u8 × u8 -> u8): 65536 entries, MLE over 16 variables --
    Add,
    Sub,
    And,
    Xor,
    Or,
}

/// Classification of table input width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TableKind {
    /// 8 boolean variables (256 entries)
    Unary,
    /// 11 boolean variables (2048 entries) — DAA with flag inputs
    Daa,
    /// 16 boolean variables (65536 entries)
    Binary,
}

impl Sm83Table {
    pub fn kind(self) -> TableKind {
        match self {
            Self::Inc | Self::Dec | Self::Rlc | Self::Rrc | Self::Sla | Self::Sra
            | Self::Srl | Self::Swap | Self::LowerNibble | Self::Bit(_) | Self::Res(_)
            | Self::Set(_) => TableKind::Unary,
            Self::Daa => TableKind::Daa,
            Self::Add | Self::Sub | Self::And | Self::Xor | Self::Or => TableKind::Binary,
        }
    }

    pub fn num_vars(self) -> usize {
        match self.kind() {
            TableKind::Unary => 8,
            TableKind::Daa => 11,
            TableKind::Binary => 16,
        }
    }

    pub fn name(self) -> String {
        match self {
            Self::Inc => "inc_8".into(),
            Self::Dec => "dec_8".into(),
            Self::Rlc => "rlc_8".into(),
            Self::Rrc => "rrc_8".into(),
            Self::Sla => "sla_8".into(),
            Self::Sra => "sra_8".into(),
            Self::Srl => "srl_8".into(),
            Self::Swap => "swap_8".into(),
            Self::LowerNibble => "lower_nibble_8".into(),
            Self::Bit(n) => format!("bit_{n}_8"),
            Self::Res(n) => format!("res_{n}_8"),
            Self::Set(n) => format!("set_{n}_8"),
            Self::Daa => "daa_11".into(),
            Self::Add => "add_8".into(),
            Self::Sub => "sub_8".into(),
            Self::And => "and_8".into(),
            Self::Xor => "xor_8".into(),
            Self::Or => "or_8".into(),
        }
    }

    /// Generate the complete truth table by calling foldiboy's pure ALU.
    /// Returns values indexed by the bit-decomposed input treated as a little-endian integer.
    pub fn truth_table(self) -> Vec<u8> {
        match self.kind() {
            TableKind::Unary => self.truth_table_unary(),
            TableKind::Daa => self.truth_table_daa(),
            TableKind::Binary => self.truth_table_binary(),
        }
    }

    fn truth_table_unary(self) -> Vec<u8> {
        (0..=255u8)
            .map(|x| match self {
                Self::Inc => alu_inc(x).value,
                Self::Dec => alu_dec(x).value,
                Self::Rlc => alu_shift(ShiftOp::Rlc, x, false).value,
                Self::Rrc => alu_shift(ShiftOp::Rrc, x, false).value,
                Self::Sla => alu_shift(ShiftOp::Sla, x, false).value,
                Self::Sra => alu_shift(ShiftOp::Sra, x, false).value,
                Self::Srl => alu_shift(ShiftOp::Srl, x, false).value,
                Self::Swap => alu_shift(ShiftOp::Swap, x, false).value,
                Self::LowerNibble => x & 0x0F,
                Self::Bit(n) => alu_bit(n, x),
                Self::Res(n) => x & !(1 << n),
                Self::Set(n) => x | (1 << n),
                _ => unreachable!(),
            })
            .collect()
    }

    fn truth_table_daa(self) -> Vec<u8> {
        // 11 variables: a[0..7] (bits of input byte), n, h, c
        // Index = a + (n << 8) + (h << 9) + (c << 10)
        let mut table = Vec::with_capacity(2048);
        for c_flag in [false, true] {
            for h_flag in [false, true] {
                for n_flag in [false, true] {
                    for a in 0..=255u8 {
                        table.push(alu_daa(a, n_flag, h_flag, c_flag).value);
                    }
                }
            }
        }
        assert_eq!(table.len(), 2048);
        table
    }

    fn truth_table_binary(self) -> Vec<u8> {
        // 16 variables: a[0..7], b[0..7]
        // Index = a + (b << 8)
        let mut table = Vec::with_capacity(65536);
        for b in 0..=255u8 {
            for a in 0..=255u8 {
                let val = match self {
                    Self::Add => alu_binary(AluOp::Add, a, b, false).value,
                    Self::Sub => alu_binary(AluOp::Sub, a, b, false).value,
                    Self::And => alu_binary(AluOp::And, a, b, false).value,
                    Self::Xor => alu_binary(AluOp::Xor, a, b, false).value,
                    Self::Or => alu_binary(AluOp::Or, a, b, false).value,
                    _ => unreachable!(),
                };
                table.push(val);
            }
        }
        assert_eq!(table.len(), 65536);
        table
    }

    /// Returns true if this table has a known compact closed-form MLE.
    pub fn has_closed_form(self) -> bool {
        matches!(
            self,
            Self::And | Self::Xor | Self::Or | Self::LowerNibble | Self::Swap
                | Self::Res(_) | Self::Set(_) | Self::Bit(_)
        )
    }

    /// All tables that should be generated.
    pub fn all() -> Vec<Sm83Table> {
        let mut tables = vec![
            // Unary
            Self::Inc,
            Self::Dec,
            Self::Rlc,
            Self::Rrc,
            Self::Sla,
            Self::Sra,
            Self::Srl,
            Self::Swap,
            Self::LowerNibble,
            // DAA
            Self::Daa,
            // Binary
            Self::Add,
            Self::Sub,
            Self::And,
            Self::Xor,
            Self::Or,
        ];
        // Bit-variant
        for bit in 0..8 {
            tables.push(Self::Bit(bit));
            tables.push(Self::Res(bit));
            tables.push(Self::Set(bit));
        }
        tables
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inc_truth_table_spot_check() {
        let tt = Sm83Table::Inc.truth_table();
        assert_eq!(tt[0], 1);      // INC(0) = 1
        assert_eq!(tt[255], 0);    // INC(255) = 0
        assert_eq!(tt[0x0F], 0x10); // INC(0x0F) = 0x10
    }

    #[test]
    fn add_truth_table_spot_check() {
        let tt = Sm83Table::Add.truth_table();
        // Index = a + (b << 8)
        assert_eq!(tt[0x3A + (0xC6 << 8)], 0x00); // 0x3A + 0xC6 = 0x00
        assert_eq!(tt[1 + (2 << 8)], 3);           // 1 + 2 = 3
        assert_eq!(tt[0xFF + (1 << 8)], 0);         // 0xFF + 1 = 0
    }

    #[test]
    fn daa_truth_table_size() {
        let tt = Sm83Table::Daa.truth_table();
        assert_eq!(tt.len(), 2048);
    }

    #[test]
    fn daa_truth_table_spot_check() {
        let tt = Sm83Table::Daa.truth_table();
        // n=false, h=false, c=false => index = a + 0
        // 0x3C with n=false, h=false, c=false: DAA should add 0x06 (low nibble > 9)
        assert_eq!(tt[0x3C], alu_daa(0x3C, false, false, false).value);
    }

    #[test]
    fn bit_truth_table_spot_check() {
        let tt = Sm83Table::Bit(4).truth_table();
        // BIT 4 of 0b0001_0000 → bit is set → Z=0, H=1 → flags = 0x20
        assert_eq!(tt[0b0001_0000], 0x20);
        // BIT 4 of 0b0000_0000 → bit is clear → Z=1, H=1 → flags = 0xA0
        assert_eq!(tt[0b0000_0000], 0xA0);
    }

    #[test]
    fn all_tables_count() {
        // 9 unary + 1 daa + 5 binary + 24 bit-variant (8*3) = 39
        assert_eq!(Sm83Table::all().len(), 39);
    }
}
