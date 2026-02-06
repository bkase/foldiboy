/// Result of a pure ALU operation: value + flags byte.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AluResult {
    pub value: u8,
    /// Flags in upper nibble: Z(7) N(6) H(5) C(4)
    pub flags: u8,
}

/// Binary ALU operations on accumulator.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AluOp {
    Add,
    Adc,
    Sub,
    Sbc,
    And,
    Xor,
    Or,
    Cp,
}

/// Shift/rotate operations (CB-prefix and the 4 A-register rotates).
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ShiftOp {
    Rlc,
    Rrc,
    Rl,
    Rr,
    Sla,
    Sra,
    Swap,
    Srl,
}

/// Build a flags byte from individual flag booleans.
pub fn flag_byte(z: bool, n: bool, h: bool, c: bool) -> u8 {
    (if z { 0x80 } else { 0 })
        | (if n { 0x40 } else { 0 })
        | (if h { 0x20 } else { 0 })
        | (if c { 0x10 } else { 0 })
}

/// Pure 8-bit binary ALU operation.
/// `carry_in` is the current carry flag (used by Adc/Sbc).
pub fn alu_binary(op: AluOp, a: u8, b: u8, carry_in: bool) -> AluResult {
    match op {
        AluOp::Add => {
            let result = a.wrapping_add(b);
            AluResult {
                value: result,
                flags: flag_byte(
                    result == 0,
                    false,
                    (a & 0x0F) + (b & 0x0F) > 0x0F,
                    (a as u16) + (b as u16) > 0xFF,
                ),
            }
        }
        AluOp::Adc => {
            let c = carry_in as u8;
            let result = a.wrapping_add(b).wrapping_add(c);
            AluResult {
                value: result,
                flags: flag_byte(
                    result == 0,
                    false,
                    (a & 0x0F) + (b & 0x0F) + c > 0x0F,
                    (a as u16) + (b as u16) + (c as u16) > 0xFF,
                ),
            }
        }
        AluOp::Sub => {
            let result = a.wrapping_sub(b);
            AluResult {
                value: result,
                flags: flag_byte(result == 0, true, (a & 0x0F) < (b & 0x0F), a < b),
            }
        }
        AluOp::Sbc => {
            let c = carry_in as u8;
            let result = a.wrapping_sub(b).wrapping_sub(c);
            AluResult {
                value: result,
                flags: flag_byte(
                    result == 0,
                    true,
                    (a & 0x0F) < (b & 0x0F) + c,
                    (a as u16) < (b as u16) + (c as u16),
                ),
            }
        }
        AluOp::And => {
            let result = a & b;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, true, false),
            }
        }
        AluOp::Xor => {
            let result = a ^ b;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, false),
            }
        }
        AluOp::Or => {
            let result = a | b;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, false),
            }
        }
        AluOp::Cp => {
            let result = a.wrapping_sub(b);
            AluResult {
                value: a, // CP does not store the result
                flags: flag_byte(result == 0, true, (a & 0x0F) < (b & 0x0F), a < b),
            }
        }
    }
}

/// Pure INC. Carry flag is unchanged (caller must preserve it).
pub fn alu_inc(value: u8) -> AluResult {
    let result = value.wrapping_add(1);
    AluResult {
        value: result,
        flags: flag_byte(result == 0, false, (value & 0x0F) + 1 > 0x0F, false),
    }
}

/// Pure DEC. Carry flag is unchanged (caller must preserve it).
pub fn alu_dec(value: u8) -> AluResult {
    let result = value.wrapping_sub(1);
    AluResult {
        value: result,
        flags: flag_byte(result == 0, true, (value & 0x0F) < 1, false),
    }
}

/// Decimal Adjust Accumulator (BCD correction).
/// Flags in: N, H, C from the prior ADD/SUB.
pub fn alu_daa(a: u8, n: bool, h: bool, c: bool) -> AluResult {
    // Compute the offset first, using the ORIGINAL value of A.
    let mut offset = 0u8;
    let mut carry = false;

    if (!n && (a & 0x0F) > 0x09) || h {
        offset |= 0x06;
    }
    if (!n && a > 0x99) || c {
        offset |= 0x60;
        carry = true;
    }

    let result = if n {
        a.wrapping_sub(offset)
    } else {
        a.wrapping_add(offset)
    };

    AluResult {
        value: result,
        flags: flag_byte(result == 0, n, false, carry),
    }
}

/// Pure shift/rotate operation.
/// `carry_in` is the current carry flag (used by RL/RR).
pub fn alu_shift(op: ShiftOp, value: u8, carry_in: bool) -> AluResult {
    match op {
        ShiftOp::Rlc => {
            let result = value.rotate_left(1);
            let carry_out = (value & 0x80) != 0;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, carry_out),
            }
        }
        ShiftOp::Rrc => {
            let result = value.rotate_right(1);
            let carry_out = (value & 0x01) != 0;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, carry_out),
            }
        }
        ShiftOp::Rl => {
            let carry_out = (value & 0x80) != 0;
            let result = (value << 1) | (carry_in as u8);
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, carry_out),
            }
        }
        ShiftOp::Rr => {
            let carry_out = (value & 0x01) != 0;
            let result = (value >> 1) | ((carry_in as u8) << 7);
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, carry_out),
            }
        }
        ShiftOp::Sla => {
            let carry_out = (value & 0x80) != 0;
            let result = value << 1;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, carry_out),
            }
        }
        ShiftOp::Sra => {
            let carry_out = (value & 0x01) != 0;
            let msb = value & 0x80;
            let result = (value >> 1) | msb;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, carry_out),
            }
        }
        ShiftOp::Swap => {
            let result = (value >> 4) | (value << 4);
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, false),
            }
        }
        ShiftOp::Srl => {
            let carry_out = (value & 0x01) != 0;
            let result = value >> 1;
            AluResult {
                value: result,
                flags: flag_byte(result == 0, false, false, carry_out),
            }
        }
    }
}

/// BIT test: returns flags byte only (Z set if bit is 0). N=0, H=1, C unchanged.
pub fn alu_bit(bit: u8, value: u8) -> u8 {
    let bit_set = (value & (1 << bit)) != 0;
    flag_byte(!bit_set, false, true, false)
}

/// ADD HL, rr — returns flags byte (Z unchanged, N=0, H from bit 11, C from bit 15).
pub fn alu_add_hl(hl: u16, other: u16) -> u8 {
    flag_byte(
        false, // Z not affected (caller must preserve)
        false,
        (hl & 0xFFF) + (other & 0xFFF) > 0xFFF,
        (hl as u32) + (other as u32) > 0xFFFF,
    )
}

/// ADD SP, e8 / LD HL, SP+e8 — returns (result, flags).
/// Flags: Z=0, N=0, H and C from unsigned low-byte addition.
pub fn alu_add_sp_i8(sp: u16, offset: i8) -> (u16, u8) {
    let result = sp.wrapping_add(offset as i16 as u16);
    let sp_low = (sp & 0xFF) as u8;
    let offset_low = offset as u8;

    let flags = flag_byte(
        false,
        false,
        (sp_low & 0xF) as u16 + (offset_low & 0xF) as u16 > 0xF,
        sp_low as u16 + offset_low as u16 > 0xFF,
    );
    (result, flags)
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Binary operations ---

    #[test]
    fn add_basic() {
        let r = alu_binary(AluOp::Add, 0x3A, 0xC6, false);
        assert_eq!(r.value, 0x00);
        assert!(r.flags & 0x80 != 0); // Z
        assert!(r.flags & 0x40 == 0); // !N
        assert!(r.flags & 0x20 != 0); // H
        assert!(r.flags & 0x10 != 0); // C
    }

    #[test]
    fn adc_with_carry() {
        let r = alu_binary(AluOp::Adc, 0x3A, 0xC6, true);
        assert_eq!(r.value, 0x01);
        assert!(r.flags & 0x80 == 0); // !Z
        assert!(r.flags & 0x20 != 0); // H
        assert!(r.flags & 0x10 != 0); // C
    }

    #[test]
    fn sub_equal() {
        let r = alu_binary(AluOp::Sub, 0x3E, 0x3E, false);
        assert_eq!(r.value, 0x00);
        assert!(r.flags & 0x80 != 0); // Z
        assert!(r.flags & 0x40 != 0); // N
        assert!(r.flags & 0x20 == 0); // !H
        assert!(r.flags & 0x10 == 0); // !C
    }

    #[test]
    fn sbc_with_carry() {
        let r = alu_binary(AluOp::Sbc, 0x3B, 0x2A, true);
        assert_eq!(r.value, 0x10);
        assert!(r.flags & 0x80 == 0); // !Z
        assert!(r.flags & 0x40 != 0); // N
        assert!(r.flags & 0x20 == 0); // !H
        assert!(r.flags & 0x10 == 0); // !C
    }

    #[test]
    fn and_basic() {
        let r = alu_binary(AluOp::And, 0x5A, 0x3F, false);
        assert_eq!(r.value, 0x1A);
        assert!(r.flags & 0x20 != 0); // H always set
        assert!(r.flags & 0x10 == 0); // C always clear
    }

    #[test]
    fn xor_self_zero() {
        let r = alu_binary(AluOp::Xor, 0xFF, 0xFF, false);
        assert_eq!(r.value, 0x00);
        assert!(r.flags & 0x80 != 0); // Z
    }

    #[test]
    fn or_basic() {
        let r = alu_binary(AluOp::Or, 0x5A, 0x3F, false);
        assert_eq!(r.value, 0x7F);
    }

    #[test]
    fn cp_does_not_store() {
        let r = alu_binary(AluOp::Cp, 0x3C, 0x2F, false);
        assert_eq!(r.value, 0x3C); // value unchanged
        assert!(r.flags & 0x40 != 0); // N
        assert!(r.flags & 0x20 != 0); // H
    }

    // --- Inc / Dec ---

    #[test]
    fn inc_half_carry() {
        let r = alu_inc(0x0F);
        assert_eq!(r.value, 0x10);
        assert!(r.flags & 0x20 != 0); // H
        assert!(r.flags & 0x40 == 0); // !N
    }

    #[test]
    fn inc_overflow() {
        let r = alu_inc(0xFF);
        assert_eq!(r.value, 0x00);
        assert!(r.flags & 0x80 != 0); // Z
    }

    #[test]
    fn dec_half_carry() {
        let r = alu_dec(0x10);
        assert_eq!(r.value, 0x0F);
        assert!(r.flags & 0x20 != 0); // H
        assert!(r.flags & 0x40 != 0); // N
    }

    #[test]
    fn dec_to_zero() {
        let r = alu_dec(0x01);
        assert_eq!(r.value, 0x00);
        assert!(r.flags & 0x80 != 0); // Z
    }

    // --- DAA ---

    #[test]
    fn daa_after_add() {
        // 0x15 + 0x27 = 0x3C binary, BCD should be 0x42
        let add = alu_binary(AluOp::Add, 0x15, 0x27, false);
        let r = alu_daa(add.value, false, add.flags & 0x20 != 0, add.flags & 0x10 != 0);
        assert_eq!(r.value, 0x42);
    }

    #[test]
    fn daa_after_sub() {
        // 0x12 - 0x09 = 0x09 binary, BCD should be 0x03
        let sub = alu_binary(AluOp::Sub, 0x12, 0x09, false);
        let r = alu_daa(sub.value, true, sub.flags & 0x20 != 0, sub.flags & 0x10 != 0);
        assert_eq!(r.value, 0x03);
    }

    // --- Shifts ---

    #[test]
    fn rlc_basic() {
        let r = alu_shift(ShiftOp::Rlc, 0b1010_1010, false);
        assert_eq!(r.value, 0b0101_0101);
        assert!(r.flags & 0x10 != 0); // C = old bit 7
    }

    #[test]
    fn rrc_basic() {
        let r = alu_shift(ShiftOp::Rrc, 0b1010_1010, false);
        assert_eq!(r.value, 0b0101_0101);
        assert!(r.flags & 0x10 == 0); // C = old bit 0 (0)
    }

    #[test]
    fn rl_through_carry() {
        let r = alu_shift(ShiftOp::Rl, 0b1010_1010, false);
        assert_eq!(r.value, 0b0101_0100);
        assert!(r.flags & 0x10 != 0); // C = old bit 7
    }

    #[test]
    fn rr_through_carry() {
        let r = alu_shift(ShiftOp::Rr, 0b1010_1010, true);
        assert_eq!(r.value, 0b1101_0101);
        assert!(r.flags & 0x10 == 0); // C = old bit 0 (0)
    }

    #[test]
    fn sla_basic() {
        let r = alu_shift(ShiftOp::Sla, 0b1000_0001, false);
        assert_eq!(r.value, 0b0000_0010);
        assert!(r.flags & 0x10 != 0); // C = old bit 7
    }

    #[test]
    fn sra_preserves_msb() {
        let r = alu_shift(ShiftOp::Sra, 0b1000_0010, false);
        assert_eq!(r.value, 0b1100_0001);
        assert!(r.flags & 0x10 == 0); // C = old bit 0
    }

    #[test]
    fn swap_nibbles() {
        let r = alu_shift(ShiftOp::Swap, 0xF1, false);
        assert_eq!(r.value, 0x1F);
    }

    #[test]
    fn srl_basic() {
        let r = alu_shift(ShiftOp::Srl, 0b1000_0001, false);
        assert_eq!(r.value, 0b0100_0000);
        assert!(r.flags & 0x10 != 0); // C = old bit 0
    }

    // --- BIT ---

    #[test]
    fn bit_set() {
        let f = alu_bit(4, 0b0001_0000);
        assert!(f & 0x80 == 0); // Z=0 (bit is set)
        assert!(f & 0x20 != 0); // H=1
    }

    #[test]
    fn bit_clear() {
        let f = alu_bit(3, 0b0000_0000);
        assert!(f & 0x80 != 0); // Z=1 (bit is clear)
    }

    // --- ADD HL ---

    #[test]
    fn add_hl_half_carry() {
        let f = alu_add_hl(0x0FFF, 0x0002);
        assert!(f & 0x20 != 0); // H
        assert!(f & 0x10 == 0); // !C
    }

    #[test]
    fn add_hl_carry() {
        let f = alu_add_hl(0xFFFF, 0x0001);
        assert!(f & 0x20 != 0); // H
        assert!(f & 0x10 != 0); // C
    }

    // --- ADD SP, i8 ---

    #[test]
    fn add_sp_positive() {
        let (result, flags) = alu_add_sp_i8(0x1000, 5);
        assert_eq!(result, 0x1005);
        assert_eq!(flags & 0x80, 0); // Z=0
        assert_eq!(flags & 0x40, 0); // N=0
    }

    #[test]
    fn add_sp_negative() {
        let (result, flags) = alu_add_sp_i8(0x00F0, -1);
        assert_eq!(result, 0x00EF);
        // low byte: 0xF0 + 0xFF = 0x1EF -> carry
        assert!(flags & 0x10 != 0); // C
    }

    // --- Exhaustive ADD test (65K iterations) ---

    #[test]
    fn exhaustive_add_flags() {
        for a in 0..=255u16 {
            for b in 0..=255u16 {
                let r = alu_binary(AluOp::Add, a as u8, b as u8, false);
                let expected = (a + b) as u8;
                assert_eq!(
                    r.value, expected,
                    "ADD {a:#04X} + {b:#04X} value mismatch"
                );
                // Z flag
                assert_eq!(
                    r.flags & 0x80 != 0,
                    expected == 0,
                    "ADD {a:#04X} + {b:#04X} Z flag mismatch"
                );
                // N flag
                assert_eq!(r.flags & 0x40, 0, "ADD should never set N");
                // H flag
                let h = (a & 0xF) + (b & 0xF) > 0xF;
                assert_eq!(
                    r.flags & 0x20 != 0,
                    h,
                    "ADD {a:#04X} + {b:#04X} H flag mismatch"
                );
                // C flag
                let c = a + b > 0xFF;
                assert_eq!(
                    r.flags & 0x10 != 0,
                    c,
                    "ADD {a:#04X} + {b:#04X} C flag mismatch"
                );
            }
        }
    }

    #[test]
    fn exhaustive_sub_flags() {
        for a in 0..=255u16 {
            for b in 0..=255u16 {
                let r = alu_binary(AluOp::Sub, a as u8, b as u8, false);
                let expected = a.wrapping_sub(b) as u8;
                assert_eq!(
                    r.value, expected,
                    "SUB {a:#04X} - {b:#04X} value mismatch"
                );
                assert_eq!(r.flags & 0x80 != 0, expected == 0);
                assert_ne!(r.flags & 0x40, 0, "SUB should always set N");
                assert_eq!(r.flags & 0x20 != 0, (a & 0xF) < (b & 0xF));
                assert_eq!(r.flags & 0x10 != 0, a < b);
            }
        }
    }

    // --- Exhaustive ADC/SBC tests (65K × 2 carry states) ---

    #[test]
    fn exhaustive_adc_flags() {
        for carry in [false, true] {
            let c = carry as u16;
            for a in 0..=255u16 {
                for b in 0..=255u16 {
                    let r = alu_binary(AluOp::Adc, a as u8, b as u8, carry);
                    let full = a + b + c;
                    let expected = full as u8;
                    assert_eq!(
                        r.value, expected,
                        "ADC {a:#04X} + {b:#04X} + {c} value"
                    );
                    assert_eq!(r.flags & 0x80 != 0, expected == 0,
                        "ADC {a:#04X} + {b:#04X} + {c} Z");
                    assert_eq!(r.flags & 0x40, 0, "ADC should never set N");
                    let h = (a & 0xF) + (b & 0xF) + c > 0xF;
                    assert_eq!(r.flags & 0x20 != 0, h,
                        "ADC {a:#04X} + {b:#04X} + {c} H");
                    assert_eq!(r.flags & 0x10 != 0, full > 0xFF,
                        "ADC {a:#04X} + {b:#04X} + {c} C");
                }
            }
        }
    }

    #[test]
    fn exhaustive_sbc_flags() {
        for carry in [false, true] {
            let c = carry as u16;
            for a in 0..=255u16 {
                for b in 0..=255u16 {
                    let r = alu_binary(AluOp::Sbc, a as u8, b as u8, carry);
                    let expected = a.wrapping_sub(b).wrapping_sub(c) as u8;
                    assert_eq!(
                        r.value, expected,
                        "SBC {a:#04X} - {b:#04X} - {c} value"
                    );
                    assert_eq!(r.flags & 0x80 != 0, expected == 0,
                        "SBC {a:#04X} - {b:#04X} - {c} Z");
                    assert_ne!(r.flags & 0x40, 0, "SBC should always set N");
                    let h = (a & 0xF) < (b & 0xF) + c;
                    assert_eq!(r.flags & 0x20 != 0, h,
                        "SBC {a:#04X} - {b:#04X} - {c} H");
                    assert_eq!(r.flags & 0x10 != 0, a < b + c,
                        "SBC {a:#04X} - {b:#04X} - {c} C");
                }
            }
        }
    }

    // --- ADD SP edge cases ---

    #[test]
    fn add_sp_wrapping_flags() {
        // SP=0xFFFF, offset=-1: low byte 0xFF + 0xFF = 0x1FE → H and C set
        let (result, flags) = alu_add_sp_i8(0xFFFF, -1);
        assert_eq!(result, 0xFFFE);
        assert_eq!(flags & 0x80, 0, "Z must be 0");
        assert_eq!(flags & 0x40, 0, "N must be 0");
        assert!(flags & 0x20 != 0, "H: 0xF + 0xF > 0xF");
        assert!(flags & 0x10 != 0, "C: 0xFF + 0xFF > 0xFF");

        // SP=0x0100, offset=-1: low byte 0x00 + 0xFF = 0xFF → no H, no C
        // (0x0 + 0xF = 0xF, not > 0xF; 0x00 + 0xFF = 0xFF, not > 0xFF)
        let (result, flags) = alu_add_sp_i8(0x0100, -1);
        assert_eq!(result, 0x00FF);
        assert!(flags & 0x20 == 0, "no H: 0x0 + 0xF = 0xF");
        assert!(flags & 0x10 == 0, "no C: 0x00 + 0xFF = 0xFF");
    }
}
