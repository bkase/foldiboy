use memory::Bus;

use crate::alu::{AluOp, ShiftOp};
use crate::registers::{Cond, Reg16, Reg8};

use super::{
    BitShift, Flag, GbInstruction, InterruptCtl, Jump, Load, Misc, Stack, U16Arith, U8Arith,
};

/// Decode one instruction starting at `pc`.
/// Returns `(instruction, new_pc)`.
///
/// `halt_bug`: if true, the first byte read does NOT advance PC.
pub fn decode(pc: u16, bus: &mut impl Bus, halt_bug: bool) -> (GbInstruction, u16) {
    let mut idx = pc;
    let mut first = true;
    let mut hb = halt_bug;

    let mut read = |idx: &mut u16| -> u8 {
        let val = bus.read(*idx);
        if first && hb {
            // Halt bug: read byte but don't advance PC
            hb = false;
            first = false;
        } else {
            *idx = idx.wrapping_add(1);
            first = false;
        }
        val
    };

    let opcode = read(&mut idx);
    let block = opcode >> 6;

    let instr = match block {
        0 => decode_block_0(opcode, &mut idx, bus),
        1 => decode_block_1(opcode),
        2 => decode_block_2(opcode),
        3 => decode_block_3(opcode, &mut idx, bus),
        _ => unreachable!(),
    };

    (instr, idx)
}

// --- Helpers ---

/// 3-bit register encoding: B=0, C=1, D=2, E=3, H=4, L=5, (HL)=6, A=7.
/// Returns `None` for (HL) slot.
fn reg8_from_bits(bits: u8) -> Option<Reg8> {
    match bits & 0x07 {
        0 => Some(Reg8::B),
        1 => Some(Reg8::C),
        2 => Some(Reg8::D),
        3 => Some(Reg8::E),
        4 => Some(Reg8::H),
        5 => Some(Reg8::L),
        6 => None, // (HL)
        7 => Some(Reg8::A),
        _ => unreachable!(),
    }
}

fn reg16_from_bits(bits: u8) -> Reg16 {
    match bits & 0x03 {
        0 => Reg16::BC,
        1 => Reg16::DE,
        2 => Reg16::HL,
        3 => Reg16::SP,
        _ => unreachable!(),
    }
}

fn reg16_stk_from_bits(bits: u8) -> Reg16 {
    match bits & 0x03 {
        0 => Reg16::BC,
        1 => Reg16::DE,
        2 => Reg16::HL,
        3 => Reg16::AF,
        _ => unreachable!(),
    }
}

fn cond_from_bits(bits: u8) -> Cond {
    match bits & 0x03 {
        0 => Cond::NZ,
        1 => Cond::Z,
        2 => Cond::NC,
        3 => Cond::C,
        _ => unreachable!(),
    }
}

fn read_u8(idx: &mut u16, bus: &mut impl Bus) -> u8 {
    let val = bus.read(*idx);
    *idx = idx.wrapping_add(1);
    val
}

fn read_u16(idx: &mut u16, bus: &mut impl Bus) -> u16 {
    let lo = read_u8(idx, bus);
    let hi = read_u8(idx, bus);
    (hi as u16) << 8 | lo as u16
}

fn alu_op_from_bits(bits: u8) -> AluOp {
    match bits & 0x07 {
        0 => AluOp::Add,
        1 => AluOp::Adc,
        2 => AluOp::Sub,
        3 => AluOp::Sbc,
        4 => AluOp::And,
        5 => AluOp::Xor,
        6 => AluOp::Or,
        7 => AluOp::Cp,
        _ => unreachable!(),
    }
}

// --- Block decoders ---

fn decode_block_0(opcode: u8, idx: &mut u16, bus: &mut impl Bus) -> GbInstruction {
    // NOP
    if opcode == 0x00 {
        return GbInstruction::Misc(Misc::Nop);
    }

    // STOP
    if opcode == 0x10 {
        return GbInstruction::Misc(Misc::Stop);
    }

    let lo4 = opcode & 0x0F;
    let hi2 = (opcode >> 4) & 0x03;

    // LD r16, n16  — xx_0001
    if lo4 == 0x01 {
        let n16 = read_u16(idx, bus);
        return GbInstruction::Load(Load::R16_N16(reg16_from_bits(hi2), n16));
    }

    // LD (r16mem), A — xx_0010
    if lo4 == 0x02 {
        return match hi2 {
            0 => GbInstruction::Load(Load::R16Mem_A(Reg16::BC)),
            1 => GbInstruction::Load(Load::R16Mem_A(Reg16::DE)),
            2 => GbInstruction::Load(Load::HLI_A),
            3 => GbInstruction::Load(Load::HLD_A),
            _ => unreachable!(),
        };
    }

    // LD A, (r16mem) — xx_1010
    if lo4 == 0x0A {
        return match hi2 {
            0 => GbInstruction::Load(Load::A_R16Mem(Reg16::BC)),
            1 => GbInstruction::Load(Load::A_R16Mem(Reg16::DE)),
            2 => GbInstruction::Load(Load::A_HLI),
            3 => GbInstruction::Load(Load::A_HLD),
            _ => unreachable!(),
        };
    }

    // LD (n16), SP — 0x08
    if opcode == 0x08 {
        let n16 = read_u16(idx, bus);
        return GbInstruction::Load(Load::N16_SP(n16));
    }

    // INC r16 — xx_0011
    if lo4 == 0x03 {
        return GbInstruction::U16Arithmetic(U16Arith::IncR16(reg16_from_bits(hi2)));
    }

    // DEC r16 — xx_1011
    if lo4 == 0x0B {
        return GbInstruction::U16Arithmetic(U16Arith::DecR16(reg16_from_bits(hi2)));
    }

    // ADD HL, r16 — xx_1001
    if lo4 == 0x09 {
        return GbInstruction::U16Arithmetic(U16Arith::AddHL(reg16_from_bits(hi2)));
    }

    // INC r8 / INC (HL) — xxx_100
    if opcode & 0x07 == 0x04 {
        let dst = (opcode >> 3) & 0x07;
        return match reg8_from_bits(dst) {
            Some(r) => GbInstruction::U8Arithmetic(U8Arith::IncR8(r)),
            None => GbInstruction::U8Arithmetic(U8Arith::IncHL),
        };
    }

    // DEC r8 / DEC (HL) — xxx_101
    if opcode & 0x07 == 0x05 {
        let dst = (opcode >> 3) & 0x07;
        return match reg8_from_bits(dst) {
            Some(r) => GbInstruction::U8Arithmetic(U8Arith::DecR8(r)),
            None => GbInstruction::U8Arithmetic(U8Arith::DecHL),
        };
    }

    // LD r8, n8 / LD (HL), n8 — xxx_110
    if opcode & 0x07 == 0x06 {
        let n8 = read_u8(idx, bus);
        let dst = (opcode >> 3) & 0x07;
        return match reg8_from_bits(dst) {
            Some(r) => GbInstruction::Load(Load::R8_N8(r, n8)),
            None => GbInstruction::Load(Load::HL_N8(n8)),
        };
    }

    // Rotates + misc (xxx_111)
    if opcode & 0x07 == 0x07 {
        let op = (opcode >> 3) & 0x07;
        return match op {
            0 => GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rlc)),
            1 => GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rrc)),
            2 => GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rl)),
            3 => GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rr)),
            4 => GbInstruction::Flag(Flag::Daa),
            5 => GbInstruction::Flag(Flag::Cpl),
            6 => GbInstruction::Flag(Flag::Scf),
            7 => GbInstruction::Flag(Flag::Ccf),
            _ => unreachable!(),
        };
    }

    // JR e8 (unconditional) — 0x18
    if opcode == 0x18 {
        let e8 = read_u8(idx, bus) as i8;
        return GbInstruction::Jumps(Jump::Jr(e8));
    }

    // JR cond, e8 — 001_cc_000
    if opcode & 0xE7 == 0x20 {
        let cc = cond_from_bits((opcode >> 3) & 0x03);
        let e8 = read_u8(idx, bus) as i8;
        return GbInstruction::Jumps(Jump::JrCond(cc, e8));
    }

    // Should not reach here for valid opcodes
    GbInstruction::Misc(Misc::Undefined(opcode))
}

fn decode_block_1(opcode: u8) -> GbInstruction {
    let src_bits = opcode & 0x07;
    let dst_bits = (opcode >> 3) & 0x07;

    // HALT: opcode 0x76 (LD (HL), (HL) position)
    if src_bits == 6 && dst_bits == 6 {
        return GbInstruction::Interrupt(InterruptCtl::Halt);
    }

    let src = reg8_from_bits(src_bits);
    let dst = reg8_from_bits(dst_bits);

    match (dst, src) {
        (Some(d), Some(s)) => GbInstruction::Load(Load::R8_R8(d, s)),
        (Some(d), None) => GbInstruction::Load(Load::R8_HL(d)),
        (None, Some(s)) => GbInstruction::Load(Load::HL_R8(s)),
        (None, None) => unreachable!(), // Already handled as HALT
    }
}

fn decode_block_2(opcode: u8) -> GbInstruction {
    let op = alu_op_from_bits((opcode >> 3) & 0x07);
    let src_bits = opcode & 0x07;

    match reg8_from_bits(src_bits) {
        Some(r) => GbInstruction::U8Arithmetic(U8Arith::BinR8(op, r)),
        None => GbInstruction::U8Arithmetic(U8Arith::BinHL(op)),
    }
}

fn decode_block_3(opcode: u8, idx: &mut u16, bus: &mut impl Bus) -> GbInstruction {
    // --- Immediate ALU: column 6/E ---
    // ADD/ADC/SUB/SBC/AND/XOR/OR/CP A, n8
    if opcode & 0xC7 == 0xC6 {
        let op = alu_op_from_bits((opcode >> 3) & 0x07);
        let n8 = read_u8(idx, bus);
        return GbInstruction::U8Arithmetic(U8Arith::BinN8(op, n8));
    }

    // --- Conditional returns: RET cc — 110_cc_000 ---
    if opcode & 0xE7 == 0xC0 {
        let cc = cond_from_bits((opcode >> 3) & 0x03);
        return GbInstruction::Jumps(Jump::RetCond(cc));
    }

    // RET — 0xC9
    if opcode == 0xC9 {
        return GbInstruction::Jumps(Jump::Ret);
    }

    // RETI — 0xD9
    if opcode == 0xD9 {
        return GbInstruction::Jumps(Jump::Reti);
    }

    // JP cc, n16 — 110_cc_010
    if opcode & 0xE7 == 0xC2 {
        let cc = cond_from_bits((opcode >> 3) & 0x03);
        let n16 = read_u16(idx, bus);
        return GbInstruction::Jumps(Jump::JpCondN16(cc, n16));
    }

    // JP n16 — 0xC3
    if opcode == 0xC3 {
        let n16 = read_u16(idx, bus);
        return GbInstruction::Jumps(Jump::JpN16(n16));
    }

    // JP HL — 0xE9
    if opcode == 0xE9 {
        return GbInstruction::Jumps(Jump::JpHL);
    }

    // CALL cc, n16 — 110_cc_100
    if opcode & 0xE7 == 0xC4 {
        let cc = cond_from_bits((opcode >> 3) & 0x03);
        let n16 = read_u16(idx, bus);
        return GbInstruction::Jumps(Jump::CallCond(cc, n16));
    }

    // CALL n16 — 0xCD
    if opcode == 0xCD {
        let n16 = read_u16(idx, bus);
        return GbInstruction::Jumps(Jump::CallN16(n16));
    }

    // RST tgt3 — 11_ttt_111
    if opcode & 0xC7 == 0xC7 {
        let tgt = (opcode >> 3) & 0x07;
        return GbInstruction::Jumps(Jump::Rst(tgt));
    }

    // CB prefix — 0xCB
    if opcode == 0xCB {
        let cb_byte = read_u8(idx, bus);
        return decode_cb(cb_byte);
    }

    // --- Loads with high memory ---
    // LDH (C), A — 0xE2
    if opcode == 0xE2 {
        return GbInstruction::Load(Load::LDH_C_A);
    }
    // LDH (n8), A — 0xE0
    if opcode == 0xE0 {
        let n8 = read_u8(idx, bus);
        return GbInstruction::Load(Load::LDH_N8_A(n8));
    }
    // LD (n16), A — 0xEA
    if opcode == 0xEA {
        let n16 = read_u16(idx, bus);
        return GbInstruction::Load(Load::N16_A(n16));
    }
    // LDH A, (C) — 0xF2
    if opcode == 0xF2 {
        return GbInstruction::Load(Load::LDH_A_C);
    }
    // LDH A, (n8) — 0xF0
    if opcode == 0xF0 {
        let n8 = read_u8(idx, bus);
        return GbInstruction::Load(Load::LDH_A_N8(n8));
    }
    // LD A, (n16) — 0xFA
    if opcode == 0xFA {
        let n16 = read_u16(idx, bus);
        return GbInstruction::Load(Load::A_N16(n16));
    }

    // --- Stack instructions ---
    // POP r16stk — xx_0001
    if opcode & 0xCF == 0xC1 {
        let r = reg16_stk_from_bits((opcode >> 4) & 0x03);
        return GbInstruction::Stack(Stack::Pop(r));
    }
    // PUSH r16stk — xx_0101
    if opcode & 0xCF == 0xC5 {
        let r = reg16_stk_from_bits((opcode >> 4) & 0x03);
        return GbInstruction::Stack(Stack::Push(r));
    }
    // ADD SP, e8 — 0xE8
    if opcode == 0xE8 {
        let e8 = read_u8(idx, bus) as i8;
        return GbInstruction::Stack(Stack::AddSP(e8));
    }
    // LD HL, SP+e8 — 0xF8
    if opcode == 0xF8 {
        let e8 = read_u8(idx, bus) as i8;
        return GbInstruction::Stack(Stack::LdHLSP(e8));
    }
    // LD SP, HL — 0xF9
    if opcode == 0xF9 {
        return GbInstruction::Stack(Stack::LdSPHL);
    }

    // --- Interrupt control ---
    // DI — 0xF3
    if opcode == 0xF3 {
        return GbInstruction::Interrupt(InterruptCtl::Di);
    }
    // EI — 0xFB
    if opcode == 0xFB {
        return GbInstruction::Interrupt(InterruptCtl::Ei);
    }

    // Undefined opcodes (0xD3, 0xDB, 0xDD, 0xE3, 0xE4, 0xEB, 0xEC, 0xED, 0xF4, 0xFC, 0xFD)
    GbInstruction::Misc(Misc::Undefined(opcode))
}

fn decode_cb(byte: u8) -> GbInstruction {
    let group = (byte >> 6) & 0x03;
    let code = (byte >> 3) & 0x07;
    let reg_bits = byte & 0x07;

    match group {
        0 => {
            // Shift/rotate ops
            let op = match code {
                0 => ShiftOp::Rlc,
                1 => ShiftOp::Rrc,
                2 => ShiftOp::Rl,
                3 => ShiftOp::Rr,
                4 => ShiftOp::Sla,
                5 => ShiftOp::Sra,
                6 => ShiftOp::Swap,
                7 => ShiftOp::Srl,
                _ => unreachable!(),
            };
            match reg8_from_bits(reg_bits) {
                Some(r) => GbInstruction::BitShift(BitShift::ShiftR8(op, r)),
                None => GbInstruction::BitShift(BitShift::ShiftHL(op)),
            }
        }
        1 => {
            // BIT
            match reg8_from_bits(reg_bits) {
                Some(r) => GbInstruction::BitShift(BitShift::BitR8(code, r)),
                None => GbInstruction::BitShift(BitShift::BitHL(code)),
            }
        }
        2 => {
            // RES
            match reg8_from_bits(reg_bits) {
                Some(r) => GbInstruction::BitShift(BitShift::ResR8(code, r)),
                None => GbInstruction::BitShift(BitShift::ResHL(code)),
            }
        }
        3 => {
            // SET
            match reg8_from_bits(reg_bits) {
                Some(r) => GbInstruction::BitShift(BitShift::SetR8(code, r)),
                None => GbInstruction::BitShift(BitShift::SetHL(code)),
            }
        }
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use memory::TestBus;

    fn decode_bytes(bytes: &[u8]) -> GbInstruction {
        let mut bus = TestBus::new();
        bus.load_rom(0, bytes);
        let (instr, _) = decode(0, &mut bus, false);
        instr
    }

    fn decode_bytes_pc(bytes: &[u8]) -> (GbInstruction, u16) {
        let mut bus = TestBus::new();
        bus.load_rom(0, bytes);
        decode(0, &mut bus, false)
    }

    // --- Block 0 ---

    #[test]
    fn nop() {
        assert_eq!(decode_bytes(&[0x00]), GbInstruction::Misc(Misc::Nop));
    }

    #[test]
    fn stop() {
        assert_eq!(decode_bytes(&[0x10]), GbInstruction::Misc(Misc::Stop));
    }

    #[test]
    fn ld_r16_n16() {
        assert_eq!(
            decode_bytes(&[0x01, 0x34, 0x12]),
            GbInstruction::Load(Load::R16_N16(Reg16::BC, 0x1234))
        );
        assert_eq!(
            decode_bytes(&[0x31, 0x56, 0x78]),
            GbInstruction::Load(Load::R16_N16(Reg16::SP, 0x7856))
        );
    }

    #[test]
    fn ld_r16mem_a() {
        assert_eq!(
            decode_bytes(&[0x02]),
            GbInstruction::Load(Load::R16Mem_A(Reg16::BC))
        );
        assert_eq!(
            decode_bytes(&[0x12]),
            GbInstruction::Load(Load::R16Mem_A(Reg16::DE))
        );
        assert_eq!(decode_bytes(&[0x22]), GbInstruction::Load(Load::HLI_A));
        assert_eq!(decode_bytes(&[0x32]), GbInstruction::Load(Load::HLD_A));
    }

    #[test]
    fn ld_a_r16mem() {
        assert_eq!(
            decode_bytes(&[0x0A]),
            GbInstruction::Load(Load::A_R16Mem(Reg16::BC))
        );
        assert_eq!(decode_bytes(&[0x2A]), GbInstruction::Load(Load::A_HLI));
        assert_eq!(decode_bytes(&[0x3A]), GbInstruction::Load(Load::A_HLD));
    }

    #[test]
    fn ld_n16_sp() {
        assert_eq!(
            decode_bytes(&[0x08, 0xCD, 0xAB]),
            GbInstruction::Load(Load::N16_SP(0xABCD))
        );
    }

    #[test]
    fn inc_dec_r16() {
        assert_eq!(
            decode_bytes(&[0x03]),
            GbInstruction::U16Arithmetic(U16Arith::IncR16(Reg16::BC))
        );
        assert_eq!(
            decode_bytes(&[0x1B]),
            GbInstruction::U16Arithmetic(U16Arith::DecR16(Reg16::DE))
        );
    }

    #[test]
    fn add_hl_r16() {
        assert_eq!(
            decode_bytes(&[0x29]),
            GbInstruction::U16Arithmetic(U16Arith::AddHL(Reg16::HL))
        );
    }

    #[test]
    fn inc_dec_r8() {
        assert_eq!(
            decode_bytes(&[0x04]),
            GbInstruction::U8Arithmetic(U8Arith::IncR8(Reg8::B))
        );
        assert_eq!(
            decode_bytes(&[0x34]),
            GbInstruction::U8Arithmetic(U8Arith::IncHL)
        );
        assert_eq!(
            decode_bytes(&[0x1D]),
            GbInstruction::U8Arithmetic(U8Arith::DecR8(Reg8::E))
        );
        assert_eq!(
            decode_bytes(&[0x35]),
            GbInstruction::U8Arithmetic(U8Arith::DecHL)
        );
    }

    #[test]
    fn ld_r8_n8() {
        assert_eq!(
            decode_bytes(&[0x06, 0x42]),
            GbInstruction::Load(Load::R8_N8(Reg8::B, 0x42))
        );
        assert_eq!(
            decode_bytes(&[0x36, 0xAB]),
            GbInstruction::Load(Load::HL_N8(0xAB))
        );
    }

    #[test]
    fn rotates_and_flag_ops() {
        assert_eq!(
            decode_bytes(&[0x07]),
            GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rlc))
        );
        assert_eq!(
            decode_bytes(&[0x0F]),
            GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rrc))
        );
        assert_eq!(
            decode_bytes(&[0x17]),
            GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rl))
        );
        assert_eq!(
            decode_bytes(&[0x1F]),
            GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rr))
        );
        assert_eq!(decode_bytes(&[0x27]), GbInstruction::Flag(Flag::Daa));
        assert_eq!(decode_bytes(&[0x2F]), GbInstruction::Flag(Flag::Cpl));
        assert_eq!(decode_bytes(&[0x37]), GbInstruction::Flag(Flag::Scf));
        assert_eq!(decode_bytes(&[0x3F]), GbInstruction::Flag(Flag::Ccf));
    }

    #[test]
    fn jr_unconditional() {
        assert_eq!(
            decode_bytes(&[0x18, 0x0E]),
            GbInstruction::Jumps(Jump::Jr(0x0E))
        );
    }

    #[test]
    fn jr_conditional() {
        assert_eq!(
            decode_bytes(&[0x20, 0x05]),
            GbInstruction::Jumps(Jump::JrCond(Cond::NZ, 0x05))
        );
        assert_eq!(
            decode_bytes(&[0x38, 0x0D]),
            GbInstruction::Jumps(Jump::JrCond(Cond::C, 0x0D))
        );
    }

    // --- Block 1 ---

    #[test]
    fn ld_r8_r8() {
        assert_eq!(
            decode_bytes(&[0x47]),
            GbInstruction::Load(Load::R8_R8(Reg8::B, Reg8::A))
        );
    }

    #[test]
    fn ld_r8_hl() {
        assert_eq!(
            decode_bytes(&[0x46]),
            GbInstruction::Load(Load::R8_HL(Reg8::B))
        );
    }

    #[test]
    fn ld_hl_r8() {
        assert_eq!(
            decode_bytes(&[0x70]),
            GbInstruction::Load(Load::HL_R8(Reg8::B))
        );
    }

    #[test]
    fn halt() {
        assert_eq!(
            decode_bytes(&[0x76]),
            GbInstruction::Interrupt(InterruptCtl::Halt)
        );
    }

    // --- Block 2 ---

    #[test]
    fn alu_r8() {
        assert_eq!(
            decode_bytes(&[0x81]),
            GbInstruction::U8Arithmetic(U8Arith::BinR8(AluOp::Add, Reg8::C))
        );
        assert_eq!(
            decode_bytes(&[0xAF]),
            GbInstruction::U8Arithmetic(U8Arith::BinR8(AluOp::Xor, Reg8::A))
        );
    }

    #[test]
    fn alu_hl() {
        assert_eq!(
            decode_bytes(&[0x96]),
            GbInstruction::U8Arithmetic(U8Arith::BinHL(AluOp::Sub))
        );
    }

    // --- Block 3 ---

    #[test]
    fn alu_n8() {
        assert_eq!(
            decode_bytes(&[0xC6, 0x12]),
            GbInstruction::U8Arithmetic(U8Arith::BinN8(AluOp::Add, 0x12))
        );
        assert_eq!(
            decode_bytes(&[0xFE, 0xF0]),
            GbInstruction::U8Arithmetic(U8Arith::BinN8(AluOp::Cp, 0xF0))
        );
    }

    #[test]
    fn jumps_and_calls() {
        assert_eq!(
            decode_bytes(&[0xC0]),
            GbInstruction::Jumps(Jump::RetCond(Cond::NZ))
        );
        assert_eq!(decode_bytes(&[0xC9]), GbInstruction::Jumps(Jump::Ret));
        assert_eq!(decode_bytes(&[0xD9]), GbInstruction::Jumps(Jump::Reti));
        assert_eq!(
            decode_bytes(&[0xC3, 0x78, 0x56]),
            GbInstruction::Jumps(Jump::JpN16(0x5678))
        );
        assert_eq!(decode_bytes(&[0xE9]), GbInstruction::Jumps(Jump::JpHL));
        assert_eq!(
            decode_bytes(&[0xCD, 0x34, 0x12]),
            GbInstruction::Jumps(Jump::CallN16(0x1234))
        );
        assert_eq!(
            decode_bytes(&[0xDF]),
            GbInstruction::Jumps(Jump::Rst(3))
        );
    }

    #[test]
    fn load_high_mem() {
        assert_eq!(decode_bytes(&[0xE2]), GbInstruction::Load(Load::LDH_C_A));
        assert_eq!(
            decode_bytes(&[0xE0, 0x42]),
            GbInstruction::Load(Load::LDH_N8_A(0x42))
        );
        assert_eq!(
            decode_bytes(&[0xEA, 0x78, 0x56]),
            GbInstruction::Load(Load::N16_A(0x5678))
        );
        assert_eq!(decode_bytes(&[0xF2]), GbInstruction::Load(Load::LDH_A_C));
        assert_eq!(
            decode_bytes(&[0xF0, 0x11]),
            GbInstruction::Load(Load::LDH_A_N8(0x11))
        );
        assert_eq!(
            decode_bytes(&[0xFA, 0x99, 0x00]),
            GbInstruction::Load(Load::A_N16(0x0099))
        );
    }

    #[test]
    fn stack_instructions() {
        assert_eq!(
            decode_bytes(&[0xC1]),
            GbInstruction::Stack(Stack::Pop(Reg16::BC))
        );
        assert_eq!(
            decode_bytes(&[0xF1]),
            GbInstruction::Stack(Stack::Pop(Reg16::AF))
        );
        assert_eq!(
            decode_bytes(&[0xC5]),
            GbInstruction::Stack(Stack::Push(Reg16::BC))
        );
        assert_eq!(
            decode_bytes(&[0xE8, 0xF4]),
            GbInstruction::Stack(Stack::AddSP(-12))
        );
        assert_eq!(
            decode_bytes(&[0xF8, 0x10]),
            GbInstruction::Stack(Stack::LdHLSP(0x10))
        );
        assert_eq!(
            decode_bytes(&[0xF9]),
            GbInstruction::Stack(Stack::LdSPHL)
        );
    }

    #[test]
    fn interrupts() {
        assert_eq!(
            decode_bytes(&[0xF3]),
            GbInstruction::Interrupt(InterruptCtl::Di)
        );
        assert_eq!(
            decode_bytes(&[0xFB]),
            GbInstruction::Interrupt(InterruptCtl::Ei)
        );
    }

    #[test]
    fn undefined_opcodes() {
        for &op in &[0xD3, 0xDB, 0xDD, 0xE3, 0xE4, 0xEB, 0xEC, 0xED, 0xF4, 0xFC, 0xFD] {
            match decode_bytes(&[op]) {
                GbInstruction::Misc(Misc::Undefined(_)) => {}
                other => panic!("Expected Undefined for opcode {op:#04X}, got {other:?}"),
            }
        }
    }

    // --- CB prefix ---

    #[test]
    fn cb_shifts() {
        assert_eq!(
            decode_bytes(&[0xCB, 0x00]),
            GbInstruction::BitShift(BitShift::ShiftR8(ShiftOp::Rlc, Reg8::B))
        );
        assert_eq!(
            decode_bytes(&[0xCB, 0x3E]),
            GbInstruction::BitShift(BitShift::ShiftHL(ShiftOp::Srl))
        );
        assert_eq!(
            decode_bytes(&[0xCB, 0x37]),
            GbInstruction::BitShift(BitShift::ShiftR8(ShiftOp::Swap, Reg8::A))
        );
    }

    #[test]
    fn cb_bit_ops() {
        assert_eq!(
            decode_bytes(&[0xCB, 0x40]),
            GbInstruction::BitShift(BitShift::BitR8(0, Reg8::B))
        );
        assert_eq!(
            decode_bytes(&[0xCB, 0x89]),
            GbInstruction::BitShift(BitShift::ResR8(1, Reg8::C))
        );
        assert_eq!(
            decode_bytes(&[0xCB, 0xFE]),
            GbInstruction::BitShift(BitShift::SetHL(7))
        );
    }

    // --- Instruction length verification ---

    #[test]
    fn instruction_lengths() {
        // 1-byte
        let (_, pc) = decode_bytes_pc(&[0x00]); // NOP
        assert_eq!(pc, 1);
        // 2-byte
        let (_, pc) = decode_bytes_pc(&[0x06, 0x42]); // LD B, n8
        assert_eq!(pc, 2);
        // 3-byte
        let (_, pc) = decode_bytes_pc(&[0x01, 0x34, 0x12]); // LD BC, n16
        assert_eq!(pc, 3);
        // CB-prefix: 2 bytes
        let (_, pc) = decode_bytes_pc(&[0xCB, 0x00]); // RLC B
        assert_eq!(pc, 2);
    }

    // --- Decode all 256 main opcodes (no panic) ---

    #[test]
    fn all_256_main_opcodes_decode_without_panic() {
        for op in 0..=255u8 {
            let mut bus = TestBus::new();
            // Provide enough trailing bytes for 3-byte instructions
            bus.load_rom(0, &[op, 0x00, 0x00, 0x00]);
            let _ = decode(0, &mut bus, false);
        }
    }

    // --- Decode all 256 CB opcodes (no panic) ---

    #[test]
    fn all_256_cb_opcodes_decode_without_panic() {
        for cb_op in 0..=255u8 {
            let mut bus = TestBus::new();
            bus.load_rom(0, &[0xCB, cb_op]);
            let _ = decode(0, &mut bus, false);
        }
    }

    // --- Halt bug ---

    #[test]
    fn halt_bug_does_not_advance_pc() {
        let mut bus = TestBus::new();
        // Place NOP at address 0, then LD B, n8 at address 0
        bus.load_rom(0, &[0x00, 0x06, 0x42]);
        let (instr, new_pc) = decode(0, &mut bus, true);
        // With halt_bug, reads 0x00 (NOP) but PC stays at 0, so new_pc = 0
        assert_eq!(instr, GbInstruction::Misc(Misc::Nop));
        assert_eq!(new_pc, 0);
    }
}
