pub mod decode;

use crate::alu::{AluOp, ShiftOp};
use crate::registers::{Cond, Reg16, Reg8};

/// Top-level instruction enum with sub-enums per category.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GbInstruction {
    Load(Load),
    U8Arithmetic(U8Arith),
    U16Arithmetic(U16Arith),
    BitShift(BitShift),
    Jumps(Jump),
    Stack(Stack),
    Flag(Flag),
    Interrupt(InterruptCtl),
    Misc(Misc),
}

// ---------------------------------------------------------------------------
// Load sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(nonstandard_style)]
pub enum Load {
    /// LD r8, r8
    R8_R8(Reg8, Reg8),
    /// LD r8, n8
    R8_N8(Reg8, u8),
    /// LD r16, n16
    R16_N16(Reg16, u16),
    /// LD r8, (HL)
    R8_HL(Reg8),
    /// LD (HL), r8
    HL_R8(Reg8),
    /// LD (r16), A  — BC or DE
    R16Mem_A(Reg16),
    /// LD A, (r16)  — BC or DE
    A_R16Mem(Reg16),
    /// LD A, (HL+)
    A_HLI,
    /// LD A, (HL-)
    A_HLD,
    /// LD (HL+), A
    HLI_A,
    /// LD (HL-), A
    HLD_A,
    /// LD (n16), SP
    N16_SP(u16),
    /// LD (HL), n8
    HL_N8(u8),
    /// LDH (C), A  — LD ($FF00+C), A
    LDH_C_A,
    /// LDH (n8), A — LD ($FF00+n8), A
    LDH_N8_A(u8),
    /// LD (n16), A
    N16_A(u16),
    /// LDH A, (C) — LD A, ($FF00+C)
    LDH_A_C,
    /// LDH A, (n8) — LD A, ($FF00+n8)
    LDH_A_N8(u8),
    /// LD A, (n16)
    A_N16(u16),
}

impl Load {
    /// Machine cycles (not T-cycles; 1 M-cycle = 4 T-cycles on DMG).
    pub const fn cycles(&self) -> u32 {
        match self {
            Self::R8_R8(_, _) => 1,
            Self::R8_N8(_, _) => 2,
            Self::R16_N16(_, _) => 3,
            Self::R8_HL(_) => 2,
            Self::HL_R8(_) => 2,
            Self::R16Mem_A(_) => 2,
            Self::A_R16Mem(_) => 2,
            Self::A_HLI | Self::A_HLD => 2,
            Self::HLI_A | Self::HLD_A => 2,
            Self::N16_SP(_) => 5,
            Self::HL_N8(_) => 3,
            Self::LDH_C_A | Self::LDH_A_C => 2,
            Self::LDH_N8_A(_) | Self::LDH_A_N8(_) => 3,
            Self::N16_A(_) | Self::A_N16(_) => 4,
        }
    }
}

// ---------------------------------------------------------------------------
// 8-bit Arithmetic sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum U8Arith {
    /// Binary op (ADD/ADC/SUB/SBC/AND/XOR/OR/CP) A, r8
    BinR8(AluOp, Reg8),
    /// Binary op A, (HL)
    BinHL(AluOp),
    /// Binary op A, n8
    BinN8(AluOp, u8),
    /// INC/DEC r8
    IncR8(Reg8),
    DecR8(Reg8),
    /// INC/DEC (HL)
    IncHL,
    DecHL,
}

impl U8Arith {
    pub const fn cycles(&self) -> u32 {
        match self {
            Self::BinR8(_, _) => 1,
            Self::BinHL(_) => 2,
            Self::BinN8(_, _) => 2,
            Self::IncR8(_) | Self::DecR8(_) => 1,
            Self::IncHL | Self::DecHL => 3,
        }
    }
}

// ---------------------------------------------------------------------------
// 16-bit Arithmetic sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum U16Arith {
    AddHL(Reg16),
    IncR16(Reg16),
    DecR16(Reg16),
}

impl U16Arith {
    pub const fn cycles(&self) -> u32 {
        match self {
            Self::AddHL(_) => 2,
            Self::IncR16(_) | Self::DecR16(_) => 2,
        }
    }
}

// ---------------------------------------------------------------------------
// BitShift sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BitShift {
    /// RLCA / RRCA / RLA / RRA — A-register rotates (Z always cleared)
    RotA(ShiftOp),
    /// CB-prefix shift/rotate on r8
    ShiftR8(ShiftOp, Reg8),
    /// CB-prefix shift/rotate on (HL)
    ShiftHL(ShiftOp),
    /// BIT b, r8
    BitR8(u8, Reg8),
    /// BIT b, (HL)
    BitHL(u8),
    /// RES b, r8
    ResR8(u8, Reg8),
    /// RES b, (HL)
    ResHL(u8),
    /// SET b, r8
    SetR8(u8, Reg8),
    /// SET b, (HL)
    SetHL(u8),
}

impl BitShift {
    pub const fn cycles(&self) -> u32 {
        match self {
            Self::RotA(_) => 1,
            Self::ShiftR8(_, _) | Self::BitR8(_, _) | Self::ResR8(_, _) | Self::SetR8(_, _) => 2,
            Self::BitHL(_) => 3,
            Self::ShiftHL(_) | Self::ResHL(_) | Self::SetHL(_) => 4,
        }
    }
}

// ---------------------------------------------------------------------------
// Jumps sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Jump {
    JpN16(u16),
    JpCondN16(Cond, u16),
    JpHL,
    Jr(i8),
    JrCond(Cond, i8),
    CallN16(u16),
    CallCond(Cond, u16),
    Ret,
    RetCond(Cond),
    Reti,
    Rst(u8),
}

impl Jump {
    /// Cycles when the jump IS taken.
    pub const fn cycles_taken(&self) -> u32 {
        match self {
            Self::JpN16(_) => 4,
            Self::JpCondN16(_, _) => 4,
            Self::JpHL => 1,
            Self::Jr(_) => 3,
            Self::JrCond(_, _) => 3,
            Self::CallN16(_) => 6,
            Self::CallCond(_, _) => 6,
            Self::Ret => 4,
            Self::RetCond(_) => 5,
            Self::Reti => 4,
            Self::Rst(_) => 4,
        }
    }

    /// Cycles when the condition is NOT taken.
    pub const fn cycles_not_taken(&self) -> u32 {
        match self {
            Self::JpCondN16(_, _) => 3,
            Self::JrCond(_, _) => 2,
            Self::CallCond(_, _) => 3,
            Self::RetCond(_) => 2,
            // Unconditional — always taken, so this should never be called:
            _ => self.cycles_taken(),
        }
    }
}

// ---------------------------------------------------------------------------
// Stack sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Stack {
    Push(Reg16),
    Pop(Reg16),
    AddSP(i8),
    LdHLSP(i8),
    LdSPHL,
}

impl Stack {
    pub const fn cycles(&self) -> u32 {
        match self {
            Self::Push(_) => 4,
            Self::Pop(_) => 3,
            Self::AddSP(_) => 4,
            Self::LdHLSP(_) => 3,
            Self::LdSPHL => 2,
        }
    }
}

// ---------------------------------------------------------------------------
// Flag sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Flag {
    Ccf,
    Scf,
    Cpl,
    Daa,
}

impl Flag {
    pub const fn cycles(&self) -> u32 {
        1
    }
}

// ---------------------------------------------------------------------------
// Interrupt control sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum InterruptCtl {
    Di,
    Ei,
    Halt,
}

impl InterruptCtl {
    pub const fn cycles(&self) -> u32 {
        1
    }
}

// ---------------------------------------------------------------------------
// Misc sub-enum
// ---------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Misc {
    Nop,
    Stop,
    /// Undefined opcode — treated as NOP (no panic).
    Undefined(u8),
}

impl Misc {
    pub const fn cycles(&self) -> u32 {
        1
    }
}
