//! Generates `SM83/RegFile.lean` — a Lean mirror of `cpu::registers`.
//!
//! The Lean types and their accessors are the single source of truth for
//! the Lean-side refinement theorems, and they must stay in lockstep with
//! the Rust emulator. This generator iterates over hand-declared variant
//! lists; each list is consumed by an exhaustive `match` below, so that
//! adding a new `Reg8` / `Reg16` / `Cond` variant in the `cpu` crate
//! immediately fails this extractor's `cargo check` and forces a
//! coordinated update here — no risk of silent drift.
//!
//! No SM83 register layout appears anywhere in hand-written Lean; every
//! field, accessor, and flag bit is emitted from this file alone.

use cpu::registers::{Cond, Reg16, Reg8};

use crate::modules::{AsModule, Module};

pub struct Sm83RegFile;

impl Sm83RegFile {
    pub fn extract() -> Self {
        Self
    }
}

/// Canonical variant ordering for `Reg8` — must cover every variant of
/// `cpu::registers::Reg8`. The exhaustive matches in `reg8_name` /
/// `reg8_field` enforce this at compile time.
const REG8_VARIANTS: &[Reg8] = &[
    Reg8::A,
    Reg8::B,
    Reg8::C,
    Reg8::D,
    Reg8::E,
    Reg8::F,
    Reg8::H,
    Reg8::L,
];

const REG16_VARIANTS: &[Reg16] = &[Reg16::AF, Reg16::BC, Reg16::DE, Reg16::HL, Reg16::SP];

const COND_VARIANTS: &[Cond] = &[Cond::NZ, Cond::Z, Cond::NC, Cond::C];

/// Lean-side constructor name for a `Reg8` variant.
fn reg8_name(r: Reg8) -> &'static str {
    match r {
        Reg8::A => "A",
        Reg8::B => "B",
        Reg8::C => "C",
        Reg8::D => "D",
        Reg8::E => "E",
        Reg8::F => "F",
        Reg8::H => "H",
        Reg8::L => "L",
    }
}

/// Lean-side struct field name for a `Reg8` variant.
fn reg8_field(r: Reg8) -> &'static str {
    match r {
        Reg8::A => "a",
        Reg8::B => "b",
        Reg8::C => "c",
        Reg8::D => "d",
        Reg8::E => "e",
        Reg8::F => "f",
        Reg8::H => "h",
        Reg8::L => "l",
    }
}

fn reg16_name(r: Reg16) -> &'static str {
    match r {
        Reg16::AF => "AF",
        Reg16::BC => "BC",
        Reg16::DE => "DE",
        Reg16::HL => "HL",
        Reg16::SP => "SP",
    }
}

fn cond_name(c: Cond) -> &'static str {
    match c {
        Cond::NZ => "NZ",
        Cond::Z => "Z",
        Cond::NC => "NC",
        Cond::C => "C",
    }
}

impl AsModule for Sm83RegFile {
    fn as_module(&self) -> std::io::Result<Module> {
        let mut out = String::new();
        out.push_str("-- Auto-generated Lean mirror of `cpu::registers`.\n");
        out.push_str("-- Source of truth: lib/crates/cpu/src/registers.rs\n");
        out.push_str("-- Do not edit by hand; regenerate via `sm83-zklean-extractor`.\n\n");

        // ----- Reg8 -----
        out.push_str("/-- 8-bit register names (mirrors `cpu::registers::Reg8`). -/\n");
        out.push_str("inductive Reg8 : Type\n");
        for r in REG8_VARIANTS {
            out.push_str(&format!("  | {}\n", reg8_name(*r)));
        }
        out.push_str("  deriving DecidableEq, Repr\n\n");

        // ----- Reg16 -----
        out.push_str("/-- 16-bit register pair names (mirrors `cpu::registers::Reg16`). -/\n");
        out.push_str("inductive Reg16 : Type\n");
        for r in REG16_VARIANTS {
            out.push_str(&format!("  | {}\n", reg16_name(*r)));
        }
        out.push_str("  deriving DecidableEq, Repr\n\n");

        // ----- Cond -----
        out.push_str(
            "/-- Condition codes for conditional jumps/calls/returns\n    (mirrors `cpu::registers::Cond`). -/\n",
        );
        out.push_str("inductive Cond : Type\n");
        for c in COND_VARIANTS {
            out.push_str(&format!("  | {}\n", cond_name(*c)));
        }
        out.push_str("  deriving DecidableEq, Repr\n\n");

        // ----- RegisterFile -----
        out.push_str(
            "/-- SM83 CPU register file (mirrors `cpu::registers::RegisterFile`).\n    The low nibble of `f` is always zero in hardware; this invariant is\n    enforced by `set_r8 Reg8.F` and by `set_af`. -/\n",
        );
        out.push_str("structure RegisterFile : Type where\n");
        out.push_str("  a  : BitVec 8\n");
        out.push_str("  f  : BitVec 8\n");
        out.push_str("  b  : BitVec 8\n");
        out.push_str("  c  : BitVec 8\n");
        out.push_str("  d  : BitVec 8\n");
        out.push_str("  e  : BitVec 8\n");
        out.push_str("  h  : BitVec 8\n");
        out.push_str("  l  : BitVec 8\n");
        out.push_str("  sp : BitVec 16\n");
        out.push_str("  pc : BitVec 16\n");
        out.push_str("  deriving DecidableEq, Repr\n\n");

        out.push_str("namespace RegisterFile\n\n");

        // ----- Flag accessors -----
        out.push_str("/-- Zero flag (bit 7 of `f`). -/\n");
        out.push_str("def zf (r : RegisterFile) : Bool := r.f.getLsbD 7\n");
        out.push_str("/-- Subtract flag (bit 6 of `f`). -/\n");
        out.push_str("def nf (r : RegisterFile) : Bool := r.f.getLsbD 6\n");
        out.push_str("/-- Half-carry flag (bit 5 of `f`). -/\n");
        out.push_str("def hf (r : RegisterFile) : Bool := r.f.getLsbD 5\n");
        out.push_str("/-- Carry flag (bit 4 of `f`). -/\n");
        out.push_str("def cf (r : RegisterFile) : Bool := r.f.getLsbD 4\n\n");

        // ----- 16-bit pair accessors (high ++ low) -----
        out.push_str("/-- `AF` register pair: `a` in the high byte, `f` in the low byte. -/\n");
        out.push_str("def af (r : RegisterFile) : BitVec 16 := r.a ++ r.f\n");
        out.push_str("def bc (r : RegisterFile) : BitVec 16 := r.b ++ r.c\n");
        out.push_str("def de (r : RegisterFile) : BitVec 16 := r.d ++ r.e\n");
        out.push_str("def hl (r : RegisterFile) : BitVec 16 := r.h ++ r.l\n\n");

        // ----- 16-bit pair writes (low nibble of F masked) -----
        out.push_str("/-- Write the 16-bit `AF` pair. The low nibble of `f` is masked to zero. -/\n");
        out.push_str("def set_af (r : RegisterFile) (v : BitVec 16) : RegisterFile :=\n");
        out.push_str("  { r with a := v.extractLsb' 8 8\n");
        out.push_str("         , f := v.extractLsb' 0 8 &&& 0xF0#8 }\n");
        out.push_str("def set_bc (r : RegisterFile) (v : BitVec 16) : RegisterFile :=\n");
        out.push_str("  { r with b := v.extractLsb' 8 8\n");
        out.push_str("         , c := v.extractLsb' 0 8 }\n");
        out.push_str("def set_de (r : RegisterFile) (v : BitVec 16) : RegisterFile :=\n");
        out.push_str("  { r with d := v.extractLsb' 8 8\n");
        out.push_str("         , e := v.extractLsb' 0 8 }\n");
        out.push_str("def set_hl (r : RegisterFile) (v : BitVec 16) : RegisterFile :=\n");
        out.push_str("  { r with h := v.extractLsb' 8 8\n");
        out.push_str("         , l := v.extractLsb' 0 8 }\n\n");

        // ----- get_r8 (exhaustive match) -----
        out.push_str("/-- Generic 8-bit register read (mirrors `RegisterFile::get_r8`). -/\n");
        out.push_str("def get_r8 (r : RegisterFile) : Reg8 → BitVec 8\n");
        for v in REG8_VARIANTS {
            out.push_str(&format!(
                "  | .{} => r.{}\n",
                reg8_name(*v),
                reg8_field(*v)
            ));
        }
        out.push('\n');

        // ----- set_r8 (F is masked) -----
        out.push_str(
            "/-- Generic 8-bit register write (mirrors `RegisterFile::set_r8`).\n    Writing to `Reg8.F` masks the low nibble to zero. -/\n",
        );
        out.push_str("def set_r8 (r : RegisterFile) : Reg8 → BitVec 8 → RegisterFile\n");
        for v in REG8_VARIANTS {
            let name = reg8_name(*v);
            let field = reg8_field(*v);
            if matches!(v, Reg8::F) {
                out.push_str(&format!(
                    "  | .{name}, v => {{ r with {field} := v &&& 0xF0#8 }}\n"
                ));
            } else {
                out.push_str(&format!(
                    "  | .{name}, v => {{ r with {field} := v }}\n"
                ));
            }
        }
        out.push('\n');

        // ----- get_r16 / set_r16 (exhaustive) -----
        out.push_str("/-- Generic 16-bit register read (mirrors `RegisterFile::get_r16`). -/\n");
        out.push_str("def get_r16 (r : RegisterFile) : Reg16 → BitVec 16\n");
        for v in REG16_VARIANTS {
            match v {
                Reg16::AF => out.push_str("  | .AF => r.af\n"),
                Reg16::BC => out.push_str("  | .BC => r.bc\n"),
                Reg16::DE => out.push_str("  | .DE => r.de\n"),
                Reg16::HL => out.push_str("  | .HL => r.hl\n"),
                Reg16::SP => out.push_str("  | .SP => r.sp\n"),
            }
        }
        out.push('\n');

        out.push_str("/-- Generic 16-bit register write (mirrors `RegisterFile::set_r16`). -/\n");
        out.push_str("def set_r16 (r : RegisterFile) : Reg16 → BitVec 16 → RegisterFile\n");
        for v in REG16_VARIANTS {
            match v {
                Reg16::AF => out.push_str("  | .AF, v => r.set_af v\n"),
                Reg16::BC => out.push_str("  | .BC, v => r.set_bc v\n"),
                Reg16::DE => out.push_str("  | .DE, v => r.set_de v\n"),
                Reg16::HL => out.push_str("  | .HL, v => r.set_hl v\n"),
                Reg16::SP => out.push_str("  | .SP, v => { r with sp := v }\n"),
            }
        }
        out.push('\n');

        // ----- check_cond -----
        out.push_str("/-- Evaluate a condition code against the current flags\n    (mirrors `RegisterFile::check_cond`). -/\n");
        out.push_str("def check_cond (r : RegisterFile) : Cond → Bool\n");
        for c in COND_VARIANTS {
            match c {
                Cond::NZ => out.push_str("  | .NZ => !r.zf\n"),
                Cond::Z => out.push_str("  | .Z  => r.zf\n"),
                Cond::NC => out.push_str("  | .NC => !r.cf\n"),
                Cond::C => out.push_str("  | .C  => r.cf\n"),
            }
        }
        out.push('\n');

        out.push_str("end RegisterFile\n");

        Ok(Module {
            name: "RegFile".into(),
            imports: vec![],
            contents: out.into_bytes(),
        })
    }
}
