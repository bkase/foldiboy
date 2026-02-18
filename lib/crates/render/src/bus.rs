use memory::Bus;
use ppu::Ppu;

use crate::joypad::Joypad;
use crate::timer::Timer;
use crate::trace_log::{BusOp, TraceLog};

/// Memory region identifiers, aligned with proof system TwistIds.
/// Rom and Regs are defined for v2 trace alignment but not yet viewable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub enum MemoryRegion {
    Wram, // TwistId(0) — C000-DFFF, 8192 bytes
    Rom,  // TwistId(1) — 0000-7FFF (banked, read-only)
    Regs, // TwistId(2) — CPU registers
    Vram, // TwistId(3) — 8000-9FFF, 8192 bytes
    Io,   // TwistId(4) — FF00-FF7F, 128 bytes
    Hram, // TwistId(5) — FF80-FFFE, 127 bytes
    Oam,  // TwistId(6) — FE00-FE9F, 160 bytes
    Eram, // TwistId(7) — A000-BFFF (banked)
}

impl MemoryRegion {
    /// Base address in the Game Boy address space.
    pub fn base_addr(self) -> u16 {
        match self {
            MemoryRegion::Wram => 0xC000,
            MemoryRegion::Rom => 0x0000,
            MemoryRegion::Regs => 0x0000, // N/A for CPU registers
            MemoryRegion::Vram => 0x8000,
            MemoryRegion::Io => 0xFF00,
            MemoryRegion::Hram => 0xFF80,
            MemoryRegion::Oam => 0xFE00,
            MemoryRegion::Eram => 0xA000,
        }
    }

    /// Display name for the debug panel header.
    pub fn label(self) -> &'static str {
        match self {
            MemoryRegion::Wram => "WRAM",
            MemoryRegion::Rom => "ROM",
            MemoryRegion::Regs => "REGS",
            MemoryRegion::Vram => "VRAM",
            MemoryRegion::Io => "I/O",
            MemoryRegion::Hram => "HRAM",
            MemoryRegion::Oam => "OAM",
            MemoryRegion::Eram => "ERAM",
        }
    }
}

/// Viewable regions for the RAM viewer (excludes Rom and Regs).
pub const VIEWABLE_REGIONS: [MemoryRegion; 6] = [
    MemoryRegion::Wram,
    MemoryRegion::Vram,
    MemoryRegion::Hram,
    MemoryRegion::Oam,
    MemoryRegion::Io,
    MemoryRegion::Eram,
];

/// MBC type detected from the cartridge header byte $0147.
#[derive(Debug, Clone, Copy, PartialEq)]
enum MbcType {
    /// ROM only (no mapper).
    None,
    /// MBC1 — up to 2 MB ROM, 32 KB RAM.
    Mbc1,
    /// MBC1 multicart (MBC1M) — wiring variant with 4-bit BANK1.
    Mbc1Multicart,
    /// MBC2 — up to 256 KB ROM, built-in 512×4-bit RAM.
    Mbc2,
    /// MBC5 — up to 8 MB ROM, 128 KB RAM. No $00→$01 zero-adjust.
    Mbc5,
    /// MBC3 — up to 2 MB ROM (4 MB for MBC30), 32 KB RAM (64 KB for MBC30).
    /// Optional RTC (stubbed — see RTC unprovability in plan docs).
    Mbc3,
}

/// Full Game Boy memory bus.
///
/// Dispatches reads/writes to the correct subsystem: ROM, VRAM, OAM, WRAM,
/// HRAM, PPU registers, Timer, Joypad, and interrupt registers.
///
/// # Memory Bank Controller (MBC1)
///
/// When the cartridge header ($0147) indicates MBC1 ($01-$03), ROM and RAM
/// banking is enabled:
///
/// - **BANK1** (5-bit, $2000-$3FFF): lower bits of ROM bank for $4000-$7FFF.
///   Writing $00 is treated as $01 (bank 0 is only accessible via $0000-$3FFF).
/// - **BANK2** (2-bit, $4000-$5FFF): upper bits of ROM bank (or RAM bank in
///   mode 1).
/// - **Mode** (1-bit, $6000-$7FFF): 0 = simple ROM banking, 1 = advanced
///   (BANK2 affects $0000-$3FFF and RAM bank select).
/// - **RAM enable** ($0000-$1FFF): lower nibble $0A enables external RAM.
///
/// MBC1 multicarts (MBC1M) use a 4-bit BANK1 shift instead of 5-bit,
/// detected by checking for Nintendo logos at $40104 in the ROM.
///
/// # Memory Bank Controller (MBC2)
///
/// When the cartridge header ($0147) indicates MBC2 ($05-$06):
///
/// - **ROMB** (4-bit): ROM bank for $4000-$7FFF. Writing $00 is treated
///   as $01 (same zero-adjust as MBC1). Only responds to writes in
///   $0000-$3FFF where address bit 8 (A8) is **set**.
/// - **RAMG**: RAM enable/disable. Only responds to writes in $0000-$3FFF
///   where A8 is **clear**. Lower nibble $0A enables; anything else disables.
/// - **Built-in RAM**: 512 × 4-bit, mapped at $A000-$A1FF, mirrored every
///   512 bytes through $BFFF. Upper nibble reads as $F. No bank switching.
/// - Writes to $4000-$7FFF are ignored (no BANK2, no mode register).
///
/// # Memory Bank Controller (MBC3)
///
/// When the cartridge header ($0147) indicates MBC3 ($0F-$13):
///
/// - **ROMB** (7-bit, $2000-$3FFF): ROM bank for $4000-$7FFF. Writing $00
///   is treated as $01 (same zero-adjust as MBC1). MBC30 uses all 8 bits
///   for up to 256 banks (4 MB). Since the same cart type codes are used
///   for both, we store all 8 bits and let `rom_bank_mask` handle wrapping.
/// - **RAMB/RTC** ($4000-$5FFF): values $00-$07 select a RAM bank; values
///   $08-$0C select an RTC register (seconds, minutes, hours, day lo,
///   day hi/flags). The RTC is **stubbed to return 0** — see the RTC
///   unprovability note in `plan/adding-new-opcode-set.md`.
/// - **RTC latch** ($6000-$7FFF): writing $00 then $01 latches the RTC.
///   Ignored (RTC stubbed).
/// - **RAM enable** ($0000-$1FFF): lower nibble $0A enables external RAM.
/// - $0000-$3FFF is always bank 0. No mode register.
///
/// # Memory Bank Controller (MBC5)
///
/// When the cartridge header ($0147) indicates MBC5 ($19-$1E):
///
/// - **ROMB_LO** (8-bit, $2000-$2FFF): lower 8 bits of ROM bank.
/// - **ROMB_HI** (1-bit, $3000-$3FFF): bit 8 of ROM bank.
/// - **RAMB** (4-bit, $4000-$5FFF): RAM bank select (independent register).
/// - **RAM enable** ($0000-$1FFF): lower nibble $0A enables external RAM.
/// - Unlike MBC1/MBC2, bank 0 **can** be mapped at $4000-$7FFF (no
///   $00→$01 zero-adjust). $0000-$3FFF is always bank 0.
/// - Writes to $6000-$7FFF are ignored (no mode register).
///
/// # OAM DMA (deliberately simplified for ZK)
///
/// Writing to $FF46 triggers an **instantaneous** OAM DMA: all 160 bytes
/// are copied in the same `write()` call. On real hardware, DMA takes
/// 160 M-cycles during which OAM reads return $FF and only HRAM is
/// accessible to the CPU. Modelling cycle-accurate DMA would add
/// significant complexity for zero benefit to real games (they all spin
/// in a HRAM loop waiting for DMA to finish anyway).
///
/// The following Mooneye tests depend on cycle-accurate DMA and are
/// deliberately skipped:
///
/// - `oam_dma_timing` — checks exact DMA duration
/// - `oam_dma_restart` — checks behaviour when restarting DMA mid-transfer
/// - `oam_dma_start` — checks the 1-M-cycle delay before DMA begins
pub struct GameBoyBus {
    // Cartridge ROM (up to 8 MB for MBC5, 2 MB for MBC1, 256 KB for MBC2)
    pub rom: Vec<u8>,

    // MBC state
    mbc_type: MbcType,
    bank1: u8,             // BANK1/ROMB register (8-bit MBC5, 5-bit MBC1, 4-bit MBC2)
    bank2: u8,             // 2-bit BANK2 (MBC1) or 1-bit ROMB_HI (MBC5)
    mbc_mode: bool,        // false = mode 0, true = mode 1 (MBC1 only)
    rom_bank_mask: usize,  // (rom_banks - 1), for wrapping bank numbers
    ram_bank_count: usize, // 0, 1, or 4 (MBC1); up to 16 (MBC5); 0 (MBC2)
    ram_bank_reg: u8,      // 4-bit RAMB register (MBC5 only)
    bank1_shift: u8,       // 8 for MBC5, 5 for standard MBC1, 4 for MBC1M/MBC2
    bank1_mask: u8,        // 0xFF for MBC5, 0x1F for standard MBC1, 0x0F for MBC1M/MBC2

    // External/built-in cart RAM
    // MBC1: up to 32 KB (4 × 8 KB banks)
    // MBC2: 512 × 4-bit built-in RAM (upper nibble reads as $F)
    pub eram: Vec<u8>,
    pub eram_enabled: bool,

    // PPU (owns VRAM + OAM)
    pub ppu: Ppu,

    // RAM
    pub wram: [u8; 8192],
    pub hram: [u8; 127],

    // I/O
    pub joypad: Joypad,
    pub timer: Timer,
    pub apu: apu::Apu,
    pub if_reg: u8, // 0xFF0F — interrupt flag
    pub ie_reg: u8, // 0xFFFF — interrupt enable

    // Serial (stub for Blargg test output)
    pub serial_data: u8,
    pub serial_control: u8,
    pub serial_output: Vec<u8>,

    // OAM DMA
    pub dma_reg: u8, // $FF46: last value written

    // Trace log for debug trace viewer
    pub trace_log: TraceLog,
}

impl GameBoyBus {
    pub fn new(rom: Vec<u8>) -> Self {
        // Detect MBC type from cartridge header
        let cart_type = rom.get(0x0147).copied().unwrap_or(0);
        let is_mbc1 = matches!(cart_type, 0x01..=0x03);
        let is_mbc2 = matches!(cart_type, 0x05..=0x06);
        let is_mbc3 = matches!(cart_type, 0x0F..=0x13);
        let is_mbc5 = matches!(cart_type, 0x19..=0x1E);

        // ROM bank count from header
        let rom_size_code = rom.get(0x0148).copied().unwrap_or(0) as usize;
        let rom_banks = 2usize << rom_size_code;
        let rom_bank_mask = rom_banks - 1;

        // RAM: MBC2 has built-in 512×4-bit RAM; others use header byte $0149
        let ram_size_code = rom.get(0x0149).copied().unwrap_or(0);
        let (ram_size, ram_bank_count) = if is_mbc2 {
            (512, 0) // Built-in RAM, no banking
        } else {
            match ram_size_code {
                2 => (8192, 1),      // 8 KB (1 bank)
                3 => (32768, 4),     // 32 KB (4 banks)
                4 => (131072, 16),   // 128 KB (16 banks) — MBC5 only
                5 => (65536, 8),     // 64 KB (8 banks) — MBC5/MBC30
                _ => (0, 0),         // No RAM
            }
        };

        // Detect MBC1 multicart: Nintendo logo present at $40104
        let mbc_type = if is_mbc1 {
            if detect_mbc1_multicart(&rom) {
                MbcType::Mbc1Multicart
            } else {
                MbcType::Mbc1
            }
        } else if is_mbc2 {
            MbcType::Mbc2
        } else if is_mbc3 {
            MbcType::Mbc3
        } else if is_mbc5 {
            MbcType::Mbc5
        } else {
            MbcType::None
        };

        let (bank1_shift, bank1_mask) = match mbc_type {
            // MBC3: bank1 holds full ROM bank (8-bit for MBC30 compat);
            // bank2 unused for ROM, so shift puts it out of the way.
            MbcType::Mbc3 | MbcType::Mbc5 => (8, 0xFF),
            MbcType::Mbc1Multicart | MbcType::Mbc2 => (4, 0x0F),
            _ => (5, 0x1F),
        };

        GameBoyBus {
            rom,
            mbc_type,
            // MBC5 powers on with ROMB_LO=1 (bank 1 at $4000-$7FFF).
            // MBC1/MBC2 power on with 0 but their zero-adjust maps $00→$01.
            bank1: if mbc_type == MbcType::Mbc5 { 1 } else { 0 },
            bank2: 0,
            mbc_mode: false,
            rom_bank_mask,
            ram_bank_count,
            ram_bank_reg: 0,
            bank1_shift,
            bank1_mask,
            eram: vec![0; if is_mbc2 { 512 } else { ram_size.max(8192) }],
            eram_enabled: false,
            ppu: Ppu::new(),
            wram: [0; 8192],
            hram: [0; 127],
            joypad: Joypad::new(),
            timer: Timer::new(),
            apu: apu::Apu::new(),
            if_reg: 0,
            ie_reg: 0,
            serial_data: 0,
            serial_control: 0,
            serial_output: Vec::new(),
            dma_reg: 0,
            trace_log: TraceLog::new(),
        }
    }

    /// Effective BANK1/ROMB value for ROM banking.
    ///
    /// MBC1/MBC2 apply $00→$01 zero-adjust: bank 0 is never mapped at
    /// $4000-$7FFF. For MBC1, the chip stores 5 bits and the MBC1M PCB masks
    /// to 4 after substitution. For MBC2, the register is natively 4-bit.
    /// MBC5 has **no** zero-adjust — bank 0 can be at $4000-$7FFF.
    fn effective_bank1(&self) -> u8 {
        if self.mbc_type == MbcType::Mbc5 {
            return self.bank1;
        }
        let effective = if self.bank1 == 0 { 1 } else { self.bank1 };
        effective & self.bank1_mask
    }

    /// ROM bank number for $0000-$3FFF.
    fn rom_bank_low(&self) -> usize {
        // MBC5, MBC2, None: $0000-$3FFF is always bank 0
        if !matches!(self.mbc_type, MbcType::Mbc1 | MbcType::Mbc1Multicart) {
            return 0;
        }
        if self.mbc_mode {
            ((self.bank2 as usize) << self.bank1_shift) & self.rom_bank_mask
        } else {
            0
        }
    }

    /// ROM bank number for $4000-$7FFF.
    fn rom_bank_high(&self) -> usize {
        if self.mbc_type == MbcType::None {
            return 1;
        }
        let bank = ((self.bank2 as usize) << self.bank1_shift)
            | (self.effective_bank1() as usize);
        bank & self.rom_bank_mask
    }

    /// RAM bank number for $A000-$BFFF.
    fn ram_bank(&self) -> usize {
        if matches!(self.mbc_type, MbcType::Mbc3 | MbcType::Mbc5) && self.ram_bank_count > 1 {
            (self.ram_bank_reg as usize) % self.ram_bank_count
        } else if self.mbc_mode && self.ram_bank_count > 1 {
            (self.bank2 as usize) % self.ram_bank_count
        } else {
            0
        }
    }

    /// Read a byte from ROM with banking.
    fn read_rom(&self, addr: u16) -> u8 {
        let (bank, offset_in_bank) = if addr < 0x4000 {
            (self.rom_bank_low(), addr as usize)
        } else {
            (self.rom_bank_high(), (addr as usize) - 0x4000)
        };
        let offset = bank * 0x4000 + offset_in_bank;
        self.rom.get(offset).copied().unwrap_or(0xFF)
    }

    /// Read a byte from external/built-in RAM.
    fn read_eram(&self, addr: u16) -> u8 {
        if !self.eram_enabled {
            return 0xFF;
        }
        if self.mbc_type == MbcType::Mbc2 {
            // 512×4-bit built-in RAM, mirrored every 512 bytes, upper nibble = $F
            let offset = (addr as usize - 0xA000) & 0x01FF;
            return self.eram.get(offset).copied().unwrap_or(0xFF) | 0xF0;
        }
        if self.mbc_type == MbcType::Mbc3 && self.ram_bank_reg >= 0x08 {
            // RTC register selected — stubbed to 0 (unprovable in ZK)
            return 0x00;
        }
        let bank = self.ram_bank();
        let offset = bank * 0x2000 + (addr as usize - 0xA000);
        self.eram.get(offset).copied().unwrap_or(0xFF)
    }

    /// Write a byte to external/built-in RAM.
    fn write_eram(&mut self, addr: u16, value: u8) {
        if !self.eram_enabled {
            return;
        }
        if self.mbc_type == MbcType::Mbc2 {
            // 512×4-bit: only lower nibble stored
            let offset = (addr as usize - 0xA000) & 0x01FF;
            if offset < self.eram.len() {
                self.eram[offset] = value & 0x0F;
            }
            return;
        }
        if self.mbc_type == MbcType::Mbc3 && self.ram_bank_reg >= 0x08 {
            // RTC register selected — writes ignored (RTC stubbed)
            return;
        }
        let bank = self.ram_bank();
        let offset = bank * 0x2000 + (addr as usize - 0xA000);
        if offset < self.eram.len() {
            self.eram[offset] = value;
        }
    }

    /// Size of a memory region in bytes.
    pub fn region_size(&self, region: MemoryRegion) -> usize {
        match region {
            MemoryRegion::Wram => 8192,
            MemoryRegion::Rom => self.rom.len(),
            MemoryRegion::Regs => 0,
            MemoryRegion::Vram => 8192,
            MemoryRegion::Io => 128,
            MemoryRegion::Hram => 127,
            MemoryRegion::Oam => 160,
            MemoryRegion::Eram => self.eram.len(),
        }
    }

    /// Read a byte from a memory region by offset (no side effects).
    pub fn read_region(&self, region: MemoryRegion, offset: usize) -> u8 {
        match region {
            MemoryRegion::Wram => {
                self.wram.get(offset).copied().unwrap_or(0xFF)
            }
            MemoryRegion::Vram => {
                let addr = 0x8000u16.wrapping_add(offset as u16);
                self.ppu.vram.read(addr)
            }
            MemoryRegion::Hram => {
                self.hram.get(offset).copied().unwrap_or(0xFF)
            }
            MemoryRegion::Oam => {
                let addr = 0xFE00u16.wrapping_add(offset as u16);
                self.ppu.oam.read(addr)
            }
            MemoryRegion::Io => {
                // Read I/O without side effects — return raw register values
                let addr = 0xFF00u16.wrapping_add(offset as u16);
                match addr {
                    0xFF00 => self.joypad.read(),
                    0xFF01 => self.serial_data,
                    0xFF02 => self.serial_control | 0x7E,
                    0xFF04..=0xFF07 => self.timer.read(addr),
                    0xFF0F => self.if_reg | 0xE0,
                    0xFF10..=0xFF26 | 0xFF30..=0xFF3F => self.apu.read_register(addr),
                    0xFF46 => self.dma_reg,
                    0xFF40..=0xFF4B => self.ppu.read_register(addr),
                    _ => 0xFF,
                }
            }
            MemoryRegion::Eram => {
                self.eram.get(offset).copied().unwrap_or(0xFF)
            }
            MemoryRegion::Rom => {
                self.rom.get(offset).copied().unwrap_or(0xFF)
            }
            MemoryRegion::Regs => 0xFF,
        }
    }

    /// Current external RAM bank number (for display).
    pub fn eram_bank(&self) -> usize {
        self.ram_bank()
    }

    fn oam_dma(&mut self, source_high: u8) {
        let base = (source_high as u16) << 8;
        for i in 0..160u16 {
            let byte = self.dma_read(base + i);
            self.ppu.oam.write(0xFE00 + i, byte);
        }
    }

    /// Read from the DMA bus perspective.  OAM DMA uses the external bus,
    /// where $E000-$FFFF is extended echo RAM (all maps to WRAM), not
    /// OAM/IO/HRAM as the CPU would see.
    fn dma_read(&self, addr: u16) -> u8 {
        match addr {
            0x0000..=0x7FFF => self.read_rom(addr),
            0x8000..=0x9FFF => self.ppu.vram.read(addr),
            0xA000..=0xBFFF => self.read_eram(addr),
            0xC000..=0xDFFF => self.wram[(addr - 0xC000) as usize],
            0xE000..=0xFFFF => self.wram[(addr - 0xE000) as usize],
        }
    }
}

/// Detect MBC1 multicart (MBC1M) by checking for a Nintendo logo
/// at offset $40104 (the header position of the second 256 KB slot).
fn detect_mbc1_multicart(rom: &[u8]) -> bool {
    if rom.len() < 0x40134 {
        return false;
    }
    rom[0x0104..0x0134] == rom[0x40104..0x40134]
}

impl Bus for GameBoyBus {
    fn read(&mut self, addr: u16) -> u8 {
        let value = match addr {
            // ROM (banked)
            0x0000..=0x7FFF => self.read_rom(addr),

            // VRAM
            0x8000..=0x9FFF => self.ppu.vram.read(addr),

            // External RAM (banked)
            0xA000..=0xBFFF => self.read_eram(addr),

            // Work RAM
            0xC000..=0xDFFF => self.wram[(addr - 0xC000) as usize],

            // Echo RAM (mirror of C000-DDFF)
            0xE000..=0xFDFF => self.wram[(addr - 0xE000) as usize],

            // OAM
            0xFE00..=0xFE9F => self.ppu.oam.read(addr),

            // Unusable
            0xFEA0..=0xFEFF => 0xFF,

            // I/O Registers
            0xFF00 => self.joypad.read(),
            0xFF01 => self.serial_data,
            0xFF02 => self.serial_control | 0x7E, // SC: bits 1-6 unused, always 1 on DMG
            0xFF04..=0xFF07 => self.timer.read(addr),
            0xFF0F => self.if_reg | 0xE0, // IF: bits 5-7 unused, always 1
            0xFF10..=0xFF26 | 0xFF30..=0xFF3F => self.apu.read_register(addr),
            0xFF46 => self.dma_reg,
            0xFF40..=0xFF4B => self.ppu.read_register(addr),

            // High RAM
            0xFF80..=0xFFFE => self.hram[(addr - 0xFF80) as usize],

            // Interrupt Enable
            0xFFFF => self.ie_reg,

            // Unmapped I/O
            _ => 0xFF,
        };
        self.trace_log.push_op(BusOp { addr, value, is_write: false });
        value
    }

    fn write(&mut self, addr: u16, value: u8) {
        match addr {
            // MBC registers ($0000-$7FFF)
            0x0000..=0x1FFF => {
                match self.mbc_type {
                    MbcType::Mbc2 => {
                        // A8 selects register: 0 = RAMG, 1 = ROMB
                        if addr & 0x0100 == 0 {
                            self.eram_enabled = (value & 0x0F) == 0x0A;
                        } else {
                            self.bank1 = value & 0x0F;
                        }
                    }
                    MbcType::None => {}
                    _ => self.eram_enabled = (value & 0x0F) == 0x0A,
                }
            }
            0x2000..=0x3FFF => {
                match self.mbc_type {
                    MbcType::Mbc2 => {
                        // A8 selects register: 0 = RAMG, 1 = ROMB
                        if addr & 0x0100 == 0 {
                            self.eram_enabled = (value & 0x0F) == 0x0A;
                        } else {
                            self.bank1 = value & 0x0F;
                        }
                    }
                    MbcType::Mbc3 => {
                        // 7-bit ROM bank (all 8 bits stored for MBC30 compat;
                        // rom_bank_mask handles wrapping to actual ROM size).
                        self.bank1 = value;
                    }
                    MbcType::Mbc5 => {
                        // $2000-$2FFF: ROMB_LO (8-bit)
                        // $3000-$3FFF: ROMB_HI (1-bit)
                        if addr < 0x3000 {
                            self.bank1 = value;
                        } else {
                            self.bank2 = value & 0x01;
                        }
                    }
                    MbcType::None => {}
                    _ => {
                        // MBC1: always store the full 5-bit value. The chip
                        // does $00→$01 substitution on 5 bits; MBC1M masking
                        // to 4 bits happens in effective_bank1() afterwards.
                        self.bank1 = value & 0x1F;
                    }
                }
            }
            0x4000..=0x5FFF => {
                match self.mbc_type {
                    MbcType::Mbc1 | MbcType::Mbc1Multicart => {
                        self.bank2 = value & 0x03;
                    }
                    MbcType::Mbc3 => {
                        // $00-$07: RAM bank select; $08-$0C: RTC register select
                        self.ram_bank_reg = value;
                    }
                    MbcType::Mbc5 => {
                        self.ram_bank_reg = value & 0x0F;
                    }
                    _ => {} // MBC2, None: ignored
                }
            }
            0x6000..=0x7FFF => {
                // MBC1 only: mode. MBC2 ignores writes here.
                if matches!(self.mbc_type, MbcType::Mbc1 | MbcType::Mbc1Multicart) {
                    self.mbc_mode = (value & 0x01) != 0;
                }
            }

            // VRAM
            0x8000..=0x9FFF => self.ppu.vram.write(addr, value),

            // External RAM (banked)
            0xA000..=0xBFFF => self.write_eram(addr, value),

            // Work RAM
            0xC000..=0xDFFF => self.wram[(addr - 0xC000) as usize] = value,

            // Echo RAM
            0xE000..=0xFDFF => self.wram[(addr - 0xE000) as usize] = value,

            // OAM
            0xFE00..=0xFE9F => self.ppu.oam.write(addr, value),

            // Unusable
            0xFEA0..=0xFEFF => {}

            // I/O Registers
            0xFF00 => self.joypad.write(value),
            0xFF01 => self.serial_data = value,
            0xFF02 => {
                self.serial_control = value;
                if value & 0x80 != 0 {
                    // Transfer requested — capture serial byte
                    self.serial_output.push(self.serial_data);
                    self.serial_control &= 0x7F; // Clear transfer flag
                }
            }
            0xFF04..=0xFF07 => self.timer.write(addr, value),
            0xFF0F => self.if_reg = value,
            0xFF10..=0xFF26 | 0xFF30..=0xFF3F => self.apu.write_register(addr, value),
            0xFF46 => {
                self.dma_reg = value;
                self.oam_dma(value);
            }
            0xFF40..=0xFF4B => {
                self.ppu.write_register(addr, value);
                // Apply STAT interrupt immediately so it's visible to the
                // CPU's interrupt check at the end of the current instruction.
                if self.ppu.take_pending_stat_irq() {
                    self.if_reg |= 0x02;
                }
            }

            // High RAM
            0xFF80..=0xFFFE => self.hram[(addr - 0xFF80) as usize] = value,

            // Interrupt Enable
            0xFFFF => self.ie_reg = value,

            // Unmapped I/O
            _ => {}
        }
        self.trace_log.push_op(BusOp { addr, value, is_write: true });
    }
}
