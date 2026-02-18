use cpu::GbCpu;
use memory::Bus;

/// Minimal MBC3 bus for profiling — supports ROM banking + basic I/O.
struct ProfilingBus {
    rom: Vec<u8>,
    ram: [u8; 0x10000], // flat 64KB for VRAM, WRAM, HRAM, I/O, etc.
    rom_bank: usize,
    ram_enabled: bool,
    ram_bank: u8,
    // Timer
    div_counter: u16,
    tima: u8,
    tma: u8,
    tac: u8,
    timer_counter: u32,
    timer_overflow: bool,
    // Scanline
    scanline_counter: u32,
    // Serial capture
    serial_output: Vec<u8>,
    // APU (needed for register reads)
    apu: apu::Apu,
}

impl ProfilingBus {
    fn new(rom: Vec<u8>) -> Self {
        Self {
            rom,
            ram: [0u8; 0x10000],
            rom_bank: 1,
            ram_enabled: false,
            ram_bank: 0,
            div_counter: 0,
            tima: 0,
            tma: 0,
            tac: 0,
            timer_counter: 0,
            timer_overflow: false,
            scanline_counter: 0,
            serial_output: Vec::new(),
            apu: apu::Apu::new(),
        }
    }

    fn tick(&mut self, m_cycles: u32) {
        self.apu.update(m_cycles);
        let t_cycles = m_cycles * 4;
        for _ in 0..t_cycles {
            self.div_counter = self.div_counter.wrapping_add(1);
            if self.tac & 0x04 != 0 {
                self.timer_counter += 1;
                let freq = match self.tac & 0x03 {
                    0 => 1024,
                    1 => 16,
                    2 => 64,
                    3 => 256,
                    _ => unreachable!(),
                };
                if self.timer_counter >= freq {
                    self.timer_counter = 0;
                    let (new_tima, overflow) = self.tima.overflowing_add(1);
                    if overflow {
                        self.tima = self.tma;
                        self.timer_overflow = true;
                    } else {
                        self.tima = new_tima;
                    }
                }
            }
        }
        if self.timer_overflow {
            self.timer_overflow = false;
            self.ram[0xFF0F] |= 0x04;
        }
        self.scanline_counter += t_cycles;
        if self.scanline_counter >= 70224 {
            self.scanline_counter -= 70224;
            if self.ram[0xFF40] & 0x80 != 0 {
                self.ram[0xFF0F] |= 0x01; // V-Blank interrupt
            }
        }
    }
}

impl Bus for ProfilingBus {
    fn read(&mut self, addr: u16) -> u8 {
        match addr {
            // ROM bank 0
            0x0000..=0x3FFF => {
                self.rom.get(addr as usize).copied().unwrap_or(0xFF)
            }
            // ROM banked area
            0x4000..=0x7FFF => {
                let offset = self.rom_bank * 0x4000 + (addr as usize - 0x4000);
                self.rom.get(offset).copied().unwrap_or(0xFF)
            }
            // External RAM
            0xA000..=0xBFFF => {
                if self.ram_enabled && self.ram_bank <= 0x07 {
                    self.ram[addr as usize] // simplified
                } else {
                    0xFF
                }
            }
            // Echo RAM
            0xE000..=0xFDFF => self.ram[addr as usize - 0x2000],
            // I/O
            0xFF02 => self.ram[addr as usize] | 0x7E,
            0xFF04 => (self.div_counter >> 8) as u8,
            0xFF05 => self.tima,
            0xFF06 => self.tma,
            0xFF07 => self.tac | 0xF8,
            0xFF0F => self.ram[addr as usize] | 0xE0,
            0xFF10..=0xFF3F => self.apu.read_register(addr),
            0xFF44 => (self.scanline_counter / 456) as u8, // LY
            _ => self.ram[addr as usize],
        }
    }

    fn write(&mut self, addr: u16, value: u8) {
        match addr {
            // MBC3: RAM enable
            0x0000..=0x1FFF => {
                self.ram_enabled = (value & 0x0F) == 0x0A;
            }
            // MBC3: ROM bank
            0x2000..=0x3FFF => {
                let bank = (value & 0x7F) as usize;
                self.rom_bank = if bank == 0 { 1 } else { bank };
            }
            // MBC3: RAM bank / RTC select
            0x4000..=0x5FFF => {
                self.ram_bank = value;
            }
            // MBC3: RTC latch (ignored)
            0x6000..=0x7FFF => {}
            // External RAM
            0xA000..=0xBFFF => {
                if self.ram_enabled && self.ram_bank <= 0x07 {
                    self.ram[addr as usize] = value;
                }
            }
            // Echo RAM
            0xE000..=0xFDFF => {
                self.ram[addr as usize - 0x2000] = value;
            }
            // Serial
            0xFF02 if value == 0x81 => {
                let data = self.ram[0xFF01];
                self.serial_output.push(data);
                self.ram[addr as usize] = 0x01;
            }
            0xFF04 => { self.div_counter = 0; }
            0xFF05 => { self.tima = value; }
            0xFF06 => { self.tma = value; }
            0xFF07 => {
                if (self.tac ^ value) & 0x07 != 0 {
                    self.timer_counter = 0;
                }
                self.tac = value;
            }
            0xFF10..=0xFF3F => self.apu.write_register(addr, value),
            _ => {
                self.ram[addr as usize] = value;
            }
        }
    }
}

/// Opcode names for the SM83 (all 256 main + 256 CB-prefixed opcodes).
/// Indices 0..255 = main opcodes, 256..511 = CB-prefixed opcodes.
fn opcode_name(index: usize) -> &'static str {
    if index >= 512 {
        return "";
    }
    if index >= 256 {
        return cb_opcode_name((index - 256) as u8);
    }
    match index as u8 {
        0x00 => "NOP",
        0x01 => "LD BC,u16",
        0x02 => "LD (BC),A",
        0x03 => "INC BC",
        0x04 => "INC B",
        0x05 => "DEC B",
        0x06 => "LD B,u8",
        0x07 => "RLCA",
        0x08 => "LD (u16),SP",
        0x09 => "ADD HL,BC",
        0x0A => "LD A,(BC)",
        0x0B => "DEC BC",
        0x0C => "INC C",
        0x0D => "DEC C",
        0x0E => "LD C,u8",
        0x0F => "RRCA",
        0x10 => "STOP",
        0x11 => "LD DE,u16",
        0x12 => "LD (DE),A",
        0x13 => "INC DE",
        0x14 => "INC D",
        0x15 => "DEC D",
        0x16 => "LD D,u8",
        0x17 => "RLA",
        0x18 => "JR i8",
        0x19 => "ADD HL,DE",
        0x1A => "LD A,(DE)",
        0x1B => "DEC DE",
        0x1C => "INC E",
        0x1D => "DEC E",
        0x1E => "LD E,u8",
        0x1F => "RRA",
        0x20 => "JR NZ,i8",
        0x21 => "LD HL,u16",
        0x22 => "LD (HL+),A",
        0x23 => "INC HL",
        0x24 => "INC H",
        0x25 => "DEC H",
        0x26 => "LD H,u8",
        0x27 => "DAA",
        0x28 => "JR Z,i8",
        0x29 => "ADD HL,HL",
        0x2A => "LD A,(HL+)",
        0x2B => "DEC HL",
        0x2C => "INC L",
        0x2D => "DEC L",
        0x2E => "LD L,u8",
        0x2F => "CPL",
        0x30 => "JR NC,i8",
        0x31 => "LD SP,u16",
        0x32 => "LD (HL-),A",
        0x33 => "INC SP",
        0x34 => "INC (HL)",
        0x35 => "DEC (HL)",
        0x36 => "LD (HL),u8",
        0x37 => "SCF",
        0x38 => "JR C,i8",
        0x39 => "ADD HL,SP",
        0x3A => "LD A,(HL-)",
        0x3B => "DEC SP",
        0x3C => "INC A",
        0x3D => "DEC A",
        0x3E => "LD A,u8",
        0x3F => "CCF",
        0x40 => "LD B,B",
        0x41 => "LD B,C",
        0x42 => "LD B,D",
        0x43 => "LD B,E",
        0x44 => "LD B,H",
        0x45 => "LD B,L",
        0x46 => "LD B,(HL)",
        0x47 => "LD B,A",
        0x48 => "LD C,B",
        0x49 => "LD C,C",
        0x4A => "LD C,D",
        0x4B => "LD C,E",
        0x4C => "LD C,H",
        0x4D => "LD C,L",
        0x4E => "LD C,(HL)",
        0x4F => "LD C,A",
        0x50 => "LD D,B",
        0x51 => "LD D,C",
        0x52 => "LD D,D",
        0x53 => "LD D,E",
        0x54 => "LD D,H",
        0x55 => "LD D,L",
        0x56 => "LD D,(HL)",
        0x57 => "LD D,A",
        0x58 => "LD E,B",
        0x59 => "LD E,C",
        0x5A => "LD E,D",
        0x5B => "LD E,E",
        0x5C => "LD E,H",
        0x5D => "LD E,L",
        0x5E => "LD E,(HL)",
        0x5F => "LD E,A",
        0x60 => "LD H,B",
        0x61 => "LD H,C",
        0x62 => "LD H,D",
        0x63 => "LD H,E",
        0x64 => "LD H,H",
        0x65 => "LD H,L",
        0x66 => "LD H,(HL)",
        0x67 => "LD H,A",
        0x68 => "LD L,B",
        0x69 => "LD L,C",
        0x6A => "LD L,D",
        0x6B => "LD L,E",
        0x6C => "LD L,H",
        0x6D => "LD L,L",
        0x6E => "LD L,(HL)",
        0x6F => "LD L,A",
        0x70 => "LD (HL),B",
        0x71 => "LD (HL),C",
        0x72 => "LD (HL),D",
        0x73 => "LD (HL),E",
        0x74 => "LD (HL),H",
        0x75 => "LD (HL),L",
        0x76 => "HALT",
        0x77 => "LD (HL),A",
        0x78 => "LD A,B",
        0x79 => "LD A,C",
        0x7A => "LD A,D",
        0x7B => "LD A,E",
        0x7C => "LD A,H",
        0x7D => "LD A,L",
        0x7E => "LD A,(HL)",
        0x7F => "LD A,A",
        0x80 => "ADD A,B",
        0x81 => "ADD A,C",
        0x82 => "ADD A,D",
        0x83 => "ADD A,E",
        0x84 => "ADD A,H",
        0x85 => "ADD A,L",
        0x86 => "ADD A,(HL)",
        0x87 => "ADD A,A",
        0x88 => "ADC A,B",
        0x89 => "ADC A,C",
        0x8A => "ADC A,D",
        0x8B => "ADC A,E",
        0x8C => "ADC A,H",
        0x8D => "ADC A,L",
        0x8E => "ADC A,(HL)",
        0x8F => "ADC A,A",
        0x90 => "SUB A,B",
        0x91 => "SUB A,C",
        0x92 => "SUB A,D",
        0x93 => "SUB A,E",
        0x94 => "SUB A,H",
        0x95 => "SUB A,L",
        0x96 => "SUB A,(HL)",
        0x97 => "SUB A,A",
        0x98 => "SBC A,B",
        0x99 => "SBC A,C",
        0x9A => "SBC A,D",
        0x9B => "SBC A,E",
        0x9C => "SBC A,H",
        0x9D => "SBC A,L",
        0x9E => "SBC A,(HL)",
        0x9F => "SBC A,A",
        0xA0 => "AND A,B",
        0xA1 => "AND A,C",
        0xA2 => "AND A,D",
        0xA3 => "AND A,E",
        0xA4 => "AND A,H",
        0xA5 => "AND A,L",
        0xA6 => "AND A,(HL)",
        0xA7 => "AND A,A",
        0xA8 => "XOR A,B",
        0xA9 => "XOR A,C",
        0xAA => "XOR A,D",
        0xAB => "XOR A,E",
        0xAC => "XOR A,H",
        0xAD => "XOR A,L",
        0xAE => "XOR A,(HL)",
        0xAF => "XOR A,A",
        0xB0 => "OR A,B",
        0xB1 => "OR A,C",
        0xB2 => "OR A,D",
        0xB3 => "OR A,E",
        0xB4 => "OR A,H",
        0xB5 => "OR A,L",
        0xB6 => "OR A,(HL)",
        0xB7 => "OR A,A",
        0xB8 => "CP A,B",
        0xB9 => "CP A,C",
        0xBA => "CP A,D",
        0xBB => "CP A,E",
        0xBC => "CP A,H",
        0xBD => "CP A,L",
        0xBE => "CP A,(HL)",
        0xBF => "CP A,A",
        0xC0 => "RET NZ",
        0xC1 => "POP BC",
        0xC2 => "JP NZ,u16",
        0xC3 => "JP u16",
        0xC4 => "CALL NZ,u16",
        0xC5 => "PUSH BC",
        0xC6 => "ADD A,u8",
        0xC7 => "RST 00h",
        0xC8 => "RET Z",
        0xC9 => "RET",
        0xCA => "JP Z,u16",
        0xCB => "PREFIX CB",
        0xCC => "CALL Z,u16",
        0xCD => "CALL u16",
        0xCE => "ADC A,u8",
        0xCF => "RST 08h",
        0xD0 => "RET NC",
        0xD1 => "POP DE",
        0xD2 => "JP NC,u16",
        0xD3 => "UNUSED",
        0xD4 => "CALL NC,u16",
        0xD5 => "PUSH DE",
        0xD6 => "SUB A,u8",
        0xD7 => "RST 10h",
        0xD8 => "RET C",
        0xD9 => "RETI",
        0xDA => "JP C,u16",
        0xDB => "UNUSED",
        0xDC => "CALL C,u16",
        0xDD => "UNUSED",
        0xDE => "SBC A,u8",
        0xDF => "RST 18h",
        0xE0 => "LD (FF00+u8),A",
        0xE1 => "POP HL",
        0xE2 => "LD (FF00+C),A",
        0xE3 => "UNUSED",
        0xE4 => "UNUSED",
        0xE5 => "PUSH HL",
        0xE6 => "AND A,u8",
        0xE7 => "RST 20h",
        0xE8 => "ADD SP,i8",
        0xE9 => "JP HL",
        0xEA => "LD (u16),A",
        0xEB => "UNUSED",
        0xEC => "UNUSED",
        0xED => "UNUSED",
        0xEE => "XOR A,u8",
        0xEF => "RST 28h",
        0xF0 => "LD A,(FF00+u8)",
        0xF1 => "POP AF",
        0xF2 => "LD A,(FF00+C)",
        0xF3 => "DI",
        0xF4 => "UNUSED",
        0xF5 => "PUSH AF",
        0xF6 => "OR A,u8",
        0xF7 => "RST 30h",
        0xF8 => "LD HL,SP+i8",
        0xF9 => "LD SP,HL",
        0xFA => "LD A,(u16)",
        0xFB => "EI",
        0xFC => "UNUSED",
        0xFD => "UNUSED",
        0xFE => "CP A,u8",
        0xFF => "RST 38h",
    }
}

/// CB-prefixed opcode names for the SM83 (all 256).
fn cb_opcode_name(op: u8) -> &'static str {
    match op {
        0x00 => "RLC B",
        0x01 => "RLC C",
        0x02 => "RLC D",
        0x03 => "RLC E",
        0x04 => "RLC H",
        0x05 => "RLC L",
        0x06 => "RLC (HL)",
        0x07 => "RLC A",
        0x08 => "RRC B",
        0x09 => "RRC C",
        0x0A => "RRC D",
        0x0B => "RRC E",
        0x0C => "RRC H",
        0x0D => "RRC L",
        0x0E => "RRC (HL)",
        0x0F => "RRC A",
        0x10 => "RL B",
        0x11 => "RL C",
        0x12 => "RL D",
        0x13 => "RL E",
        0x14 => "RL H",
        0x15 => "RL L",
        0x16 => "RL (HL)",
        0x17 => "RL A",
        0x18 => "RR B",
        0x19 => "RR C",
        0x1A => "RR D",
        0x1B => "RR E",
        0x1C => "RR H",
        0x1D => "RR L",
        0x1E => "RR (HL)",
        0x1F => "RR A",
        0x20 => "SLA B",
        0x21 => "SLA C",
        0x22 => "SLA D",
        0x23 => "SLA E",
        0x24 => "SLA H",
        0x25 => "SLA L",
        0x26 => "SLA (HL)",
        0x27 => "SLA A",
        0x28 => "SRA B",
        0x29 => "SRA C",
        0x2A => "SRA D",
        0x2B => "SRA E",
        0x2C => "SRA H",
        0x2D => "SRA L",
        0x2E => "SRA (HL)",
        0x2F => "SRA A",
        0x30 => "SWAP B",
        0x31 => "SWAP C",
        0x32 => "SWAP D",
        0x33 => "SWAP E",
        0x34 => "SWAP H",
        0x35 => "SWAP L",
        0x36 => "SWAP (HL)",
        0x37 => "SWAP A",
        0x38 => "SRL B",
        0x39 => "SRL C",
        0x3A => "SRL D",
        0x3B => "SRL E",
        0x3C => "SRL H",
        0x3D => "SRL L",
        0x3E => "SRL (HL)",
        0x3F => "SRL A",
        0x40 => "BIT 0,B",
        0x41 => "BIT 0,C",
        0x42 => "BIT 0,D",
        0x43 => "BIT 0,E",
        0x44 => "BIT 0,H",
        0x45 => "BIT 0,L",
        0x46 => "BIT 0,(HL)",
        0x47 => "BIT 0,A",
        0x48 => "BIT 1,B",
        0x49 => "BIT 1,C",
        0x4A => "BIT 1,D",
        0x4B => "BIT 1,E",
        0x4C => "BIT 1,H",
        0x4D => "BIT 1,L",
        0x4E => "BIT 1,(HL)",
        0x4F => "BIT 1,A",
        0x50 => "BIT 2,B",
        0x51 => "BIT 2,C",
        0x52 => "BIT 2,D",
        0x53 => "BIT 2,E",
        0x54 => "BIT 2,H",
        0x55 => "BIT 2,L",
        0x56 => "BIT 2,(HL)",
        0x57 => "BIT 2,A",
        0x58 => "BIT 3,B",
        0x59 => "BIT 3,C",
        0x5A => "BIT 3,D",
        0x5B => "BIT 3,E",
        0x5C => "BIT 3,H",
        0x5D => "BIT 3,L",
        0x5E => "BIT 3,(HL)",
        0x5F => "BIT 3,A",
        0x60 => "BIT 4,B",
        0x61 => "BIT 4,C",
        0x62 => "BIT 4,D",
        0x63 => "BIT 4,E",
        0x64 => "BIT 4,H",
        0x65 => "BIT 4,L",
        0x66 => "BIT 4,(HL)",
        0x67 => "BIT 4,A",
        0x68 => "BIT 5,B",
        0x69 => "BIT 5,C",
        0x6A => "BIT 5,D",
        0x6B => "BIT 5,E",
        0x6C => "BIT 5,H",
        0x6D => "BIT 5,L",
        0x6E => "BIT 5,(HL)",
        0x6F => "BIT 5,A",
        0x70 => "BIT 6,B",
        0x71 => "BIT 6,C",
        0x72 => "BIT 6,D",
        0x73 => "BIT 6,E",
        0x74 => "BIT 6,H",
        0x75 => "BIT 6,L",
        0x76 => "BIT 6,(HL)",
        0x77 => "BIT 6,A",
        0x78 => "BIT 7,B",
        0x79 => "BIT 7,C",
        0x7A => "BIT 7,D",
        0x7B => "BIT 7,E",
        0x7C => "BIT 7,H",
        0x7D => "BIT 7,L",
        0x7E => "BIT 7,(HL)",
        0x7F => "BIT 7,A",
        0x80 => "RES 0,B",
        0x81 => "RES 0,C",
        0x82 => "RES 0,D",
        0x83 => "RES 0,E",
        0x84 => "RES 0,H",
        0x85 => "RES 0,L",
        0x86 => "RES 0,(HL)",
        0x87 => "RES 0,A",
        0x88 => "RES 1,B",
        0x89 => "RES 1,C",
        0x8A => "RES 1,D",
        0x8B => "RES 1,E",
        0x8C => "RES 1,H",
        0x8D => "RES 1,L",
        0x8E => "RES 1,(HL)",
        0x8F => "RES 1,A",
        0x90 => "RES 2,B",
        0x91 => "RES 2,C",
        0x92 => "RES 2,D",
        0x93 => "RES 2,E",
        0x94 => "RES 2,H",
        0x95 => "RES 2,L",
        0x96 => "RES 2,(HL)",
        0x97 => "RES 2,A",
        0x98 => "RES 3,B",
        0x99 => "RES 3,C",
        0x9A => "RES 3,D",
        0x9B => "RES 3,E",
        0x9C => "RES 3,H",
        0x9D => "RES 3,L",
        0x9E => "RES 3,(HL)",
        0x9F => "RES 3,A",
        0xA0 => "RES 4,B",
        0xA1 => "RES 4,C",
        0xA2 => "RES 4,D",
        0xA3 => "RES 4,E",
        0xA4 => "RES 4,H",
        0xA5 => "RES 4,L",
        0xA6 => "RES 4,(HL)",
        0xA7 => "RES 4,A",
        0xA8 => "RES 5,B",
        0xA9 => "RES 5,C",
        0xAA => "RES 5,D",
        0xAB => "RES 5,E",
        0xAC => "RES 5,H",
        0xAD => "RES 5,L",
        0xAE => "RES 5,(HL)",
        0xAF => "RES 5,A",
        0xB0 => "RES 6,B",
        0xB1 => "RES 6,C",
        0xB2 => "RES 6,D",
        0xB3 => "RES 6,E",
        0xB4 => "RES 6,H",
        0xB5 => "RES 6,L",
        0xB6 => "RES 6,(HL)",
        0xB7 => "RES 6,A",
        0xB8 => "RES 7,B",
        0xB9 => "RES 7,C",
        0xBA => "RES 7,D",
        0xBB => "RES 7,E",
        0xBC => "RES 7,H",
        0xBD => "RES 7,L",
        0xBE => "RES 7,(HL)",
        0xBF => "RES 7,A",
        0xC0 => "SET 0,B",
        0xC1 => "SET 0,C",
        0xC2 => "SET 0,D",
        0xC3 => "SET 0,E",
        0xC4 => "SET 0,H",
        0xC5 => "SET 0,L",
        0xC6 => "SET 0,(HL)",
        0xC7 => "SET 0,A",
        0xC8 => "SET 1,B",
        0xC9 => "SET 1,C",
        0xCA => "SET 1,D",
        0xCB => "SET 1,E",
        0xCC => "SET 1,H",
        0xCD => "SET 1,L",
        0xCE => "SET 1,(HL)",
        0xCF => "SET 1,A",
        0xD0 => "SET 2,B",
        0xD1 => "SET 2,C",
        0xD2 => "SET 2,D",
        0xD3 => "SET 2,E",
        0xD4 => "SET 2,H",
        0xD5 => "SET 2,L",
        0xD6 => "SET 2,(HL)",
        0xD7 => "SET 2,A",
        0xD8 => "SET 3,B",
        0xD9 => "SET 3,C",
        0xDA => "SET 3,D",
        0xDB => "SET 3,E",
        0xDC => "SET 3,H",
        0xDD => "SET 3,L",
        0xDE => "SET 3,(HL)",
        0xDF => "SET 3,A",
        0xE0 => "SET 4,B",
        0xE1 => "SET 4,C",
        0xE2 => "SET 4,D",
        0xE3 => "SET 4,E",
        0xE4 => "SET 4,H",
        0xE5 => "SET 4,L",
        0xE6 => "SET 4,(HL)",
        0xE7 => "SET 4,A",
        0xE8 => "SET 5,B",
        0xE9 => "SET 5,C",
        0xEA => "SET 5,D",
        0xEB => "SET 5,E",
        0xEC => "SET 5,H",
        0xED => "SET 5,L",
        0xEE => "SET 5,(HL)",
        0xEF => "SET 5,A",
        0xF0 => "SET 6,B",
        0xF1 => "SET 6,C",
        0xF2 => "SET 6,D",
        0xF3 => "SET 6,E",
        0xF4 => "SET 6,H",
        0xF5 => "SET 6,L",
        0xF6 => "SET 6,(HL)",
        0xF7 => "SET 6,A",
        0xF8 => "SET 7,B",
        0xF9 => "SET 7,C",
        0xFA => "SET 7,D",
        0xFB => "SET 7,E",
        0xFC => "SET 7,H",
        0xFD => "SET 7,L",
        0xFE => "SET 7,(HL)",
        0xFF => "SET 7,A",
    }
}

#[test]
fn opcode_profile_pokemon_red() {
    let rom_path = "../../../../nightboy/roms/tetris.gb";
    let rom_data = match std::fs::read(rom_path) {
        Ok(d) => d,
        Err(e) => {
            println!("Skipping: could not load Pokemon Red ROM: {e}");
            return;
        }
    };

    let mut bus = ProfilingBus::new(rom_data);
    // DMG post-boot I/O state
    bus.ram[0xFF40] = 0x91; // LCDC: LCD on, BG on
    bus.ram[0xFF0F] = 0x00; // IF: clear
    bus.ram[0xFFFF] = 0x01; // IE: V-Blank
    // APU init
    bus.apu.write_register(0xFF26, 0x80);
    bus.apu.write_register(0xFF24, 0x77);
    bus.apu.write_register(0xFF25, 0xF3);
    bus.apu.write_register(0xFF10, 0x80);
    bus.apu.write_register(0xFF11, 0xBF);
    bus.apu.write_register(0xFF12, 0xF3);

    let mut cpu = GbCpu::new(bus);
    cpu.regs = cpu::RegisterFile::post_boot_dmg();
    cpu.regs.pc = 0x0100;

    let mut histogram = [0u64; 512]; // 0..255 = main, 256..511 = CB-prefix
    let mut total_instructions = 0u64;
    let mut halt_cycles = 0u64;
    let max_cycles: u64 = 50_000_000; // ~12 seconds of gameplay

    let mut stuck_pc = 0xFFFFu16;
    let mut stuck_count = 0u32;

    while cpu.total_cycles < max_cycles {
        if !cpu.halted && !cpu.stopped {
            let pc = cpu.regs.pc;
            let opcode = cpu.bus.read(pc);
            if opcode == 0xCB {
                let cb_byte = cpu.bus.read(pc.wrapping_add(1));
                histogram[256 + cb_byte as usize] += 1;
            } else {
                histogram[opcode as usize] += 1;
            }
            total_instructions += 1;

            // Detect infinite loop (non-HALT)
            if cpu.regs.pc == stuck_pc {
                stuck_count += 1;
                if stuck_count > 5000 {
                    println!(
                        "Stopped early: stuck at PC=0x{:04X} after {} M-cycles ({} instructions)",
                        pc, cpu.total_cycles, total_instructions
                    );
                    break;
                }
            } else {
                stuck_pc = cpu.regs.pc;
                stuck_count = 0;
            }
        } else {
            halt_cycles += 1;
        }

        let cycles = cpu.step();
        cpu.bus.tick(cycles);
    }

    let frames = cpu.total_cycles as f64 / 17556.0; // ~17556 M-cycles per frame
    println!("=== Pokemon Red Opcode Profile ===");
    println!("Total M-cycles:      {}", cpu.total_cycles);
    println!("Total instructions:  {}", total_instructions);
    println!("HALT cycles:         {}", halt_cycles);
    println!("Approx frames:       {:.1}", frames);
    println!();

    // Target opcodes
    let add_hl_bc = histogram[0x09];
    let add_hl_de = histogram[0x19];
    let add_hl_hl = histogram[0x29];
    let add_hl_sp = histogram[0x39];
    println!("--- ADD HL,rr ---");
    println!(
        "  ADD HL,BC (0x09): {:>10}  ({:.4}%)",
        add_hl_bc,
        add_hl_bc as f64 / total_instructions as f64 * 100.0
    );
    println!(
        "  ADD HL,DE (0x19): {:>10}  ({:.4}%)",
        add_hl_de,
        add_hl_de as f64 / total_instructions as f64 * 100.0
    );
    println!(
        "  ADD HL,HL (0x29): {:>10}  ({:.4}%)",
        add_hl_hl,
        add_hl_hl as f64 / total_instructions as f64 * 100.0
    );
    println!(
        "  ADD HL,SP (0x39): {:>10}  ({:.4}%)",
        add_hl_sp,
        add_hl_sp as f64 / total_instructions as f64 * 100.0
    );
    let total_add_hl = add_hl_bc + add_hl_de + add_hl_hl + add_hl_sp;
    println!(
        "  TOTAL ADD HL,rr:  {:>10}  ({:.4}%)",
        total_add_hl,
        total_add_hl as f64 / total_instructions as f64 * 100.0
    );
    println!();

    // Top 100 opcodes
    let mut sorted: Vec<(usize, u64)> = histogram
        .iter()
        .enumerate()
        .filter(|(_, &c)| c > 0)
        .map(|(i, &c)| (i, c))
        .collect();
    sorted.sort_by(|a, b| b.1.cmp(&a.1));

    println!("--- Top 100 opcodes ---");
    for (rank, (opcode, count)) in sorted.iter().take(100).enumerate() {
        let pct = *count as f64 / total_instructions as f64 * 100.0;
        let (prefix, byte) = if *opcode >= 256 {
            ("CB", *opcode - 256)
        } else {
            ("  ", *opcode)
        };
        let name = opcode_name(*opcode);
        println!(
            "  {:2}. {} 0x{:02X}  {:>10}  ({:5.2}%)  {}",
            rank + 1,
            prefix,
            byte,
            count,
            pct,
            name
        );
    }

    // Unique opcodes used
    let unique = sorted.len();
    println!();
    println!("Unique opcodes used: {}/512", unique);
}
