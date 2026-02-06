use crate::Bus;

/// Flat 64KB RAM for isolated CPU testing.
/// No memory mapping, no peripherals — just raw byte storage.
pub struct TestBus {
    mem: Box<[u8; 65536]>,
}

impl TestBus {
    pub fn new() -> Self {
        Self {
            mem: Box::new([0u8; 65536]),
        }
    }

    /// Load data into memory starting at `base`.
    pub fn load_rom(&mut self, base: u16, data: &[u8]) {
        let start = base as usize;
        self.mem[start..start + data.len()].copy_from_slice(data);
    }
}

impl Default for TestBus {
    fn default() -> Self {
        Self::new()
    }
}

impl Bus for TestBus {
    fn read(&mut self, addr: u16) -> u8 {
        // LY register (0xFF44) returns 0x90 to satisfy LCD wait loops in test ROMs
        if addr == 0xFF44 {
            return 0x90;
        }
        self.mem[addr as usize]
    }

    fn write(&mut self, addr: u16, value: u8) {
        self.mem[addr as usize] = value;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let mut bus = TestBus::new();
        bus.write(0x1234, 0xAB);
        assert_eq!(bus.read(0x1234), 0xAB);
    }

    #[test]
    fn load_rom() {
        let mut bus = TestBus::new();
        bus.load_rom(0x100, &[0x01, 0x02, 0x03]);
        assert_eq!(bus.read(0x100), 0x01);
        assert_eq!(bus.read(0x101), 0x02);
        assert_eq!(bus.read(0x102), 0x03);
    }

    #[test]
    fn ly_returns_0x90() {
        let mut bus = TestBus::new();
        assert_eq!(bus.read(0xFF44), 0x90);
    }
}
