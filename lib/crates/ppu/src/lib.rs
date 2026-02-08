pub mod registers;
pub mod vram;
pub mod oam;
mod scanline;

use registers::*;
use vram::VideoRam;
use oam::SpriteAttributeTable;

pub const SCREEN_WIDTH: usize = 160;
pub const SCREEN_HEIGHT: usize = 144;

/// Result of a PPU update — tells the caller what happened.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PpuEvent {
    /// Nothing notable happened.
    None,
    /// A full frame just completed (entering VBlank). Render the framebuffer now.
    FrameComplete,
}

/// Interrupt flags the PPU wants to raise.
#[derive(Debug, Clone, Copy, Default)]
pub struct PpuInterrupts {
    pub vblank: bool,
    pub stat: bool,
}

/// The 160x144 framebuffer.
pub struct Screen {
    pixels: [Colour; SCREEN_WIDTH * SCREEN_HEIGHT],
}

impl Screen {
    pub fn new() -> Self {
        Screen {
            pixels: [Colour::White; SCREEN_WIDTH * SCREEN_HEIGHT],
        }
    }

    pub fn get(&self, x: u8, y: u8) -> Colour {
        if (x as usize) < SCREEN_WIDTH && (y as usize) < SCREEN_HEIGHT {
            self.pixels[y as usize * SCREEN_WIDTH + x as usize]
        } else {
            Colour::Black
        }
    }

    pub fn set(&mut self, x: u8, y: u8, colour: Colour) {
        if (x as usize) < SCREEN_WIDTH && (y as usize) < SCREEN_HEIGHT {
            self.pixels[y as usize * SCREEN_WIDTH + x as usize] = colour;
        }
    }

    /// Convert to RGBA8 bytes for GPU upload (classic DMG green palette).
    pub fn to_rgba8(&self) -> Vec<u8> {
        let mut rgba = Vec::with_capacity(SCREEN_WIDTH * SCREEN_HEIGHT * 4);
        for colour in &self.pixels {
            let [r, g, b] = colour.to_rgb();
            rgba.extend_from_slice(&[r, g, b, 255]);
        }
        rgba
    }
}

/// DMG Pixel Processing Unit.
///
/// Owns VRAM, OAM, the screen framebuffer, and all PPU registers.
/// Call [`Ppu::update`] after each CPU step, passing the number of M-cycles
/// consumed by that instruction.
pub struct Ppu {
    pub screen: Screen,
    pub vram: VideoRam,
    pub oam: SpriteAttributeTable,

    // Registers
    pub lcdc: Lcdc,
    pub stat: Stat,
    pub scy: u8,
    pub scx: u8,
    pub ly: u8,
    pub lyc: u8,
    pub bgp: Palette,
    pub obp0: Palette,
    pub obp1: Palette,
    pub wy: u8,
    pub wx: u8,

    // Internal state
    clock: u32,
    window_line: u8,
    window_triggered: bool,
}

impl Ppu {
    pub fn new() -> Self {
        Ppu {
            screen: Screen::new(),
            vram: VideoRam::new(),
            oam: SpriteAttributeTable::new(),
            lcdc: Lcdc(0x91), // LCD on, BG on
            stat: Stat(0x82), // bit 7 always 1, start in mode 2
            scy: 0,
            scx: 0,
            ly: 0,
            lyc: 0,
            bgp: Palette(0xFC),
            obp0: Palette(0),
            obp1: Palette(0),
            wy: 0,
            wx: 0,
            clock: 0,
            window_line: 0,
            window_triggered: false,
        }
    }

    /// Advance the PPU by the given number of M-cycles.
    ///
    /// Returns a `PpuEvent` indicating whether a frame just completed, and
    /// any interrupt flags the PPU wants to raise.
    pub fn update(&mut self, m_cycles: u32) -> (PpuEvent, PpuInterrupts) {
        if !self.lcdc.lcd_enable() {
            return (PpuEvent::None, PpuInterrupts::default());
        }

        let dots = m_cycles * 4;
        self.clock += dots;

        let mut event = PpuEvent::None;
        let mut interrupts = PpuInterrupts::default();

        let mode = self.stat.mode();
        match mode {
            2 => {
                // OAM Search → Data Transfer after 80 dots
                if self.clock >= 80 {
                    self.clock -= 80;
                    self.stat.set_mode(3);
                    self.window_triggered =
                        self.window_triggered || self.ly == self.wy;
                }
            }
            3 => {
                // Data Transfer → HBlank after 172 dots
                if self.clock >= 172 {
                    self.clock -= 172;
                    self.draw_scanline();
                    self.stat.set_mode(0);
                    if self.stat.hblank_int() {
                        interrupts.stat = true;
                    }
                }
            }
            0 => {
                // HBlank → next line after 204 dots
                if self.clock >= 204 {
                    self.clock -= 204;
                    self.ly += 1;
                    self.check_lyc(&mut interrupts);

                    if self.ly >= 144 {
                        // Enter VBlank
                        self.stat.set_mode(1);
                        interrupts.vblank = true;
                        if self.stat.vblank_int() {
                            interrupts.stat = true;
                        }
                        event = PpuEvent::FrameComplete;
                    } else {
                        self.stat.set_mode(2);
                        if self.stat.oam_int() {
                            interrupts.stat = true;
                        }
                    }
                }
            }
            1 => {
                // VBlank: 10 lines of 456 dots each
                if self.clock >= 456 {
                    self.clock -= 456;
                    self.ly += 1;
                    self.check_lyc(&mut interrupts);

                    if self.ly > 153 {
                        // Frame complete, start new frame
                        self.ly = 0;
                        self.window_line = 0;
                        self.window_triggered = false;
                        self.stat.set_mode(2);
                        self.check_lyc(&mut interrupts);
                        if self.stat.oam_int() {
                            interrupts.stat = true;
                        }
                    }
                }
            }
            _ => unreachable!(),
        }

        (event, interrupts)
    }

    fn check_lyc(&mut self, interrupts: &mut PpuInterrupts) {
        let eq = self.ly == self.lyc;
        self.stat.set_lyc_eq_ly(eq);
        if eq && self.stat.lyc_int() {
            interrupts.stat = true;
        }
    }

    fn draw_scanline(&mut self) {
        scanline::draw_background_scanline(
            &mut self.screen,
            &self.vram,
            self.lcdc,
            self.bgp,
            self.scx,
            self.scy,
            self.ly,
        );

        if self.window_triggered {
            let drew_window = scanline::draw_window_scanline(
                &mut self.screen,
                &self.vram,
                self.lcdc,
                self.bgp,
                self.wx,
                self.ly,
                self.window_line,
            );
            if drew_window {
                self.window_line += 1;
            }
        }

        scanline::draw_sprites_scanline(
            &mut self.screen,
            &self.vram,
            &self.oam,
            self.lcdc,
            self.obp0,
            self.obp1,
            self.ly,
        );
    }

    /// Get the framebuffer as RGBA8 bytes (160 * 144 * 4 = 92,160 bytes).
    pub fn framebuffer_rgba8(&self) -> Vec<u8> {
        self.screen.to_rgba8()
    }

    /// Read a PPU register by I/O address (0xFF40-0xFF4B).
    pub fn read_register(&self, addr: u16) -> u8 {
        match addr {
            0xFF40 => self.lcdc.0,
            0xFF41 => self.stat.0 | 0x80,
            0xFF42 => self.scy,
            0xFF43 => self.scx,
            0xFF44 => self.ly,
            0xFF45 => self.lyc,
            // 0xFF46: DMA — handled by bus, not PPU
            0xFF47 => self.bgp.0,
            0xFF48 => self.obp0.0,
            0xFF49 => self.obp1.0,
            0xFF4A => self.wy,
            0xFF4B => self.wx,
            _ => 0xFF,
        }
    }

    /// Write a PPU register by I/O address (0xFF40-0xFF4B).
    pub fn write_register(&mut self, addr: u16, val: u8) {
        match addr {
            0xFF40 => {
                let was_on = self.lcdc.lcd_enable();
                self.lcdc = Lcdc(val);
                if was_on && !self.lcdc.lcd_enable() {
                    // LCD turned off: reset to mode 0
                    self.ly = 0;
                    self.clock = 0;
                    self.stat.set_mode(0);
                }
                if !was_on && self.lcdc.lcd_enable() {
                    // LCD turned on: start from mode 2
                    self.stat.set_mode(2);
                    self.clock = 0;
                }
            }
            0xFF41 => {
                // Only bits 3-6 are writable
                self.stat.0 = (self.stat.0 & 0x87) | (val & 0x78);
            }
            0xFF42 => self.scy = val,
            0xFF43 => self.scx = val,
            0xFF44 => {} // LY is read-only
            0xFF45 => self.lyc = val,
            0xFF47 => self.bgp = Palette(val),
            0xFF48 => self.obp0 = Palette(val),
            0xFF49 => self.obp1 = Palette(val),
            0xFF4A => self.wy = val,
            0xFF4B => self.wx = val,
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Screen tests ---

    #[test]
    fn screen_new_is_white() {
        let screen = Screen::new();
        for y in 0..144u8 {
            for x in 0..160u8 {
                assert_eq!(screen.get(x, y), Colour::White);
            }
        }
    }

    #[test]
    fn screen_set_get() {
        let mut screen = Screen::new();
        screen.set(10, 20, Colour::Black);
        assert_eq!(screen.get(10, 20), Colour::Black);
        assert_eq!(screen.get(11, 20), Colour::White);
    }

    #[test]
    fn screen_out_of_bounds() {
        let screen = Screen::new();
        // Out of bounds returns Black
        assert_eq!(screen.get(160, 0), Colour::Black);
        assert_eq!(screen.get(0, 144), Colour::Black);
    }

    #[test]
    fn screen_to_rgba8_size() {
        let screen = Screen::new();
        let rgba = screen.to_rgba8();
        assert_eq!(rgba.len(), 160 * 144 * 4);
    }

    #[test]
    fn screen_to_rgba8_white_pixel() {
        let screen = Screen::new();
        let rgba = screen.to_rgba8();
        // First pixel is White → [155, 188, 15, 255]
        assert_eq!(rgba[0], 155);
        assert_eq!(rgba[1], 188);
        assert_eq!(rgba[2], 15);
        assert_eq!(rgba[3], 255);
    }

    // --- PPU mode transition tests ---

    #[test]
    fn initial_state() {
        let ppu = Ppu::new();
        assert_eq!(ppu.stat.mode(), 2); // starts in OAM Search
        assert_eq!(ppu.ly, 0);
        assert_eq!(ppu.clock, 0);
        assert!(ppu.lcdc.lcd_enable());
    }

    #[test]
    fn mode_2_to_3() {
        let mut ppu = Ppu::new();
        assert_eq!(ppu.stat.mode(), 2);

        // 80 dots = 20 M-cycles → transition to mode 3
        ppu.update(20);
        assert_eq!(ppu.stat.mode(), 3);
    }

    #[test]
    fn mode_3_to_0() {
        let mut ppu = Ppu::new();
        ppu.update(20); // mode 2 → 3
        assert_eq!(ppu.stat.mode(), 3);

        // 172 dots = 43 M-cycles → transition to mode 0
        ppu.update(43);
        assert_eq!(ppu.stat.mode(), 0);
    }

    #[test]
    fn mode_0_to_2_next_line() {
        let mut ppu = Ppu::new();
        ppu.update(20); // → mode 3
        ppu.update(43); // → mode 0
        assert_eq!(ppu.ly, 0);

        // 204 dots = 51 M-cycles → mode 2, LY=1
        ppu.update(51);
        assert_eq!(ppu.stat.mode(), 2);
        assert_eq!(ppu.ly, 1);
    }

    /// Helper: advance PPU one full scanline (456 dots = 114 M-cycles).
    fn advance_scanline(ppu: &mut Ppu) -> (PpuEvent, PpuInterrupts) {
        // Feed 1 M-cycle at a time to properly trigger transitions
        let mut last_event = PpuEvent::None;
        let mut combined_interrupts = PpuInterrupts::default();
        for _ in 0..114 {
            let (ev, int) = ppu.update(1);
            if ev != PpuEvent::None {
                last_event = ev;
            }
            combined_interrupts.vblank |= int.vblank;
            combined_interrupts.stat |= int.stat;
        }
        (last_event, combined_interrupts)
    }

    #[test]
    fn full_scanline_cycle() {
        let mut ppu = Ppu::new();
        // One full scanline: 456 dots
        advance_scanline(&mut ppu);
        assert_eq!(ppu.ly, 1);
        assert_eq!(ppu.stat.mode(), 2); // back to OAM search for next line
    }

    #[test]
    fn vblank_at_ly_144() {
        let mut ppu = Ppu::new();

        // Run through 143 scanlines (LY 0 through 142)
        for _ in 0..143 {
            advance_scanline(&mut ppu);
        }
        assert_eq!(ppu.ly, 143);
        assert_eq!(ppu.stat.mode(), 2);

        // Scanline 143: should trigger VBlank at the end
        let (event, interrupts) = advance_scanline(&mut ppu);
        assert_eq!(ppu.ly, 144);
        assert_eq!(ppu.stat.mode(), 1); // VBlank mode
        assert_eq!(event, PpuEvent::FrameComplete);
        assert!(interrupts.vblank);
    }

    #[test]
    fn vblank_duration_10_lines() {
        let mut ppu = Ppu::new();

        // Run to VBlank
        for _ in 0..144 {
            advance_scanline(&mut ppu);
        }
        assert_eq!(ppu.stat.mode(), 1);
        assert_eq!(ppu.ly, 144);

        // VBlank lasts 10 lines (LY 144-153)
        for expected_ly in 145..=153 {
            advance_scanline(&mut ppu);
            assert_eq!(ppu.ly, expected_ly);
            assert_eq!(ppu.stat.mode(), 1, "should stay in VBlank at LY={expected_ly}");
        }

        // After LY 153, LY wraps to 0 and mode goes back to 2
        advance_scanline(&mut ppu);
        assert_eq!(ppu.ly, 0);
        assert_eq!(ppu.stat.mode(), 2);
    }

    #[test]
    fn full_frame_154_scanlines() {
        let mut ppu = Ppu::new();
        let mut frame_complete_count = 0;

        // 154 scanlines = one full frame
        for _ in 0..154 {
            let (event, _) = advance_scanline(&mut ppu);
            if event == PpuEvent::FrameComplete {
                frame_complete_count += 1;
            }
        }

        assert_eq!(frame_complete_count, 1);
        assert_eq!(ppu.ly, 0);
        assert_eq!(ppu.stat.mode(), 2);
    }

    #[test]
    fn two_full_frames() {
        let mut ppu = Ppu::new();
        let mut frame_count = 0;

        for _ in 0..308 {
            let (event, _) = advance_scanline(&mut ppu);
            if event == PpuEvent::FrameComplete {
                frame_count += 1;
            }
        }

        assert_eq!(frame_count, 2);
        assert_eq!(ppu.ly, 0);
    }

    // --- LYC / STAT interrupt tests ---

    #[test]
    fn lyc_match_flag() {
        let mut ppu = Ppu::new();
        ppu.lyc = 1;

        // At LY=0, LYC != LY
        assert!(!ppu.stat.lyc_eq_ly());

        // Advance to LY=1
        advance_scanline(&mut ppu);
        assert_eq!(ppu.ly, 1);
        assert!(ppu.stat.lyc_eq_ly());
    }

    #[test]
    fn lyc_stat_interrupt() {
        let mut ppu = Ppu::new();
        ppu.lyc = 1;
        // Enable LYC interrupt (bit 6 of STAT)
        ppu.stat.0 |= 0x40;

        // Advance to LY=1
        let (_, interrupts) = advance_scanline(&mut ppu);
        assert!(interrupts.stat, "STAT interrupt should fire on LYC match");
    }

    #[test]
    fn hblank_stat_interrupt() {
        let mut ppu = Ppu::new();
        // Enable HBlank STAT interrupt (bit 3)
        ppu.stat.0 |= 0x08;

        // Run through mode 2 (80 dots) and mode 3 (172 dots) to reach HBlank
        ppu.update(20); // → mode 3
        let (_, interrupts) = ppu.update(43); // → mode 0 (HBlank)
        assert!(interrupts.stat, "STAT interrupt should fire on HBlank");
    }

    #[test]
    fn oam_stat_interrupt() {
        let mut ppu = Ppu::new();
        // Enable OAM STAT interrupt (bit 5)
        ppu.stat.0 |= 0x20;

        // Complete one scanline to transition back to mode 2
        let (_, interrupts) = advance_scanline(&mut ppu);
        assert!(interrupts.stat, "STAT interrupt should fire on OAM search");
    }

    #[test]
    fn vblank_stat_interrupt() {
        let mut ppu = Ppu::new();
        // Enable VBlank STAT interrupt (bit 4)
        ppu.stat.0 |= 0x10;

        // Run to VBlank
        for _ in 0..143 {
            advance_scanline(&mut ppu);
        }
        let (_, interrupts) = advance_scanline(&mut ppu);
        assert!(interrupts.stat, "STAT interrupt should fire on VBlank");
        assert!(interrupts.vblank, "VBlank interrupt should also fire");
    }

    // --- Register I/O tests ---

    #[test]
    fn register_read_write_roundtrip() {
        let mut ppu = Ppu::new();

        ppu.write_register(0xFF42, 42); // SCY
        assert_eq!(ppu.read_register(0xFF42), 42);

        ppu.write_register(0xFF43, 100); // SCX
        assert_eq!(ppu.read_register(0xFF43), 100);

        ppu.write_register(0xFF47, 0xE4); // BGP
        assert_eq!(ppu.read_register(0xFF47), 0xE4);

        ppu.write_register(0xFF48, 0xD2); // OBP0
        assert_eq!(ppu.read_register(0xFF48), 0xD2);

        ppu.write_register(0xFF49, 0x3C); // OBP1
        assert_eq!(ppu.read_register(0xFF49), 0x3C);

        ppu.write_register(0xFF4A, 80); // WY
        assert_eq!(ppu.read_register(0xFF4A), 80);

        ppu.write_register(0xFF4B, 7); // WX
        assert_eq!(ppu.read_register(0xFF4B), 7);
    }

    #[test]
    fn ly_is_read_only() {
        let mut ppu = Ppu::new();
        advance_scanline(&mut ppu);
        assert_eq!(ppu.ly, 1);

        // Writing to LY should be ignored
        ppu.write_register(0xFF44, 0);
        assert_eq!(ppu.ly, 1);
        assert_eq!(ppu.read_register(0xFF44), 1);
    }

    #[test]
    fn stat_bit7_always_set() {
        let ppu = Ppu::new();
        assert_eq!(ppu.read_register(0xFF41) & 0x80, 0x80);
    }

    #[test]
    fn stat_writable_bits() {
        let mut ppu = Ppu::new();
        // Write 0xFF to STAT — only bits 3-6 should change
        ppu.write_register(0xFF41, 0xFF);
        let stat = ppu.read_register(0xFF41);
        // Bits 0-2: mode and LYC flag (read-only) — mode is 2, LYC flag depends
        assert_eq!(stat & 0x78, 0x78); // bits 3-6 all set
        assert_eq!(stat & 0x80, 0x80); // bit 7 always 1
    }

    #[test]
    fn lcd_off_resets_ly() {
        let mut ppu = Ppu::new();
        advance_scanline(&mut ppu);
        assert_eq!(ppu.ly, 1);

        // Turn LCD off
        ppu.write_register(0xFF40, 0x00);
        assert_eq!(ppu.ly, 0);
        assert_eq!(ppu.stat.mode(), 0);
    }

    #[test]
    fn lcd_on_starts_mode2() {
        let mut ppu = Ppu::new();
        // Turn LCD off first
        ppu.write_register(0xFF40, 0x00);
        assert_eq!(ppu.stat.mode(), 0);

        // Turn LCD on
        ppu.write_register(0xFF40, 0x91);
        assert_eq!(ppu.stat.mode(), 2);
    }

    #[test]
    fn lcd_off_no_updates() {
        let mut ppu = Ppu::new();
        ppu.write_register(0xFF40, 0x00); // LCD off

        let (event, interrupts) = ppu.update(114);
        assert_eq!(event, PpuEvent::None);
        assert!(!interrupts.vblank);
        assert!(!interrupts.stat);
        assert_eq!(ppu.ly, 0);
    }

    // --- Framebuffer tests ---

    #[test]
    fn framebuffer_rgba8_size() {
        let ppu = Ppu::new();
        let fb = ppu.framebuffer_rgba8();
        assert_eq!(fb.len(), 160 * 144 * 4);
    }

    // --- Window line counter tests ---

    #[test]
    fn window_line_resets_each_frame() {
        let mut ppu = Ppu::new();
        ppu.wy = 0;
        ppu.wx = 7;
        ppu.lcdc = Lcdc(0xB1); // LCD on, window on, BG on

        // Run one full frame
        for _ in 0..154 {
            advance_scanline(&mut ppu);
        }

        // window_line should have been reset
        assert_eq!(ppu.window_line, 0);
    }
}
