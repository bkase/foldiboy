/// Game Boy button.
#[derive(Clone, Copy, Debug)]
pub enum Button {
    Right,
    Left,
    Up,
    Down,
    A,
    B,
    Select,
    Start,
}

/// Joypad register (0xFF00).
pub struct Joypad {
    /// Select bits (bits 4-5 of 0xFF00, active low)
    select: u8,
    /// Direction button states (active low): Down, Up, Left, Right
    directions: u8,
    /// Action button states (active low): Start, Select, B, A
    buttons: u8,
}

impl Joypad {
    pub fn new() -> Self {
        Joypad {
            select: 0x30,
            directions: 0x0F,
            buttons: 0x0F,
        }
    }

    pub fn read(&self) -> u8 {
        let mut lower = 0x0F;
        if self.select & 0x10 == 0 {
            // Direction keys selected
            lower &= self.directions;
        }
        if self.select & 0x20 == 0 {
            // Button keys selected
            lower &= self.buttons;
        }
        (self.select | 0xC0) | lower
    }

    pub fn write(&mut self, val: u8) {
        self.select = val & 0x30;
    }

    /// Set button state. `pressed = true` means the button is held down.
    pub fn set_button(&mut self, button: Button, pressed: bool) {
        let (reg, bit) = match button {
            Button::Right  => (&mut self.directions, 0),
            Button::Left   => (&mut self.directions, 1),
            Button::Up     => (&mut self.directions, 2),
            Button::Down   => (&mut self.directions, 3),
            Button::A      => (&mut self.buttons, 0),
            Button::B      => (&mut self.buttons, 1),
            Button::Select => (&mut self.buttons, 2),
            Button::Start  => (&mut self.buttons, 3),
        };
        if pressed {
            *reg &= !(1 << bit); // Active low: 0 = pressed
        } else {
            *reg |= 1 << bit; // Active low: 1 = released
        }
    }
}
