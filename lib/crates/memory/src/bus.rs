/// All CPU memory access goes through this trait.
/// Implementations can intercept, record, or redirect operations.
/// `&mut self` on both methods enables future TracingBus without RefCell.
pub trait Bus {
    fn read(&mut self, addr: u16) -> u8;
    fn write(&mut self, addr: u16, value: u8);
}
