use byteorder::{ByteOrder, LittleEndian};

#[derive(Debug)]
pub struct Bus {
    memory: Vec<u8>,
}

pub const MEMORY_SIZE: usize = 128 * 1024;

impl Default for Bus {
    fn default() -> Self {
        Self::new(MEMORY_SIZE)
    }
}

impl Bus {
    pub fn new(memory_bytes: usize) -> Self {
        Self {
            memory: vec![0; memory_bytes],
        }
    }

    pub fn read_at(&self, addr: usize, len: usize) -> &[u8] {
        &self.memory[addr..addr + len]
    }

    pub fn copy_from_exact(&mut self, addr: usize, len: usize, src: &[u8]) -> (usize, usize) {
        self.memory[addr..addr + len].copy_from_slice(src);
        (addr, addr + len)
    }

    pub fn store_u32(&mut self, addr: usize, value: u32) {
        LittleEndian::write_u32(&mut self.memory[addr..addr + 4], value);
    }

    pub fn store_u64(&mut self, addr: usize, value: u64) {
        LittleEndian::write_u64(&mut self.memory[addr..addr + 8], value);
    }

    pub fn load_i8(&self, addr: usize) -> i8 {
        self.memory[addr] as i8
    }

    pub fn load_i32(&self, addr: usize) -> i32 {
        LittleEndian::read_i32(&self.memory[addr..addr + 4])
    }

    pub fn load_u32(&self, addr: usize) -> u32 {
        LittleEndian::read_u32(&self.memory[addr..addr + 4])
    }
}
