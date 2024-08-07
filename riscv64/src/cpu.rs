use crate::asm::{self, Instruction, Register};
use anyhow::anyhow;
use byteorder::ByteOrder;
use std::os::fd::BorrowedFd;
use thiserror::Error;

// TODO(mdlayher): make configurable when splitting out memory.
const MEMORY_SIZE: usize = 128 * 1024;
const BASE_ADDR: usize = 0x0;

#[derive(Debug, Default)]
pub struct Cpu {
    registers: [u64; 32],
    pc: usize,
    memory: Vec<u8>,
}

impl Cpu {
    pub fn new(elf_bytes: &[u8]) -> Result<Self> {
        let mut cpu = Self {
            registers: [0; 32],
            pc: 0,
            memory: vec![0; MEMORY_SIZE],
        };

        cpu.load_elf(elf_bytes)?;

        // TODO(mdlayher): stack pointer.

        Ok(cpu)
    }

    fn load_elf(&mut self, buf: &[u8]) -> Result<()> {
        // The CPU assumes ELF riscv64/little-endian/executable.
        let elf_bytes = elf::ElfBytes::<elf::endian::LittleEndian>::minimal_parse(buf)
            .map_err(|err| Error::InvalidBinary(anyhow!("failed to read ELF binary: {err}")))?;

        let program_headers = elf_bytes.segments().ok_or(Error::InvalidBinary(anyhow!(
            "found no ELF program headers"
        )))?;

        for ph in program_headers
            .iter()
            .filter(|ph| ph.p_type == elf::abi::PT_LOAD)
        {
            // For each loadable segment, calculate the appropriate offsets and
            // load the program code and data into memory.
            let start = BASE_ADDR + ph.p_vaddr as usize;
            let end = start + ph.p_memsz as usize;

            let offset = ph.p_offset as usize;

            self.memory[start..end].copy_from_slice(&buf[offset..offset + ph.p_filesz as usize]);
        }

        // Start PC at the entrypoint.
        self.pc = BASE_ADDR + elf_bytes.ehdr.e_entry as usize;

        Ok(())
    }

    pub fn fetch(&mut self) -> Result<Instruction> {
        // All instructions are 4 bytes.
        //
        // TODO(mdlayher): compressed instructions.
        let word = byteorder::LE::read_u32(&self.memory[self.pc..self.pc + 4]);
        let ret = Instruction::try_from(word).map_err(Error::UnknownInstruction);

        if ret.is_ok() {
            // Debugging.
            println!(
                "fetch: {:#010x}-{:#010x}, word: {:#010x}, asm: {}",
                self.pc,
                self.pc + 4,
                word,
                Instruction::try_from(word).unwrap(),
            );
        }

        ret
    }

    pub fn execute(&mut self, inst: &Instruction) -> Result<()> {
        let res = match inst {
            Instruction::IType(itype) => self.execute_itype(itype),
            Instruction::RType(rtype) => self.execute_rtype(rtype),
            Instruction::SType(stype) => self.execute_stype(stype),
            Instruction::UType(utype) => self.execute_utype(utype),
        };

        // Increment PC _after_ processing to make sure instructions that use
        // the PC work properly.
        self.pc += 4;
        res
    }

    fn execute_itype(&mut self, itype: &asm::IType) -> Result<()> {
        let inst = match asm::ITypeInst::try_from(itype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        match inst {
            asm::ITypeInst::ADDI => self.execute_addi(itype),
            asm::ITypeInst::EBREAK => return Err(Error::UnimplementedInstruction("ebreak")),
            asm::ITypeInst::ECALL => {
                // System call results are passed in registers a0/a1 by
                // convention.
                let (ret0, ret1) = self.execute_ecall()?;
                self.write_register(Register::A0, ret0);
                self.write_register(Register::A1, ret1);
            }
        }

        Ok(())
    }

    fn execute_rtype(&mut self, rtype: &asm::RType) -> Result<()> {
        let _inst = match asm::RTypeInst::try_from(rtype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        panic!("cannot execute R-Type yet: {}", rtype);
    }

    fn execute_stype(&mut self, stype: &asm::SType) -> Result<()> {
        let inst = match asm::STypeInst::try_from(stype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        match inst {
            asm::STypeInst::SD => self.execute_sd(stype),
        }

        Ok(())
    }

    fn execute_utype(&mut self, utype: &asm::UType) -> Result<()> {
        let inst = match asm::UTypeInst::try_from(utype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        match inst {
            asm::UTypeInst::AUIPC => self.execute_auipc(utype),
        }

        Ok(())
    }

    fn execute_addi(&mut self, itype: &asm::IType) {
        // rd = rs1 + imm
        let rs1 = self.read_register(itype.rs1());
        let add = rs1 + itype.immediate() as u64;
        self.write_register(itype.rd(), add)
    }

    fn execute_auipc(&mut self, utype: &asm::UType) {
        // rd = pc + (imm << 12)
        self.write_register(
            utype.rd(),
            (self.pc as u64) + ((utype.immediate() << 12) as u64),
        )
    }

    fn execute_ecall(&mut self) -> Result<(u64, u64)> {
        // syscall(2) on Linux states the following conventions:
        //
        // Arch/ABI    Instruction           System  Ret  Ret  Error
        //                                   call #  val  val2
        // ─────────────────────────────────────────────────────────
        // riscv       ecall                 a7      a0   a1   -
        let syscall = Syscall::try_from(self.read_register(Register::A7))?;

        // TODO(mdlayher): clean up.
        self.debug();

        match syscall {
            Syscall::Write => {
                // Safety: we have to interpret a raw u64 as a file descriptor
                // from the first argument register per convention.
                let fd = unsafe { BorrowedFd::borrow_raw(self.read_register(Register::A0) as i32) };

                // Determine the memory address and length to write.
                let addr = self.read_register(Register::A1) as usize;
                let len = self.read_register(Register::A2) as usize;

                match nix::unistd::write(fd, &self.memory[addr..addr + len]) {
                    Ok(n) => Ok((n as u64, 0)),
                    // XXX(mdlayher): figure out errno return convention.
                    Err(errno) => panic!("write errno: {}", errno),
                }
            }
            Syscall::Exit => {
                // Exit the process and halt the CPU.
                let code = self.read_register(Register::A0);
                Err(Error::Exit(code))
            }
        }
    }

    fn execute_sd(&mut self, stype: &asm::SType) {
        // XXX(mdlayher): verify correctness.

        // M[rs1+imm] = rs2
        let rs1 = self.read_register(stype.rs1()) as usize;
        let imm = stype.immediate() as usize;
        let rs2 = self.read_register(stype.rs2());

        byteorder::LittleEndian::write_u64(&mut self.memory[rs1 + imm..rs1 + imm + 8], rs2);
    }

    fn read_register(&self, reg: asm::Register) -> u64 {
        self.registers[reg as usize]
    }

    fn write_register(&mut self, reg: asm::Register, value: u64) {
        if reg == Register::X0 {
            // Hard-wired to zero.
            return;
        }

        self.registers[reg as usize] = value
    }

    // XXX(mdlayher): turn this into something nicer with log crate.
    fn debug(&self) {
        println!("DEBUG: pc: {:#010x}", self.pc);

        for (i, r) in self.registers.iter().enumerate() {
            if *r == 0 {
                continue;
            }

            let reg = Register::try_from(i as u32).unwrap();
            println!("DEBUG: {}: {:#010x}", reg, *r);
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Syscall {
    Write,
    Exit,
}

impl TryFrom<u64> for Syscall {
    type Error = Error;

    fn try_from(value: u64) -> Result<Self> {
        // Reference: https://jborza.com/post/2021-05-11-riscv-linux-syscalls/
        match value {
            64 => Ok(Self::Write),
            93 => Ok(Self::Exit),
            _ => Err(Error::UnknownSyscall(value)),
        }
    }
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("exit(2)")]
    Exit(u64),
    #[error("unknown syscall number: {0}")]
    UnknownSyscall(u64),
    #[error("invalid riscv64 ELF binary: {0}")]
    InvalidBinary(anyhow::Error),
    #[error("unknown instruction: {0}")]
    UnknownInstruction(anyhow::Error),
    #[error("unimplemented instruction: {0}")]
    UnimplementedInstruction(&'static str),
}

#[test]
fn test_cpu_execute_addi() {
    let inst = Instruction::try_from(0x00100513).unwrap();

    let mut cpu = Cpu::default();
    cpu.execute(&inst).unwrap();
}

#[test]
fn test_cpu_execute_ecall_exit() {
    let mut cpu = Cpu::default();
    let mut exited = false;

    let words = [0x00100513, 0x05d00893, 0x00000073];
    for word in words {
        let inst = Instruction::try_from(word).unwrap();

        if let Err(err) = cpu.execute(&inst) {
            match err {
                Error::Exit(code) => {
                    assert_eq!(1, code, "incorrect exit code");
                    exited = true;
                }
                _ => panic!("failed to execute: {}", err),
            };
        }
    }

    if !exited {
        panic!("CPU did not call exit(2)");
    }
}
