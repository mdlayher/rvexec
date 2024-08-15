use crate::asm::{self, Instruction, Register};
use crate::bus::Bus;
use std::os::fd::BorrowedFd;
use thiserror::Error;

#[derive(Debug, Default)]
pub struct Cpu {
    registers: [u64; 32],
    pc: usize,
    pc_end: usize,
    // TODO(mdlayher): borrow bus instead?
    bus: Bus,
}

#[derive(Debug, Default, PartialEq)]
pub struct TermState {
    registers: [u64; 32],
}

#[derive(Default)]
struct ExecuteState {
    pc_next: Option<usize>,
}

impl Cpu {
    pub fn new(bus: Bus, pc: (usize, usize)) -> Self {
        // TODO(mdlayher): stack pointer.
        let mut cpu = Self {
            registers: [0; 32],
            pc: pc.0,
            pc_end: pc.1,
            bus,
        };

        // Initial stack pointer.
        cpu.write_register(Register::SP, 0x7ff0);

        cpu
    }

    pub fn fetch(&mut self) -> Result<Instruction> {
        // All instructions are 4 bytes.
        //
        // TODO(mdlayher): compressed instructions.
        let word = self.bus.load_u32(self.pc);
        let ret = Instruction::try_from(word).map_err(Error::UnknownInstruction);

        // Debugging.
        if ret.is_ok() {
            println!(
                "fetch: {:#010x}-{:#010x}, word: {:#010x}, asm: {}",
                self.pc,
                self.pc + 4,
                word,
                Instruction::try_from(word).unwrap(),
            );
        } else {
            println!(
                "fetch: {:#010x}-{:#010x}, word: {:#010x}, asm: TODO",
                self.pc,
                self.pc + 4,
                word,
            );
        }

        ret
    }

    pub fn execute(&mut self, inst: &Instruction) -> Result<()> {
        let state = match inst {
            Instruction::B(btype) => self.execute_btype(btype),
            Instruction::I(itype) => self.execute_itype(itype),
            Instruction::J(jtype) => self.execute_jtype(jtype),
            Instruction::R(rtype) => self.execute_rtype(rtype),
            Instruction::S(stype) => self.execute_stype(stype),
            Instruction::U(utype) => self.execute_utype(utype),
        }?;

        // Increment PC _after_ processing to make sure instructions that use
        // the PC work properly.
        match state.pc_next {
            // Jump instruction modified PC.
            Some(pc) => self.pc = pc,
            // No jump, move to the next word.
            None => self.pc += 4,
        };

        if self.pc >= self.pc_end {
            // Program has executed the last instruction.
            return Err(Error::Eof);
        }

        Ok(())
    }

    #[cfg(test)]
    fn terminate(self) -> TermState {
        // Terminate and consume the CPU, returning the final execution state.
        TermState {
            registers: self.registers,
        }
    }

    fn execute_btype(&self, btype: &asm::BType) -> Result<ExecuteState> {
        let inst = match asm::BTypeInst::try_from(btype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        let state = match inst {
            asm::BTypeInst::BEQ => self.execute_beq(btype),
        };

        Ok(state)
    }

    fn execute_beq(&self, btype: &asm::BType) -> ExecuteState {
        // if (rs1 == rs2) pc += imm
        let rs1 = self.read_register(btype.rs1());
        let rs2 = self.read_register(btype.rs2());

        let pc_next = if rs1 == rs2 {
            Some(self.pc + btype.immediate() as usize)
        } else {
            None
        };

        ExecuteState { pc_next }
    }

    fn execute_itype(&mut self, itype: &asm::IType) -> Result<ExecuteState> {
        let inst = match asm::ITypeInst::try_from(itype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        let state = match inst {
            asm::ITypeInst::ADDI => self.execute_addi(itype),
            asm::ITypeInst::EBREAK => return Err(Error::UnimplementedInstruction("ebreak")),
            asm::ITypeInst::ECALL => {
                // System call results are passed in registers a0/a1 by
                // convention.
                let (ret0, ret1) = self.execute_ecall()?;
                self.write_register(Register::A0, ret0);
                self.write_register(Register::A1, ret1);

                ExecuteState::default()
            }
            asm::ITypeInst::JALR => self.execute_jalr(itype),
            asm::ITypeInst::LB => self.execute_lb(itype),
            asm::ITypeInst::LW => self.execute_lw(itype),
        };

        Ok(state)
    }

    fn execute_jtype(&mut self, jtype: &asm::JType) -> Result<ExecuteState> {
        let inst = match asm::JTypeInst::try_from(jtype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        let state = match inst {
            asm::JTypeInst::JAL => self.execute_jal(jtype),
        };

        Ok(state)
    }

    fn execute_rtype(&mut self, rtype: &asm::RType) -> Result<ExecuteState> {
        let inst = match asm::RTypeInst::try_from(rtype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        match inst {
            // TODO(mdlayher): I'm sure addw is wrong.
            asm::RTypeInst::ADD | asm::RTypeInst::ADDW | asm::RTypeInst::SUB => {
                self.execute_rtype_arithmetic(inst, rtype)
            }
        }

        Ok(ExecuteState::default())
    }

    fn execute_rtype_arithmetic(&mut self, inst: asm::RTypeInst, rtype: &asm::RType) {
        // rd = rs1 (op) rs2
        let rs1 = self.read_register(rtype.rs1());
        let rs2 = self.read_register(rtype.rs2());

        let res = match inst {
            asm::RTypeInst::ADD | asm::RTypeInst::ADDW => rs1 + rs2,
            asm::RTypeInst::SUB => rs1 - rs2,
        };

        self.write_register(rtype.rd(), res)
    }

    fn execute_stype(&mut self, stype: &asm::SType) -> Result<ExecuteState> {
        let inst = match asm::STypeInst::try_from(stype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        match inst {
            asm::STypeInst::SD => self.execute_sd(stype),
            asm::STypeInst::SW => self.execute_sw(stype),
        }

        Ok(ExecuteState::default())
    }

    fn execute_utype(&mut self, utype: &asm::UType) -> Result<ExecuteState> {
        let inst = match asm::UTypeInst::try_from(utype) {
            Ok(inst) => inst,
            Err(err) => return Err(Error::UnknownInstruction(err)),
        };

        match inst {
            asm::UTypeInst::AUIPC => self.execute_auipc(utype),
        }

        Ok(ExecuteState::default())
    }

    fn execute_addi(&mut self, itype: &asm::IType) -> ExecuteState {
        // rd = rs1 + imm
        let rs1 = self.read_register(itype.rs1()) as i64;
        let add = rs1 + itype.immediate() as i64;
        self.write_register(itype.rd(), add as u64);

        ExecuteState::default()
    }

    fn execute_auipc(&mut self, utype: &asm::UType) {
        // rd = pc + (imm << 12)
        self.write_register(
            utype.rd(),
            (self.pc as u64) + ((utype.immediate() << 12) as u64),
        )
    }

    fn execute_ecall(&self) -> Result<(u64, u64)> {
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

                match nix::unistd::write(fd, self.bus.read_at(addr, len)) {
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

    fn execute_jal(&mut self, jtype: &asm::JType) -> ExecuteState {
        // rd = pc + 4; pc += imm
        self.write_register(jtype.rd(), self.pc as u64 + 4);

        let pc_next = self.pc as i64 + jtype.immediate() as i64;

        ExecuteState {
            pc_next: Some(pc_next as usize),
        }
    }

    fn execute_jalr(&mut self, itype: &asm::IType) -> ExecuteState {
        // rd = pc + 4; pc = rs1 + imm
        self.write_register(itype.rd(), self.pc as u64 + 4);

        let rs1 = self.read_register(itype.rs1()) as usize;

        ExecuteState {
            pc_next: Some(rs1 + itype.immediate() as usize),
        }
    }

    fn execute_lb(&mut self, itype: &asm::IType) -> ExecuteState {
        // rd = M[rs1+imm][0:7]
        let rs1 = self.read_register(itype.rs1()) as i64;
        let value = self.bus.load_i8((rs1 + itype.immediate() as i64) as usize);
        self.write_register(itype.rd(), value as u64);

        ExecuteState::default()
    }

    fn execute_lw(&mut self, itype: &asm::IType) -> ExecuteState {
        // rd = M[rs1+imm][0:15]
        let rs1 = self.read_register(itype.rs1()) as i64;
        let value = self.bus.load_i32((rs1 + itype.immediate() as i64) as usize);
        self.write_register(itype.rd(), value as u64);

        ExecuteState::default()
    }

    fn execute_sd(&mut self, stype: &asm::SType) {
        // XXX(mdlayher): verify correctness.

        // M[rs1+imm] = rs2
        let rs1 = self.read_register(stype.rs1()) as i64;
        let imm = stype.immediate() as i64;
        let rs2 = self.read_register(stype.rs2());

        self.bus.store_u64((rs1 + imm) as usize, rs2)
    }

    fn execute_sw(&mut self, stype: &asm::SType) {
        // XXX(mdlayher): verify correctness.

        // M[rs1+imm][0:31] = rs2[0:31]
        let rs1 = self.read_register(stype.rs1()) as i64;
        let imm = stype.immediate() as i64;
        let rs2 = self.read_register(stype.rs2()) as u32;

        self.bus.store_u32((rs1 + imm) as usize, rs2)
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
    #[error("eof")]
    Eof,
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
    let mut cpu = Cpu {
        pc_end: 0xff,
        ..Default::default()
    };

    let words = [0x00100513, 0x00250613];
    for word in words {
        let inst = Instruction::try_from(word).expect("parse instruction");
        cpu.execute(&inst).expect("execute instruction");
    }

    let mut want = TermState::default();
    want.registers[Register::A0 as usize] = 0x01;
    want.registers[Register::A2 as usize] = 0x03;

    assert_eq!(want, cpu.terminate());
}

#[test]
fn test_cpu_execute_ecall_exit() {
    let mut cpu = Cpu {
        pc_end: 0xff,
        ..Default::default()
    };

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
