use anyhow::{anyhow, Result};

use crate::asm;

#[derive(Debug, Default)]
pub struct Cpu {
    registers: [u64; 32],
}

impl Cpu {
    pub fn execute(&mut self, inst: &asm::Instruction) -> Result<()> {
        match inst {
            asm::Instruction::IType(itype) => self.execute_itype(itype),
            asm::Instruction::UType(_utype) => Ok(()),
        }
    }

    fn execute_itype(&mut self, itype: &asm::IType) -> Result<()> {
        let inst = match asm::ITypeInst::try_from(itype) {
            Ok(inst) => inst,
            Err(err) => return Err(err),
        };

        match inst {
            asm::ITypeInst::ADDI => self.execute_addi(itype),
            asm::ITypeInst::EBREAK => {
                return Err(anyhow!("CPU cannot execute I-Type instruction {}", inst))
            }
            asm::ITypeInst::ECALL => {
                // TODO
            }
        }

        Ok(())
    }

    fn execute_addi(&mut self, itype: &asm::IType) {
        let rs1: u32 = itype.rs1().into();
        let rs1 = self.registers[rs1 as usize];

        let rd: u32 = itype.rd().into();
        self.registers[rd as usize] = rs1 + itype.immediate() as u64
    }
}

#[test]
fn test_cpu_execute_addi() {
    let inst = asm::Instruction::try_from(0x00100513).unwrap();

    let mut cpu = Cpu::default();
    cpu.execute(&inst).unwrap();

    dbg!(cpu);
}
