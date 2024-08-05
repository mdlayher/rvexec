use anyhow::{anyhow, Result};
use std::fmt;

// TODO(mdlayher): swap in ABI name registers.

enum Register {
    X0,
    X1,
    X2,
    X3,
    X4,
    X5,
    X6,
    X7,
    X8,
    X9,
    X10,
    X11,
    X12,
    X13,
    X14,
    X15,
    X16,
    X17,
    X18,
    X19,
    X20,
    X21,
    X22,
    X23,
    X24,
    X25,
    X26,
    X27,
    X28,
    X29,
    X30,
    X31,
}

impl From<u32> for Register {
    fn from(value: u32) -> Self {
        match value {
            0x00 => Self::X0,
            0x01 => Self::X1,
            0x02 => Self::X2,
            0x03 => Self::X3,
            0x04 => Self::X4,
            0x05 => Self::X5,
            0x06 => Self::X6,
            0x07 => Self::X7,
            0x08 => Self::X8,
            0x09 => Self::X9,
            0x0a => Self::X10,
            0x0b => Self::X11,
            0x0c => Self::X12,
            0x0d => Self::X13,
            0x0e => Self::X14,
            0x0f => Self::X15,
            0x10 => Self::X16,
            0x11 => Self::X17,
            0x12 => Self::X18,
            0x13 => Self::X19,
            0x14 => Self::X20,
            0x15 => Self::X21,
            0x16 => Self::X22,
            0x17 => Self::X23,
            0x18 => Self::X24,
            0x19 => Self::X25,
            0x20 => Self::X26,
            0x21 => Self::X27,
            0x22 => Self::X28,
            0x23 => Self::X29,
            0x24 => Self::X30,
            0x25 => Self::X31,
            _ => Self::X0,
        }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let reg = match self {
            Self::X0 => "x0",
            Self::X1 => "x1",
            Self::X2 => "x2",
            Self::X3 => "x3",
            Self::X4 => "x4",
            Self::X5 => "x5",
            Self::X6 => "x6",
            Self::X7 => "x7",
            Self::X8 => "x8",
            Self::X9 => "x9",
            Self::X10 => "x10",
            Self::X11 => "x11",
            Self::X12 => "x12",
            Self::X13 => "x13",
            Self::X14 => "x14",
            Self::X15 => "x15",
            Self::X16 => "x16",
            Self::X17 => "x17",
            Self::X18 => "x18",
            Self::X19 => "x19",
            Self::X20 => "x20",
            Self::X21 => "x21",
            Self::X22 => "x22",
            Self::X23 => "x23",
            Self::X24 => "x24",
            Self::X25 => "x25",
            Self::X26 => "x26",
            Self::X27 => "x27",
            Self::X28 => "x28",
            Self::X29 => "x29",
            Self::X30 => "x30",
            Self::X31 => "x31",
        };

        write!(f, "{}", reg)
    }
}

#[derive(Debug)]
pub enum Instruction {
    System(System),
    IType(IType),
    UType(UType),
}

impl TryFrom<u32> for Instruction {
    type Error = anyhow::Error;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        // Mask off to find the opcode and then pass the raw value for each type
        // to interpret the entire value as an instruction of a given format.
        //
        // Reference:
        // https://github.com/jameslzhu/riscv-card/blob/master/riscv-card.pdf
        let masked = value & 0x7f;
        match masked {
            0b0010011 => Ok(Self::IType(IType(value))),
            0b0011011 | 0b00010111 => Ok(Self::UType(UType(value))),
            0b1110011 => Ok(Self::System(System(value))),
            _ => Err(anyhow!("no matching opcode: {:#02x}", masked)),
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::System(system) => {
                let inst = match Inst::try_from(system) {
                    Ok(inst) => inst.to_string(),
                    Err(_) => "system(???)".to_string(),
                };

                write!(f, "{}", inst)
            }
            Self::IType(itype) => {
                let inst = match Inst::try_from(itype) {
                    Ok(inst) => inst.to_string(),
                    Err(_) => "itype(???)".to_string(),
                };

                write!(
                    f,
                    "{} {}, {}, {}",
                    inst,
                    itype.rd(),
                    itype.rs1(),
                    itype.immediate(),
                )
            }
            Self::UType(utype) => {
                let inst = match Inst::try_from(utype) {
                    Ok(inst) => inst.to_string(),
                    Err(_) => "utype(???)".to_string(),
                };

                write!(f, "{} {}, {}", inst, utype.rd(), utype.immediate(),)
            }
        }
    }
}

#[derive(Debug)]
pub struct System(u32);

impl System {
    fn immediate(&self) -> u32 {
        self.0 >> 20
    }
}

impl TryFrom<&System> for Inst {
    type Error = anyhow::Error;

    fn try_from(value: &System) -> Result<Self, Self::Error> {
        match value.immediate() {
            0x0 => Ok(Inst::ECALL),
            0x1 => Ok(Inst::EBREAK),
            _ => Err(anyhow!(
                "unhandled system immediate: {:#02x}",
                value.immediate(),
            )),
        }
    }
}

#[derive(Debug)]
pub struct IType(u32);

impl IType {
    fn funct3(&self) -> u8 {
        ((self.0 >> 12) & 0x07) as u8
    }

    fn rs1(&self) -> Register {
        Register::from(self.0 >> 15 & 0x1f)
    }

    fn rd(&self) -> Register {
        Register::from(self.0 >> 7 & 0x1f)
    }

    fn immediate(&self) -> u32 {
        self.0 >> 20
    }
}

impl TryFrom<&IType> for Inst {
    type Error = anyhow::Error;

    fn try_from(value: &IType) -> Result<Self, Self::Error> {
        match value.funct3() {
            0x0 => Ok(Inst::ADDI),
            _ => Err(anyhow!("unhandled I-Type funct3: {:#02x}", value.funct3())),
        }
    }
}

#[derive(Debug)]

pub struct UType(u32);

impl UType {
    fn rd(&self) -> Register {
        Register::from(self.0 >> 7 & 0x1f)
    }

    fn immediate(&self) -> u32 {
        self.0 >> 20
    }
}

impl TryFrom<&UType> for Inst {
    type Error = anyhow::Error;

    fn try_from(value: &UType) -> Result<Self, Self::Error> {
        match value.0 & 0x7f {
            0b00010111 => Ok(Inst::AUIPC),
            _ => Err(anyhow!("unhandled U-Type opcode: {:#02x}", value.0 & 0x7f)),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
enum Inst {
    ADDI,
    AUIPC,
    ECALL,
    EBREAK,
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::ADDI => "addi",
            Self::AUIPC => "auipc",
            Self::EBREAK => "ebreak",
            Self::ECALL => "ecall",
        };

        write!(f, "{}", op)
    }
}

#[test]
fn test_instruction_illegal() {
    let err = Instruction::try_from(0x00000000).unwrap_err();
    assert_eq!("no matching opcode: 0x0", err.to_string());
}

#[test]
fn test_instruction_addi() {
    let inst = Instruction::try_from(0x00100513).unwrap();
    assert_eq!("addi x10, x0, 1", inst.to_string());
}

#[test]
fn test_instruction_auipc() {
    let inst = Instruction::try_from(0x00001597).unwrap();
    assert_eq!("auipc x11, 0", inst.to_string());
}

#[test]
fn test_instruction_ebreak() {
    let inst = Instruction::try_from(0x00100073).unwrap();
    assert_eq!("ebreak", inst.to_string());
}

#[test]
fn test_instruction_ecall() {
    let inst = Instruction::try_from(0x00000073).unwrap();
    assert_eq!("ecall", inst.to_string());
}
