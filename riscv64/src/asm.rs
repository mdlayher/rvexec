use anyhow::{anyhow, Result};
use std::fmt;

#[derive(PartialEq)]
#[repr(u32)]
pub enum Register {
    X0,
    RA,
    SP,
    GP,
    TP,
    T0,
    T1,
    T2,
    FP,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
}

impl TryFrom<u32> for Register {
    type Error = anyhow::Error;

    fn try_from(value: u32) -> Result<Self> {
        match value {
            // Safety: Register is repr(u32) and values 0-31 are valid register
            // numbers.
            0..31 => Ok(unsafe { std::mem::transmute::<u32, Register>(value) }),
            _ => Err(anyhow!("unknown register number: {}", value)),
        }
    }
}

impl From<Register> for u32 {
    fn from(value: Register) -> Self {
        // Safety: Register is repr(u32).
        unsafe { std::mem::transmute::<Register, u32>(value) }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let reg = match self {
            Self::X0 => "x0",
            Self::RA => "ra",
            Self::SP => "sp",
            Self::GP => "gp",
            Self::TP => "tp",
            Self::T0 => "t0",
            Self::T1 => "t1",
            Self::T2 => "t2",
            Self::FP => "fp",
            Self::S1 => "s1",
            Self::A0 => "a0",
            Self::A1 => "a1",
            Self::A2 => "a2",
            Self::A3 => "a3",
            Self::A4 => "a4",
            Self::A5 => "a5",
            Self::A6 => "a6",
            Self::A7 => "a7",
            Self::S2 => "s2",
            Self::S3 => "s3",
            Self::S4 => "s4",
            Self::S5 => "s5",
            Self::S6 => "s6",
            Self::S7 => "s7",
            Self::S8 => "s8",
            Self::S9 => "s9",
            Self::S10 => "s10",
            Self::S11 => "s11",
            Self::T3 => "t3",
            Self::T4 => "t4",
            Self::T5 => "t5",
            Self::T6 => "t6",
        };

        write!(f, "{}", reg)
    }
}

#[derive(Debug)]
pub enum Instruction {
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
            0b0010011 | 0b1110011 => Ok(Self::IType(IType(value))),
            0b0011011 | 0b00010111 => Ok(Self::UType(UType(value))),
            _ => Err(anyhow!("no matching opcode: {:#02x}", masked)),
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::IType(itype) => itype.fmt(f),
            Self::UType(utype) => utype.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct IType(u32);

impl IType {
    fn opcode(&self) -> u8 {
        (self.0 & 0x7f) as u8
    }

    fn funct3(&self) -> u8 {
        ((self.0 >> 12) & 0x07) as u8
    }

    pub fn rs1(&self) -> Register {
        Register::try_from(self.0 >> 15 & 0x1f).expect("rs1 must occupy exactly 5 bits")
    }

    pub fn rd(&self) -> Register {
        Register::try_from(self.0 >> 7 & 0x1f).expect("rd must occupy exactly 5 bits")
    }

    pub fn immediate(&self) -> u32 {
        self.0 >> 20
    }
}

impl TryFrom<&IType> for ITypeInst {
    type Error = anyhow::Error;

    fn try_from(value: &IType) -> Result<Self, Self::Error> {
        match value.opcode() {
            0b00010011 => match value.funct3() {
                0x0 => Ok(ITypeInst::ADDI),
                _ => Err(anyhow!("unhandled I-Type funct3: {:#02x}", value.funct3())),
            },
            0b01110011 => match value.immediate() {
                // System immediates.
                0x0 => Ok(ITypeInst::ECALL),
                0x1 => Ok(ITypeInst::EBREAK),
                _ => Err(anyhow!(
                    "unhandled I-Type system immediate: {:#02x}",
                    value.immediate()
                )),
            },
            _ => Err(anyhow!("unhandled I-Type opcode: {:#02x}", value.opcode())),
        }
    }
}

impl fmt::Display for IType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match ITypeInst::try_from(self) {
            Ok(inst) => match inst {
                ITypeInst::EBREAK | ITypeInst::ECALL => inst.fmt(f),
                _ => write!(
                    f,
                    "{} {}, {}, {}",
                    inst,
                    self.rd(),
                    self.rs1(),
                    self.immediate(),
                ),
            },
            Err(_) => write!(
                f,
                "itype(???) {}, {}, {}",
                self.rd(),
                self.rs1(),
                self.immediate(),
            ),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
pub enum ITypeInst {
    ADDI,
    EBREAK,
    ECALL,
}

impl fmt::Display for ITypeInst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::ADDI => "addi",
            Self::EBREAK => "ebreak",
            Self::ECALL => "ecall",
        };

        write!(f, "{}", op)
    }
}

#[derive(Debug)]
pub struct UType(u32);

impl UType {
    fn opcode(&self) -> u8 {
        (self.0 & 0x7f) as u8
    }

    fn rd(&self) -> Register {
        Register::try_from(self.0 >> 7 & 0x1f).expect("rd must occupy exactly 5 bits")
    }

    fn immediate(&self) -> u32 {
        self.0 >> 20
    }
}

impl TryFrom<&UType> for UTypeInst {
    type Error = anyhow::Error;

    fn try_from(value: &UType) -> Result<Self, Self::Error> {
        match value.opcode() {
            0b00010111 => Ok(UTypeInst::AUIPC),
            _ => Err(anyhow!("unhandled U-Type opcode: {:#02x}", value.opcode())),
        }
    }
}

impl fmt::Display for UType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match UTypeInst::try_from(self) {
            Ok(inst) => match inst {
                UTypeInst::AUIPC => write!(f, "{} {}, {}", inst, self.rd(), self.immediate()),
            },
            Err(_) => write!(f, "utype(???) {}, {}", self.rd(), self.immediate(),),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
pub enum UTypeInst {
    AUIPC,
}

impl fmt::Display for UTypeInst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::AUIPC => "auipc",
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
    assert_eq!("addi a0, x0, 1", inst.to_string());
}

#[test]
fn test_instruction_auipc() {
    let inst = Instruction::try_from(0x00001597).unwrap();
    assert_eq!("auipc a1, 0", inst.to_string());
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
