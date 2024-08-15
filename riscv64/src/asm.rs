use anyhow::{anyhow, Error, Result};
use std::fmt;

macro_rules! impl_opcode {
    () => {
        fn opcode(&self) -> u8 {
            (self.0 & 0x7f) as u8
        }
    };
}

macro_rules! impl_funct3 {
    () => {
        fn funct3(&self) -> u8 {
            ((self.0 >> 12) & 0x07) as u8
        }
    };
}

macro_rules! impl_rs1 {
    () => {
        pub fn rs1(&self) -> Register {
            Register::try_from(self.0 >> 15 & 0x1f).expect("rs1 must occupy exactly 5 bits")
        }
    };
}

macro_rules! impl_rs2 {
    () => {
        pub fn rs2(&self) -> Register {
            Register::try_from(self.0 >> 20 & 0xf).expect("rs2 must occupy exactly 4 bits")
        }
    };
}

macro_rules! impl_rd {
    () => {
        pub fn rd(&self) -> Register {
            Register::try_from(self.0 >> 7 & 0x1f).expect("rd must occupy exactly 5 bits")
        }
    };
}

#[derive(Debug, PartialEq)]
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
    S0,
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
    type Error = Error;

    fn try_from(value: u32) -> Result<Self> {
        match value {
            // Safety: Register is repr(u32) and values 0-31 are valid register
            // numbers.
            0..32 => Ok(unsafe { std::mem::transmute::<u32, Register>(value) }),
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
            Self::S0 => "s0",
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
    B(BType),
    I(IType),
    J(JType),
    R(RType),
    S(SType),
    U(UType),
}

impl TryFrom<u32> for Instruction {
    type Error = Error;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        // Mask off to find the opcode and then pass the raw value for each type
        // to interpret the entire value as an instruction of a given format.
        //
        // Reference:
        // https://github.com/jameslzhu/riscv-card/blob/master/riscv-card.pdf
        let masked = value & 0x7f;
        match masked {
            0b0110_0011 => Ok(Self::B(BType(value))),
            0b0001_0011 | 0b0111_0011 | 0b0000_0011 | 0b0110_0111 => Ok(Self::I(IType(value))),
            0b0110_1111 => Ok(Self::J(JType(value))),
            0b0011_1011 | 0b0011_0011 => Ok(Self::R(RType(value))),
            0b0010_0011 => Ok(Self::S(SType(value))),
            0b0001_1011 | 0b0001_0111 => Ok(Self::U(UType(value))),
            _ => Err(anyhow!("no matching opcode: {:#02x}", masked)),
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::B(btype) => btype.fmt(f),
            Self::I(itype) => itype.fmt(f),
            Self::J(jtype) => jtype.fmt(f),
            Self::R(rtype) => rtype.fmt(f),
            Self::S(stype) => stype.fmt(f),
            Self::U(utype) => utype.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct BType(u32);

impl BType {
    impl_opcode!();
    impl_funct3!();
    impl_rs1!();
    impl_rs2!();

    pub fn immediate(&self) -> i32 {
        // XXX(mdlayher): I'm pretty sure this is still wrong.
        let imm_1 = self.0 as i32 >> 25;
        let imm_2 = (self.0 as i32 >> 7) & 0x1f;

        imm_1 << 5 | imm_2
    }
}

impl fmt::Display for BType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match BTypeInst::try_from(self) {
            Ok(inst) => match inst {
                BTypeInst::BEQ => write!(
                    f,
                    "{} {}, {}, {}",
                    inst,
                    self.rs1(),
                    self.rs2(),
                    self.immediate()
                ),
            },
            Err(_) => write!(f, "btype(???)"),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
pub enum BTypeInst {
    BEQ,
}

impl TryFrom<&BType> for BTypeInst {
    type Error = Error;

    fn try_from(value: &BType) -> Result<Self, Self::Error> {
        match (value.opcode(), value.funct3()) {
            (0b0110_0011, 0x0) => Ok(Self::BEQ),
            _ => Err(anyhow!(
                "unhandled B-Type opcode: {:#02x}, funct3: {:#02x}",
                value.opcode(),
                value.funct3()
            )),
        }
    }
}

impl fmt::Display for BTypeInst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::BEQ => "beq",
        };

        write!(f, "{}", op)
    }
}

#[derive(Debug)]
pub struct IType(u32);

impl IType {
    impl_opcode!();
    impl_funct3!();
    impl_rs1!();
    impl_rd!();

    pub fn immediate(&self) -> i32 {
        // XXX(mdlayher): I'm pretty sure this is still wrong.
        self.0 as i32 >> 20
    }
}

impl TryFrom<&IType> for ITypeInst {
    type Error = Error;

    fn try_from(value: &IType) -> Result<Self, Self::Error> {
        match value.opcode() {
            0b0001_0011 => match value.funct3() {
                0x0 => Ok(ITypeInst::ADDI),
                _ => Err(anyhow!(
                    "unhandled I-Type immediate funct3: {:#02x}",
                    value.funct3()
                )),
            },
            0b0000_0011 => match value.funct3() {
                0x0 => Ok(ITypeInst::LB),
                0x2 => Ok(ITypeInst::LW),
                _ => Err(anyhow!(
                    "unhandled I-Type load funct3: {:#02x}",
                    value.funct3()
                )),
            },
            0b0111_0011 => match value.immediate() {
                // System immediates.
                0x0 => Ok(ITypeInst::ECALL),
                0x1 => Ok(ITypeInst::EBREAK),
                _ => Err(anyhow!(
                    "unhandled I-Type system immediate: {:#02x}",
                    value.immediate()
                )),
            },
            0b0110_0111 => match value.funct3() {
                0x0 => Ok(ITypeInst::JALR),
                _ => Err(anyhow!(
                    "unhandled I-Type jump funct3: {:#02x}",
                    value.funct3()
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
                ITypeInst::JALR | ITypeInst::LB => write!(
                    f,
                    "{} {}, {}({})",
                    inst,
                    self.rd(),
                    self.immediate(),
                    self.rs1(),
                ),
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
    JALR,
    LB,
    LW,
}

impl fmt::Display for ITypeInst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::ADDI => "addi",
            Self::EBREAK => "ebreak",
            Self::ECALL => "ecall",
            Self::JALR => "jalr",
            Self::LB => "lb",
            Self::LW => "lw",
        };

        write!(f, "{}", op)
    }
}

#[derive(Debug)]
pub struct JType(u32);

impl JType {
    impl_opcode!();
    impl_rd!();

    pub fn immediate(&self) -> i32 {
        let imm20 = self.0 >> 31;
        let imm10_1 = (self.0 >> 21) & 0x3ff;
        let imm11 = (self.0 >> 20) & 0x1;
        let imm19_12 = (self.0 >> 12) & 0xff;

        // Reassemble the 20 bit immediate with 12 bits of upper padding. Then
        // shift left and convert to i32->i64 to sign extend. Drop the extra
        // bits by converting back to i32 and shifting down, multiplying the
        // final result by 2 for the real offset.
        //
        // This is terrible, there's certainly a better way.
        let imm = imm20 << 19 | imm19_12 << 11 | imm11 << 10 | imm10_1;
        let imm = ((imm << 12) as i32 as i64 as i32) >> 12;

        2 * imm
    }
}

impl TryFrom<&JType> for JTypeInst {
    type Error = Error;

    fn try_from(value: &JType) -> Result<Self, Self::Error> {
        match value.opcode() {
            0b0110_1111 => Ok(Self::JAL),
            _ => Err(anyhow!("unhandled J-Type opcode: {:#02x}", value.opcode())),
        }
    }
}

impl fmt::Display for JType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match JTypeInst::try_from(self) {
            Ok(inst) => match inst {
                JTypeInst::JAL => write!(f, "{} {}, {}", inst, self.rd(), self.immediate()),
            },
            Err(_) => write!(f, "jtype(???) {}, {}", self.rd(), self.immediate(),),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
pub enum JTypeInst {
    JAL,
}

impl fmt::Display for JTypeInst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::JAL => "jal",
        };

        write!(f, "{}", op)
    }
}

#[derive(Debug)]
pub struct RType(u32);

impl RType {
    impl_opcode!();
    impl_funct3!();
    impl_rs1!();
    impl_rs2!();
    impl_rd!();

    fn funct7(&self) -> u8 {
        ((self.0 >> 25) & 0x7f) as u8
    }
}

impl fmt::Display for RType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match RTypeInst::try_from(self) {
            Ok(inst) => write!(f, "{} {}, {}, {}", inst, self.rd(), self.rs1(), self.rs2()),
            Err(_) => write!(f, "rtype(???)"),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
pub enum RTypeInst {
    ADD,
    ADDW,
    SUB,
}

impl TryFrom<&RType> for RTypeInst {
    type Error = Error;

    fn try_from(value: &RType) -> Result<Self, Self::Error> {
        match value.opcode() {
            0b0011_0011 => match (value.funct3(), value.funct7()) {
                (0x0, 0x00) => Ok(Self::ADD),
                (0x0, 0x20) => Ok(Self::SUB),
                _ => Err(anyhow!(
                    "unhandled R-Type rv32i funct3: {:#02x}, funct7: {:#02x}",
                    value.funct3(),
                    value.funct7()
                )),
            },
            0b0011_1011 => match (value.funct3(), value.funct7()) {
                (0x00, 0x00) => Ok(Self::ADDW),
                _ => Err(anyhow!(
                    "unhandled R-Type rv64i funct3: {:#02x}, funct7: {:#02x}",
                    value.funct3(),
                    value.funct7()
                )),
            },
            _ => Err(anyhow!("unhandled R-Type opcode: {:#02x}", value.opcode())),
        }
    }
}

impl fmt::Display for RTypeInst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::ADD => "add",
            Self::ADDW => "addw",
            Self::SUB => "sub",
        };

        write!(f, "{}", op)
    }
}

#[derive(Debug)]
pub struct SType(u32);

impl SType {
    impl_opcode!();
    impl_funct3!();
    impl_rs1!();
    impl_rs2!();

    pub fn immediate(&self) -> i32 {
        // XXX(mdlayher): I'm pretty sure this is still wrong.
        let imm_1 = self.0 as i32 >> 25;
        let imm_2 = (self.0 as i32 >> 7) & 0x1f;

        imm_1 << 5 | imm_2
    }
}

impl TryFrom<&SType> for STypeInst {
    type Error = Error;

    fn try_from(value: &SType) -> Result<Self, Self::Error> {
        match value.opcode() {
            0b0010_0011 => match value.funct3() {
                0x2 => Ok(Self::SW),
                0x3 => Ok(Self::SD),
                _ => Err(anyhow!("unhandled S-Type funct3: {:#02x}", value.funct3())),
            },
            _ => Err(anyhow!("unhandled S-Type opcode: {:#02x}", value.opcode())),
        }
    }
}

impl fmt::Display for SType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match STypeInst::try_from(self) {
            Ok(inst) => write!(
                f,
                "{} {}, {}({})",
                inst,
                self.rs2(),
                self.immediate(),
                self.rs1()
            ),
            Err(_) => write!(f, "stype(???)"),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
pub enum STypeInst {
    SD,
    SW,
}

impl fmt::Display for STypeInst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = match self {
            Self::SD => "sd",
            Self::SW => "sw",
        };

        write!(f, "{}", op)
    }
}

#[derive(Debug)]
pub struct UType(u32);

impl UType {
    impl_opcode!();
    impl_rd!();

    pub fn immediate(&self) -> u32 {
        self.0 >> 12
    }
}

impl TryFrom<&UType> for UTypeInst {
    type Error = Error;

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
fn test_instruction_add() {
    let tests = [
        (0x000002b3, "add t0, x0, x0"),
        (0x00a28333, "add t1, t0, a0"),
    ];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_addi() {
    let tests = [
        (0x00100513, "addi a0, x0, 1"),
        (0xfe010113, "addi sp, sp, -32"),
    ];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_auipc() {
    let inst = Instruction::try_from(0x00001597).unwrap();
    assert_eq!("auipc a1, 1", inst.to_string());
}

#[test]
fn test_instruction_beq() {
    let tests = [(0x00030663, "beq t1, x0, 12")];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
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

#[test]
fn test_instruction_jal() {
    let tests = [(0x0300006f, "jal x0, 48"), (0xfc1ff0ef, "jal ra, -64")];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_jalr() {
    let tests = [(0x00008067, "jalr x0, 0(ra)")];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_lb() {
    let tests = [(0x00030303, "lb t1, 0(t1)")];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_lw() {
    let tests = [
        (0x00c12083, "lw ra, sp, 12"),
        (0xff442503, "lw a0, s0, -12"),
        (0x00812403, "lw s0, sp, 8"),
    ];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_sd() {
    let tests = [
        (0x00813c23, "sd s0, 24(sp)"),
        (0x00113423, "sd ra, 8(sp)"),
        (0x00813023, "sd s0, 0(sp)"),
    ];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_sw() {
    let tests = [
        (0xfea42a23, "sw a0, -12(s0)"),
        (0x00812423, "sw s0, 8(sp)"),
        (0x00112623, "sw ra, 12(sp)"),
    ];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}

#[test]
fn test_instruction_sub() {
    let tests = [(0x40650e33, "sub t3, a0, t1")];

    for test in tests {
        let inst = Instruction::try_from(test.0).unwrap();
        assert_eq!(test.1, inst.to_string());
    }
}
