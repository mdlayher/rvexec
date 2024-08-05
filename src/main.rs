use anyhow::{anyhow, Ok, Result};
use byteorder::ReadBytesExt;
use elf::abi;
use elf::endian::LittleEndian;
use elf::file::Class;
use std::fmt;
use std::fs;
use std::io::{BufRead, Cursor};
use std::path::PathBuf;
use uleb128::ReadULeb128Ext;

fn main() {
    let path = "./asm/hello";

    let file = fs::File::open(PathBuf::from(path)).expect("open hello binary");

    let mut elf_file = elf::ElfStream::<elf::endian::LittleEndian, _>::open_stream(file)
        .expect("open little endian ELF stream");

    println!(
        "file: {:?}, class: {:?}, type: {:?}, machine: {:?}",
        path,
        elf_file.ehdr.class,
        elf::to_str::e_type_to_human_str(elf_file.ehdr.e_type),
        elf::to_str::e_machine_to_human_str(elf_file.ehdr.e_machine),
    );

    if let Err(err) = check_header(&elf_file.ehdr) {
        panic!("failed to parse header: {}", err);
    }

    let (section_headers, string_table) = elf_file
        .section_headers_with_strtab()
        .expect("read section headers");
    let string_table = string_table.expect("invalid strtab");

    let section_headers: Vec<_> = section_headers
        .iter()
        .map(|sh| {
            let name = string_table
                .get(sh.sh_name as usize)
                .expect("section name should parse");
            (name.to_string(), *sh)
        })
        .collect();

    for (name, sh) in section_headers {
        let (data, compress) = elf_file.section_data(&sh).expect("ok");
        if compress.is_some() {
            panic!(
                "rvexec: compression header not implemented for header type {:?}",
                sh.sh_type
            );
        }

        match (name.as_str(), sh.sh_type) {
            ("", abi::SHT_NULL) => continue,
            (".riscv.attributes", abi::SHT_RISCV_ATTRIBUTES) => {
                let _attrs = AttributeParser::new(data).parse().expect("parse");
                //dbg!(attrs);
            }
            (".text", abi::SHT_PROGBITS) => {
                let mut cursor = Cursor::new(data);

                println!("assembly:");
                while (data.len() - cursor.position() as usize) > 0 {
                    let buf = cursor.read_u32::<byteorder::LE>().unwrap();

                    let inst = Instruction::from(buf);
                    println!("    {}", inst);
                }
            }
            (".data", abi::SHT_PROGBITS) => {
                //dbg!(data);
            }
            _ => {
                //println!("type: {}, name: {}", sh.sh_type, name);
            }
        }
    }
}

fn check_header(header: &elf::file::FileHeader<LittleEndian>) -> Result<()> {
    if header.class == Class::ELF64
        && header.e_machine == abi::EM_RISCV
        && header.version == abi::EV_CURRENT.into()
        && header.e_type == abi::ET_EXEC
    {
        Ok(())
    } else {
        Err(anyhow!("only ELFv1 riscv64 executables are supported"))
    }
}

#[derive(Debug)]
pub struct Attributes {
    pub format_version: char,
    pub sub_sections: Vec<AttributesSubSection>,
}

#[derive(Debug)]
pub struct AttributesSubSection {
    pub length: u32,
    pub vendor_name: String,
    pub sub_sections: Vec<AttributesSubSubSection>,
}

#[derive(Debug)]
pub struct AttributesSubSubSection {
    pub tag: u32,
    pub length: u32,
    pub tags: Vec<AttributesTag>,
}

#[derive(Debug)]
pub struct AttributesTag {
    pub tag: u32,
    pub value: AttributeValue,
}

#[derive(Debug)]
pub enum AttributeValue {
    String(String),
}

/// Parses RISC-V attributes from an ELF binary.
///
/// See also:
/// https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc#layout-of-riscvattributes-section
struct AttributeParser<'a> {
    length: usize,
    cursor: Cursor<&'a [u8]>,
}

impl<'a> AttributeParser<'a> {
    fn new(src: &'a [u8]) -> Self {
        Self {
            length: src.len(),
            cursor: Cursor::new(src),
        }
    }

    fn parse(mut self) -> Result<Attributes> {
        // Magic number.
        let format_version = self.cursor.read_u8()? as char;
        if format_version != 'A' {
            return Err(anyhow!("unknown format version: {:?}", format_version));
        }

        let mut sub_sections = Vec::new();
        while let Some(sub_section) = self.parse_sub_section()? {
            sub_sections.push(sub_section);
        }

        Ok(Attributes {
            format_version,
            sub_sections,
        })
    }

    fn parse_sub_section(&mut self) -> Result<Option<AttributesSubSection>> {
        if self.remaining() == 0 {
            return Ok(None);
        }

        let length = self.cursor.read_u32::<byteorder::LE>()?;
        let vendor_name = self.read_ntbs()?;

        let mut sub_sub_sections = Vec::new();
        while let Some(section) = self.parse_sub_sub_section()? {
            sub_sub_sections.push(section);
        }

        Ok(Some(AttributesSubSection {
            length,
            vendor_name,
            sub_sections: sub_sub_sections,
        }))
    }

    fn parse_sub_sub_section(&mut self) -> Result<Option<AttributesSubSubSection>> {
        if self.remaining() == 0 {
            return Ok(None);
        }

        let tag = self.cursor.read_uleb128_u32()?;
        let sub_sub_length = self.cursor.read_u32::<byteorder::LE>()?;

        let mut tags = Vec::new();
        while let Some(tag) = self.parse_attribute_tag()? {
            tags.push(tag);
        }

        Ok(Some(AttributesSubSubSection {
            tag,
            length: sub_sub_length,
            tags,
        }))
    }

    fn parse_attribute_tag(&mut self) -> Result<Option<AttributesTag>> {
        if self.remaining() == 0 {
            return Ok(None);
        }

        let tag = self.cursor.read_uleb128_u32()?;

        // Per docs, even values are integers, odd values are NTBS.
        let value = if tag % 2 == 0 {
            // XXX(mdlayher): what format are these in?
            panic!("rvexec: TODO integer values")
        } else {
            AttributeValue::String(self.read_ntbs()?)
        };

        Ok(Some(AttributesTag { tag, value }))
    }

    fn remaining(&self) -> usize {
        self.length - self.cursor.position() as usize
    }

    fn read_ntbs(&mut self) -> Result<String> {
        // Read until the next NULL and pop the final byte.
        let mut buf = Vec::new();
        self.cursor.read_until(b'\0', &mut buf)?;
        buf.pop();
        let str = String::from_utf8(buf)?;
        Ok(str)
    }
}

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
enum Instruction {
    None,
    System(System),
    IType(IType),
    UType(UType),
}

impl From<u32> for Instruction {
    fn from(value: u32) -> Self {
        match value & 0x7f {
            0b0010011 => Self::IType(IType(value)),
            0b0011011 | 0b00010111 => Self::UType(UType(value)),
            0b1110011 => Self::System(System(value)),
            _ => Self::None,
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::IType(itype) => {
                write!(
                    f,
                    "{} {}, {}, {}",
                    itype.inst().unwrap(),
                    itype.rd(),
                    itype.rs1(),
                    itype.immediate(),
                )
            }
            Self::System(system) => {
                write!(f, "{}", system.inst().unwrap())
            }
            Self::UType(utype) => {
                write!(
                    f,
                    "{} {}, {}",
                    utype.inst().unwrap(),
                    utype.rd(),
                    utype.immediate(),
                )
            }
            Self::None => write!(f, "illegal"),
        }
    }
}

#[derive(Debug)]
struct System(u32);

impl System {
    fn inst(&self) -> Option<Inst> {
        match self.immediate() {
            0x0 => Some(Inst::ECALL),
            0x1 => Some(Inst::EBREAK),
            _ => None,
        }
    }

    fn immediate(&self) -> u32 {
        self.0 >> 20
    }
}

#[derive(Debug)]
struct IType(u32);

impl IType {
    fn inst(&self) -> Option<Inst> {
        match self.funct3() {
            0x0 => Some(Inst::ADDI),
            _ => None,
        }
    }

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

#[derive(Debug)]

struct UType(u32);

impl UType {
    fn inst(&self) -> Option<Inst> {
        match self.0 & 0x7f {
            0b00010111 => Some(Inst::AUIPC),
            _ => None,
        }
    }

    fn rd(&self) -> Register {
        Register::from(self.0 >> 7 & 0x1f)
    }

    fn immediate(&self) -> u32 {
        self.0 >> 20
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
            Self::ECALL => "ecall",
            Self::EBREAK => "ebreak",
        };

        write!(f, "{}", op)
    }
}
