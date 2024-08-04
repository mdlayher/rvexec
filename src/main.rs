use anyhow::{anyhow, Ok, Result};
use byteorder::ReadBytesExt;
use elf::abi;
use elf::endian::LittleEndian;
use elf::file::Class;
use elf::section::SectionHeader;
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

    // Copy headers so we can end the mutable borrow of the file.
    let section_headers: Vec<SectionHeader> = section_headers.to_vec();

    // TODO(mdlayher): match on various attribute types.
    let mut rvattrs: Option<SectionHeader> = None;
    for sh in section_headers {
        let _name = string_table.get(sh.sh_name as usize).expect("read string");
        if sh.sh_type != abi::SHT_RISCV_ATTRIBUTES {
            continue;
        }

        rvattrs = Some(sh);
    }

    if let Some(rv) = rvattrs {
        let (data, _compress) = elf_file.section_data(&rv).expect("ok");

        let attrs = AttributeParser::new(data).parse().expect("parse");
        dbg!(attrs);
    };
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
