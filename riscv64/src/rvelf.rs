use anyhow::{anyhow, Result};
use byteorder::ReadBytesExt;
use std::io::{BufRead, Cursor};
use uleb128::ReadULeb128Ext;

#[derive(Debug)]
pub struct Attributes {
    pub sub_sections: Vec<AttributesSubSection>,
}

#[derive(Debug)]
pub struct AttributesSubSection {
    pub vendor_name: String,
    pub sub_sections: Vec<AttributesSubSubSection>,
}

#[derive(Debug)]
pub struct AttributesSubSubSection {
    pub tag: u32,
    pub tags: Vec<AttributesTag>,
}

#[derive(Debug)]
pub struct AttributesTag {
    pub tag: u32,
    pub value: AttributeValue,
}

#[derive(Debug)]
pub enum AttributeValue {
    Todo,
    String(String),
}

/// Parses RISC-V attributes from an ELF binary.
///
/// See also:
/// <https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc#layout-of-riscvattributes-section>
pub struct AttributeParser<'a> {
    length: usize,
    cursor: Cursor<&'a [u8]>,
}

impl<'a> AttributeParser<'a> {
    pub fn new(src: &'a [u8]) -> Self {
        Self {
            length: src.len(),
            cursor: Cursor::new(src),
        }
    }

    pub fn parse(mut self) -> Result<Attributes> {
        // Magic number.
        let format_version = self.cursor.read_u8()? as char;
        if format_version != 'A' {
            return Err(anyhow!("unknown format version: {:?}", format_version));
        }

        let mut sub_sections = Vec::new();
        while let Some(sub_section) = self.parse_sub_section()? {
            sub_sections.push(sub_section);
        }

        Ok(Attributes { sub_sections })
    }

    fn parse_sub_section(&mut self) -> Result<Option<AttributesSubSection>> {
        if self.remaining() == 0 {
            return Ok(None);
        }

        let _length = self.cursor.read_u32::<byteorder::LE>()?;
        let vendor_name = self.read_ntbs()?;

        let mut sub_sub_sections = Vec::new();
        while let Some(section) = self.parse_sub_sub_section()? {
            sub_sub_sections.push(section);
        }

        Ok(Some(AttributesSubSection {
            vendor_name,
            sub_sections: sub_sub_sections,
        }))
    }

    fn parse_sub_sub_section(&mut self) -> Result<Option<AttributesSubSubSection>> {
        if self.remaining() == 0 {
            return Ok(None);
        }

        let tag = self.cursor.read_uleb128_u32()?;
        let _sub_sub_length = self.cursor.read_u32::<byteorder::LE>()?;

        let mut tags = Vec::new();
        while let Some(tag) = self.parse_attribute_tag()? {
            tags.push(tag);
        }

        Ok(Some(AttributesSubSubSection { tag, tags }))
    }

    fn parse_attribute_tag(&mut self) -> Result<Option<AttributesTag>> {
        if self.remaining() == 0 {
            return Ok(None);
        }

        let tag = self.cursor.read_uleb128_u32()?;

        // Per docs, even values are integers, odd values are NTBS.
        let value = if tag % 2 == 0 {
            // XXX(mdlayher): what format are these in?
            return Ok(Some(AttributesTag {
                tag,
                value: AttributeValue::Todo,
            }));
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
