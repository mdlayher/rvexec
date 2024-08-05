use anyhow::{anyhow, Result};
use byteorder::ReadBytesExt;
use elf::abi;
use elf::endian::LittleEndian;
use elf::file::Class;
use riscv64::{asm, cpu, rvelf};
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

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
                let _attrs = rvelf::AttributeParser::new(data).parse().expect("parse");
                //dbg!(attrs);
            }
            (".text", abi::SHT_PROGBITS) => {
                let mut cursor = Cursor::new(data);
                let mut cpu = cpu::Cpu::default();

                println!("assembly:");
                while (data.len() - cursor.position() as usize) > 0 {
                    let buf = cursor.read_u32::<byteorder::LE>().unwrap();

                    let inst = asm::Instruction::try_from(buf).expect("parse instruction");
                    let _ = cpu.execute(&inst);

                    println!("    {}", inst);
                }

                println!("cpu:");
                dbg!(cpu);
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
