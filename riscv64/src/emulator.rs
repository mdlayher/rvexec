use crate::bus::Bus;
use crate::cpu::{self, Cpu};
use crate::rvelf;
use anyhow::anyhow;
use elf::abi;
use elf::endian::LittleEndian;
use elf::section::SectionHeader;
use elf::ElfBytes;
use thiserror::Error;

/// The `Emulator` is the primary entry point for rvexec. It loads a riscv64 ELF
/// binary and executes it until `exit(2)` is invoked.
pub struct Emulator {
    cpu: Cpu,
}

impl Emulator {
    /// Create an `Emulator` by loading the contents of an ELF binary.
    pub fn new(elf_bytes: &[u8]) -> Result<Self> {
        let mut bus = Bus::default();
        let pc = load_elf(&mut bus, elf_bytes)?;

        Ok(Self {
            cpu: Cpu::new(bus, pc),
        })
    }

    /// Execute the binary until termination. Returns the process's exit code or
    /// a runtime error.
    pub fn run(mut self) -> Result<usize> {
        loop {
            let inst = match self.cpu.fetch() {
                Ok(inst) => inst,
                Err(err) => return Err(Error::Runtime(err)),
            };

            if let Err(err) = self.cpu.execute(&inst) {
                match err {
                    cpu::Error::Exit(code) => {
                        // Program called exit(2).
                        return Ok(code as usize);
                    }
                    cpu::Error::Eof => {
                        // End of program.
                        return Ok(0);
                    }
                    _ => {
                        // All other errors return well-formatted messages.
                        return Err(Error::Runtime(err));
                    }
                }
            }
        }
    }
}

// Loads an ELF binary into memory owned by the Bus. Returns the entry point
// address and end of program address for the CPU to begin execution.
fn load_elf(bus: &mut Bus, buf: &[u8]) -> Result<(usize, usize)> {
    // The CPU assumes ELF riscv64/little-endian/executable.
    let elf_bytes = ElfBytes::<LittleEndian>::minimal_parse(buf)
        .map_err(|err| Error::InvalidBinary(anyhow!("failed to read ELF binary: {err}")))?;

    if let Err(err) = check_headers(&elf_bytes) {
        return Err(Error::InvalidBinary(anyhow!("invalid ELF headers: {err}")));
    }

    let program_headers = elf_bytes.segments().ok_or(Error::InvalidBinary(anyhow!(
        "found no ELF program segments"
    )))?;

    // Look for the program entry and exit points.
    let entry = elf_bytes.ehdr.e_entry as usize;
    let mut pc: (usize, usize) = (entry, 0);

    for ph in program_headers
        .iter()
        .filter(|ph| ph.p_type == abi::PT_LOAD)
    {
        // For each loadable segment, calculate the appropriate offsets and
        // load the program code and data into memory.
        let offset = ph.p_offset as usize;

        let (start, end) = bus.copy_from_exact(
            ph.p_vaddr as usize,
            ph.p_memsz as usize,
            &buf[offset..offset + ph.p_filesz as usize],
        );

        if entry >= start && entry <= end {
            // This PT_LOAD section encompasses the entrypoint.
            pc.1 = end;
        }
    }

    Ok(pc)
}

// Verifies an ELF binary is a riscv64 executable with extensions supported by
// rvexec.
fn check_headers(elf_bytes: &ElfBytes<LittleEndian>) -> anyhow::Result<()> {
    if elf_bytes.ehdr.class != elf::file::Class::ELF64
        || elf_bytes.ehdr.e_machine != abi::EM_RISCV
        || elf_bytes.ehdr.e_type != abi::ET_EXEC
    {
        return Err(anyhow!("only riscv64 executables are supported"));
    }

    let arch = parse_section_headers_arch(elf_bytes)
        .map_err(|err| anyhow!("failed to find RISC-V arch in ELF attributes: {err}"))?;

    match arch.as_str() {
        "rv64i2p0" | "rv64i2p1" => Ok(()),
        _ => Err(anyhow!("unsupported riscv64 arch value: {arch}")),
    }
}

// Parses RISC-V ELF attributes to find the arch string indicating which
// extensions the binary was compiled with.
fn parse_section_headers_arch(elf_bytes: &ElfBytes<LittleEndian>) -> anyhow::Result<String> {
    let section_headers = elf_bytes
        .section_headers()
        .ok_or(anyhow!("no ELF section headers"))?;

    let sh: Vec<SectionHeader> = section_headers
        .iter()
        .filter(|sh| sh.sh_type == abi::SHT_RISCV_ATTRIBUTES)
        .collect();
    if sh.len() != 1 {
        return Err(anyhow!("found no attributes section"));
    }

    let (data, compress) = elf_bytes
        .section_data(&sh[0])
        .map_err(|err| (anyhow!("read attributes: {err}")))?;
    if compress.is_some() {
        return Err(anyhow!("cannot decode compressed attributes"));
    }

    // Raw data must be parsed to find the arch.
    let parser = rvelf::AttributeParser::new(data);
    let attributes = parser
        .parse()
        .map_err(|err| anyhow!("parse attributes: {err}"))?;

    let subs: Vec<&rvelf::AttributesSubSection> = attributes
        .sub_sections
        .iter()
        .filter(|ss| ss.vendor_name == "riscv")
        .collect();
    if subs.len() != 1 {
        return Err(anyhow!("found no RISC-V vendor section"));
    }

    let subs: Vec<&rvelf::AttributesSubSubSection> = subs[0]
        .sub_sections
        .iter()
        .filter(|ss| ss.tag == 1 /* Tag_file */)
        .collect();
    if subs.len() != 1 {
        return Err(anyhow!("found no RISC-V Tag_file section"));
    }

    let tags: Vec<&rvelf::AttributesTag> = subs[0]
        .tags
        .iter()
        .filter(|t| t.tag == 5 /* Tag_RISCV_arch */)
        .collect();
    if tags.len() != 1 {
        return Err(anyhow!("found no RISC-V Tag_RISCV_arch tag"));
    }

    match &tags[0].value {
        rvelf::AttributeValue::String(s) => Ok(s.clone()),
        rvelf::AttributeValue::Todo => Ok("todo".to_string()),
    }
}

/// A `Result` type specialized for `Error`.
pub type Result<T> = std::result::Result<T, Error>;

/// Possible types of errors the `Emulator` can return.
#[derive(Debug, Error)]
pub enum Error {
    #[error("invalid riscv64 ELF binary: {0}")]
    InvalidBinary(anyhow::Error),
    #[error("runtime error: {0}")]
    Runtime(cpu::Error),
}
