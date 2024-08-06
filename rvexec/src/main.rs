use riscv64::cpu;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

fn main() -> ExitCode {
    let path = "./asm/hello";

    let file = fs::read(PathBuf::from(path)).expect("open hello binary");

    let mut cpu = cpu::Cpu::new(&file).expect("create CPU");
    loop {
        let inst = match cpu.fetch() {
            Ok(inst) => inst,
            Err(err) => panic!("{}", err),
        };

        if let Err(err) = cpu.execute(&inst) {
            match err {
                cpu::Error::Exit(code) => {
                    // Program called exit(2).
                    if code != 0 {
                        println!("rvexec: exit code {}", code);
                    }

                    return ExitCode::from(code as u8);
                }
                _ => {
                    // All other errors return well-formatted messages.
                    println!("rvexec: {}", err);
                    return ExitCode::from(1);
                }
            }
        }
    }
}
