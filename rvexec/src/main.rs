use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    // Default program for testing, or use one specified by CLI.
    let mut path = "./asm/loop/loop.elf";
    if args.len() == 2 {
        path = args[1].as_str();
    }

    let file = match fs::read(PathBuf::from(path)) {
        Ok(file) => file,
        Err(err) => {
            println!("rvexec: failed to open file {}: {}", path, err);
            return ExitCode::from(1);
        }
    };

    let emulator = match riscv64::Emulator::new(&file) {
        Ok(emu) => emu,
        Err(err) => {
            println!("rvexec: failed to create emulator: {}", err);
            return ExitCode::from(1);
        }
    };

    match emulator.run() {
        Ok(code) => {
            if code != 0 {
                println!("rvexec: exit code {}", code);
            }

            ExitCode::from(code as u8)
        }
        Err(err) => {
            // All other errors return well-formatted messages.
            println!("rvexec: {}", err);
            ExitCode::from(1)
        }
    }
}
