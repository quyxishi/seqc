use log::{error, info};
use std::{
    fs,
    io::{self, BufReader, Read},
    path::PathBuf,
    time::Instant,
};
use thousands::Separable;

use clap::{Parser, ValueEnum};
use memmap2::MmapMut;
use seqc::{Dialect, Pattern, VariableDialect, VariablePattern};

mod elog;

use crate::elog::ResultExt;

#[derive(Debug, Clone, ValueEnum)]
enum Dialects {
    V0,
}

impl Into<VariableDialect> for Dialects {
    fn into(self) -> VariableDialect {
        match self {
            Self::V0 => VariableDialect::Binary(Dialect::new([
                VariablePattern::Ternary(Pattern::from([b'm', b'e', b'w'])),
                VariablePattern::Ternary(Pattern::from([b'e', b'l', b'y'])),
            ])),
        }
    }
}

#[derive(Debug, Clone, ValueEnum)]
enum Mode {
    Encrypt,
    Decrypt,
}

/// A pattern-based encoding cli
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Dialect to use
    #[arg(short, long, value_enum)]
    dialect: Dialects,

    /// Operation mode
    #[arg(short, long, value_enum)]
    mode: Mode,

    /// Input file
    input: PathBuf,

    /// Output file
    output: PathBuf,
}

fn main() {
    let args: Args = Args::parse();

    let _ = elog::Dispatcher::new()
        .chain(io::stdout(), log::LevelFilter::Trace)
        .filter_only_self(true)
        .apply();

    if !args.input.is_file() {
        error!("either input file doesn't exists or it's not a file");
        std::process::exit(1);
    }

    if args.output.exists() && !args.output.is_file() {
        error!("provided output is pointing to existing non-file object");
        std::process::exit(1);
    }

    info!(
        "{} v{}",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION")
    );

    info!(
        "dialect: {:?}, mode: {:?}, '{}' -> '{}'",
        args.dialect,
        args.mode,
        args.input.file_name().unwrap().to_string_lossy(),
        args.output.file_name().unwrap().to_string_lossy()
    );

    let now: Instant = Instant::now();
    let dialect: VariableDialect = args.dialect.into();

    let mut input_file: BufReader<fs::File> = BufReader::new(
        fs::OpenOptions::new()
            .read(true)
            .open(&args.input)
            .unwrap_or_log("unable to open handle to the input file due"),
    );

    let mut input_buffer: Vec<u8> = Vec::with_capacity(
        args.input
            .metadata()
            .unwrap_or_log("unable to retrieve metadata of the input file due")
            .len() as usize,
    );

    input_file
        .read_to_end(&mut input_buffer)
        .unwrap_or_log("during input file reading encountered unexpected error");

    let output_file: fs::File = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(true)
        .open(args.output)
        .unwrap_or_log("unable to open handle to the output file due");

    let output_size: usize = match args.mode {
        Mode::Encrypt => dialect.measure_encode_capacity(&input_buffer),
        Mode::Decrypt => input_buffer.len(),
    };

    output_file
        .set_len(output_size as u64)
        .unwrap_or_log("unable to pre-allocate output file due");

    let mut mmap: MmapMut = unsafe {
        MmapMut::map_mut(&output_file)
            .unwrap_or_log("unable to open memory-mapped file handle of the output file due")
    };

    let mmap_slice: &mut [u8] = &mut mmap[..];

    let output_size: usize = match args.mode {
        Mode::Encrypt => dialect
            .encode_slice(&input_buffer, mmap_slice)
            .unwrap_or_log("unable to encode payload using Dialect due:"),

        Mode::Decrypt => dialect
            .decode_slice(&input_buffer, mmap_slice)
            .unwrap_or_log("unable to decode payload using Dialect due:"),
    };

    info!("wrote {} bytes", output_size.separate_with_commas());

    mmap.flush()
        .unwrap_or_log("during flushing encountered unexpected error");

    drop(mmap);

    output_file
        .set_len(output_size as u64)
        .unwrap_or_log("unable to shrink output file due");

    let elapsed: std::time::Duration = now.elapsed();

    info!("elapsed \x1b[30;47m{:.2?}\x1b[0m", elapsed);
}
