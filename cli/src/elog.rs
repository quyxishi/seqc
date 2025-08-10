#![allow(dead_code)]

// use chrono::Local;
// use parking_lot::RwLock;
use std::{
    fmt::Debug,
    fs,
    io::{self, Write},
};

use colored::{Color, Colorize};

macro_rules! std_chain_impl {
    ($sink:ident, $sink_type:ty, $sink_enum:expr) => {
        impl $sink {
            #[inline]
            fn log(&self, record: &log::Record) {
                write!(
                    self.stream.lock(),
                    "{}{}",
                    Dispatcher::format_msg(record, self.colored),
                    self.line_separator
                )
                .ok();
            }

            #[inline]
            fn flush(&self) {
                let _ = self.stream.lock().flush();
            }
        }

        impl From<$sink_type> for Chain {
            fn from(value: $sink_type) -> Self {
                $sink_enum($sink {
                    stream: value,
                    line_separator: "\n",
                    colored: true,
                })
            }
        }
    };
}

pub enum Chain {
    Stdout(StdoutChain),
    Stderr(StderrChain),
    // String(StringChain),
    File(FileChain),
}

pub struct StdoutChain {
    stream: io::Stdout,
    line_separator: &'static str,
    colored: ColorMode,
}

pub struct StderrChain {
    stream: io::Stderr,
    line_separator: &'static str,
    colored: ColorMode,
}

// pub struct StringChain {
//     stream: &'static RwLock<String>,
//     line_separator: &'static str,
// }

pub struct FileChain {
    stream: fs::File,
    line_separator: &'static str,
    colored: ColorMode,
}

std_chain_impl!(StdoutChain, io::Stdout, Chain::Stdout);
std_chain_impl!(StderrChain, io::Stderr, Chain::Stderr);

// impl From<&'static RwLock<String>> for Chain {
//     fn from(value: &'static RwLock<String>) -> Self {
//         Chain::String(StringChain {
//             stream: value,
//             line_separator: "\n",
//         })
//     }
// }

impl From<fs::File> for Chain {
    fn from(value: fs::File) -> Self {
        Chain::File(FileChain {
            stream: value,
            line_separator: "\n",
            colored: false,
        })
    }
}

// impl StringChain {
//     #[inline]
//     fn log(&self, record: &log::Record) {
//         self.stream.write().push_str(&format!(
//             "{}{}",
//             Dispatcher::format_msg(record),
//             self.line_separator
//         ))
//     }

//     #[inline]
//     fn flush(&self) {}
// }

impl FileChain {
    #[inline]
    fn log(&self, record: &log::Record) {
        let mut stream: fs::File = self.stream.try_clone().unwrap();

        write!(
            stream,
            "{}{}",
            Dispatcher::format_msg(record, self.colored),
            self.line_separator
        )
        .ok();
    }

    #[inline]
    fn flush(&self) {
        let mut stream: fs::File = self.stream.try_clone().unwrap();
        stream.flush().ok();
    }
}

impl Chain {
    #[inline]
    fn log(&self, record: &log::Record) {
        match self {
            Chain::Stdout(chain) => chain.log(record),
            Chain::Stderr(chain) => chain.log(record),
            // Chain::String(chain) => chain.log(record),
            Chain::File(chain) => chain.log(record),
        }
    }

    #[inline]
    fn flush(&self) {
        match self {
            Chain::Stdout(chain) => chain.flush(),
            Chain::Stderr(chain) => chain.flush(),
            // Chain::String(chain) => chain.flush(),
            Chain::File(chain) => chain.flush(),
        }
    }
}

// *

pub type ColorMode = bool;

pub struct Dispatcher {
    pub chains: Vec<(Chain, log::LevelFilter)>,
    pub filter_only_self: bool,
}

impl Dispatcher {
    #[inline]
    pub fn new() -> Self {
        Self {
            chains: Vec::new(),
            filter_only_self: false,
        }
    }

    #[inline]
    pub fn chain<T>(mut self, chain: T, level: log::LevelFilter) -> Self
    where
        T: Into<Chain>,
    {
        self.chains.push((chain.into(), level));
        self
    }

    #[inline]
    pub fn try_chain<T>(mut self, chain: Option<T>, level: log::LevelFilter) -> Self
    where
        T: Into<Chain>,
    {
        if let Some(chain) = chain {
            self.chains.push((chain.into(), level));
        }

        self
    }

    #[inline]
    pub fn filter_only_self(mut self, is: bool) -> Self {
        self.filter_only_self = is;
        self
    }

    #[inline]
    fn format_msg(record: &log::Record, colored: ColorMode) -> String {
        let level: log::Level = record.level();
        let level_color: Color = match level {
            log::Level::Error => Color::BrightRed,
            log::Level::Warn => Color::BrightYellow,
            log::Level::Info => Color::BrightWhite,
            log::Level::Debug => Color::BrightBlack,
            log::Level::Trace => Color::BrightCyan,
        };

        let _fmt: String = format!(
            "\x1b[1;{}m{}\x1b[0m\x1b[1m:\x1b[0m {}",
            // Local::now().format("%Y-%m-%d %H:%M:%S%.3f"),
            level_color.to_fg_str(),
            level.as_str().to_ascii_lowercase(),
            record.args()
        );

        if colored {
            _fmt
        } else {
            (&*_fmt).clear().to_string()
        }
    }

    #[inline]
    pub fn apply(self) -> Result<(), log::SetLoggerError> {
        let max_level: log::LevelFilter = self
            .chains
            .iter()
            .map(|chain| chain.1)
            .max()
            .unwrap_or(log::LevelFilter::Trace);

        log::set_boxed_logger(Box::new(self))?;
        log::set_max_level(max_level);

        Ok(())
    }
}

impl log::Log for Dispatcher {
    fn enabled(&self, metadata: &log::Metadata) -> bool {
        (if self.filter_only_self {
            metadata.target().starts_with(env!("CARGO_CRATE_NAME"))
        } else {
            true
        }) && self.chains.iter().any(|chain| metadata.level() <= chain.1)
    }

    fn log(&self, record: &log::Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        for chain in self.chains.iter() {
            if record.level() <= chain.1 {
                chain.0.log(record);
            }
        }
    }

    fn flush(&self) {
        for chain in self.chains.iter() {
            chain.0.flush();
        }
    }
}

// *

pub trait OptionExt<T> {
    fn unwrap_or_log(self, msg: &str) -> T;
}

impl<T> OptionExt<T> for Option<T> {
    #[inline]
    #[track_caller]
    fn unwrap_or_log(self, msg: &str) -> T {
        match self {
            Some(value) => value,
            None => {
                log::error!("{}", msg);
                std::process::exit(1)
            }
        }
    }
}

pub trait ResultExt<T, E> {
    fn unwrap_or_log(self, msg: &str) -> T
    where
        E: Debug;
}

impl<T, E: Debug> ResultExt<T, E> for Result<T, E> {
    #[inline]
    #[track_caller]
    fn unwrap_or_log(self, msg: &str) -> T {
        match self {
            Ok(value) => value,
            Err(error) => {
                log::error!("{}: {:?}", msg, error);
                std::process::exit(1)
            }
        }
    }
}
