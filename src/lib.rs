#![feature(iter_array_chunks)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "from_bytes", feature(slice_as_array))]

//! Seqc is a pattern-based encoding library for encoding binary data into human-readable patterns of repeated characters,
//! creating textual representations that resemble visual or rhythmic sequences. It transforms raw bytes into
//! space-separated "words" composed of repeating symbols, where repetition counts encode the original bit patterns.
//!
//! The library supports customizable "dialects" that define the characters and patterns used, making it flexible
//! for various encoding needs. It is `no_std` compatible by default, with optional `std` features for convenience
//! functions like vector-based encoding and decoding.
//!
//! # How to use Seqc
//!
//! There are two primary ways to use Seqc:
//!
//! - **High-level encoding and decoding** with dialects provides the simplest interface for most users.
//!   - Use [`Dialect<N>`] or [`VariableDialect<N>`] to define patterns and perform encoding/decoding operations.
//!   - The [`encode`] and [`decode`] methods (available with `std` feature) handle vector-based operations efficiently.
//!   - For `no_std` environments, use [`encode_slice`] and [`decode_slice`] for direct buffer manipulation.
//! - **Custom patterns** allow fine-grained control over encoding logic.
//!   - Define individual [`Pattern<N>`] instances with 2 to 6 distinct characters.
//!   - Combine patterns into [`VariablePattern<N>`] and dialects for variable-length encoding schemes.
//!   - Use [`encode`] and [`decode`] on patterns for low-level bit manipulation.
//!
//! [`encode`]: dialect/struct.Dialect.html#method.encode
//! [`decode`]: dialect/struct.Dialect.html#method.decode
//! [`encode_slice`]: dialect/struct.Dialect.html#method.encode_slice
//! [`decode_slice`]: dialect/struct.Dialect.html#method.decode_slice
//!
//! # Usage
//!
//! First, add `seqc` to your `Cargo.toml` with `std` feature enabled.
//!
//! Next, to use pattern-based encoding, create a dialect with desired
//! patterns and apply it to your data:
//!
//! ```
//! let dialect: Dialect<2> = Dialect::new([
//!     VariablePattern::Ternary(Pattern::from([b'a', b'b', b'c'])),
//!     VariablePattern::Quaternary(Pattern::from([b'x', b'y', b'z', b'w'])),
//! ]);
//!
//! let data = vec![0xAA, 0xBB, 0xCC, 0xDD];
//! let encoded = dialect.encode(&data);
//! let decoded = dialect.decode(&encoded).unwrap();
//!
//! assert_eq!(str::from_utf8(&encoded).unwrap(),
//!     "aaabbbccc xxxyyyzzww aaabbbbcccc xyyyyzw abbbbcc xyyyyzww "
//! );
//! assert_eq!(decoded, data);
//! ```
//!
//! For `no_std` usage, pre-allocate buffers based on measured capacity:
//!
//! ```
//! use seq::{Dialect, Pattern, VariablePattern};
//!
//! const DIALECT: Dialect<1> = Dialect::new([
//!     VariablePattern::Binary(Pattern::from([b'0', b'1'])),
//! ]);
//!
//! const DATA: &[u8] = &[0xB4];
//!
//! let mut buffer = [0u8; DIALECT.measure_encode_capacity(DATA)];
//! let bytes_written = DIALECT.encode_slice(DATA, &mut buffer).unwrap();
//!
//! assert_eq!(bytes_written, 14);
//! assert_eq!(&buffer[..bytes_written], b"001111 011111 ");
//! ```
//!
//! # Crate Layout
//!
//! The main types are organized as follows:
//! - [`Pattern<N>`]: Defines fixed-chunk patterns for encoding 6-bit values.
//! - [`VariablePattern<N>`]: Enum for patterns with varying chunk counts (2-6).
//! - [`Dialect<N>`]: Fixed-number pattern collections for encoding.
//! - [`VariableDialect<N>`]: Enum for dialects with varying pattern counts (1-6).
//! - [`PatternWord`]: Represents encoded words in a fixed buffer.
//! - [`DialectError`]: Errors for encoding/decoding operations.
//!
//! Utility functions like [`Dialect::measure_encode_capacity`] help with buffer sizing.
//!
//! # Edge Cases and Testing
//!
//! Seqc handles empty inputs, single bytes, and variable lengths robustly. Extensive tests ensure
//! consistency, including round-trip verification and in-place decoding.
//!
//! For targets without `std`, the library relies on core features, maintaining compatibility.

pub mod dialect;
pub mod error;
pub mod pattern;

pub use dialect::{Dialect, VariableDialect};
pub use error::DialectError;
pub use pattern::{Pattern, PatternWord, VariablePattern};

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use super::{dialect::*, pattern::*};
    use core::slice;
    use rand::{self, Rng};

    #[test]
    fn test_pattern_consistency() {
        let pattern: Pattern<3> = Pattern::from([b'a', b'b', b'c']);

        for sample in 0..64u8 {
            let encoded: PatternWord = pattern.encode(sample);
            let decoded = pattern.decode(encoded);

            assert_eq!(sample, decoded);
        }
    }

    #[test]
    fn test_iterative_roundtrip_single_dialect() {
        const ITERATIONS: usize = 100;

        let dialect: Dialect<2> = Dialect::new([
            VariablePattern::Ternary(Pattern::<3>::from([b'a', b'b', b'c'])),
            VariablePattern::Quaternary(Pattern::<4>::from([b'x', b'y', b'z', b'w'])),
        ]);

        let mut rng: rand::prelude::ThreadRng = rand::rng();

        for _ in 0..ITERATIONS {
            let sample_size: usize = rng.random_range::<usize, _>(100..=1024);
            let sample_data: Vec<u8> = (&mut rng).random_iter::<u8>().take(sample_size).collect();

            let encoded: Vec<u8> = dialect.encode(&sample_data);
            let decoded: Vec<u8> = dialect.decode(&encoded).unwrap();

            assert!(encoded.len() != 0);
            assert_eq!(sample_data, decoded);
        }
    }

    #[test]
    fn test_decode_in_place() {
        let dialect: Dialect<2> = Dialect::new([
            VariablePattern::Ternary(Pattern::<3>::from([b'a', b'b', b'c'])),
            VariablePattern::Quaternary(Pattern::<4>::from([b'x', b'y', b'z', b'w'])),
        ]);

        let mut encoded: [u8; 58] = *b"aaabbbccc xxxyyyzzww aaabbbbcccc xyyyyzw abbbbcc xyyyyzww ";

        let in_ptr: *const u8 = &encoded as *const _ as *const u8;
        let out_ptr: *mut u8 = &mut encoded as *mut _ as *mut u8;

        let in_slice: &[u8] = unsafe { slice::from_raw_parts(in_ptr, encoded.len()) };
        let out_slice: &mut [u8] = unsafe { slice::from_raw_parts_mut(out_ptr, encoded.len()) };

        let bytes_written: usize = dialect.decode_slice(in_slice, out_slice).unwrap();

        assert_eq!(bytes_written, 4);
        assert_eq!(&encoded[..bytes_written], &[0xAA, 0xBB, 0xCC, 0xDD]);
    }

    #[test]
    fn test_edge_case_empty() {
        let dialect: Dialect<2> = Dialect::new([
            VariablePattern::Ternary(Pattern::<3>::from([b'a', b'b', b'c'])),
            VariablePattern::Quaternary(Pattern::<4>::from([b'x', b'y', b'z', b'w'])),
        ]);

        let sample_data: Vec<u8> = Vec::new();
        let encoded: Vec<u8> = dialect.encode(sample_data);

        assert!(encoded.is_empty());
    }

    #[test]
    fn test_edge_case_single_byte() {
        let dialect: Dialect<2> = Dialect::new([
            VariablePattern::Ternary(Pattern::<3>::from([b'a', b'b', b'c'])),
            VariablePattern::Quaternary(Pattern::<4>::from([b'x', b'y', b'z', b'w'])),
        ]);

        let sample_data: Vec<u8> = vec![255];

        let encoded: Vec<u8> = dialect.encode(&sample_data);
        let decoded: Vec<u8> = dialect.decode(&encoded).unwrap();

        assert_eq!(sample_data, decoded);
    }

    #[test]
    fn test_edge_case_double_byte() {
        let dialect: Dialect<2> = Dialect::new([
            VariablePattern::Ternary(Pattern::<3>::from([b'a', b'b', b'c'])),
            VariablePattern::Quaternary(Pattern::<4>::from([b'x', b'y', b'z', b'w'])),
        ]);

        let sample_data: Vec<u8> = vec![255, 63];

        let encoded: Vec<u8> = dialect.encode(&sample_data);
        let decoded: Vec<u8> = dialect.decode(&encoded).unwrap();

        assert_eq!(sample_data, decoded);
    }
}
