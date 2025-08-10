#[allow(unused_imports)]
use core::fmt;

use crate::error::DialectError;

/// Represents a variable-length word stored in a fixed-size, 16-byte buffer.
///
/// The data within the buffer is not guaranteed to be null-terminated.
#[derive(Debug)]
pub struct PatternWord {
    pub length: usize,
    pub buffer: [u8; 16],
}

impl PatternWord {
    pub fn new() -> Self {
        PatternWord {
            length: 0,
            buffer: [b'\0'; 16],
        }
    }
}

impl AsRef<str> for PatternWord {
    fn as_ref(&self) -> &str {
        str::from_utf8(&self.buffer[..self.length])
            .map_err(|_| DialectError::NonUtf8Payload)
            .unwrap()
    }
}

/// Represents a pattern with a fixed number of chunks.
///
/// # Parameters
///
/// * `N` - Number of pattern chunks in range \[2, 6]
pub struct Pattern<const N: usize> {
    chunks: [u8; N],
    lookup_table: [u8; 256],
}

impl<const N: usize> Pattern<N> {
    const SENTINEL: u8 = u8::MAX;

    const fn construct_table(chunks: [u8; N]) -> [u8; 256] {
        let mut lookup_table: [u8; 256] = [Self::SENTINEL; 256];

        // Since usage of iterators are limited in const-fn context
        // using weirdo while-loop is necessary.
        let mut i: usize = 0;

        while i < chunks.len() {
            lookup_table[chunks[i] as usize] = i as u8;
            i += 1;
        }

        lookup_table
    }

    const fn is_distinct(chunks: [u8; N]) -> bool {
        let mut seen_table: [bool; 256] = [false; 256];
        let mut i: usize = 0;

        while i < chunks.len() {
            let chunk: usize = chunks[i] as usize;

            if seen_table[chunk] {
                return false;
            }

            seen_table[chunk] = true;
            i += 1;
        }

        true
    }

    /// Construct a new `Pattern` from a fixed-size array.
    ///
    /// # Panics
    ///
    /// - If the length of `chunks` is not in the range \[2, 6].
    /// - If elements of `chunks` is not distinct.
    pub const fn from(chunks: [u8; N]) -> Self {
        assert!(
            chunks.len() > 1 && chunks.len() <= 6,
            "Pattern::from requires chunks length to be within the range [2, 6]"
        );
        assert!(
            Self::is_distinct(chunks),
            "Pattern::from requires chunks elements to be distinct"
        );

        Self {
            chunks,
            lookup_table: Self::construct_table(chunks),
        }
    }

    /// Construct a new `Pattern` from a fixed-size array, without checking.
    pub const unsafe fn from_unchecked(chunks: [u8; N]) -> Self {
        Self {
            chunks,
            lookup_table: Self::construct_table(chunks),
        }
    }

    /// Construct a new `Pattern` from a slice of bytes.
    #[cfg(feature = "from_bytes")]
    pub fn from_bytes(chunks: impl AsRef<[u8]>) -> Option<Self> {
        let chunks: [u8; N] = *chunks.as_ref().as_array::<N>()?;

        Some(Self {
            chunks,
            lookup_table: Self::construct_table(chunks),
        })
    }

    pub const fn chunks_len(&self) -> usize {
        N
    }

    const fn encode_capacity_even_distribution(&self, bits: u8) -> usize {
        let bits_per_chunk: usize = 6 / N;
        let mask: u8 = (1u8 << bits_per_chunk) - 1;

        let (mut chunk_idx, mut capacity) = (0usize, 0usize);

        while chunk_idx < N {
            capacity += (((bits >> ((N - chunk_idx - 1) * bits_per_chunk)) & mask) + 1) as usize;
            chunk_idx += 1;
        }

        capacity
    }

    const fn encode_capacity_uneven_distribution(&self, bits: u8) -> usize {
        let dbits_count: usize = 6 % N;
        let (mut bits_idx, mut capacity) = (0usize, 0usize);

        // Chunks that get 2 bits each
        while bits_idx < dbits_count {
            capacity += (((bits >> (4 - (bits_idx * 2))) & 0x03) + 1) as usize;
            bits_idx += 1;
        }

        let remaining_count: usize = 6 - (dbits_count * 2);
        bits_idx = 0;

        // Remaining chunks that get 1 bit each
        while bits_idx < remaining_count {
            capacity += (((bits >> (remaining_count - bits_idx - 1)) & 0x01) + 1) as usize;
            bits_idx += 1;
        }

        capacity
    }

    #[inline]
    pub const fn measure_encode_capacity(&self, bits: u8) -> usize {
        if 6 % N == 0 {
            self.encode_capacity_even_distribution(bits)
        } else {
            self.encode_capacity_uneven_distribution(bits)
        }
    }

    #[inline(always)]
    fn encode_even_distribution(&self, bits: u8, buffer: &mut [u8; 16]) -> usize {
        let bits_per_chunk: usize = 6 / N;
        let mask: u8 = (1 << bits_per_chunk) - 1;
        let mut pos: usize = 0;

        for (i, &chunk) in self.chunks.iter().enumerate() {
            let chunk_len: usize = usize::from(((bits >> (N - i - 1) * bits_per_chunk) & mask) + 1);

            unsafe {
                buffer.get_unchecked_mut(pos..pos + chunk_len).fill(chunk);
            }

            pos += chunk_len;
        }

        pos
    }

    #[inline(always)]
    fn encode_uneven_distribution(&self, bits: u8, buffer: &mut [u8; 16]) -> usize {
        let dbits_count: usize = 6 % N;
        let mut pos: usize = 0;

        // Chunks that get 2 bits each
        for i in 0..dbits_count {
            let chunk_len: usize = usize::from(((bits >> 4 - (i * 2)) & 0x03) + 1);

            unsafe {
                buffer
                    .get_unchecked_mut(pos..pos + chunk_len)
                    .fill(self.chunks[i]);
            }

            pos += chunk_len;
        }

        let remaining_count: usize = 6 - (dbits_count * 2);

        // Remaining chunks that get 1 bit each
        for i in 0..remaining_count {
            let chunk_len: usize = usize::from(((bits >> remaining_count - i - 1) & 0x01) + 1);

            unsafe {
                buffer
                    .get_unchecked_mut(pos..pos + chunk_len)
                    .fill(self.chunks[dbits_count + i]);
            }

            pos += chunk_len;
        }

        pos
    }

    /// Encodes a 6-bit value into a character pattern.
    ///
    /// The encoding distributes the bits across `N` chunks, where each chunk
    /// determines the repeat count for its corresponding character.
    #[inline]
    pub fn encode(&self, bits: u8) -> PatternWord {
        let mut word: PatternWord = PatternWord::new();

        word.length = if 6 % N == 0 {
            self.encode_even_distribution(bits, &mut word.buffer)
        } else {
            self.encode_uneven_distribution(bits, &mut word.buffer)
        };

        word
    }

    #[inline(always)]
    fn decode_even_distribution(&self, chunk_count: &[u8; N]) -> u8 {
        let mut bits: u8 = 0u8;

        let bits_per_chunk: usize = 6 / N;
        let mask: u8 = (1 << bits_per_chunk) - 1;

        for (i, &chunk_count) in chunk_count.iter().enumerate() {
            let chunk_bits: u8 = (chunk_count - 1) & mask;
            bits |= chunk_bits << (N - i - 1) * bits_per_chunk;
        }

        bits
    }

    #[inline(always)]
    fn decode_uneven_distribution(&self, chunk_count: &[u8; N]) -> u8 {
        let mut bits: u8 = 0u8;
        let dbits_count: usize = 6 % N;

        // Chunks that get 2 bits each
        for i in 0..dbits_count {
            let chunk_bits: u8 = (chunk_count[i] - 1) & 0x03;
            bits |= chunk_bits << 4 - (i * 2);
        }

        let remaining_count: usize = 6 - (dbits_count * 2);

        // Remaining chunks that get 1 bit each
        for i in 0..remaining_count {
            let chunk_bits: u8 = (chunk_count[dbits_count + i] - 1) & 0x01;
            bits |= chunk_bits << remaining_count - i - 1;
        }

        bits
    }

    /// Decodes a character pattern into a 6-bit value.
    ///
    /// The decoding distributes the bits across `N` chunks, where each chunk
    /// determines the repeat count for its corresponding character.
    #[inline]
    pub fn decode(&self, word: impl AsRef<str>) -> u8 {
        let word: &str = word.as_ref();
        let mut chunk_count: [u8; N] = [0; N];

        for word_chunk in word.chars() {
            let chunk_index: u8 = self.lookup_table[word_chunk as usize];

            if chunk_index != Self::SENTINEL {
                unsafe {
                    *chunk_count.get_unchecked_mut(usize::from(chunk_index)) += 1;
                }
            }
        }

        if 6 % N == 0 {
            self.decode_even_distribution(&chunk_count)
        } else {
            self.decode_uneven_distribution(&chunk_count)
        }
    }
}

#[cfg(feature = "std")]
impl<const N: usize> fmt::Debug for Pattern<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Pattern")
            .field("chunks", &str::from_utf8(&self.chunks))
            .field("lookup_table", &format_args!("[... 256 bytes ...]"))
            .finish()
    }
}

macro_rules! impl_variable_pattern {
    (
        $(#[$outer:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$inner:meta])*
                $variant:ident($inner_ty:ty)
            ),*
            $(,)?
        }
    ) => {
        $(#[$outer])*
        $vis enum $name {
            $(
                $(#[$inner])*
                $variant($inner_ty),
            )*
        }

        impl $name {
            pub const fn measure_encode_capacity(&self, bits: u8) -> usize {
                match self {
                    $( Self::$variant(p) => p.measure_encode_capacity(bits), )*
                }
            }

            pub fn encode(&self, bits: u8) -> PatternWord {
                match self {
                    $( Self::$variant(p) => p.encode(bits), )*
                }
            }

            pub fn decode(&self, word: impl AsRef<str>) -> u8 {
                match self {
                    $( Self::$variant(p) => p.decode(word), )*
                }
            }

            pub const fn chunks_len(&self) -> usize {
                match self {
                    $( Self::$variant(p) => p.chunks_len(), )*
                }
            }
        }
    };
}

impl_variable_pattern! {
    /// Represents a pattern with a variable number of chunks.
    #[cfg_attr(feature = "std", derive(Debug))]
    pub enum VariablePattern {
        /// Pattern with 2 chunks.
        Binary(Pattern<2>),
        /// Pattern with 3 chunks.
        Ternary(Pattern<3>),
        /// Pattern with 4 chunks.
        Quaternary(Pattern<4>),
        /// Pattern with 5 chunks.
        Quinary(Pattern<5>),
        /// Pattern with 6 chunks.
        Senary(Pattern<6>),
    }
}
