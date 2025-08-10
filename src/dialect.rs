use crate::{error::DialectError, pattern::VariablePattern};

/// Represents a dialect with a fixed number of patterns.
///
/// # Parameters
///
/// * `N` - Number of patterns
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Dialect<const N: usize> {
    pub patterns: [VariablePattern; N],
}

impl<const N: usize> Dialect<N> {
    pub const fn new(patterns: [VariablePattern; N]) -> Self {
        Self { patterns }
    }

    pub const fn measure_encode_capacity(&self, payload: &[u8]) -> usize {
        let (mut pattern_idx, mut i) = (0usize, 0usize);
        let mut capacity: usize = 0;

        while i < payload.len() {
            let remaining: usize = payload.len() - i;
            let chunk_size: usize = if remaining >= 3 { 3 } else { remaining };

            let groups: &[u8] = match chunk_size {
                3 => &[
                    // Bits 23-18
                    (((((payload[i] as u32) << 16)
                        | ((payload[i + 1] as u32) << 8)
                        | (payload[i + 2] as u32))
                        >> 18)
                        & 0x3f) as u8,
                    // Bits 17-12
                    (((((payload[i] as u32) << 16)
                        | ((payload[i + 1] as u32) << 8)
                        | (payload[i + 2] as u32))
                        >> 12)
                        & 0x3f) as u8,
                    // Bits 11-6
                    (((((payload[i] as u32) << 16)
                        | ((payload[i + 1] as u32) << 8)
                        | (payload[i + 2] as u32))
                        >> 6)
                        & 0x3f) as u8,
                    // Bits 5-0
                    ((((payload[i] as u32) << 16)
                        | ((payload[i + 1] as u32) << 8)
                        | (payload[i + 2] as u32))
                        & 0x3f) as u8,
                ],
                2 => &[
                    // Bits 15-10
                    (((((payload[i] as u16) << 8) | (payload[i + 1] as u16)) >> 10) & 0x3f) as u8,
                    // Bits 9-4
                    (((((payload[i] as u16) << 8) | (payload[i + 1] as u16)) >> 4) & 0x3f) as u8,
                    // Bits 3-0
                    ((((payload[i] as u16) << 8) | (payload[i + 1] as u16)) & 0xf) as u8,
                ],
                1 => &[(payload[i] >> 4) & 0x0f, payload[i] & 0x0f],
                _ => &[],
            };

            let mut group_idx: usize = 0;

            while group_idx < groups.len() {
                let bits: u8 = groups[group_idx];
                let pattern: &VariablePattern = &self.patterns[pattern_idx % self.patterns.len()];

                capacity += pattern.measure_encode_capacity(bits) + 1;
                pattern_idx += 1;
                group_idx += 1;
            }

            i += chunk_size;
        }

        capacity
    }

    /// Encodes a byte slice into a pre-allocated buffer using the dialect's patterns.
    ///
    /// This is the core, `no_std`-compatible encoding function. It processes the
    /// input `payload` in chunks, distributing the bits from each chunk across a
    /// series of words according to the dialect's patterns. These words are then
    /// written sequentially into the output `buffer`.
    ///
    /// # Parameters
    ///
    /// * `payload`: The raw byte slice to be encoded.
    /// * `buffer`: A mutable byte slice that will receive the encoded output. Its
    ///   length must be sufficient to hold the entire encoded message. Use
    ///   [`Dialect::measure_encode_capacity`] to determine the required size.
    ///
    /// # Returns
    ///
    /// A `Result` which is:
    /// * `Ok(usize)`: The number of bytes written to the `buffer`.
    /// * `Err(DialectError)`: If an error occurs during encoding.
    ///
    /// # Errors
    /// * [`DialectError::BufferExhausted`]: If the provided `buffer` is too small
    ///   to hold the encoded data.
    ///
    /// # Examples
    ///
    /// ```
    /// use seqc::{Dialect, Pattern, VariablePattern};
    ///
    /// const DIALECT: Dialect<1> = Dialect::new([
    ///     VariablePattern::Binary(Pattern::from([b'0', b'1'])),
    /// ]);
    ///
    /// const DATA: &[u8] = &[0xB4];
    ///
    /// let mut buffer = [0u8; DIALECT.measure_encode_capacity(DATA)];
    /// let bytes_written = DIALECT.encode_slice(DATA, &mut buffer).unwrap();
    ///
    /// // The output reflects the bit distribution for the single byte.
    /// assert_eq!(bytes_written, 14);
    /// assert_eq!(&buffer[..bytes_written], b"001111 011111 ");
    /// ```
    pub fn encode_slice(&self, payload: &[u8], buffer: &mut [u8]) -> Result<usize, DialectError> {
        let (mut pattern_idx, mut buffer_idx) = (0usize, 0usize);

        macro_rules! write_word {
            ($bits:expr) => {
                let pattern = &self.patterns[pattern_idx % N];
                pattern_idx += 1;

                let word = pattern.encode($bits);

                if buffer_idx + word.length > buffer.len() {
                    return Err(DialectError::BufferExhausted);
                }

                buffer[buffer_idx..buffer_idx + word.length]
                    .copy_from_slice(&word.buffer[..word.length]);
                buffer_idx += word.length;

                buffer[buffer_idx] = b' ';
                buffer_idx += 1;
            };
        }

        for bytes in payload.chunks(3) {
            match bytes.len() {
                // Process 3 bytes (24 bits), producing 4 words
                3 => {
                    let packed_value: u32 = (u32::from(bytes[0]) << 16)
                        | (u32::from(bytes[1]) << 8)
                        | u32::from(bytes[2]);

                    let group0: u8 = ((packed_value >> 18) & 0x3f) as u8; // Bits 23-18
                    let group1: u8 = ((packed_value >> 12) & 0x3f) as u8; // Bits 17-12
                    let group2: u8 = ((packed_value >> 6) & 0x3f) as u8; // Bits 11-6
                    let group3: u8 = (packed_value & 0x3f) as u8; // Bits 5-0

                    write_word!(group0);
                    write_word!(group1);
                    write_word!(group2);
                    write_word!(group3);
                }
                // Process 2 bytes (16 bits), producing 3 words
                2 => {
                    let packed_value: u16 = (u16::from(bytes[0]) << 8) | u16::from(bytes[1]);

                    // Split into groups: 6 bits, 6 bits, 4 bits
                    let group0: u8 = ((packed_value >> 10) & 0x3f) as u8; // Bits 15-10
                    let group1: u8 = ((packed_value >> 4) & 0x3f) as u8; // Bits 9-4
                    let group2: u8 = (packed_value & 0xf) as u8; // Bits 3-0

                    write_word!(group0);
                    write_word!(group1);
                    write_word!(group2);
                }
                // Process 1 byte (8 bits), producing 2 words
                1 => {
                    let hi_bits: u8 = (bytes[0] >> 4) & 0x0f;
                    let lo_bits: u8 = bytes[0] & 0x0f;

                    write_word!(hi_bits);
                    write_word!(lo_bits);
                }
                _ => unreachable!(),
            }
        }

        Ok(buffer_idx)
    }

    /// Decodes a slice of space-separated words into a pre-allocated buffer.
    ///
    /// This is the core, `no_std`-compatible decoding function. It interprets the
    /// `payload` as a UTF-8 string of words separated by spaces. It processes the
    /// words in groups, reconstructing the original byte chunks by collecting bits
    /// from each word according to the dialect's patterns. The resulting raw bytes
    /// are written to the output `buffer`.
    ///
    /// # Parameters
    ///
    /// * `payload`: The encoded byte slice. Must contain valid UTF-8 characters.
    /// * `buffer`: A mutable byte slice that will receive the decoded raw bytes.
    ///   Its length should be sufficient to hold the output.
    ///
    /// # Returns
    ///
    /// A `Result` which is:
    /// * `Ok(usize)`: The number of decoded bytes written to the `buffer`.
    /// * `Err(DialectError)`: If an error occurs during decoding.
    ///
    /// # Errors
    ///
    /// * [`DialectError::NonUtf8Payload`]: If the `payload` is not a valid UTF-8 string.
    /// * [`DialectError::UnexpectedRemainder`]: If the `payload` contains a number of
    ///   words that cannot be fully decoded back.
    ///
    /// # Examples
    ///
    /// ```
    /// use seqc::{Dialect, Pattern, VariablePattern};
    ///
    /// let dialect: Dialect<2> = Dialect::new([
    ///     VariablePattern::Ternary(Pattern::from([b'a', b'b', b'c'])),
    ///     VariablePattern::Quaternary(Pattern::from([b'x', b'y', b'z', b'w'])),
    /// ]);
    ///
    /// const ENCODED: &str = "aaabbbccc xxxyyyzzww aaabbbbcccc xyyyyzw abbbbcc xyyyyzww ";
    ///
    /// let mut buffer = [0u8; ENCODED.len()];
    /// let bytes_written = dialect.decode_slice(ENCODED.as_bytes(), &mut buffer).unwrap();
    ///
    /// assert_eq!(bytes_written, 4);
    /// assert_eq!(&buffer[..bytes_written], &[0xAA, 0xBB, 0xCC, 0xDD]);
    /// ```
    pub fn decode_slice(&self, payload: &[u8], buffer: &mut [u8]) -> Result<usize, DialectError> {
        let (mut pattern_idx, mut buffer_idx) = (0usize, 0usize);

        let payload_str: &str =
            str::from_utf8(payload).map_err(|_| DialectError::NonUtf8Payload)?;

        let mut chunks_iter = payload_str.split_ascii_whitespace().array_chunks::<4>();

        macro_rules! decode_word {
            ($word:expr) => {
                (|pattern_idx: &mut usize| {
                    let pattern = &self.patterns[*pattern_idx % N];
                    *pattern_idx += 1;

                    pattern.decode($word)
                })(&mut pattern_idx)
            };
        }

        macro_rules! write_bytes {
            ($bytes:expr) => {
                buffer[buffer_idx..buffer_idx + $bytes.len()].copy_from_slice($bytes);
                buffer_idx += $bytes.len();
            };
        }

        // Process 4 words, producing 3 bytes (24 bits)
        while let Some(bytes) = chunks_iter.next() {
            let group0: u8 = decode_word!(bytes[0]);
            let group1: u8 = decode_word!(bytes[1]);
            let group2: u8 = decode_word!(bytes[2]);
            let group3: u8 = decode_word!(bytes[3]);

            let bits0: u8 = group0 & 0x3f;
            let bits1: u8 = group1 & 0x3f;
            let bits2: u8 = group2 & 0x3f;
            let bits3: u8 = group3 & 0x3f;

            // Assemble full 24-bit value
            let packed_value: u32 = (u32::from(bits0) << 18)
                | (u32::from(bits1) << 12)
                | (u32::from(bits2) << 6)
                | u32::from(bits3);

            // Extract 3 bytes
            let byte0: u8 = ((packed_value >> 16) & 0xff) as u8;
            let byte1: u8 = ((packed_value >> 8) & 0xff) as u8;
            let byte2: u8 = (packed_value & 0xff) as u8;

            write_bytes!(&[byte0, byte1, byte2]);
        }

        let remainder = chunks_iter.into_remainder().unwrap();
        let remainder_slice: &[&str] = remainder.as_slice();

        match remainder.len() {
            // Process 3 words, producing 2 bytes (16 bits)
            3 => {
                let group0: u8 = decode_word!(remainder_slice[0]);
                let group1: u8 = decode_word!(remainder_slice[1]);
                let group2: u8 = decode_word!(remainder_slice[2]);

                let bits0: u8 = group0 & 0x3f; // 6 bits
                let bits1: u8 = group1 & 0x3f; // 6 bits
                let bits2: u8 = group2 & 0xf; // 4 bits

                // Assemble 16-bit value
                let packed_value: u32 =
                    (u32::from(bits0) << 10) | (u32::from(bits1) << 4) | u32::from(bits2);

                // Extract 2 bytes
                let byte0: u8 = ((packed_value >> 8) & 0xff) as u8;
                let byte1: u8 = (packed_value & 0xff) as u8;

                write_bytes!(&[byte0, byte1]);
            }
            // Process 2 words, producing 1 byte (8 bits)
            2 => {
                let hi_group: u8 = decode_word!(remainder_slice[0]);
                let lo_group: u8 = decode_word!(remainder_slice[1]);

                // Assemble 8-bit value
                let hi_bits: u8 = hi_group & 0xf; // 4 bits
                let lo_bits: u8 = lo_group & 0xf; // 4 bits

                // Extract byte
                let byte: u8 = (hi_bits << 4) | lo_bits;

                write_bytes!(&[byte]);
            }
            0 => (),
            _ => return Err(DialectError::UnexpectedRemainder),
        }

        Ok(buffer_idx)
    }

    /// Encodes a byte slice into a new `Vec<u8>` using the dialect's pattern.
    ///
    /// This method provides a convenient, high-level interface for encoding. It first
    /// calculates the exact required buffer size, allocates a `Vec<u8>`, and then
    /// processes the input payload by distributing bits across chunks (e.g., even or
    /// uneven distribution). This function is only available when the `std` feature
    /// is enabled.
    ///
    /// # Parameters
    ///
    /// * `payload`: A type that can be referenced as a byte slice
    ///   containing the raw data to be encoded.
    ///
    /// # Returns
    ///
    /// A `Vec<u8>` containing the encoded, human-readable data.
    ///
    /// # Examples
    ///
    /// ```
    /// use seqc::{Dialect, Pattern, VariablePattern};
    ///
    /// let dialect: Dialect<2> = Dialect::new([
    ///     VariablePattern::Ternary(Pattern::from([b'a', b'b', b'c'])),
    ///     VariablePattern::Quaternary(Pattern::from([b'x', b'y', b'z', b'w'])),
    /// ]);
    ///
    /// let data = vec![0xAA, 0xBB, 0xCC, 0xDD];
    /// let encoded = dialect.encode(&data);
    ///
    /// assert_eq!(
    ///     &*String::from_utf8_lossy(&encoded),
    ///     "aaabbbccc xxxyyyzzww aaabbbbcccc xyyyyzw abbbbcc xyyyyzww "
    /// );
    ///
    /// ```
    #[cfg(feature = "std")]
    pub fn encode(&self, payload: impl AsRef<[u8]>) -> Vec<u8> {
        let payload: &[u8] = payload.as_ref();
        let mut buffer: Vec<u8> = vec![0u8; self.measure_encode_capacity(payload)];

        // SAFETY: Since the buffer is pre-allocated with the measured encoded size,
        // we can guarantee that [`Dialect::encode_slice`] will not throw.
        self.encode_slice(payload, &mut buffer)
            .map(|x| {
                unsafe { buffer.set_len(x) };
                buffer.shrink_to_fit();

                buffer
            })
            .unwrap()
    }

    /// Decodes a slice of space-separated words back into a new `Vec<u8>`.
    ///
    /// This high-level method provides a convenient interface for decoding. It
    /// allocates a `Vec<u8>` and processes the input payload, which is expected to
    /// be a UTF-8 string of words separated by spaces. It reconstructs the original
    /// raw bytes by interpreting the words according to the dialect's patterns. This
    /// function is only available when the `std` feature is enabled.
    ///
    /// # Parameters
    ///
    /// * `payload`: A type that can be referenced as a byte slice
    ///   containing the encoded, space-separated words.
    ///
    /// # Returns
    ///
    /// A `Result` which is:
    /// * `Ok(Vec<u8>)`: A new vector containing the decoded raw data.
    /// * `Err(DialectError)`: If an error occurs during decoding.
    ///
    /// # Errors
    ///
    /// This function can fail if the input payload is not valid UTF-8 or if it
    /// contains a number of words that cannot be decoded back into bytes using
    /// dialect's patterns.
    ///
    /// # Examples
    ///
    /// ```
    /// use seqc::{Dialect, Pattern, VariablePattern};
    ///
    /// let dialect: Dialect<2> = Dialect::new([
    ///     VariablePattern::Ternary(Pattern::from([b'a', b'b', b'c'])),
    ///     VariablePattern::Quaternary(Pattern::from([b'x', b'y', b'z', b'w'])),
    /// ]);
    ///
    /// // Corresponds to the encoded form of `[0xAA, 0xBB, 0xCC, 0xDD]`
    /// let encoded_data = b"aaabbbccc xxxyyyzzww aaabbbbcccc xyyyyzw abbbbcc xyyyyzww ";
    /// let decoded = dialect.decode(encoded_data).unwrap();
    ///
    /// assert_eq!(decoded, vec![0xAA, 0xBB, 0xCC, 0xDD]);
    /// ```
    #[cfg(feature = "std")]
    pub fn decode(&self, payload: impl AsRef<[u8]>) -> Result<Vec<u8>, DialectError> {
        let payload: &[u8] = payload.as_ref();
        let mut buffer: Vec<u8> = vec![0u8; payload.len()];

        self.decode_slice(payload, &mut buffer).map(|x| {
            unsafe { buffer.set_len(x) };
            buffer.shrink_to_fit();

            buffer
        })
    }
}

macro_rules! impl_variable_dialect {
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
            pub const fn measure_encode_capacity(&self, payload: &[u8]) -> usize {
                match self {
                    $( Self::$variant(p) => p.measure_encode_capacity(payload), )*
                }
            }

            pub fn encode_slice(&self, payload: &[u8], buffer: &mut [u8]) -> Result<usize, DialectError> {
                match self {
                    $( Self::$variant(p) => p.encode_slice(payload, buffer), )*
                }
            }

            pub fn decode_slice(&self, payload: &[u8], buffer: &mut [u8]) -> Result<usize, DialectError> {
                match self {
                    $( Self::$variant(p) => p.decode_slice(payload, buffer), )*
                }
            }

            #[cfg(feature = "std")]
            pub fn encode(&self, payload: impl AsRef<[u8]>) -> Vec<u8> {
                match self {
                    $( Self::$variant(p) => p.encode(payload), )*
                }
            }

            #[cfg(feature = "std")]
            pub fn decode(&self, payload: impl AsRef<[u8]>) -> Result<Vec<u8>, DialectError> {
                match self {
                    $( Self::$variant(p) => p.decode(payload), )*
                }
            }
        }
    };
}

// todo! think about ambiguous size fix due `lookup_table`
impl_variable_dialect! {
    /// Represents a dialect with a variable number of patterns.
    #[cfg_attr(feature = "std", derive(Debug))]
    #[allow(clippy::large_enum_variant)]
    pub enum VariableDialect {
        /// Dialect with 1 pattern.
        Unary(Dialect<1>),
        /// Dialect with 2 patterns.
        Binary(Dialect<2>),
        /// Dialect with 3 patterns.
        Ternary(Dialect<3>),
        /// Dialect with 4 patterns.
        Quaternary(Dialect<4>),
        /// Dialect with 5 patterns.
        Quinary(Dialect<5>),
        /// Dialect with 6 patterns.
        Senary(Dialect<6>),
    }
}
