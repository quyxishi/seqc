#[derive(Debug)]
pub enum DialectError {
    /// Payload consigned for decryption consists from non-utf8 characters.
    NonUtf8Payload,
    /// Output buffer is too small to fit encrypted/decrypted data.
    BufferExhausted,
    /// During decoding encountered unexpected remaining tail.
    UnexpectedRemainder,
}
