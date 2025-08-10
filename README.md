# seqc

Pattern-based encoding library for encoding binary data into human-readable patterns of repeated characters,
creating textual representations that resemble visual or rhythmic sequences. It transforms raw bytes into
space-separated "words" composed of repeating symbols, where repetition counts encode the original bit patterns.

The library supports customizable "dialects" that define the characters and patterns used, making it flexible
for various encoding needs. It is `no_std` compatible by default, with optional `std` features for convenience
functions like vector-based encoding and decoding.

## Usage

First, add `seqc` to your `Cargo.toml` with `std` feature enabled.

Next, to use pattern-based encoding, create a dialect with desired
patterns and apply it to your data:

```rust
let dialect: Dialect<2> = Dialect::new([
    VariablePattern::Ternary(Pattern::from([b'a', b'b', b'c'])),
    VariablePattern::Quaternary(Pattern::from([b'x', b'y', b'z', b'w'])),
]);

let data = vec![0xAA, 0xBB, 0xCC, 0xDD];
let encoded = dialect.encode(&data);
let decoded = dialect.decode(&encoded).unwrap();

assert_eq!(str::from_utf8(&encoded).unwrap(),
    "aaabbbccc xxxyyyzzww aaabbbbcccc xyyyyzw abbbbcc xyyyyzww "
);
assert_eq!(decoded, data);
```

For `no_std` usage, pre-allocate buffers based on measured capacity:

```rust
use seqc::{Dialect, Pattern, VariablePattern};

const DIALECT: Dialect<1> = Dialect::new([
    VariablePattern::Binary(Pattern::from([b'0', b'1'])),
]);

const DATA: &[u8] = &[0xB4];

let mut buffer = [0u8; DIALECT.measure_encode_capacity(DATA)];
let bytes_written = DIALECT.encode_slice(DATA, &mut buffer).unwrap();

assert_eq!(bytes_written, 14);
assert_eq!(&buffer[..bytes_written], b"001111 011111 ");
```
