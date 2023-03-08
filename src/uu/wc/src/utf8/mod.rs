mod lossy;
mod read;

pub use lossy::LossyDecoder;
pub use read::{BufReadDecoder, BufReadDecoderError};

use std::cmp;
use std::error::Error;
use std::fmt;
use std::str;

///
/// Incremental, zero-copy UTF-8 decoding with error handling
///
/// The original implemention was written by Simon Sapin in the utf-8 crate (https://crates.io/crates/utf-8).
/// uu_wc used to depend on that crate.
/// The author archived the repository (https://github.com/SimonSapin/rust-utf8).
/// They suggested incorporating the source directly into uu_wc (https://github.com/uutils/coreutils/issues/4289).
///

/// The replacement character, U+FFFD. In lossy decoding, insert it for every decoding error.
pub const REPLACEMENT_CHARACTER: &'static str = "\u{FFFD}";

#[derive(Debug, Copy, Clone)]
pub enum DecodeError<'a> {
    /// In lossy decoding insert `valid_prefix`, then `"\u{FFFD}"`,
    /// then call `decode()` again with `remaining_input`.
    Invalid {
        valid_prefix: &'a str,
        invalid_sequence: &'a [u8],
        remaining_input: &'a [u8],
    },

    /// Call the `incomplete_suffix.try_complete` method with more input when available.
    /// If no more input is available, this is an invalid byte sequence.
    Incomplete {
        valid_prefix: &'a str,
        incomplete_suffix: Incomplete,
    },
}

impl<'a> fmt::Display for DecodeError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DecodeError::Invalid {
                valid_prefix,
                invalid_sequence,
                remaining_input,
            } => write!(
                f,
                "found invalid byte sequence {invalid_sequence:02x?} after \
                 {valid_byte_count} valid bytes, followed by {unprocessed_byte_count} more \
                 unprocessed bytes",
                invalid_sequence = invalid_sequence,
                valid_byte_count = valid_prefix.len(),
                unprocessed_byte_count = remaining_input.len()
            ),
            DecodeError::Incomplete {
                valid_prefix,
                incomplete_suffix,
            } => write!(
                f,
                "found incomplete byte sequence {incomplete_suffix:02x?} after \
                 {valid_byte_count} bytes",
                incomplete_suffix = incomplete_suffix,
                valid_byte_count = valid_prefix.len()
            ),
        }
    }
}

impl<'a> Error for DecodeError<'a> {}

#[derive(Debug, Copy, Clone)]
pub struct Incomplete {
    pub buffer: [u8; 4],
    pub buffer_len: u8,
}

pub fn decode(input: &[u8]) -> Result<&str, DecodeError> {
    let error = match str::from_utf8(input) {
        Ok(valid) => return Ok(valid),
        Err(error) => error,
    };

    // FIXME: separate function from here to guide inlining?
    let (valid, after_valid) = input.split_at(error.valid_up_to());
    let valid = unsafe { str::from_utf8_unchecked(valid) };

    match error.error_len() {
        Some(invalid_sequence_length) => {
            let (invalid, rest) = after_valid.split_at(invalid_sequence_length);
            Err(DecodeError::Invalid {
                valid_prefix: valid,
                invalid_sequence: invalid,
                remaining_input: rest,
            })
        }
        None => Err(DecodeError::Incomplete {
            valid_prefix: valid,
            incomplete_suffix: Incomplete::new(after_valid),
        }),
    }
}

impl Incomplete {
    pub fn empty() -> Self {
        Incomplete {
            buffer: [0, 0, 0, 0],
            buffer_len: 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.buffer_len == 0
    }

    pub fn new(bytes: &[u8]) -> Self {
        let mut buffer = [0, 0, 0, 0];
        let len = bytes.len();
        buffer[..len].copy_from_slice(bytes);
        Incomplete {
            buffer: buffer,
            buffer_len: len as u8,
        }
    }

    /// * `None`: still incomplete, call `try_complete` again with more input.
    ///   If no more input is available, this is invalid byte sequence.
    /// * `Some((result, remaining_input))`: We’re done with this `Incomplete`.
    ///   To keep decoding, pass `remaining_input` to `decode()`.
    pub fn try_complete<'input>(
        &mut self,
        input: &'input [u8],
    ) -> Option<(Result<&str, &[u8]>, &'input [u8])> {
        let (consumed, opt_result) = self.try_complete_offsets(input);
        let result = opt_result?;
        let remaining_input = &input[consumed..];
        let result_bytes = self.take_buffer();
        let result = match result {
            Ok(()) => Ok(unsafe { str::from_utf8_unchecked(result_bytes) }),
            Err(()) => Err(result_bytes),
        };
        Some((result, remaining_input))
    }

    fn take_buffer(&mut self) -> &[u8] {
        let len = self.buffer_len as usize;
        self.buffer_len = 0;
        &self.buffer[..len as usize]
    }

    /// (consumed_from_input, None): not enough input
    /// (consumed_from_input, Some(Err(()))): error bytes in buffer
    /// (consumed_from_input, Some(Ok(()))): UTF-8 string in buffer
    fn try_complete_offsets(&mut self, input: &[u8]) -> (usize, Option<Result<(), ()>>) {
        let initial_buffer_len = self.buffer_len as usize;
        let copied_from_input;
        {
            let unwritten = &mut self.buffer[initial_buffer_len..];
            copied_from_input = cmp::min(unwritten.len(), input.len());
            unwritten[..copied_from_input].copy_from_slice(&input[..copied_from_input]);
        }
        let spliced = &self.buffer[..initial_buffer_len + copied_from_input];
        match str::from_utf8(spliced) {
            Ok(_) => {
                self.buffer_len = spliced.len() as u8;
                (copied_from_input, Some(Ok(())))
            }
            Err(error) => {
                let valid_up_to = error.valid_up_to();
                if valid_up_to > 0 {
                    let consumed = valid_up_to.checked_sub(initial_buffer_len).unwrap();
                    self.buffer_len = valid_up_to as u8;
                    (consumed, Some(Ok(())))
                } else {
                    match error.error_len() {
                        Some(invalid_sequence_length) => {
                            let consumed = invalid_sequence_length
                                .checked_sub(initial_buffer_len)
                                .unwrap();
                            self.buffer_len = invalid_sequence_length as u8;
                            (consumed, Some(Err(())))
                        }
                        None => {
                            self.buffer_len = spliced.len() as u8;
                            (copied_from_input, None)
                        }
                    }
                }
            }
        }
    }
}
#[cfg(test)]
mod test {
    use super::*;

    use std::borrow::Cow;
    use std::collections::VecDeque;
    use std::io;

    /// A re-implementation of std::str::from_utf8
    pub fn str_from_utf8(input: &[u8]) -> Result<&str, usize> {
        match decode(input) {
            Ok(s) => return Ok(s),
            Err(DecodeError::Invalid { valid_prefix, .. })
            | Err(DecodeError::Incomplete { valid_prefix, .. }) => Err(valid_prefix.len()),
        }
    }

    #[test]
    fn test_str_from_utf8() {
        let xs = b"hello";
        assert_eq!(str_from_utf8(xs), Ok("hello"));

        let xs = "ศไทย中华Việt Nam".as_bytes();
        assert_eq!(str_from_utf8(xs), Ok("ศไทย中华Việt Nam"));

        let xs = b"hello\xFF";
        assert!(str_from_utf8(xs).is_err());
    }

    #[test]
    fn test_is_utf8() {
        // Chars of 1, 2, 3, and 4 bytes
        assert!(str_from_utf8("eé€\u{10000}".as_bytes()).is_ok());
        // invalid prefix
        assert!(str_from_utf8(&[0x80]).is_err());
        // invalid 2 byte prefix
        assert!(str_from_utf8(&[0xc0]).is_err());
        assert!(str_from_utf8(&[0xc0, 0x10]).is_err());
        // invalid 3 byte prefix
        assert!(str_from_utf8(&[0xe0]).is_err());
        assert!(str_from_utf8(&[0xe0, 0x10]).is_err());
        assert!(str_from_utf8(&[0xe0, 0xff, 0x10]).is_err());
        // invalid 4 byte prefix
        assert!(str_from_utf8(&[0xf0]).is_err());
        assert!(str_from_utf8(&[0xf0, 0x10]).is_err());
        assert!(str_from_utf8(&[0xf0, 0xff, 0x10]).is_err());
        assert!(str_from_utf8(&[0xf0, 0xff, 0xff, 0x10]).is_err());

        // deny overlong encodings
        assert!(str_from_utf8(&[0xc0, 0x80]).is_err());
        assert!(str_from_utf8(&[0xc0, 0xae]).is_err());
        assert!(str_from_utf8(&[0xe0, 0x80, 0x80]).is_err());
        assert!(str_from_utf8(&[0xe0, 0x80, 0xaf]).is_err());
        assert!(str_from_utf8(&[0xe0, 0x81, 0x81]).is_err());
        assert!(str_from_utf8(&[0xf0, 0x82, 0x82, 0xac]).is_err());
        assert!(str_from_utf8(&[0xf4, 0x90, 0x80, 0x80]).is_err());

        // deny surrogates
        assert!(str_from_utf8(&[0xED, 0xA0, 0x80]).is_err());
        assert!(str_from_utf8(&[0xED, 0xBF, 0xBF]).is_err());

        assert!(str_from_utf8(&[0xC2, 0x80]).is_ok());
        assert!(str_from_utf8(&[0xDF, 0xBF]).is_ok());
        assert!(str_from_utf8(&[0xE0, 0xA0, 0x80]).is_ok());
        assert!(str_from_utf8(&[0xED, 0x9F, 0xBF]).is_ok());
        assert!(str_from_utf8(&[0xEE, 0x80, 0x80]).is_ok());
        assert!(str_from_utf8(&[0xEF, 0xBF, 0xBF]).is_ok());
        assert!(str_from_utf8(&[0xF0, 0x90, 0x80, 0x80]).is_ok());
        assert!(str_from_utf8(&[0xF4, 0x8F, 0xBF, 0xBF]).is_ok());
    }

    /// A re-implementation of String::from_utf8_lossy
    pub fn string_from_utf8_lossy(input: &[u8]) -> Cow<str> {
        let mut result = decode(input);
        if let Ok(s) = result {
            return s.into();
        }
        let mut string = String::with_capacity(input.len() + REPLACEMENT_CHARACTER.len());
        loop {
            match result {
                Ok(s) => {
                    string.push_str(s);
                    return string.into();
                }
                Err(DecodeError::Incomplete { valid_prefix, .. }) => {
                    string.push_str(valid_prefix);
                    string.push_str(REPLACEMENT_CHARACTER);
                    return string.into();
                }
                Err(DecodeError::Invalid {
                    valid_prefix,
                    remaining_input,
                    ..
                }) => {
                    string.push_str(valid_prefix);
                    string.push_str(REPLACEMENT_CHARACTER);
                    result = decode(remaining_input);
                }
            }
        }
    }

    pub const DECODED_LOSSY: &'static [(&'static [u8], &'static str)] = &[
        (b"hello", "hello"),
        (
            b"\xe0\xb8\xa8\xe0\xb9\x84\xe0\xb8\x97\xe0\xb8\xa2\xe4\xb8\xad\xe5\x8d\x8e",
            "ศไทย中华",
        ),
        (b"Vi\xe1\xbb\x87t Nam", "Việt Nam"),
        (b"Hello\xC2 There\xFF ", "Hello\u{FFFD} There\u{FFFD} "),
        (b"Hello\xC0\x80 There", "Hello\u{FFFD}\u{FFFD} There"),
        (b"\xE6\x83 Goodbye", "\u{FFFD} Goodbye"),
        (b"\xF5foo\xF5\x80bar", "\u{FFFD}foo\u{FFFD}\u{FFFD}bar"),
        (b"\xF5foo\xF5\xC2", "\u{FFFD}foo\u{FFFD}\u{FFFD}"),
        (
            b"\xF1foo\xF1\x80bar\xF1\x80\x80baz",
            "\u{FFFD}foo\u{FFFD}bar\u{FFFD}baz",
        ),
        (
            b"\xF4foo\xF4\x80bar\xF4\xBFbaz",
            "\u{FFFD}foo\u{FFFD}bar\u{FFFD}\u{FFFD}baz",
        ),
        (
            b"\xF0\x80\x80\x80foo\xF0\x90\x80\x80bar",
            "\u{FFFD}\u{FFFD}\u{FFFD}\u{FFFD}foo\u{10000}bar",
        ),
        (b"\xF0\x90\x80foo", "\u{FFFD}foo"),
        // surrogates
        (
            b"\xED\xA0\x80foo\xED\xBF\xBFbar",
            "\u{FFFD}\u{FFFD}\u{FFFD}foo\u{FFFD}\u{FFFD}\u{FFFD}bar",
        ),
    ];

    #[test]
    fn test_string_from_utf8_lossy() {
        for &(input, expected) in DECODED_LOSSY {
            assert_eq!(string_from_utf8_lossy(input), expected);
        }
    }

    pub fn all_partitions<'a, F>(input: &'a [u8], f: F)
    where
        F: Fn(&[&[u8]]),
    {
        fn all_partitions_inner<'a, F>(chunks: &mut Vec<&'a [u8]>, input: &'a [u8], f: &F)
        where
            F: Fn(&[&[u8]]),
        {
            if input.is_empty() {
                f(chunks)
            }
            for i in 1..(input.len() + 1) {
                chunks.push(&input[..i]);
                all_partitions_inner(chunks, &input[i..], f);
                chunks.pop();
            }
        }

        let mut chunks = Vec::new();
        all_partitions_inner(&mut chunks, input, &f);
        assert_eq!(chunks.len(), 0);
    }

    #[test]
    fn test_incremental_decoder() {
        for &(input, expected) in DECODED_LOSSY {
            all_partitions(input, |chunks| {
                let mut string = String::new();
                {
                    let mut decoder = LossyDecoder::new(|s| string.push_str(s));
                    for &chunk in &*chunks {
                        decoder.feed(chunk);
                    }
                }
                assert_eq!(string, expected);
            });
        }
    }

    #[test]
    fn test_bufread_decoder() {
        for &(input, expected) in DECODED_LOSSY {
            all_partitions(input, |chunks| {
                let chunks = Chunks(chunks.to_vec().into());
                let string = BufReadDecoder::read_to_string_lossy(chunks).unwrap();
                assert_eq!(string, expected)
            });
        }
    }

    struct Chunks<'a>(VecDeque<&'a [u8]>);

    impl<'a> io::Read for Chunks<'a> {
        fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
            unimplemented!()
        }
    }

    impl<'a> io::BufRead for Chunks<'a> {
        fn fill_buf(&mut self) -> io::Result<&[u8]> {
            Ok(*self.0.front().unwrap())
        }

        fn consume(&mut self, bytes: usize) {
            {
                let front = self.0.front_mut().unwrap();
                *front = &front[bytes..];
                if !front.is_empty() {
                    return;
                }
            }
            if self.0.len() > 1 {
                self.0.pop_front();
            }
        }
    }
}
