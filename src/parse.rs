//! This module implements [`FromStr`] for the [`Size`] crate

use core::fmt;
use core::num::{ParseFloatError, ParseIntError};
use core::str::FromStr;

use crate::sealed::AsIntermediate;
use crate::{Intermediate, Size};

/// The error type returned by [`Size`]'s [`FromStr::from_str`] function
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ParseError {
    /// Input was empty
    Empty,

    /// non-ascii or other invalid character in source string
    InvalidCharacter,

    /// Unable to parse floating-point number
    InvalidFloat(ParseFloatError),

    /// Unable to parse integer number
    InvalidInt(ParseIntError),

    /// Invalid size suffix
    InvalidSuffix,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let msg = match self {
            Self::Empty => "input was empty",
            Self::InvalidCharacter => "invalid character in string",
            Self::InvalidFloat(_) => "unable to parse floating-point value",
            Self::InvalidInt(_) => "unable to parse integer value",
            Self::InvalidSuffix => "invalid size suffix",
        };
        f.pad(msg)
    }
}

impl From<ParseFloatError> for ParseError {
    fn from(err: ParseFloatError) -> ParseError {
        ParseError::InvalidFloat(err)
    }
}

impl From<ParseIntError> for ParseError {
    fn from(err: ParseIntError) -> ParseError {
        ParseError::InvalidInt(err)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Empty | Self::InvalidCharacter | Self::InvalidSuffix => None,
            Self::InvalidFloat(err) => Some(err),
            Self::InvalidInt(err) => Some(err),
        }
    }
}

/// helper type for [`Size::from_str`]
enum Number {
    Float(f64),
    Int(i64),
}

impl AsIntermediate for Number {
    #[inline]
    fn as_(self) -> Intermediate {
        match self {
            Self::Float(f) => f.as_(),
            Self::Int(i) => i.as_(),
        }
    }
}

impl FromStr for Size {
    type Err = ParseError;

    /// Parse a string into a [`Size`]
    ///
    /// The input string must be a valid `i64` or `f64` string (as parsed by the Rust standard
    /// library), followed by zero or more whitespace characters, optionally followed by a valid
    /// suffix. All overall leading and trailing whitespace in the input is ignored.
    ///
    /// Currently only short suffixes are handled, matched case-insensitively: `b`, `kb`, `mb`,
    /// `gb`, `tb`, `pb`, `eb`, `kib`, `mib`, `gib`, `tib`, `pib`, `eib`. If no suffix is present,
    /// bytes are assumed.
    fn from_str(s: &str) -> Result<Size, ParseError> {
        // allow and ignore arbitrary leading/trailng whitespace
        let s = s.trim();

        // bail early if we're empty, allowing for a nicer return type
        if s.is_empty() {
            return Err(ParseError::Empty);
        }

        // Any non-ascii character is automatically invalid in a number or suffix, so assert that
        // early on and we can treat `bytes` and `s` interchangeably
        if !s.is_ascii() {
            return Err(ParseError::InvalidCharacter);
        }
        let bytes = s.as_bytes();

        // find the end of the number portion. num_end points one past the last valid digit
        // character. We let the stdlib's number parsing handle invalid combinations of these
        // digits.
        let (num_str, suffix) = {
            let mut num_end = bytes
                .iter()
                .take_while(|b| matches!(b, b'-' | b'.' | b'e' | b'E' | b'0'..=b'9'))
                .count();

            // special case: if the last character of the number was an E, then we treat that as part
            // of the suffix rather than as part of a floating-point number
            if num_end > 0 && matches!(bytes[num_end - 1], b'e' | b'E') {
                num_end -= 1;
            }
            s.split_at(num_end)
        };
        // trim whitespace from the suffix
        let suffix = suffix.trim();

        // parse the number as either an f64 or an i64
        let num = match num_str.contains(&['.', 'e', 'E']) {
            true => Number::Float(num_str.parse()?),
            false => Number::Int(num_str.parse()?),
        };

        // allocation-free str::to_ascii_lowercase() on the stack. SUFFIX_MAX_LEN must be at least
        // as long as the longest suffix we parse.
        // TODO: check full suffixes too and increase max len accordingly
        const SUFFIX_MAX_LEN: usize = 4;
        if suffix.len() > SUFFIX_MAX_LEN {
            // if the suffix is longer than the max thing we'll check for
            return Err(ParseError::InvalidSuffix);
        }

        let mut suffix_lower_arr = [0u8; SUFFIX_MAX_LEN];
        let suffix_lower = &mut suffix_lower_arr[..suffix.len()];
        for (src, dst) in suffix.bytes().zip(suffix_lower.iter_mut()) {
            *dst = src.to_ascii_lowercase();
        }

        // finally match on the suffix and delegate to Size's constructors. We can pass 'num'
        // directly because we made it implement AsIntermediate. The from_utf8 unwrap can't fail
        // because we filled it with ascii bytes from `s`
        Ok(match core::str::from_utf8(suffix_lower).unwrap() {
            "" | "b" => Size::from_bytes(num),
            "kb" => Size::from_kb(num),
            "mb" => Size::from_mb(num),
            "gb" => Size::from_gb(num),
            "tb" => Size::from_tb(num),
            "pb" => Size::from_pb(num),
            "eb" => Size::from_eb(num),
            "kib" => Size::from_kib(num),
            "mib" => Size::from_mib(num),
            "gib" => Size::from_gib(num),
            "tib" => Size::from_tib(num),
            "pib" => Size::from_pib(num),
            "eib" => Size::from_eib(num),
            _ => return Err(ParseError::InvalidSuffix),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::ParseError;
    use crate::Size;

    macro_rules! ok {
        ($input:expr, $result:expr) => {
            assert_eq!($input.parse::<Size>().unwrap(), $result);
        };
    }

    macro_rules! err {
        ($input:expr, $err:pat) => {
            match $input.parse::<Size>() {
                Err($err) => (),
                result => panic!("expected Err({}) got {:?}", stringify!($err), result),
            }
        };
    }

    #[test]
    fn test_parse_ints() {
        ok!("1", Size::from_bytes(1));
        ok!("0", Size::from_bytes(0));
        ok!("-1234", Size::from_bytes(-1234));
        ok!("200 b", Size::from_bytes(200));
        ok!(" 200    kB", Size::from_kb(200));
        ok!("300KiB", Size::from_kib(300));

        err!("", ParseError::Empty);
        err!("asdf kb", ParseError::InvalidInt(_));
        err!("9999999999999999999 GB", ParseError::InvalidInt(_));
        err!("1 aaaaaaa", ParseError::InvalidSuffix);
    }

    // too big for an i64 intermediate
    #[test]
    #[cfg_attr(not(feature = "std"), ignore)]
    fn test_parse_big() {
        ok!("8eb", Size::from_eb(8));
        ok!("-8 eib", Size::from_eib(-8));
        ok!("9 EiB", Size::from_eib(9)); // out of range, but valid and saturates
    }

    // rounding will be different in no_std mode, so skip these tests
    #[test]
    #[cfg_attr(not(feature = "std"), ignore)]
    fn test_parse_floats() {
        ok!("1.0", Size::from_bytes(1));
        ok!("123.45MB", Size::from_mb(123.45));
        ok!("456.789 GiB", Size::from_gib(456.789));
        ok!("1e10", Size::from_bytes(10_000_000_000.0));
        ok!("1.5e6mb", Size::from_mb(1.5e6));
        ok!("1e0eb", Size::from_eb(1));

        err!("-1.234-B", ParseError::InvalidFloat(_));
        err!("1.23E", ParseError::InvalidSuffix);
        err!(".5 f", ParseError::InvalidSuffix);
    }
}
