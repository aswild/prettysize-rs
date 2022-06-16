#![cfg_attr(not(feature = "std"), no_std)]

mod ops;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_nostd;

use core::fmt;
#[cfg(feature = "std")]
use self::Unit::*;
use num_traits::AsPrimitive;

#[cfg(feature = "std")]
type Underlying = f64;
#[cfg(not(feature = "std"))]
type Underlying = i64;

#[cfg(feature = "std")]
const DEFAULT_BASE: Base = Base::Base2;
#[cfg(feature = "std")]
const DEFAULT_STYLE: Style = Style::Smart;

pub const BYTE: i64 = 1;
pub const KILOBYTE: i64 = 1000;
pub const MEGABYTE: i64 = 1000 * KILOBYTE;
pub const GIGABYTE: i64 = 1000 * MEGABYTE;
pub const TERABYTE: i64 = 1000 * GIGABYTE;
pub const PETABYTE: i64 = 1000 * TERABYTE;
pub const EXABYTE: i64 = 1000 * PETABYTE;

pub const B: i64 = BYTE;
pub const KB: i64 = KILOBYTE;
pub const MB: i64 = MEGABYTE;
pub const GB: i64 = GIGABYTE;
pub const TB: i64 = TERABYTE;
pub const PB: i64 = PETABYTE;
pub const EB: i64 = EXABYTE;

pub const KIBIBYTE: i64 = 1 << 10;
pub const MEBIBYTE: i64 = 1 << 20;
pub const GIBIBYTE: i64 = 1 << 30;
pub const TEBIBYTE: i64 = 1 << 40;
pub const PEBIBYTE: i64 = 1 << 50;
pub const EXBIBYTE: i64 = 1 << 60;

#[allow(non_upper_case_globals)]
pub const KiB: i64 = KIBIBYTE;
#[allow(non_upper_case_globals)]
pub const MiB: i64 = MEBIBYTE;
#[allow(non_upper_case_globals)]
pub const GiB: i64 = GIBIBYTE;
#[allow(non_upper_case_globals)]
pub const TiB: i64 = TEBIBYTE;
#[allow(non_upper_case_globals)]
pub const PiB: i64 = PEBIBYTE;
#[allow(non_upper_case_globals)]
pub const EiB: i64 = EXBIBYTE;

#[cfg(feature = "std")]
pub enum Base {
    Base2,
    Base10,
}

pub enum Unit {
    Byte,
    Kibibyte,
    Kilobyte,
    Mebibyte,
    Megabyte,
    Gibibyte,
    Gigabyte,
    Tebibyte,
    Terabyte,
    Pebibyte,
    Petabyte,
    Exbibyte,
    Exabyte,
}

#[cfg(feature = "std")]
impl Unit {
    fn text(&self) -> (&'static str, &'static str, &'static str, &'static str) {
        match &self {
            &Byte => ("byte", "Byte", "b", "B"),

            &Kilobyte => ("kilobyte", "Kilobyte", "kb", "KB"),
            &Megabyte => ("megabyte", "Megabyte", "mb", "MB"),
            &Gigabyte => ("gigabyte", "Gigabyte", "gb", "GB"),
            &Terabyte => ("terabyte", "Terabyte", "tb", "TB"),
            &Petabyte => ("petabyte", "Petabyte", "pb", "PB"),
            &Exabyte  => ("exabyte",  "Exabyte",  "eb", "EB"),

            &Kibibyte => ("kibibyte", "Kibibyte", "kib", "KiB"),
            &Mebibyte => ("mebibyte", "Mebibyte", "mib", "MiB"),
            &Gibibyte => ("gibibyte", "Gibibyte", "gib", "GiB"),
            &Pebibyte => ("pebibyte", "Pebibyte", "pib", "PiB"),
            &Tebibyte => ("tebibyte", "Tebibyte", "tib", "TiB"),
            &Exbibyte => ("exbibyte", "Exbibyte", "eib", "EiB"),
        }
    }

    fn format(&self, mut fmt: &mut fmt::Formatter, bytes: i64, style: &Style) -> fmt::Result {
        match style {
            Style::Smart => match &self {
                &Unit::Byte => self.format(&mut fmt, bytes, &Style::FullLowerCase),
                _ => self.format(&mut fmt, bytes, &Style::Abbreviated),
            },
            style @ _ => match bytes {
                1 => match style {
                    Style::Smart => unreachable!("already covered above"),
                    Style::FullLowerCase => write!(fmt, " {}", self.text().0),
                    Style::Full => write!(fmt, " {}", self.text().1),
                    Style::AbbreviatedLowerCase => write!(fmt, " {}", self.text().2),
                    Style::Abbreviated => write!(fmt, " {}", self.text().3),
                },
                _ => match style {
                    Style::Smart => unreachable!("already covered above"),
                    Style::FullLowerCase => write!(fmt, " {}s", self.text().0),
                    Style::Full => write!(fmt, " {}s", self.text().1),
                    Style::AbbreviatedLowerCase => write!(fmt, " {}", self.text().2),
                    Style::Abbreviated => write!(fmt, " {}", self.text().3),
                },
            },
        }
    }
}

#[derive(Copy, Clone)]
#[non_exhaustive]
pub enum Size<T> {
    Bytes(T),
    Kibibytes(T),
    Kilobytes(T),
    Mebibytes(T),
    Megabytes(T),
    Gibibytes(T),
    Gigabytes(T),
    Tebibytes(T),
    Terabytes(T),
    Pebibytes(T),
    Petabytes(T),
    Exbibytes(T),
    Exabytes(T),
}

impl<T> Size<T> {
    #![allow(non_snake_case)]

    pub const fn B(t: T) -> Self { Self::Bytes(t) }
    pub const fn KiB(t: T) -> Self { Self::Kibibytes(t) }
    pub const fn KB(t: T) -> Self { Self::Kilobytes(t) }
    pub const fn MiB(t: T) -> Self { Self::Mebibytes(t) }
    pub const fn MB(t: T) -> Self { Self::Megabytes(t) }
    pub const fn GiB(t: T) -> Self { Self::Gibibytes(t) }
    pub const fn GB(t: T) -> Self { Self::Gigabytes(t) }
    pub const fn TiB(t: T) -> Self { Self::Tebibytes(t) }
    pub const fn TB(t: T) -> Self { Self::Terabytes(t) }
    pub const fn PiB(t: T) -> Self { Self::Pebibytes(t) }
    pub const fn PB(t: T) -> Self { Self::Petabytes(t) }
    pub const fn EiB(t: T) -> Self { Self::Exbibytes(t) }
    pub const fn EB(t: T) -> Self { Self::Exabytes(t) }
}

#[cfg(feature = "std")]
pub enum Style {
    Abbreviated,
    AbbreviatedLowerCase,
    Full,
    Smart,
    FullLowerCase,
}

#[cfg(feature = "std")]
impl<T> std::fmt::Display for Size<T>
where
    T: AsPrimitive<f64>,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.format(fmt, &DEFAULT_BASE, &DEFAULT_STYLE)
    }
}

impl<T> core::fmt::Debug for Size<T>
where
    T: AsPrimitive<Underlying>
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{} bytes", self.bytes())
    }
}

impl<T, U> PartialEq<Size<U>> for Size<T>
where
    T: AsPrimitive<Underlying>,
    U: AsPrimitive<Underlying>,
{
    fn eq(&self, other: &Size<U>) -> bool {
        self.bytes() == other.bytes()
    }
}

struct Fmt<F>(pub F)
where
    F: Fn(&mut fmt::Formatter) -> fmt::Result;

impl<F> fmt::Debug for Fmt<F>
where
    F: Fn(&mut fmt::Formatter) -> fmt::Result,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (self.0)(f)
    }
}

impl<T> Size<T>
where
    T: AsPrimitive<Underlying>
{
    pub fn bytes(&self) -> i64 {
        use self::Size::*;

        (match &self {
            &Bytes(x) => x.as_(),
            &Kilobytes(x) => x.as_() * KILOBYTE as Underlying,
            &Megabytes(x) => x.as_() * MEGABYTE as Underlying,
            &Gigabytes(x) => x.as_() * GIGABYTE as Underlying,
            &Terabytes(x) => x.as_() * TERABYTE as Underlying,
            &Petabytes(x) => x.as_() * PETABYTE as Underlying,
            &Exabytes(x)  => x.as_() * EXABYTE  as Underlying,
            &Kibibytes(x) => x.as_() * KIBIBYTE as Underlying,
            &Mebibytes(x) => x.as_() * MEBIBYTE as Underlying,
            &Gibibytes(x) => x.as_() * GIBIBYTE as Underlying,
            &Tebibytes(x) => x.as_() * TEBIBYTE as Underlying,
            &Pebibytes(x) => x.as_() * PEBIBYTE as Underlying,
            &Exbibytes(x) => x.as_() * EXBIBYTE as Underlying,
        }) as i64
    }

    #[cfg(feature = "std")]
    pub fn to_string(&self, base: Base, style: Style) -> String {
        return format!("{:?}", Fmt(|f| self.format(f, &base, &style)));
    }

    #[cfg(feature = "std")]
    fn format(&self, mut fmt: &mut fmt::Formatter, base: &Base, style: &Style) -> fmt::Result {
        let bytes = match self.bytes() {
            x@ 0.. => x,
            y => {
                write!(fmt, "-")?;

                // The absolute magnitude of T::min_value() for a signed number is one more than
                // that of T::max_value(), meaning T::min_value().abs() will panic.
                match y.checked_abs() {
                    Some(abs) => abs,
                    None => i64::max_value(),
                }
            }
        };

        const BASE2_TEMP: usize = BASE2_RULES.len() - 1;
        const BASE10_TEMP: usize = BASE10_RULES.len() - 1;
        let rule = match base {
            Base::Base2 => match BASE2_RULES.binary_search_by_key(&bytes, |rule| rule.less_than) {
                Ok(BASE2_TEMP) => &BASE2_RULES[BASE2_TEMP],
                Ok(index) => &BASE2_RULES[index + 1],
                Err(index) => &BASE2_RULES[index],
            },
            Base::Base10 => {
                match BASE10_RULES.binary_search_by_key(&bytes, |rule| rule.less_than) {
                    Ok(BASE10_TEMP) => &BASE10_RULES[BASE10_TEMP],
                    Ok(index) => &BASE10_RULES[index + 1],
                    Err(index) => &BASE10_RULES[index],
                }
            }
        };

        (rule.formatter)(&mut fmt, bytes)?;
        rule.unit.format(&mut fmt, bytes, &style)?;

        return Ok(());
    }
}

#[cfg(feature = "std")]
struct FormatRule {
    less_than: i64,
    formatter: fn(&mut fmt::Formatter, bytes: i64) -> fmt::Result,
    unit: Unit,
}

#[cfg(feature = "std")]
const BASE10_RULES: [FormatRule; 17] = [
    FormatRule {
        less_than: 1 * KILOBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes),
        unit: Byte,
    },
    FormatRule {
        less_than: 10 * KILOBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * KILOBYTE) as f64)),
        unit: Kilobyte,
    },
    FormatRule {
        less_than: 100 * KILOBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * KILOBYTE) as f64)),
        unit: Kilobyte,
    },
    FormatRule {
        less_than: 1 * MEGABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * KILOBYTE) as f64)),
        unit: Kilobyte,
    },
    FormatRule {
        less_than: 10 * MEGABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * MEGABYTE) as f64)),
        unit: Megabyte,
    },
    FormatRule {
        less_than: 100 * MEGABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * MEGABYTE) as f64)),
        unit: Megabyte,
    },
    FormatRule {
        less_than: 1 * GIGABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * MEGABYTE) as f64)),
        unit: Megabyte,
    },
    FormatRule {
        less_than: 10 * GIGABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * GIGABYTE) as f64)),
        unit: Gigabyte,
    },
    FormatRule {
        less_than: 100 * GIGABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * GIGABYTE) as f64)),
        unit: Gigabyte,
    },
    FormatRule {
        less_than: 1 * TERABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * GIGABYTE) as f64)),
        unit: Gigabyte,
    },
    FormatRule {
        less_than: 10 * TERABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * TERABYTE) as f64)),
        unit: Terabyte,
    },
    FormatRule {
        less_than: 100 * TERABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * TERABYTE) as f64)),
        unit: Terabyte,
    },
    FormatRule {
        less_than: 1 * PETABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * TERABYTE) as f64)),
        unit: Terabyte,
    },
    FormatRule {
        less_than: 10 * PETABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * PETABYTE) as f64)),
        unit: Petabyte,
    },
    FormatRule {
        less_than: 100 * PETABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * PETABYTE) as f64)),
        unit: Petabyte,
    },
    FormatRule {
        less_than: 1 * EXABYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * PETABYTE) as f64)),
        unit: Petabyte,
    },
    FormatRule {
        less_than: i64::max_value(),
        formatter: |fmt, bytes| write!(fmt, "{:0}", bytes as f64 / ((1i64 * EXABYTE) as f64)),
        unit: Exabyte,
    },
];

#[cfg(feature = "std")]
const BASE2_RULES: [FormatRule; 17] = [
    FormatRule {
        less_than: 1 * KIBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes),
        unit: Byte,
    },
    FormatRule {
        less_than: 10 * KIBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * KIBIBYTE) as f64)),
        unit: Kibibyte,
    },
    FormatRule {
        less_than: 100 * KIBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * KIBIBYTE) as f64)),
        unit: Kibibyte,
    },
    FormatRule {
        less_than: 1 * MEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * KIBIBYTE) as f64)),
        unit: Kibibyte,
    },
    FormatRule {
        less_than: 10 * MEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * MEBIBYTE) as f64)),
        unit: Mebibyte,
    },
    FormatRule {
        less_than: 100 * MEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * MEBIBYTE) as f64)),
        unit: Mebibyte,
    },
    FormatRule {
        less_than: 1 * GIBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * MEBIBYTE) as f64)),
        unit: Mebibyte,
    },
    FormatRule {
        less_than: 10 * GIBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * GIBIBYTE) as f64)),
        unit: Gibibyte,
    },
    FormatRule {
        less_than: 100 * GIBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * GIBIBYTE) as f64)),
        unit: Gibibyte,
    },
    FormatRule {
        less_than: 1 * TEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * GIBIBYTE) as f64)),
        unit: Gibibyte,
    },
    FormatRule {
        less_than: 10 * TEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * TEBIBYTE) as f64)),
        unit: Tebibyte,
    },
    FormatRule {
        less_than: 100 * TEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * TEBIBYTE) as f64)),
        unit: Tebibyte,
    },
    FormatRule {
        less_than: 1 * PEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * TEBIBYTE) as f64)),
        unit: Tebibyte,
    },
    FormatRule {
        less_than: 10 * PEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.2}", bytes as f64 / ((1i64 * PEBIBYTE) as f64)),
        unit: Pebibyte,
    },
    FormatRule {
        less_than: 100 * PEBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.1}", bytes as f64 / ((1i64 * PEBIBYTE) as f64)),
        unit: Pebibyte,
    },
    FormatRule {
        less_than: 1 * EXBIBYTE,
        formatter: |fmt, bytes| write!(fmt, "{:.0}", bytes as f64 / ((1i64 * PEBIBYTE) as f64)),
        unit: Pebibyte,
    },
    FormatRule {
        less_than: i64::max_value(),
        formatter: |fmt, bytes| write!(fmt, "{:0}", bytes as f64 / ((1i64 * EXBIBYTE) as f64)),
        unit: Exbibyte,
    },
];
