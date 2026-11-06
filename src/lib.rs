#![warn(clippy::pedantic)]
// Lints old vs new rust causes issues
#![allow(unknown_lints)]
#![allow(clippy::uninlined_format_args, clippy::single_range_in_vec_init)]
use core::fmt::{Debug, Display, Formatter};
use core::ops::RangeInclusive;
use std::num::{IntErrorKind, NonZeroUsize};

const UNIT_SEP: &str = "bytes=";
/// Function that parses the content of a range header.
///
/// Follows the [spec here](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Range)
///
/// And [RFC-9110 here](https://www.rfc-editor.org/rfc/rfc9110.html)
///
/// Will only accept byte-ranges, will update when [this spec](https://www.iana.org/assignments/http-parameters/http-parameters.xhtml) changes to allow other units.
///
/// Parses ranges strictly.
///
/// Ranges such as `bytes=0-15, 16-20, abc` will be rejected immediately.
///
/// It preserves the range ordering, the specification leaves it open to the server to determine whether
/// ranges that are out of order are correct or not, ie `bytes=20-30, 0-15`
///
/// Allows a maximum of `100` ranges per request to limit DoS-risk, if more ranges are desired
/// use [`parse_range_header_with_max_ranges`].
///
/// # Example no trailing whitespace
/// ```
/// // Ok
/// assert!(http_range_header::parse_range_header("bytes=0-15").is_ok());
/// // Not allowed
/// assert!(http_range_header::parse_range_header("bytes=0-15 ").is_err());
/// // Leading is allowed
/// assert!(http_range_header::parse_range_header("bytes= 0-15").is_ok());
/// ```
///
/// # Example No negative values, no plus-sign
/// ```
/// // No negatives
/// assert!(http_range_header::parse_range_header("bytes=-12-15").is_err());
/// // Leading zeroes are allowed
/// assert!(http_range_header::parse_range_header("bytes=00-15").is_ok());
/// // No plus sign
/// assert!(http_range_header::parse_range_header("bytes=+0-15").is_err());
/// ```
///
/// # Example Max 30 digits per position
/// The rule exists to prevent unbounded string searching:
/// ```
/// // u64::MAX and some extra is fine
/// assert!(http_range_header::parse_range_header("bytes=00-0018446744073709551615").is_ok());
/// // above 30 digits are rejected
/// assert!(http_range_header::parse_range_header("bytes=00-000000000000000000000000000000000000000000000000000001").is_err());
/// ```
///
/// Makes two passes and parses ranges strictly. On the first pass, if any range is malformed returns an `Err`.
///
/// On the second pass it filters out unsatisfiable ranges. Invalid ranges produce an error.
/// # Example with a standard valid range
///
/// ```
/// let input = "bytes=0-15";
/// let file_size_bytes = 512;
/// let parsed_ranges = http_range_header::parse_range_header(input);
///
/// match parsed_ranges {
///     Ok(ranges) => {
///         match ranges.validate(file_size_bytes) {
///             Ok(valid_ranges) => {
///                 for range in valid_ranges {
///                     // do something with ranges
///                     assert_eq!(0..=15, range)
///                 }
///             }
///             Err(_err) => {
///                 // Do something when ranges doesn't make sense
///                 panic!("Weird range!")
///             }
///         }
///     }
///     Err(_err) => {
///         // Do something with malformed ranges
///         panic!("Malformed range!")
///     }
/// }
/// ```
///
/// The parser makes two passes, one without a known file-size, ensuring all ranges are syntactically correct.
/// The returned struct will through its `validate` method accept a file-size and figure out whether or not the
/// syntactically correct ranges actually makes sense in context
///
/// The range `bytes=0-20` on a file with 15 bytes will be accepted in the first pass as the content size is unknown.
/// On the second pass (`validate`) it will be truncated to `file_size - 1` as per [the spec](https://httpwg.org/specs/rfc9110.html#rfc.section.14.1.2).
/// # Example range truncates in `validate` because it exceedes
/// ```
/// let input = "bytes=0-20";
/// let file_size_bytes = 15;
/// let parsed_ranges = http_range_header::parse_range_header(input)
///     // Is syntactically correct
///     .unwrap();
/// let validated = parsed_ranges.validate(file_size_bytes).unwrap();
/// assert_eq!(vec![0..=14], validated);
/// ```
///
/// The range `bytes=0-20, 5-10` will become two syntactically correct overlapping ranges.
/// However, `bytes=0-20, 5-10, 12-13` will be rejected on `validate`.
///
/// This is an opinionated implementation, [the spec](https://www.rfc-editor.org/rfc/rfc9110.html)
/// allows a server to determine its implementation of more than two overlapping ranges,
/// this api currently does not allow it. It will accept at most 2 overlapping ranges.
///
/// # Example multipart-range `validate` on a single overlap, but not two
/// ```
/// let input = "bytes=0-15, 10-20, 30-50";
/// let file_size_bytes = 512;
/// let parsed_ranges = http_range_header::parse_range_header(input)
///     // Is syntactically correct
///     .unwrap();
/// let validated = parsed_ranges.validate(file_size_bytes);
/// assert_eq!(Ok(vec![0..=15, 10..=20, 30..=50]), validated);
/// let input = "bytes=0-15, 10-20, 30-50, 45-";
/// let file_size_bytes = 512;
/// let parsed_ranges = http_range_header::parse_range_header(input)
///     // Is syntactically correct
///     .unwrap();
/// let validated = parsed_ranges.validate(file_size_bytes);
/// // Some ranges overlap, producing an error
/// assert!(validated.is_err());
/// ```
/// # Errors
/// Will return an error if the `range_header_value` cannot be strictly parsed into a range
/// per the http spec.
#[allow(clippy::missing_panics_doc)]
pub fn parse_range_header(
    range_header_value: &str,
) -> Result<ParsedRanges, RangeUnsatisfiableError> {
    // Const unwrap not available in 1.60.0
    const NZ_100: NonZeroUsize = match NonZeroUsize::new(100) {
        None => {
            unreachable!();
        }
        Some(nz) => nz,
    };
    // Picked somewhat arbitrarily, on my bench machine this comes in at sub 2 micros (parse + validate).
    // A value that should be async-safe based on: <https://ryhl.io/blog/async-what-is-blocking/>
    parse_range_header_with_max_ranges(range_header_value, NZ_100)
}

/// Like [`parse_range_header`] with a configurable maximum amount of acceptable ranges
/// in a single header value.
/// # Errors
/// Same as [`parse_range_header`]
pub fn parse_range_header_with_max_ranges(
    range_header_value: &str,
    max_ranges: NonZeroUsize,
) -> Result<ParsedRanges, RangeUnsatisfiableError> {
    const COMMA: char = ',';
    let indicated_range = match range_header_value.get(..UNIT_SEP.len()) {
        Some(r) => {
            if !r.eq_ignore_ascii_case(UNIT_SEP) {
                return Err(RangeUnsatisfiableError::Invalid(
                    RangeInvalid::DoesNotStartWithToken,
                ));
            }
            match range_header_value.get(UNIT_SEP.len()..) {
                Some(r) => r,
                None => {
                    // Unreachable, but `split_at_checked` is not possible at `Rust 1.60`
                    return Err(RangeUnsatisfiableError::Invalid(
                        RangeInvalid::DoesNotStartWithToken,
                    ));
                }
            }
        }
        None => {
            return Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::DoesNotStartWithToken,
            ));
        }
    };
    let mut last_err = None;
    let mut num_empty = 0;
    let mut ranges = Vec::new();
    for range in indicated_range.split(COMMA) {
        if num_empty >= MAX_EMPTY {
            return Err(RangeUnsatisfiableError::Rejected(
                RangeRejected::TooManyUnparseable,
            ));
        }
        let val = if let Some(trimmed) = trim(range) {
            if trimmed.is_empty() {
                num_empty += 1;
                continue;
            }
            match parse_inner(trimmed) {
                Ok(parsed) => parsed,
                Err(e) => {
                    last_err = Some(e);
                    num_empty += 1;
                    continue;
                }
            }
        } else {
            last_err = Some(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace,
            ));
            num_empty += 1;
            continue;
        };
        ranges.push(val);
        if ranges.len() > max_ranges.get() {
            return Err(RangeUnsatisfiableError::Rejected(RangeRejected::TooMany));
        }
    }
    if let Some(last_err) = last_err {
        return Err(last_err);
    }
    if indicated_range.ends_with(space_or_tab) {
        // Having a final empty group with whitespace is allowed
        if !indicated_range
            .trim_end_matches(space_or_tab)
            .ends_with(',')
        {
            return Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace,
            ));
        }
    }
    if ranges.is_empty() {
        Err(RangeUnsatisfiableError::Invalid(RangeInvalid::NoNonempty))
    } else {
        Ok(ParsedRanges::new(ranges))
    }
}

const MAX_EMPTY: usize = 15;

fn trim(s: &str) -> Option<&str> {
    let trimmed = s.trim_matches(space_or_tab);
    if trimmed.starts_with(char::is_whitespace) || trimmed.ends_with(char::is_whitespace) {
        None
    } else {
        Some(trimmed)
    }
}

fn space_or_tab(ch: char) -> bool {
    ch == ' ' || ch == '\t'
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum SyntacticallyCorrectRange {
    FromStart(u64),
    FromLast(u64),
    // Guaranteed 0 <= 1
    Indexed(u64, u64),
}

#[inline]
fn parse_inner(range: &str) -> Result<SyntacticallyCorrectRange, RangeUnsatisfiableError> {
    if let Some((start, end)) = range.split_once('-') {
        if start.is_empty() {
            let end = strict_parse_u64(end)?;
            return Ok(SyntacticallyCorrectRange::FromLast(end));
        }
        let start = strict_parse_u64(start)?;
        if end.is_empty() {
            return Ok(SyntacticallyCorrectRange::FromStart(start));
        }
        let end = strict_parse_u64(end)?;
        if start > end {
            return Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Reversed));
        }
        return Ok(SyntacticallyCorrectRange::Indexed(start, end));
    }
    Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable))
}

fn strict_parse_u64(s: &str) -> Result<u64, RangeUnsatisfiableError> {
    const MAX_DIGITS: usize = 30;
    if s.starts_with('+') {
        return Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable));
    }
    if s.len() > MAX_DIGITS {
        // We don't actually know if there are only digits in there yet
        return Err(RangeUnsatisfiableError::Rejected(
            RangeRejected::TooManyDigits,
        ));
    }
    match s.parse::<u64>() {
        Ok(o) => Ok(o),
        Err(e)
            if e.kind() == &IntErrorKind::PosOverflow
                && s.chars().all(|ch| ch.is_ascii_digit()) =>
        {
            // We're relying on the file not actually being larger than u64::MAX
            // implicitly treating an overflow as full-file (which is the correct spec-following behavior).
            // This does mean that a reversed range will be hidden, though it will still be a
            // `Unsatisfiable` error if it's the only range, so this is just pedantics.
            Ok(u64::MAX)
        }
        Err(_) => Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable)),
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ParsedRanges {
    ranges: Vec<SyntacticallyCorrectRange>,
}

impl ParsedRanges {
    fn new(ranges: Vec<SyntacticallyCorrectRange>) -> Self {
        ParsedRanges { ranges }
    }

    #[must_use]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.ranges.len()
    }

    #[must_use]
    pub fn into_ranges(self) -> Vec<SyntacticallyCorrectRange> {
        self.ranges
    }

    /// Validates a parsed range for a given file-size in bytes.
    /// Can return an empty vector if no ranges are usable (only possible on `file_size_bytes=0`).
    /// # Errors
    /// If all ranges are unsatisfiable or the ranges are intolerable
    pub fn validate(
        &self,
        file_size_bytes: u64,
    ) -> Result<Vec<RangeInclusive<u64>>, RangeUnsatisfiableError> {
        let len = self.ranges.len();
        if file_size_bytes == 0 {
            return match self.zero_len_validate() {
                Some(e) => Err(e),
                None => Ok(vec![]),
            };
        }
        let mut validated = Vec::with_capacity(len);
        let mut bad_range = false;
        for parsed in &self.ranges {
            let (start, end) = match *parsed {
                SyntacticallyCorrectRange::FromStart(i) => {
                    if i > file_size_bytes.saturating_sub(1) {
                        bad_range = true;
                        continue;
                    }
                    let end = file_size_bytes.saturating_sub(1);
                    (i, end)
                }
                SyntacticallyCorrectRange::FromLast(i) => {
                    if i == 0 {
                        bad_range = true;
                        continue;
                    }
                    // RFC 9110 14.1.2: a suffix longer than the representation selects all of it
                    (
                        file_size_bytes.saturating_sub(i),
                        file_size_bytes.saturating_sub(1),
                    )
                }
                SyntacticallyCorrectRange::Indexed(start, end) => {
                    let end = core::cmp::min(end, file_size_bytes.saturating_sub(1));
                    // This is not a range-reversal, that's already checked
                    if start > end {
                        bad_range = true;
                        continue;
                    }
                    (start, end)
                }
            };
            let valid = RangeInclusive::new(start, end);
            validated.push(valid);
        }

        if validated.is_empty() && bad_range {
            return Err(RangeUnsatisfiableError::Unsatisfiable);
        }
        match validate_ranges(validated.as_slice()) {
            RangeValidationResult::Valid => Ok(validated),
            RangeValidationResult::Overlapping => Err(RangeUnsatisfiableError::Rejected(
                RangeRejected::TooManyOverlapping,
            )),
        }
    }

    #[inline(never)]
    fn zero_len_validate(&self) -> Option<RangeUnsatisfiableError> {
        let mut last_error = None;
        let mut any_passing = false;
        for parsed in &self.ranges {
            match *parsed {
                SyntacticallyCorrectRange::FromStart(_)
                | SyntacticallyCorrectRange::Indexed(_, _) => {
                    last_error = Some(RangeUnsatisfiableError::Unsatisfiable);
                }
                SyntacticallyCorrectRange::FromLast(i) => {
                    if i == 0 {
                        // RFC 9110 14.1.2
                        // > When a selected representation has zero length,
                        // > the only satisfiable form of range-spec in a GET request is a
                        // > suffix-range with a non-zero suffix-length.
                        // This is unsatisfiable, but not invalid, so it doesn't cause an immediate
                        // exit. This is mostly pedantics since it's an empty file, any other ranges
                        // will not produce a particularly interesting result even if we continue.
                        last_error = Some(RangeUnsatisfiableError::Unsatisfiable);
                        continue;
                    }
                    any_passing = true;
                }
            }
        }
        match (any_passing, last_error) {
            (false, Some(e)) => Some(e),
            _ => None,
        }
    }
}

/// A server MAY always ignore a range header <https://www.rfc-editor.org/rfc/rfc9110.html#section-14.2-3>
/// which means falling back to ignoring the range header is spec-compliant.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[non_exhaustive]
pub enum RangeUnsatisfiableError {
    Invalid(RangeInvalid),
    Rejected(RangeRejected),
    /// Spec says this SHOULD be a 416 <https://www.rfc-editor.org/rfc/rfc9110.html#section-14.2-13>
    Unsatisfiable,
}

/// Unless the variant says otherwise, the spec says implementors
/// MAY ignore or reject <https://www.rfc-editor.org/rfc/rfc9110.html#section-14.2-6>
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[non_exhaustive]
pub enum RangeInvalid {
    Reversed,
    IllegalWhitespace,
    /// This error cannot be disambiguated from certain other malformed starts of ranges.
    /// Therefore, the only spec-compliant way of handling this error-code is ignoring the range
    /// <https://www.rfc-editor.org/rfc/rfc9110.html#section-14.2-5>
    DoesNotStartWithToken,
    NoNonempty,
    Unparseable,
}

/// Rejected because of tolerance, possibly an abusive client.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[non_exhaustive]
pub enum RangeRejected {
    /// Spec says ignore or reject <https://www.rfc-editor.org/rfc/rfc9110.html#section-14.2-6>.
    /// Spec says reject with a 416 (if rejecting) <https://www.rfc-editor.org/rfc/rfc9110.html#section-15.5.17>
    TooManyOverlapping,
    TooManyUnparseable,
    TooManyDigits,
    /// Spec says ignore or reject (with a 416) <https://www.rfc-editor.org/rfc/rfc9110.html#section-15.5.17>
    TooMany,
}

impl Display for RangeUnsatisfiableError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            RangeUnsatisfiableError::Invalid(r) => match r {
                RangeInvalid::Reversed => f.write_str("range invalid: reversed"),
                RangeInvalid::IllegalWhitespace => f.write_str("range invalid: illegal whitespace"),
                RangeInvalid::DoesNotStartWithToken => f.write_fmt(format_args!(
                    "range invalid: range does not start with token '{UNIT_SEP}'"
                )),
                RangeInvalid::NoNonempty => f.write_str("range invalid: no nonempty ranges remain"),
                RangeInvalid::Unparseable => {
                    f.write_str("range invalid: provided input did not make sense")
                }
            },
            RangeUnsatisfiableError::Rejected(r) => match r {
                RangeRejected::TooManyOverlapping => {
                    f.write_str("range rejected: too many overlapping ranges")
                }
                RangeRejected::TooManyUnparseable => {
                    f.write_str("range rejected: too many unparseable ranges")
                }
                RangeRejected::TooMany => f.write_str("range rejected: too many ranges"),
                RangeRejected::TooManyDigits => {
                    f.write_str("range rejected: too many characters in the range digit-position")
                }
            },
            RangeUnsatisfiableError::Unsatisfiable => f.write_str("range unsatisfiable"),
        }
    }
}

impl std::error::Error for RangeUnsatisfiableError {}

enum RangeValidationResult {
    Valid,
    Overlapping,
}

fn validate_ranges(ranges: &[RangeInclusive<u64>]) -> RangeValidationResult {
    let mut sorted = true;
    let mut prev_start = 0;
    for range in ranges {
        let start = *range.start();
        sorted &= prev_start <= start;
        prev_start = start;
    }
    if ranges.len() == 1 {
        return RangeValidationResult::Valid;
    }
    let bounds = ranges.iter().map(|r| (*r.start(), *r.end()));
    let too_many = if sorted {
        has_multiple_overlaps(bounds)
    } else {
        let mut by_start: Vec<_> = bounds.collect();
        by_start.sort_unstable_by_key(|&(start, _)| start);
        has_multiple_overlaps(by_start.into_iter())
    };
    if too_many {
        RangeValidationResult::Overlapping
    } else {
        RangeValidationResult::Valid
    }
}

fn has_multiple_overlaps(mut by_start: impl Iterator<Item = (u64, u64)>) -> bool {
    // MSRV
    #[allow(clippy::manual_let_else)]
    let mut max_end = match by_start.next() {
        Some((_, end)) => end,
        None => return false,
    };
    let mut seen_overlap = false;
    for (start, end) in by_start {
        if start <= max_end {
            if seen_overlap {
                return true;
            }
            seen_overlap = true;
        }
        max_end = max_end.max(end);
    }
    false
}

#[cfg(test)]
mod tests {
    use crate::{
        parse_range_header, parse_range_header_with_max_ranges, ParsedRanges, RangeInvalid,
        RangeRejected, RangeUnsatisfiableError, SyntacticallyCorrectRange,
    };
    use core::ops::RangeInclusive;
    use rand::seq::SliceRandom;
    use std::fmt::Write;
    use std::num::NonZeroUsize;

    const TEST_FILE_LENGTH: u64 = 10_000;
    /// Testing standard range compliance against <https://datatracker.ietf.org/doc/html/rfc7233>
    #[test]
    fn rfc_7233_standard_test1() {
        let input = "bytes=0-499";
        let expect = SyntacticallyCorrectRange::Indexed(0, 499);
        let actual = parse_range_header(input).unwrap();
        assert_eq!(single_range(expect), actual);
        let expect = RangeInclusive::new(0, 499);
        let actual = actual.validate(TEST_FILE_LENGTH).unwrap()[0].clone();
        assert_eq!(expect, actual);
    }

    #[test]
    fn rfc_7233_standard_test2() {
        let input = "bytes=500-999";
        let expect = SyntacticallyCorrectRange::Indexed(500, 999);
        let actual = parse_range_header(input).unwrap();
        assert_eq!(single_range(expect), actual);
        let expect = RangeInclusive::new(500, 999);
        let actual = actual.validate(TEST_FILE_LENGTH).unwrap()[0].clone();
        assert_eq!(expect, actual);
    }

    /// Testing suffix compliance against <https://datatracker.ietf.org/doc/html/rfc7233>
    #[test]
    fn rfc_7233_suffixed_test() {
        let input = "bytes=-500";
        let expect = SyntacticallyCorrectRange::FromLast(500);
        let actual = parse_range_header(input).unwrap();
        assert_eq!(single_range(expect), actual);
        let expect = RangeInclusive::new(9500, 9999);
        let actual = actual.validate(10_000).unwrap()[0].clone();
        assert_eq!(expect, actual);
    }

    /// Testing open range compliance against <https://datatracker.ietf.org/doc/html/rfc7233>
    #[test]
    fn rfc_7233_open_range_test() {
        let input = "bytes=9500-";
        let expect = SyntacticallyCorrectRange::FromStart(9500);
        let actual = parse_range_header(input).unwrap();
        assert_eq!(single_range(expect), actual);
        let expect = RangeInclusive::new(9500, 9999);
        let actual = actual.validate(10_000).unwrap()[0].clone();
        assert_eq!(expect, actual);
    }

    /// Testing first and last bytes compliance against <https://datatracker.ietf.org/doc/html/rfc7233>
    #[test]
    fn rfc_7233_first_and_last() {
        let input = "bytes=0-0, -1";
        let expect = vec![
            SyntacticallyCorrectRange::Indexed(0, 0),
            SyntacticallyCorrectRange::FromLast(1),
        ];
        let actual = parse_range_header(input).unwrap();
        assert_eq!(expect, actual.ranges);
        let expect = vec![0..=0, 9999..=9999];
        let actual = actual.validate(10_000).unwrap();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_standard_range() {
        let input = "bytes=0-1023";
        let expect = SyntacticallyCorrectRange::Indexed(0, 1023);
        let actual = parse_range_header(input).unwrap();
        assert_eq!(single_range(expect), actual);
        let expect = RangeInclusive::new(0, 1023);
        let actual = actual.validate(TEST_FILE_LENGTH).unwrap()[0].clone();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_open_ended_range() {
        let input = "bytes=0-";
        let expect = SyntacticallyCorrectRange::FromStart(0);
        let actual = parse_range_header(input).unwrap();
        assert_eq!(single_range(expect), actual);
        let expect = RangeInclusive::new(0, TEST_FILE_LENGTH - 1);
        let actual = actual.validate(TEST_FILE_LENGTH).unwrap()[0].clone();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_suffix_range_edge() {
        let input = &format!("bytes=-{}", TEST_FILE_LENGTH);
        let expect = SyntacticallyCorrectRange::FromLast(TEST_FILE_LENGTH);
        let actual = parse_range_header(input).unwrap();
        assert_eq!(single_range(expect), actual);
        let expect = RangeInclusive::new(0, TEST_FILE_LENGTH - 1);
        let actual = actual.validate(TEST_FILE_LENGTH).unwrap()[0].clone();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_empty_as_invalid() {
        let input = "";
        let parsed = parse_range_header(input);
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::DoesNotStartWithToken
            ))
        );
    }

    #[test]
    fn parse_empty_range_as_invalid() {
        let input = "bytes=";
        let parsed = parse_range_header(input);
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::NoNonempty))
        );
    }

    #[test]
    fn parse_range_starting_with_whitespace_is_valid() {
        let input = "bytes= 0-15";
        let parsed = parse_range_header(input);
        assert_eq!(Ok(vec![0..=15]), parsed.unwrap().validate(TEST_FILE_LENGTH));
    }

    #[test]
    fn parse_range_token_starting_with_whitespace_as_invalid() {
        let input = " bytes=0-15";
        let parsed = parse_range_header(input);
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::DoesNotStartWithToken
            ))
        );
    }

    #[test]
    fn parse_range_strict_parse_numerical() {
        let input = "bytes=+0-15";
        let parsed = parse_range_header(input);
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable))
        );
    }

    #[test]
    fn parse_bad_unit_as_invalid() {
        let input = "abcde=0-10";
        let parsed = parse_range_header(input);
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::DoesNotStartWithToken
            ))
        );
    }

    #[test]
    fn parse_missing_equals_as_malformed() {
        let input = "bytes0-10";
        let parsed = parse_range_header(input);
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::DoesNotStartWithToken
            ))
        );
    }

    #[test]
    fn parse_negative_bad_characters_in_range_as_malformed() {
        let input = "bytes=1-10a";
        let parsed = parse_range_header(input);
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable))
        );
    }

    #[test]
    fn parse_negative_numbers_as_malformed() {
        let input = "bytes=-1-10";
        let parsed = parse_range_header(input);
        // Becomes bad eor, since -1 signals suffixed range
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable))
        );
    }

    #[test]
    fn parse_bad_characters_in_start_of_range() {
        let input = "bytes=a1-10";
        let parsed = parse_range_header(input);
        // Becomes bad eor, since -1 signals suffixed range
        assert_eq!(
            parsed,
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable))
        );
    }

    #[test]
    fn parse_out_of_bounds_overrun_as_content_length() {
        let input = &format!("bytes=0-{}", TEST_FILE_LENGTH);
        let expect = vec![RangeInclusive::new(0, TEST_FILE_LENGTH - 1)];
        let actual = parse_range_header(input)
            .unwrap()
            .validate(TEST_FILE_LENGTH)
            .unwrap();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_suffix_longer_than_file_as_whole_file() {
        let input = &format!("bytes=-{}", TEST_FILE_LENGTH + 1);
        let parsed = parse_range_header(input)
            .unwrap()
            .validate(TEST_FILE_LENGTH)
            .unwrap();
        assert_eq!(parsed, vec![0..=TEST_FILE_LENGTH - 1]);
    }

    #[test]
    fn parse_suffix_of_empty_file_as_satisfiable_returns_no_ranges() {
        let parsed = parse_range_header("bytes=-1").unwrap().validate(0);
        assert_eq!(parsed, Ok(vec![]));
    }

    #[test]
    fn parse_zero_length_suffix_as_unsatisfiable() {
        let input = "bytes=-0";
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(
            parsed.validate(TEST_FILE_LENGTH),
            Err(RangeUnsatisfiableError::Unsatisfiable)
        );
    }

    #[test]
    fn parse_zero_length_suffix_retains_satisfiable_ranges() {
        let input = "bytes=15-20,-0";
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(Ok(vec![15..=20]), parsed.validate(TEST_FILE_LENGTH));
    }

    #[test]
    fn retains_satisfiable_ranges() {
        let input = "bytes=10-20,0-0";
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(Ok(vec![0..=0]), parsed.validate(10));
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(Ok(vec![10..=19, 0..=0]), parsed.validate(20));
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(Ok(vec![10..=20, 0..=0]), parsed.validate(21));
    }

    #[test]
    fn rejects_invalid_range_even_when_oob() {
        let input = "bytes=20-10,0-0";
        assert_eq!(
            parse_range_header(input),
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Reversed)),
        );
    }

    #[test]
    fn retains_satisfiable_ranges_reordered() {
        let input = "bytes=0-0,10-20";
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(Ok(vec![0..=0]), parsed.validate(10));
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(Ok(vec![0..=0, 10..=19]), parsed.validate(20));
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(Ok(vec![0..=0, 10..=20]), parsed.validate(21));
    }

    #[test]
    fn parse_single_reversed_as_invalid() {
        let input = "bytes=15-0";
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Reversed)),
            parse_range_header(input),
        );
    }

    #[test]
    fn parse_zero_range_as_invalid() {
        let input = "bytes=15-";
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(
            parsed.validate(0),
            Err(RangeUnsatisfiableError::Unsatisfiable)
        );
    }

    #[test]
    fn empty_file_quirks() {
        let parsed = parse_range_header("bytes=-0").unwrap();
        assert_eq!(
            parsed.validate(0),
            Err(RangeUnsatisfiableError::Unsatisfiable)
        );
        let parsed = parse_range_header("bytes=-0,-1").unwrap();
        assert_eq!(parsed.validate(0), Ok(vec![]));
    }

    #[test]
    fn parse_multi_range() {
        let input = "bytes=0-1023, 2015-3000, 4000-4500, 8000-9999";
        let expected_ranges = vec![
            SyntacticallyCorrectRange::Indexed(0, 1023),
            SyntacticallyCorrectRange::Indexed(2015, 3000),
            SyntacticallyCorrectRange::Indexed(4000, 4500),
            SyntacticallyCorrectRange::Indexed(8000, 9999),
        ];
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(expected_ranges, parsed.ranges);
        let validated = parsed.validate(TEST_FILE_LENGTH).unwrap();
        assert_eq!(
            vec![0..=1023, 2015..=3000, 4000..=4500, 8000..=9999],
            validated
        );
    }

    #[test]
    fn parse_multi_range_with_open() {
        let input = "bytes=0-1023, 1024-";
        let expected_ranges = vec![
            SyntacticallyCorrectRange::Indexed(0, 1023),
            SyntacticallyCorrectRange::FromStart(1024),
        ];
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(expected_ranges, parsed.ranges);
        let validated = parsed.validate(TEST_FILE_LENGTH).unwrap();
        assert_eq!(vec![0..=1023, 1024..=9999], validated);
    }

    #[test]
    fn parse_multi_range_with_suffix() {
        let input = "bytes=0-1023, -1000";
        let expected_ranges = vec![
            SyntacticallyCorrectRange::Indexed(0, 1023),
            SyntacticallyCorrectRange::FromLast(1000),
        ];
        let parsed = parse_range_header(input).unwrap();
        assert_eq!(expected_ranges, parsed.ranges);
        let validated = parsed.validate(TEST_FILE_LENGTH).unwrap();
        assert_eq!(vec![0..=1023, 9000..=9999], validated);
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_standard() {
        let prepared = parse_range_header("bytes=500-700,601-999").unwrap();
        assert_eq!(
            Ok(vec![500..=700, 601..=999]),
            prepared.validate(TEST_FILE_LENGTH)
        );
        let prepared = parse_range_header("bytes=0-1023, 500-800").unwrap();
        assert_eq!(
            Ok(vec![0..=1023, 500..=800]),
            prepared.validate(TEST_FILE_LENGTH)
        );
        let prepared = parse_range_header("bytes=0-0, 0-15").unwrap();
        assert_eq!(Ok(vec![0..=0, 0..=15]), prepared.validate(TEST_FILE_LENGTH));
        let prepared = parse_range_header("bytes=0-20, 20-35").unwrap();
        assert_eq!(
            Ok(vec![0..=20, 20..=35]),
            prepared.validate(TEST_FILE_LENGTH)
        );
        let input = "bytes=0-1023, 500-800, 450-650";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
        let input = "bytes=0-1023, 500-800, 1000-1001";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
        let input = "bytes=0-1023, 500-800, 1000-";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
        let input = "bytes=0-, 0-0, 0-15";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
        let input = "bytes=0-20, 20-35, 35-";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_open() {
        let input = "bytes=0-, 1-, 5000-6000";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
        let parsed = parse_range_header("bytes=0-, 5000-6000").unwrap();
        assert_eq!(
            Ok(vec![0..=TEST_FILE_LENGTH - 1, 5000..=6000]),
            parsed.validate(TEST_FILE_LENGTH)
        );
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_suffixed() {
        let parsed = parse_range_header("bytes=8000-9000, -1001").unwrap();
        assert_eq!(
            Ok(vec![8000..=9000, 8999..=TEST_FILE_LENGTH - 1]),
            parsed.validate(TEST_FILE_LENGTH)
        );
        let parsed = parse_range_header("bytes=8000-9000, -1000").unwrap();
        assert_eq!(
            Ok(vec![8000..=9000, 9000..=TEST_FILE_LENGTH - 1]),
            parsed.validate(TEST_FILE_LENGTH)
        );
        let input = "bytes=8000-9000, -1001, -500";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
        let input = "bytes=8000-9000, -1000, -400";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_suffixed_open() {
        let parsed = parse_range_header("bytes=0-, -1").unwrap();
        assert_eq!(
            Ok(vec![
                0..=TEST_FILE_LENGTH - 1,
                TEST_FILE_LENGTH - 1..=TEST_FILE_LENGTH - 1
            ]),
            parsed.validate(TEST_FILE_LENGTH)
        );
        let input = "bytes=0-, 5-6, -1";
        assert_validation_err(
            input,
            RangeUnsatisfiableError::Rejected(RangeRejected::TooManyOverlapping),
        );
    }

    #[test]
    fn parse_start_boundaries() {
        let parsed = parse_range_header("bytes=9999-").unwrap();
        assert_eq!(Ok(vec![9999..=9999]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=10000-").unwrap();
        assert_eq!(
            Err(RangeUnsatisfiableError::Unsatisfiable),
            parsed.validate(TEST_FILE_LENGTH)
        );
    }

    #[test]
    fn parse_multi_range_with_a_reversed_as_invalid() {
        let input = "bytes=0-15, 30-20";
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Reversed)),
            parse_range_header(input)
        );
    }

    #[track_caller]
    fn assert_validation_err(input: &str, err: RangeUnsatisfiableError) {
        let parsed = parse_range_header(input)
            .unwrap()
            .validate(TEST_FILE_LENGTH);
        assert_eq!(Err(err), parsed);
    }

    #[test]
    fn parse_multi_range_rejects_invalid() {
        let input = "bytes=0-15, 25, 9, ";
        let parsed = parse_range_header(input);
        assert!(parsed.is_err());
    }

    #[quickcheck_macros::quickcheck]
    #[allow(clippy::needless_pass_by_value)]
    fn never_panics(input: String) -> quickcheck::TestResult {
        if let Ok(passed_first_pass) = parse_range_header(&input) {
            let _v = passed_first_pass.validate(u64::MAX);
            quickcheck::TestResult::passed()
        } else {
            quickcheck::TestResult::passed()
        }
    }

    #[quickcheck_macros::quickcheck]
    #[allow(clippy::needless_pass_by_value)]
    fn never_panics_empty_validate(input: String) -> quickcheck::TestResult {
        if let Ok(passed_first_pass) = parse_range_header(&input) {
            let _v = passed_first_pass.validate(0);
            quickcheck::TestResult::passed()
        } else {
            quickcheck::TestResult::passed()
        }
    }

    #[test]
    #[allow(clippy::cast_possible_truncation)]
    fn zero_length_file_does_not_return_an_unusable_range_on_suffixed() {
        const BYTES: &[u8; 0] = &[];
        let parsed = parse_range_header("bytes=-1").unwrap();
        let val = parsed.validate(0).unwrap();
        for range in val {
            for val in range {
                let value = BYTES[val as usize];
                // This is just a dummy value, the array isn't indexable and should explode
                assert_eq!(15, value);
            }
        }
    }

    #[test]
    fn zero_length_file_does_not_accept_any_staring_range() {
        let parsed = parse_range_header("bytes=0-").unwrap();
        assert_eq!(
            Err(RangeUnsatisfiableError::Unsatisfiable),
            parsed.validate(0)
        );
        let parsed = parse_range_header("bytes=0-0").unwrap();
        assert_eq!(
            Err(RangeUnsatisfiableError::Unsatisfiable),
            parsed.validate(0)
        );
        let parsed = parse_range_header("bytes=0-100").unwrap();
        assert_eq!(
            Err(RangeUnsatisfiableError::Unsatisfiable),
            parsed.validate(0)
        );
    }

    #[test]
    fn zero_length_file_will_not_give_an_error_if_any_range_is_satisfiable() {
        // https://www.rfc-editor.org/rfc/rfc9110.html#section-14.1.2-12
        let parsed = parse_range_header("bytes=0-0,-1").unwrap();
        assert_eq!(Ok(vec![]), parsed.validate(0));
        let parsed = parse_range_header("bytes=1-,-1").unwrap();
        assert_eq!(Ok(vec![]), parsed.validate(0));
    }

    #[test]
    fn zero_length_file_will_not_accept_reversed_ranges() {
        assert_eq!(
            parse_range_header("bytes=15-0,-1"),
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Reversed)),
        );
    }

    #[test]
    fn accepts_any_case() {
        let _parsed = parse_range_header("bytes=0-0").unwrap();
        let _parsed = parse_range_header("Bytes=0-0").unwrap();
        let _parsed = parse_range_header("ByTeS=0-0").unwrap();
    }

    #[test]
    fn accepts_leading_zeroes() {
        // https://www.rfc-editor.org/rfc/rfc9110.html#section-14.1.1
        // Spec only says one or more digits
        let parsed = parse_range_header("bytes=1-2").unwrap();
        assert_eq!(Ok(vec![1..=2]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=01-2").unwrap();
        assert_eq!(Ok(vec![1..=2]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=001-2").unwrap();
        assert_eq!(Ok(vec![1..=2]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=00001-2").unwrap();
        assert_eq!(Ok(vec![1..=2]), parsed.validate(TEST_FILE_LENGTH));
    }

    #[test]
    fn accepts_whitespace_around_separators() {
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace
            )),
            parse_range_header("bytes=1-2 ")
        );
        parse_range_header("bytes= , 0-1,3-4").unwrap();
        parse_range_header("bytes=0-1,3-4").unwrap();
        parse_range_header("bytes=0-1, 3-4").unwrap();
        parse_range_header("bytes=0-1,  3-4").unwrap();
        parse_range_header("bytes=0-1 , 3-4").unwrap();
        parse_range_header("bytes=0-1  ,3-4").unwrap();
        parse_range_header("bytes=0-1,\t3-4").unwrap();
        parse_range_header("bytes=0-1,\t\t3-4").unwrap();
        parse_range_header("bytes=0-1 ,\t3-4").unwrap();
        parse_range_header("bytes=0-1 \t,3-4").unwrap();
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace
            )),
            parse_range_header("bytes=0-1,\n3-4")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace
            )),
            parse_range_header("bytes=0-1,\n 3-4")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace
            )),
            parse_range_header("bytes=0-1\n, 3-4")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace
            )),
            parse_range_header("bytes=0-1,3-4\n")
        );
    }

    #[test]
    fn rejects_long_number_even_if_its_not_a_number() {
        // Guards against an infinite `0`'s string
        let expect = ParsedRanges {
            ranges: vec![SyntacticallyCorrectRange::Indexed(0, 15)],
        };
        assert_eq!(
            Ok(expect),
            parse_range_header("bytes=0-000000000000000000000000000015")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Rejected(
                RangeRejected::TooManyDigits
            )),
            parse_range_header("bytes=0-0000000000000000000000000000015")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Rejected(
                RangeRejected::TooManyDigits
            )),
            parse_range_header("bytes=0-xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")
        );
    }

    #[test]
    fn accepts_max_u64_value() {
        let parsed = parse_range_header("bytes=0-18446744073709551615").unwrap();
        assert_eq!(
            Ok(vec![0..=TEST_FILE_LENGTH.saturating_sub(1)]),
            parsed.validate(TEST_FILE_LENGTH)
        );
    }
    #[test]
    fn does_not_accept_a_completely_empty_range() {
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::NoNonempty)),
            parse_range_header("bytes=")
        );
    }

    #[test]
    fn accepts_a_few_empty_elements() {
        let parsed = parse_range_header("bytes=0-1,,3-4,").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=,0-1,,3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=0-1,,3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=0-1 , , 3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=0-1 ,, , 3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=0-1 , , , 3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=0-1 ,, ,, 3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=0-1 ,,,,, 3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));

        let parsed = parse_range_header("bytes=0-1,,,,,,,,,,,,,,,3-4").unwrap();
        assert_eq!(Ok(vec![0..=1, 3..=4]), parsed.validate(TEST_FILE_LENGTH));
        assert_eq!(
            Err(RangeUnsatisfiableError::Rejected(
                RangeRejected::TooManyUnparseable
            )),
            parse_range_header("bytes=0-1,,,,,,,,,,,,,,,,3-4")
        );
    }

    #[test]
    fn regression_empty_err_on_only_comma() {
        let parsed = parse_range_header("bytes=,,");
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::NoNonempty)),
            parsed
        );
        let parsed = parse_range_header("bytes=,  ,");
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::NoNonempty)),
            parsed
        );
    }

    #[test]
    fn regression_disallowed_valid_white_spacing_allowed_invalid_white_spacing() {
        let _parsed = parse_range_header("bytes=0-1 ,").unwrap();
        // No trailing whitespace
        let parsed = parse_range_header("bytes=0-1 ");
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::IllegalWhitespace
            )),
            parsed
        );
        // An empty group is allowed
        let _parsed = parse_range_header("bytes=0-1, ").unwrap();
    }

    #[test]
    fn regression_u64_overflow_clamps_to_end_of_file() {
        let parsed = parse_range_header("bytes=0-18446744073709551615000000000").unwrap();
        assert_eq!(Ok(vec![0..=9999]), parsed.validate(TEST_FILE_LENGTH));
        let parsed = parse_range_header("bytes=-18446744073709551615000000000").unwrap();
        assert_eq!(Ok(vec![0..=9999]), parsed.validate(TEST_FILE_LENGTH));
        let parsed =
            parse_range_header("bytes=18446744073709551615000000000-18446744073709551615000000000")
                .unwrap();
        assert_eq!(
            Err(RangeUnsatisfiableError::Unsatisfiable),
            parsed.validate(TEST_FILE_LENGTH)
        );
    }

    #[test]
    fn regression_u64_parsing_allows_garbage() {
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable)),
            parse_range_header("bytes=0-99999999999999999999abc")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable)),
            parse_range_header("bytes=0-99999999999999999999-5")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable)),
            parse_range_header("bytes=0-99999999999999999999 5")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable)),
            parse_range_header("bytes=-99999999999999999999abc")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable)),
            parse_range_header("bytes=99999999999999999999abc-,0-1")
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(RangeInvalid::Unparseable)),
            parse_range_header("bytes=0-18446744073709551615x")
        );
    }

    #[test]
    fn regression_char_boundary_check() {
        assert_eq!(
            Err(RangeUnsatisfiableError::Invalid(
                RangeInvalid::DoesNotStartWithToken
            )),
            parse_range_header("bytesé=0-1")
        );
    }

    #[test]
    fn spec_contradiction() {
        // The spec gives this as an example:
        // <https://www.rfc-editor.org/rfc/rfc9110.html#section-14.1.2-9.3.1>
        // But in the definition <https://www.rfc-editor.org/rfc/rfc9110.html#section-5.6.1.2-2>
        // it does not define optional leading whitespace.
        // Edit: Errata here, this should pass
        // <https://errata.rfc-editor.org/eid7306/>
        assert_eq!(
            Ok(vec![0..=999, 4500..=5499, 9000..=9999]),
            parse_range_header("bytes= 0-999, 4500-5499, -1000")
                .unwrap()
                .validate(TEST_FILE_LENGTH)
        );
    }

    #[test]
    fn default_100_ranges() {
        let mut spec = "bytes=".to_string();
        let cases = 200;
        for i in (0..cases).step_by(2) {
            let start = i;
            let end = i + 1;
            spec.write_fmt(format_args!("{}-{},", start, end)).unwrap();
        }
        spec.pop();
        let parsed = parse_range_header(&spec).unwrap();
        parsed.validate(TEST_FILE_LENGTH).unwrap();
        let mut spec = "bytes=".to_string();
        let cases = 200;
        for i in (0..cases).rev().step_by(2) {
            let start = i;
            let end = i + 1;
            spec.write_fmt(format_args!("{}-{},", start, end)).unwrap();
        }
        spec.pop();
        let parsed = parse_range_header(&spec).unwrap();
        parsed.validate(TEST_FILE_LENGTH).unwrap();
        let mut spec = "bytes=".to_string();
        let cases = 201;
        for i in (0..cases).rev().step_by(2) {
            let start = i;
            let end = i + 1;
            spec.write_fmt(format_args!("{}-{},", start, end)).unwrap();
        }
        spec.pop();

        assert_eq!(
            Err(RangeUnsatisfiableError::Rejected(RangeRejected::TooMany)),
            parse_range_header(&spec)
        );
    }

    #[test]
    fn random_ranges_overlap_check() {
        // These ranges don't overlap, and shouldn't in any order
        let mut ranges = Vec::with_capacity(100);
        let cases = 200;
        for i in (0..cases).rev().step_by(2) {
            let start = i;
            let end = i + 1;
            ranges.push(format!("{}-{},", start, end));
        }
        let mut rng = rand::rng();
        ranges.shuffle(&mut rng);
        let mut spec = "bytes=".to_string();
        for val in ranges {
            spec.push_str(&val);
        }
        spec.pop();
        let parsed = parse_range_header(&spec).unwrap();
        parsed.validate(TEST_FILE_LENGTH).unwrap();
    }

    #[test]
    fn configurable_ranges() {
        assert!(
            parse_range_header_with_max_ranges("bytes=1-2", NonZeroUsize::new(1).unwrap()).is_ok()
        );
        assert_eq!(
            Err(RangeUnsatisfiableError::Rejected(RangeRejected::TooMany)),
            parse_range_header_with_max_ranges("bytes=1-2,2-3", NonZeroUsize::new(1).unwrap())
        );
    }

    fn single_range(syntactically_correct: SyntacticallyCorrectRange) -> ParsedRanges {
        ParsedRanges::new(vec![syntactically_correct])
    }
}
