mod macros;
use std::ops::RangeInclusive;

/// Function that parses the content of a range header
/// Follows the spec here https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Range
/// But with a bit more lax parsing, leaving the user to determine whether or not to accept partially invalid ranges
///
/// # Example with a standard valid range
///
/// ```
/// let input = "bytes=0-15";///
/// let file_size_bytes = 512;
/// let parsed_ranges = parse_range_headers::parse_range_header(input);
/// if parsed_ranges.any_invalid() {
///     // Hande malformed ranges, just return a 416 or silently ignore
/// }
/// if parsed_ranges.any_well_formed() {
///     // To know if a given range is valid we need to know the underlying content size
///     let validated = parsed_ranges.validate(file_size_bytes);
///     for range in validated {
///         match range {
///
///         }
///     }
///
/// }
/// // This will serve files in the "assets" directory and
/// // its subdirectories
/// let service = ServeDir::new("assets");
///
/// # async {
/// // Run our service using `hyper`
/// let addr = std::net::SocketAddr::from(([127, 0, 0, 1], 3000));
/// hyper::Server::bind(&addr)
///     .serve(tower::make::Shared::new(service))
///     .await
///     .expect("server error");
/// # };
/// ```
///
pub fn parse_range_header(range_header_value: &str) -> ParsedRanges {
    parse_range_header_value(range_header_value, "bytes=")
}

pub fn parse_range_header_with_unit(range_header_value: &str, unit: &str) -> ParsedRanges {
    parse_range_header_value(range_header_value, &format!("{}=", unit))
}

#[inline]
fn parse_range_header_value(range_header_value: &str, unit_sep: &str) -> ParsedRanges {
    if !range_header_value.starts_with(unit_sep) {
        return ParsedRanges::single(invalid!(format!(
            "Range: {} is not acceptable, does not start with {}",
            range_header_value, unit_sep,
        )));
    }
    let unit_sep_count = range_header_value.match_indices(unit_sep).count();
    if unit_sep_count != 1 {
        return ParsedRanges::single(invalid!(format!(
            "Range: {} is not acceptable, unit separator {} occurs more than once",
            range_header_value, unit_sep,
        )));
    }
    let start = split_once(range_header_value, unit_sep);
    let mut ranges = ParsedRanges::empty();

    if let Some((_, indicated_range)) = start {
        for range in indicated_range.split(", ") {
            ranges.push(parse_inner(range));
        }
    } else {
        ranges.push(invalid!(format!(
            "Range: {} is not acceptable, range does not start with '{}'",
            range_header_value, unit_sep
        )));
    }
    if !ranges.any_invalid() && !ranges.any_well_formed() {
        ParsedRanges::single(invalid!(format!(
            "Range: {} could not be parsed for an unknown reason, please file an issue",
            range_header_value
        )))
    } else {
        ranges
    }
}

#[inline]
fn parse_inner(range: &str) -> ParsedRange {
    if range.contains(' ') {
        return invalid!(format!(
            "Range: {} is not acceptable, contains whitespace in range part.",
            range
        ));
    }
    let sep_count = range.match_indices("-").count();
    if sep_count != 1 {
        if sep_count == 0 {
            return invalid!(format!(
                "Range: {} is not acceptable, contains no dashes (-).",
                range
            ));
        } else {
            return invalid!(format!(
                "Range: {} is not acceptable, contains multiple dashes (-).",
                range
            ));
        }
    }
    if let Some((start, end)) = split_once(range, "-") {
        if start == "" {
            if let Some(end) = strict_parse_u64(end) {
                if end == 0 {
                    return invalid!(format!("Range: {} is not satisfiable, suffixed number of bytes to retrieve is zero.", range));
                } else {
                    return ParsedRange::syntactically_correct(
                        RangePosition::FromLast(end),
                        RangePosition::LastByte,
                    );
                }
            }
            return invalid!(format!(
                "Range: {} is not acceptable, end of range not parseable.",
                range
            ));
        }
        if let Some(start) = strict_parse_u64(start) {
            if end == "" {
                return ParsedRange::syntactically_correct(
                    RangePosition::Index(start),
                    RangePosition::LastByte,
                );
            }
            if let Some(end) = strict_parse_u64(end) {
                return ParsedRange::syntactically_correct(
                    RangePosition::Index(start),
                    RangePosition::Index(end),
                );
            }
            return invalid!(format!(
                "Range: {} is not acceptable, end of range not parseable.",
                range
            ));
        }
        return invalid!(format!(
            "Range: {} is not acceptable, start of range not parseable.",
            range
        ));
    }
    invalid!(format!(
        "Range: {} is not acceptable, range does not contain any dashes.",
        range
    ))
}

fn strict_parse_u64(s: &str) -> Option<u64> {
    if !s.starts_with("+") && (s.len() == 1 || !s.starts_with("0")) {
        return s.parse().ok();
    }
    None
}

fn split_once<'a>(s: &'a str, pat: &'a str) -> Option<(&'a str, &'a str)> {
    let mut iter = s.split(pat);
    let left = iter.next()?;
    let right = iter.next()?;
    Some((left, right))
}

#[derive(Debug, Eq, PartialEq)]
pub struct ParsedRanges {
    ranges: Vec<ParsedRange>,
    invalid: usize,
    well_formed: usize,
}

impl ParsedRanges {
    fn empty() -> Self {
        ParsedRanges {
            ranges: vec![],
            invalid: 0,
            well_formed: 0
        }
    }

    fn single(range: ParsedRange) -> Self {
        let mut new = ParsedRanges::empty();
        new.push(range);
        new
    }

    fn push(&mut self, range: ParsedRange) {
        if range.invalid() {
            self.invalid += 1;
        } else {
            self.well_formed += 1;
        }
        self.ranges.push(range);
    }

    pub fn any_invalid(&self) -> bool {
        self.invalid > 0
    }

    pub fn any_well_formed(&self) -> bool {
        self.well_formed > 0
    }

    pub fn num_invalid(&self) -> usize {
        self.invalid
    }

    pub fn num_well_formed(&self) -> usize {
        self.well_formed
    }

    pub fn validate(&self, file_size_bytes: u64) -> Vec<ValidatedRange> {
        let mut validated = Vec::new();
        let len = self.ranges.len();
        for parsed in &self.ranges {
            match parsed {
                ParsedRange::SyntacticallyCorrect(syntactically_correct) => {
                    let end = match syntactically_correct.end {
                        RangePosition::Index(i) => i,
                        RangePosition::LastByte => file_size_bytes - 1,
                        RangePosition::FromLast(_) => {
                            validated.push(unsatisfiable!(
                            "Problem parsing range, please file an issue".to_string()
                        ));
                            continue;
                        }
                    };
                    let start = match syntactically_correct.start {
                        RangePosition::Index(i) => i,
                        RangePosition::LastByte => {
                            validated.push(unsatisfiable!(
                            "Problem parsing range, please file an issue".to_string()
                        ));
                            continue;
                        }
                        RangePosition::FromLast(i) => {
                            let last_byte = file_size_bytes - 1;
                            if i > last_byte {
                                validated.push(unsatisfiable!(
                                "File suffix out of bounds (larger than file bytes)".to_string()
                            ));
                                continue;
                            }
                            file_size_bytes - i
                        }
                    };
                    if end < file_size_bytes {
                        let valid = RangeInclusive::new(start, end);
                        validated.push(ValidatedRange::Satisfiable(valid));
                        if len == 1 {
                            return validated;
                        }
                    } else {
                        validated.push(unsatisfiable!("Range end exceedes EOF".to_string()));
                        if len == 1 {
                            return validated;
                        }
                    }
                }
            }
        }
        match validate_ranges(validated.as_slice()) {
            RangeValidationResult::Valid => validated,
            RangeValidationResult::Overlapping => vec![unsatisfiable!("Ranges overlap")],
            RangeValidationResult::Reversed => vec![unsatisfiable!("Range reversed")],
        }
        validated
    }
}

#[derive(Debug, Clone)]
#[cfg(feature = "with_error_cause")]
pub enum ValidatedRange {
    Satisfiable(RangeInclusive<u64>),
    Unsatisfiable(String)
}

#[derive(Debug, Clone)]
#[cfg(not(feature = "with_error_cause"))]
pub enum ValidatedRange {
    Satisfiable(RangeInclusive<u64>),
    Unsatisfiable
}

enum RangeValidationResult {
    Valid,
    Overlapping,
    Reversed,
}

#[inline]
fn validate_ranges(ranges: &[RangeInclusive<u64>]) -> RangeValidationResult {
    let mut bounds = Vec::new();
    for range in ranges {
        let start = range.start();
        let end = range.end();
        if start > end {
            return RangeValidationResult::Reversed;
        }
        bounds.push((range.start(), range.end()));
    }
    for i in 0..bounds.len() {
        for j in i + 1..bounds.len() {
            if bounds[i].0 <= bounds[j].1 && bounds[j].0 <= bounds[i].1 {
                return RangeValidationResult::Overlapping;
            }
        }
    }
    RangeValidationResult::Valid
}

#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg(feature = "with_error_cause")]
pub enum ParsedRange {
    SyntacticallyCorrect(SyntacticallyCorrectRange),
    Invalid(String),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg(not(feature = "with_error_cause"))]
pub enum ParsedRange {
    SyntacticallyCorrect(SyntacticallyCorrectRange),
    Invalid,
}

impl ParsedRange {
    fn syntactically_correct(start: RangePosition, end: RangePosition) -> Self {
        ParsedRange::SyntacticallyCorrect(SyntacticallyCorrectRange::new(start, end))
    }

    #[cfg(feature = "with_error_cause")]
    pub fn invalid(&self) -> bool {
        matches!(self, ParsedRange::Invalid(_))
    }

    #[cfg(not(feature = "with_error_cause"))]
    pub fn invalid(&self) -> bool {
        matches!(self, ParsedRange::Invalid)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct SyntacticallyCorrectRange {
    start: RangePosition,
    end: RangePosition,
}

impl SyntacticallyCorrectRange {
    fn new(start: RangePosition, end_of_range: RangePosition) -> Self {
        SyntacticallyCorrectRange {
            start,
            end: end_of_range,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RangePosition {
    Index(u64),
    LastByte,
    FromLast(u64),
}

#[cfg(test)]
mod tests {
    use crate::{
        parse_range_header, parse_range_header_value, ParsedRange, ParsedRanges, RangePosition,
    };
    use std::ops::RangeInclusive;

    const TEST_FILE_LENGTH: u64 = 10_000;

    #[test]
    fn parse_standard_range() {
        let input = "bytes=0-1023";
        let expect = ParsedRange::syntactically_correct(RangePosition::Index(0), RangePosition::Index(1023));
        let actual = parse_range_header(input);
        assert_eq!(ParsedRanges::single(expect), actual);
        let expect = ParsedRange::Validated(RangeInclusive::new(0, 1023));
        let actual = actual.validate(TEST_FILE_LENGTH)[0].clone();
        assert_eq!(expect, actual)
    }

    #[test]
    fn parse_standard_range_with_custom_unit() {
        let input = "my_unit=0-1023";
        let expect = ParsedRange::syntactically_correct(RangePosition::Index(0), RangePosition::Index(1023));
        let actual = parse_range_header_value(input, "my_unit=");
        assert_eq!(ParsedRanges::single(expect), actual);
        let expect = ParsedRange::Validated(RangeInclusive::new(0, 1023));
        let actual = actual.validate(TEST_FILE_LENGTH)[0].clone();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_open_ended_range() {
        let input = "bytes=0-";
        let expect = ParsedRange::syntactically_correct(RangePosition::Index(0), RangePosition::LastByte);
        let actual = parse_range_header(input);
        assert_eq!(ParsedRanges::single(expect), actual);
        let expect = ParsedRange::Validated(RangeInclusive::new(0, TEST_FILE_LENGTH - 1));
        let actual = actual.validate(TEST_FILE_LENGTH)[0].clone();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_suffix_range() {
        let input = "bytes=-15";
        let expect = ParsedRange::syntactically_correct(RangePosition::FromLast(15), RangePosition::LastByte);
        let actual = parse_range_header(input);
        assert_eq!(ParsedRanges::single(expect), actual);
        let expect = ParsedRange::Validated(RangeInclusive::new(
            TEST_FILE_LENGTH - 15,
            TEST_FILE_LENGTH - 1,
        ));
        let actual = actual.validate(TEST_FILE_LENGTH)[0].clone();
        assert_eq!(expect, actual);
    }

    #[test]
    fn parse_empty_as_invalid() {
        let input = "";
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_empty_range_as_invalid() {
        let input = "bytes=";
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_bad_unit_as_invalid() {
        let input = "abcde=0-10";
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_missing_equals_as_malformed() {
        let input = "abcde0-10";
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_negative_bad_characters_in_range_as_malformed() {
        let input = "bytes=1-10a";
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_negative_numbers_as_malformed() {
        let input = "bytes=-1-10";
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_out_of_bounds_overrun_as_unsatisfiable() {
        let input = &format!("bytes=0-{}", TEST_FILE_LENGTH);
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_out_of_bounds_suffix_overrun_as_unsatisfiable() {
        let input = &format!("bytes=-{}", TEST_FILE_LENGTH);
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_zero_length_suffix_as_unsatisfiable() {
        let input = &format!("bytes=-0");
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH)[0].clone();
        assert_invalid(parsed);
    }

    #[test]
    fn parse_multi_range() {
        let input = "bytes=0-1023, 2015-3000, 4000-4500, 8000-9999";
        let expected_ranges = vec![
            ParsedRange::syntactically_correct(RangePosition::Index(0), RangePosition::Index(1023)),
            ParsedRange::syntactically_correct(RangePosition::Index(2015), RangePosition::Index(3000)),
            ParsedRange::syntactically_correct(RangePosition::Index(4000), RangePosition::Index(4500)),
            ParsedRange::syntactically_correct(RangePosition::Index(8000), RangePosition::Index(9999)),
        ];
        let mut expect = ParsedRanges::empty();
        expected_ranges.into_iter()
            .for_each(|pr| expect.push(pr));
        assert_eq!(expect, parse_range_header_value(input, "bytes="));
    }

    #[test]
    fn parse_multi_range_with_open() {
        let input = "bytes=0-1023, 1024-";
        let expected_ranges = vec![
            ParsedRange::syntactically_correct(RangePosition::Index(0), RangePosition::Index(1023)),
            ParsedRange::syntactically_correct(RangePosition::Index(1024), RangePosition::LastByte),
        ];
        let mut expect = ParsedRanges::empty();
        expected_ranges.into_iter()
            .for_each(|pr| expect.push(pr));
        assert_eq!(expect, parse_range_header_value(input, "bytes="));
    }

    #[test]
    fn parse_multi_range_with_suffix() {
        let input = "bytes=0-1023, -1000";
        let expected_ranges = vec![
            ParsedRange::syntactically_correct(RangePosition::Index(0), RangePosition::Index(1023)),
            ParsedRange::syntactically_correct(RangePosition::FromLast(1000), RangePosition::LastByte),
        ];
        let mut expect = ParsedRanges::empty();
        expected_ranges.into_iter()
            .for_each(|pr| expect.push(pr));
        assert_eq!(expect, parse_range_header_value(input, "bytes="));
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_standard() {
        let input = "bytes=0-1023, 500-800";
        let parsed =
            parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH);
        assert_eq!(1, parsed.len());
        assert_invalid(parsed[0].clone());
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_open() {
        let input = "bytes=0-, 5000-6000";
        let parsed = parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH);
        assert_eq!(1, parsed.len());
        assert_invalid(parsed[0].clone());
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_suffixed() {
        let input = "bytes=8000-9000, -1001";
        let parsed = parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH);
        assert_eq!(1, parsed.len());
        assert_invalid(parsed[0].clone());
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_suffixed_open() {
        let input = "bytes=0-, -1";
        let parsed = parse_range_header_value(input, "bytes=").validate(TEST_FILE_LENGTH);
        assert_eq!(1, parsed.len());
        assert_invalid(parsed[0].clone());
    }

    #[test]
    fn parse_multi_range_accepts_invalid() {
        let input = "bytes=0-15, 25, 9, ";
        let parsed = parse_range_header_value(input, "bytes=");
        assert_eq!(3, parsed.num_invalid());
        assert_eq!(1, parsed.num_well_formed());
        let validated = parsed.validate(TEST_FILE_LENGTH);
        let valid = validated.into_iter()
            .filter(|p| matches!(p, ParsedRange::Validated(_)))
            .count();
        assert_eq!(1, valid);
    }

    #[cfg(feature = "with_error_cause")]
    fn assert_invalid(left: ParsedRange) {
        assert!(matches!(left, ParsedRange::Invalid(_)))
    }

    #[cfg(not(feature = "with_error_cause"))]
    fn assert_invalid(left: ParsedRange) {
        assert!(matches!(left, ParsedRange::Invalid))
    }
}
