mod macros;
use std::ops::RangeInclusive;

pub struct RangeHeaderParserBuilder<'a> {
    file_size: Option<u64>,
    unit_label: Option<&'a str>,
}

impl<'a> RangeHeaderParserBuilder<'a> {
    pub fn new() -> Self {
        Self {
            file_size: None,
            unit_label: None,
        }
    }

    pub fn with_file_size(self, file_size: u64) -> Self {
        Self {
            file_size: Some(file_size),
            unit_label: self.unit_label,
        }
    }

    pub fn with_unit_label(self, unit_label: &'a str) -> Self {
        Self {
            file_size: self.file_size,
            unit_label: Some(unit_label),
        }
    }

    pub fn build(self) -> RangeHeaderParser {
        RangeHeaderParser {
            file_size: self.file_size.unwrap_or(u64::MAX),
            unit_sep: self.unit_label.map(|s| format!("{}=", s)).unwrap_or("bytes=".to_owned())
        }
    }


}

pub struct RangeHeaderParser {
    file_size: u64,
    unit_sep: String,
}

impl RangeHeaderParser {
    pub fn parse(&self, range_header_value: &str) -> ParsedRangeHeader {
        parse_range_header_value(range_header_value, self.file_size, &self.unit_sep)
    }
}


/// Function that parses the content of a range-header
/// If correctly formatted returns the requested ranges
/// If syntactically correct but unsatisfiable due to file-constraints returns `Unsatisfiable`
/// If un-parseable as a range returns `Malformed`
fn parse_range_header_value(range_header_value: &str, file_size: u64, unit_sep: &str) -> ParsedRangeHeader {
    if !range_header_value.starts_with(unit_sep) {
        return malformed!(format!(
                    "Range: {} is not acceptable, does not start with {}",
                    range_header_value,
                    unit_sep,
                ));
    }
    let unit_sep_count = range_header_value.match_indices(unit_sep).count();
    if unit_sep_count != 1 {
        return malformed!(format!(
                    "Range: {} is not acceptable, unit separator {} occurs more than once",
                    range_header_value,
                    unit_sep,
                ));
    }
    let start = split_once(range_header_value, unit_sep);
    let mut ranges = Vec::new();
    if let Some((_, indicated_range)) = start {
        for range in indicated_range.split(", ") {
            if range.contains(' ') {
                return malformed!(format!(
                    "Range: {} is not acceptable, contains whitespace in range part.",
                    range
                ));
            }
            let sep_count = range.match_indices("-").count();
            if sep_count != 1 {
                return malformed!(format!(
                    "Range: {} is not acceptable, contains multiple dashes (-).",
                    range
                ));
            }
            if let Some((start, end)) = split_once(range, "-") {
                if start == "" {
                    if let Some(end) = strict_parse_u64(end) {
                        if end >= file_size {
                            return unsatisfiable!(format!(
                                "Range: {} is not satisfiable, end of range exceeds file boundary.",
                                range
                            ));
                        }
                        if end == 0 {
                            return unsatisfiable!(format!("Range: {} is not satisfiable, suffixed number of bytes to retrieve is zero.", range));
                        }
                        let start = file_size - 1 - end;
                        ranges.push(RangeInclusive::new(start, file_size - 1));
                        continue;
                    }
                    return malformed!(format!(
                        "Range: {} is not acceptable, end of range not parseable.",
                        range
                    ));
                }
                if let Some(start) = strict_parse_u64(start) {
                    if end == "" {
                        ranges.push(RangeInclusive::new(start, file_size - 1));
                        continue;
                    }
                    if let Some(end) = strict_parse_u64(end) {
                        if end >= file_size {
                            return unsatisfiable!(format!(
                                "Range: {} is not satisfiable, end of range exceeds file boundary.",
                                range
                            ));
                        }
                        ranges.push(RangeInclusive::new(start, end));
                        continue;
                    }
                    return malformed!(format!(
                        "Range: {} is not acceptable, end of range not parseable.",
                        range
                    ));
                }
                return malformed!(format!(
                    "Range: {} is not acceptable, start of range not parseable.",
                    range
                ));
            }
            return malformed!(format!(
                "Range: {} is not acceptable, range does not contain any dashes.",
                range
            ));
        }
    } else {
        return malformed!(format!(
            "Range: {} is not acceptable, range does not start with '{}='",
            range_header_value,
            unit_sep
        ));
    }
    if ranges.is_empty() {
        return malformed!(format!(
            "Range: {} could not be parsed for an unknown reason, please file an issue",
            range_header_value
        ));
    } else {
        match validate_ranges(&ranges) {
            RangeValidationResult::Valid => ParsedRangeHeader::Range(ranges),
            RangeValidationResult::Overlapping => unsatisfiable!(format!(
                "Range header: {} is not satisfiable, ranges overlap",
                range_header_value
            )),
            RangeValidationResult::Reversed => unsatisfiable!(format!(
                "Range header: {} is not satisfiable, range reversed",
                range_header_value
            )),
            RangeValidationResult::Empty => unsatisfiable!(format!(
                "Range header: {} is not satisfiable, range empty",
                range_header_value
            ))
        }

    }
}

fn strict_parse_u64(s: &str) -> Option<u64> {
    if !s.starts_with("+") && !s.starts_with("0") {
        return s.parse().ok();
    }
    None
}

enum RangeValidationResult {
    Valid,
    Overlapping,
    Empty,
    Reversed,
}

fn validate_ranges(ranges: &[RangeInclusive<u64>]) -> RangeValidationResult {
    let mut bounds = Vec::new();
    for range in ranges {
        let start = range.start();
        let end = range.end();
        if start > end {
            return RangeValidationResult::Reversed;
        }
        if start == end {
            return RangeValidationResult::Empty;
        }
        bounds.push((range.start(), range.end()));
    }
    for i in 0..bounds.len() {
        for j in i + 1..bounds.len() {
            if bounds[i].0 <= bounds[j].1 && bounds[j].0 <= bounds[i].1 {
                return RangeValidationResult::Overlapping
            }
        }
    }
    RangeValidationResult::Valid
}

fn split_once<'a>(s: &'a str, pat: &'a str) -> Option<(&'a str, &'a str)> {
    let mut iter = s.split(pat);
    let left = iter.next()?;
    let right = iter.next()?;
    Some((left, right))
}


#[derive(Debug, PartialEq)]
#[cfg(feature = "debug")]
pub enum ParsedRangeHeader {
    Range(Vec<RangeInclusive<u64>>),
    Unsatisfiable(String),
    Malformed(String),
}

#[derive(Debug, PartialEq)]
#[cfg(not(feature = "debug"))]
pub enum ParsedRangeHeader {
    Range(Vec<RangeInclusive<u64>>),
    Unsatisfiable,
    Malformed,
}

impl ParsedRangeHeader {

}


#[cfg(test)]
mod tests {
    use std::ops::RangeInclusive;
    use crate::{ParsedRangeHeader, parse_range_header_value, RangeHeaderParserBuilder};

    const TEST_FILE_LENGTH: u64 = 10_000;

    #[test]
    fn fuzz() {
    }

    #[test]
    fn parse_with_builder() {
        let parser = RangeHeaderParserBuilder::new()
            .with_file_size(TEST_FILE_LENGTH)
            .build();
        let input = "bytes=0-1023";
        assert_eq!(
            ParsedRangeHeader::Range(vec![RangeInclusive::new(0, 1023)]),
            parser.parse(input)
        );
    }

    #[test]
    fn parse_standard_range() {
        let input = "bytes=0-1023";
        assert_eq!(
            ParsedRangeHeader::Range(vec![RangeInclusive::new(0, 1023)]),
            parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=")
        );
    }

    #[test]
    fn parse_standard_range_with_custom_unit() {
        let input = "my_unit=0-1023";
        assert_eq!(
            ParsedRangeHeader::Range(vec![RangeInclusive::new(0, 1023)]),
            parse_range_header_value(input, TEST_FILE_LENGTH, "my_unit=")
        );
    }

    #[test]
    fn parse_open_ended_range() {
        let input = &format!("bytes=0-{}", TEST_FILE_LENGTH - 1);
        assert_eq!(
            ParsedRangeHeader::Range(vec![RangeInclusive::new(0, TEST_FILE_LENGTH - 1)]),
            parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=")
        );
    }

    #[test]
    fn parse_suffix_range() {
        let input = "bytes=-15";
        assert_eq!(
            ParsedRangeHeader::Range(vec![RangeInclusive::new(
                TEST_FILE_LENGTH - 15 - 1,
                TEST_FILE_LENGTH - 1
            )]),
            parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=")
        );
    }

    #[test]
    fn parse_empty_as_malformed() {
        let input = "";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_malformed(parsed);
    }

    #[test]
    fn parse_empty_range_as_malformed() {
        let input = "bytes=";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_malformed(parsed);
    }

    #[test]
    fn parse_bad_unit_as_malformed() {
        let input = "abcde=0-10";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_malformed(parsed);
    }

    #[test]
    fn parse_missing_equals_as_malformed() {
        let input = "abcde0-10";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_malformed(parsed);
    }

    #[test]
    fn parse_negative_bad_characters_in_range_as_malformed() {
        let input = "bytes=1-10a";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_malformed(parsed);
    }

    #[test]
    fn parse_negative_numbers_as_malformed() {
        let input = "bytes=-1-10";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_malformed(parsed);
    }

    #[test]
    fn parse_out_of_bounds_overrun_as_unsatisfiable() {
        let input = &format!("bytes=0-{}", TEST_FILE_LENGTH);
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_unsatisfiable(parsed);
    }

    #[test]
    fn parse_out_of_bounds_suffix_overrun_as_unsatisfiable() {
        let input = &format!("bytes=-{}", TEST_FILE_LENGTH);
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_unsatisfiable(parsed);
    }

    #[test]
    fn parse_zero_length_suffix_as_unsatisfiable() {
        let input = &format!("bytes=-0");
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_unsatisfiable(parsed);
    }

    #[test]
    fn parse_multi_range() {
        let input = "bytes=0-1023, 2015-3000, 4000-4500, 8000-9999";
        let expected_ranges = vec![
            RangeInclusive::new(0, 1023),
            RangeInclusive::new(2015, 3000),
            RangeInclusive::new(4000, 4500),
            RangeInclusive::new(8000, 9999),
        ];
        let expect = ParsedRangeHeader::Range(expected_ranges);
        assert_eq!(expect, parse_range_header_value(input, 10_000, "bytes="));
    }

    #[test]
    fn parse_multi_range_with_open() {
        let input = "bytes=0-1023, 1024-";
        let expected_ranges = vec![
            RangeInclusive::new(0, 1023),
            RangeInclusive::new(1024, 9999),
        ];
        let expect = ParsedRangeHeader::Range(expected_ranges);
        assert_eq!(expect, parse_range_header_value(input, 10_000, "bytes="));
    }

    #[test]
    fn parse_multi_range_with_suffix() {
        let input = "bytes=0-1023, -1000";
        let expected_ranges = vec![
            RangeInclusive::new(0, 1023),
            RangeInclusive::new(8999, 9999),
        ];
        let expect = ParsedRangeHeader::Range(expected_ranges);
        assert_eq!(expect, parse_range_header_value(input, 10_000, "bytes="));
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_standard() {
        let input = "bytes=0-1023, 500-800";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_unsatisfiable(parsed);
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_open() {
        let input = "bytes=0-, 5000-6000";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_unsatisfiable(parsed);
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_suffixed() {
        let input = "bytes=8000-9000, -1001";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_unsatisfiable(parsed);
    }

    #[test]
    fn parse_overlapping_multi_range_as_unsatisfiable_suffixed_open() {
        let input = "bytes=0-, -1";
        let parsed = parse_range_header_value(input, TEST_FILE_LENGTH, "bytes=");
        assert_unsatisfiable(parsed);
    }

    #[cfg(feature = "debug")]
    fn assert_unsatisfiable(left: ParsedRangeHeader) {
        assert!(matches!(left, ParsedRangeHeader::Unsatisfiable(_)))
    }

    #[cfg(not(feature = "debug"))]
    fn assert_unsatisfiable(left: ParsedRangeHeader) {
        assert_eq!(left, ParsedRangeHeader::Unsatisfiable)
    }

    #[cfg(feature = "debug")]
    fn assert_malformed(left: ParsedRangeHeader) {
        assert!(matches!(left, ParsedRangeHeader::Malformed(_)))
    }

    #[cfg(not(feature = "debug"))]
    fn assert_malformed(left: ParsedRangeHeader) {
        assert_eq!(left, ParsedRangeHeader::Malformed)
    }
}
