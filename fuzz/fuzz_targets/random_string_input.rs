#![no_main]
use libfuzzer_sys::fuzz_target;
use parse_range_headers::{RangeHeaderParserBuilder, ParsedRangeHeader};
use regex::Regex;

lazy_static::lazy_static! {
    static ref STANDARD_RANGE: Regex = Regex::new("^bytes=((\\d+-\\d+,\\s)|(\\d+-,\\s)|(-\\d+,\\s))*((\\d+-\\d+)|(\\d+-)|(-\\d+))+$").unwrap();
}

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if STANDARD_RANGE.is_match(s) {
            return;
        }

        let parser = RangeHeaderParserBuilder::new()
            .with_unit_label("bytes")
            .build();

        let parsed = parser.parse(s);

        assert!(parsed == ParsedRangeHeader::Unsatisfiable || parsed == ParsedRangeHeader::Malformed, "Range was not rejected input=`{}` range={:?}", s, parsed);
    }
});
