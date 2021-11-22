#![no_main]
use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::Arbitrary;
use parse_range_headers::{RangeHeaderParserBuilder, ParsedRangeHeader};
use regex::Regex;
use std::io::Write;
use std::fs::OpenOptions;
use headers::{HeaderValue, Range};
use regex::internal::Input;

lazy_static::lazy_static! {
    static ref STANDARD_RANGE: Regex = Regex::new("^bytes=((\\d+-\\d+,\\s)|(\\d+-,\\s)|(-\\d+,\\s))*((\\d+-\\d+)|(\\d+-)|(-\\d+))+$").unwrap();
}

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        /*
        let header = HeaderValue::from_static(s);
        let h = headers::Header::<Range>::decode(s);

         */
        if STANDARD_RANGE.is_match(s) {
            return;
        }
        let parser = RangeHeaderParserBuilder::new()
            .with_unit_label("bytes")
            .build();

        let parsed = parser.parse(s);
        /*
        if parsed != ParsedRangeHeader::Unsatisfiable && parsed != ParsedRangeHeader::Malformed {
            let mut file = OpenOptions::new()
            .read(true)
            .append(true)
            .open("valid.txt")
            .unwrap();
            file.write(format!("{}\n", s).as_bytes())
            .unwrap();
        }

         */
        assert!(parsed == ParsedRangeHeader::Unsatisfiable || parsed == ParsedRangeHeader::Malformed, "Range was not rejected input=`{}` range={:?}", s, parsed);
        // assert!(h.iter().is_empty(), "Range was not rejected by headers, input=`{}`");
        /*
        if s.starts_with("bytes=") {
            assert_eq!(parsed, ParsedRangeHeader::Unsatisfiable, "input = {} should be unsatisfiable", s)
        } else {
            assert_eq!(parser.parse(s), ParsedRangeHeader::Malformed, "input = {} should be malformed", s)
        }

         */
    }
});
