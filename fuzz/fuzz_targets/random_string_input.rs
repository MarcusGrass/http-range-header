#![no_main]
use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::Arbitrary;
use parse_range_headers::{RangeHeaderParserBuilder, ParsedRangeHeader};
use regex::Regex;
use std::io::Write;
use std::fs::OpenOptions;
use headers::{HeaderValue, Range};
use headers::Header;
use regex::internal::Input;

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
        if let Ok(header) = HeaderValue::from_str(s) {
            if let Ok(h) = headers::Range::decode(&mut vec![header].iter()) {
                let mut it = h.iter();
                let mut res = "".to_owned();
                for v in h.iter() {
                    res = format!("{}, {:?}", res, v)
                }
                if res != "" {
                let mut file = OpenOptions::new()
                    .read(true)
                    .append(true)
                    .open("valid.txt")
                    .unwrap();
                    file.write(format!("{}: {}\n", s, res).as_bytes())
                        .unwrap();
                }

                //assert!(n.is_none(), "Range was not rejected by headers, input=`{}` range={:?}", s, n);
            }
        }

        assert!(parsed == ParsedRangeHeader::Unsatisfiable || parsed == ParsedRangeHeader::Malformed, "Range was not rejected input=`{}` range={:?}", s, parsed);
        /*
        if s.starts_with("bytes=") {
            assert_eq!(parsed, ParsedRangeHeader::Unsatisfiable, "input = {} should be unsatisfiable", s)
        } else {
            assert_eq!(parser.parse(s), ParsedRangeHeader::Malformed, "input = {} should be malformed", s)
        }

         */
    }
});
