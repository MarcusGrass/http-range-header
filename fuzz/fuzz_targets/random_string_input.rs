#![no_main]
use libfuzzer_sys::fuzz_target;
use parse_range_headers::{parse_range_header, ParsedRange};
use regex::Regex;
use std::fs::OpenOptions;
use std::io::Write;

lazy_static::lazy_static! {
    static ref STANDARD_RANGE: Regex = Regex::new("^bytes=((\\d+-\\d+,\\s)|(\\d+-,\\s)|(-\\d+,\\s))*((\\d+-\\d+)|(\\d+-)|(-\\d+))+$").unwrap();
}

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        /*
        if STANDARD_RANGE.is_match(s) {
            return;
        }


         */
        assert_no_other_start_than_bytes(s);
        save_accepted_outside_rex(s);
    }

});

fn save_accepted_outside_rex(s: &str) {
    if !STANDARD_RANGE.is_match(s) {
        let mut write = OpenOptions::new()
            .append(true)
            .open("valid.txt")
            .unwrap();
        let validated = parse_range_header(s)
            .validate(10);
        if validated.iter().any(|p| matches!(p, ParsedRange::Validated(_))) {
            let res = format!("{} : {:?}\n", s, validated);
            write.write(res.as_bytes()).unwrap();
        }
    }
}

fn assert_no_other_start_than_bytes(s: &str) {
    let input = if !s.starts_with("bytes=") {
        s.to_owned()
    } else {
        s.replace("bytes", "")
    };
    let any_valid = parse_range_header(&input)
        .validate(u64::MAX)
        .into_iter()
        .any(|p| matches!(p, ParsedRange::Validated(_)));
    assert!(!any_valid, "Found valid {:?}", &input)
}
