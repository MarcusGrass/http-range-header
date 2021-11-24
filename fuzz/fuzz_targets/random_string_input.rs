#![no_main]
use libfuzzer_sys::fuzz_target;
use parse_range_headers::{parse_range_header};
use regex::Regex;
use std::fs::OpenOptions;
use std::io::Write;

lazy_static::lazy_static! {
    static ref STANDARD_RANGE: Regex = Regex::new("^bytes=((\\d+-\\d+,\\s?)|(\\d+-,\\s?)|(-\\d+,\\s?))*((\\d+-\\d+)|(\\d+-)|(-\\d+))+$").unwrap();
}

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if STANDARD_RANGE.is_match(s) {
            return;
        }
        //assert_no_other_start_than_bytes(s);
        save_accepted_outside_rex(s);
    }

});

fn save_accepted_outside_rex(s: &str) {
    if let Ok(parsed) = parse_range_header(s) {
        if let Ok(validated) = parsed.validate(u64::MAX) {
            let mut write = OpenOptions::new()
                .append(true)
                .open("valid.txt")
                .unwrap();
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
    if let Ok(parsed) = parse_range_header(&input) {
        assert!(parsed.validate(u64::MAX).is_err());
    }
}
