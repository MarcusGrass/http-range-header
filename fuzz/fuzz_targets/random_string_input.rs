#![no_main]
use http_range_header::parse_range_header;
use libfuzzer_sys::fuzz_target;
use regex::Regex;

lazy_static::lazy_static! {
    // Should match most valid ranges
    static ref STANDARD_RANGE: Regex = Regex::new("^((\\d+-\\d+,\\s?)|(\\d+-,\\s?)|(-\\d+,\\s?))*((\\d+-\\d+)|(\\d+-)|(-\\d+))+$").unwrap();
}

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        // This test is specifically looking for panics
        if let Ok(parsed) = parse_range_header(s) {
            let _v = parsed.validate(u64::MAX);
        }
    }
});
