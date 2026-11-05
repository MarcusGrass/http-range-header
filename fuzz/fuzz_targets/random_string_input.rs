#![no_main]
use http_range_header::parse_range_header;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let val = rand::random();
    if let Ok(s) = std::str::from_utf8(data) {
        // This test is specifically looking for panics
        if let Ok(parsed) = parse_range_header(s) {
            let _v = parsed.validate(val);
        }
    }
});
