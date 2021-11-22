#![no_main]
use libfuzzer_sys::fuzz_target;
use regex::Regex;
use headers::{HeaderValue};
use headers::Header;

lazy_static::lazy_static! {
    static ref STANDARD_RANGE: Regex = Regex::new("^bytes=((\\d+-\\d+,\\s)|(\\d+-,\\s)|(-\\d+,\\s))*((\\d+-\\d+)|(\\d+-)|(-\\d+))+$").unwrap();
}

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if STANDARD_RANGE.is_match(s) {
            return;
        }
        if let Ok(header) = HeaderValue::from_str(s) {
            if let Ok(_h) = headers::Range::decode(&mut vec![header].iter()) {
                //assert!(n.is_none(), "Range was not rejected by headers, input=`{}` range={:?}", s, n);
            }
        }
    }
});
