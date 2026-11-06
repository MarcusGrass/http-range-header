#![no_main]
use http_range_header::parse_range_header;
use libfuzzer_sys::fuzz_target;

fn pick_file_size(selector: u8, raw: u64) -> u64 {
    match selector % 4 {
        0 => 0,
        1 => raw % 256,
        2 => u64::MAX - raw % 256,
        _ => raw,
    }
}

fuzz_target!(|input: (u8, u64, &str)| {
    let (selector, raw_size, header) = input;
    let file_size = pick_file_size(selector, raw_size);
    if let Ok(parsed) = parse_range_header(header) {
        if let Ok(ranges) = parsed.validate(file_size) {
            for range in ranges {
                // Should always return a usable range
                assert!(
                    range.start() <= range.end() && *range.end() < file_size,
                    "header {:?} produced unusable range {:?} for a file of {} bytes",
                    header,
                    range,
                    file_size
                );
            }
        }
    }
});
