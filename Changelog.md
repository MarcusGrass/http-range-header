<!-- markdownlint-disable blanks-around-headings blanks-around-lists no-duplicate-heading -->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- next-header -->
## [TBD] - Release date

A lot of changes to match https://www.rfc-editor.org/rfc/rfc9110.html, that mainly means relaxing strictness.
This has led to a performance increase of on average around ~25% on the benchmarks.

More valid expressions will now produce ranges. Unsatisfiable ranges will no longer cause an error if there are also 
satisfiable ranges. Generally, the rule is: If there is at least one satisfiable, valid range and no invalid ones 
it's not an error . 
Satisfiable ranges are filtered if they cannot properly index the file at the given validation length
(Only applies to an empty file).

Hides the internal ranges so that assumptions about validity can't be invalidated but offers functions to view/take 
internals.

### Added

- `parse_range_header_with_max_ranges` that accepts a configurable number of ranges, for when 100 just isn't enough.
- [`ParsedRanges::len`] which gives the number of ranges
- [`ParsedRanges::into_ranges`] which destroys the struct, yielding the ranges https://github.com/MarcusGrass/http-range-header/issues/9

### Changed
- Validation on file with zero length will not return unindexable ranges, but accept the supplied input as valid.
That specifically means that `parse_range_header("bytes=-1").unwrap().validate(0) == Ok(vec![])`, before it 
returned `Err(FileSuffixOutOfBounds)`.
- Removed the `Empty` error kind
- `parse_range_header` with `bytes=-0` will now succeed, but `validate` will fail instead.
- Error enum changed now groups errors into:
* `RangeUnsatisfiableError::Invalid` when a range is rejected because it doesn't make sense
* `RangeUnsatisfiableError::Rejected` when a range is rejected because of tolerance (too many ranges, overlapping, empty ranges, etc.)
* `RangeUnsatisfiableError::Unsatisfiable` when a range is syntactically valid but cannot be satisfied against a given file size
- clamps values above u64::MAX
- at most 30 digits per range value
- two ranges may now overlap, but no more than two <https://www.rfc-editor.org/rfc/rfc9110.html#section-14.2-6>
- `parse_range_header` will by default reject more than 100 ranges in a single input.
- units are case-insensitive
- more whitespacing is allowed
- empty ranges are sometimes tolerated, up to a limit.
- internal range representation changed, and are no longer public
- reversed ranges are now rejected by `parse_range_header` instead of `validate`

### Fixed
- A suffix range longer than the file (`bytes=-N` with N larger than the file size) now selects the whole file instead of being unsatisfiable, as specified by RFC 9110 14.1.2.
- Relaxed spec-compliant handling of unsatisfiable vs invalid ranges. Mixed-ranges with satisfiable and unsatisfiable
ranges will return only the satisfiable ones, not an error.
- Relaxed spec-compliant handling of case sensitivity. https://www.rfc-editor.org/rfc/rfc9110.html#section-14.1-4
E.g., this is okay: `Bytes=0-10`
- Relaxed spec-compliant handling of leading zeroes. https://www.rfc-editor.org/rfc/rfc9110.html#section-14.1.1
E.g., this is okay: `bytes=00-10`
- Relaxed spec-compliant handling of whitespace. https://www.rfc-editor.org/rfc/rfc9110.html#section-5.6.3
E.g., this is okay: `bytes=00-10 , 15-20`
- Relaxed spec-compliant handling of empty ranges. https://www.rfc-editor.org/rfc/rfc9110.html#section-5.6.1.2
E.g., this is okay: `bytes=0-1 ,, , 3-4` and produces the ranges `0..=1` and `3..=4`

## [0.4.2] - 2024-11-28

### Changed

- Relaxed visibility of some intermediate-structs on from 
parsing internals to public, see https://github.com/MarcusGrass/http-range-header/issues/9

## [0.4.1] - 2024-05-03

### Fixed

- Panic at validation step if file-size doesn't make sense with the range, 
should have been an Error, thanks @cholcombe973

## [0.4.0] - 2023-07-21
### Added
- Bench error performance

### Changed
- Msrv set to 1.60.0 to match [tower-http](https://github.com/tower-rs/tower-http)
- Use higher `Rust` version features to improve performance
- Remove feature `with_error_cause`
- Convert Error into an enum

### Fixed

## [0.3.1] - 2023-07-21

### Fixed
- Now accepts ranges that are out of bounds, but truncates them down to an in-range 
value, according to the spec, thanks @jfaust!
- Clean up with clippy pedantic, update docs, format, etc. Resulted in a bench improvement of almost
5%.

## [0.3.0] - 2021-11-25

### Changed

- Only expose a single error-type to make usage more ergonomic

## [0.2.1] - 2021-11-25

### Added

- Make some optimizations

## [0.2.0] - 2021-11-25

### Changed

- Rename to http-range-header

## [0.1.0] - 2021-11-25

### Added

- Released first version under parse_range_headers
