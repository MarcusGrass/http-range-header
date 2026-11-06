# Range header parsing

[![Latest workflow](https://github.com/MarcusGrass/parse-range-headers/workflows/CI/badge.svg)](https://github.com/MarcusGrass/parse-range-headers/actions)
[![CratesIo](https://shields.io/crates/v/http-range-header)](https://crates.io/crates/http-range-header)

The main goals of this parser is:

* Follow specification [RFC-9110](https://www.rfc-editor.org/rfc/rfc9110.html)
(previously followed the now obsolete [RFC-2616](https://www.ietf.org/rfc/rfc2616.txt))
* Behave as expected [MDN](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Range)
* Accuracy - parses headers strictly
* Security - Never panics, ensured by fuzzing
* Stability
* No dependencies

Secondary goals are:

* Speed
* Information on why the header was rejected

The parser is strict. Any range where all parts are not syntactically correct is rejected.
Invalid ranges produce an error.

## Known spec divergence/vagueness

1. Huge reversed ranges will not be invalidated
A range start/end that's bigger than u64::MAX will be clamped u64::MAX (if not above 30 digits) as the spec states that
larger-than-file means to the end of the file. Since no comparison can be made between start/end u64::MAX values
there is no way of telling if the range is reversed and invalidating the entire spec.
The result is that either: 1. The range is rejected anyway, if it's a single range, or 2. The range is ignored
if it's part of a multi-range where other ranges are valid. 2 breaks spec.
There is of course a way of telling which number is bigger, but manual bigint-counting or pulling in a dependency
to handle this specific invalid case does not seem worth it.
Numerals over 30 digits are rejected.
A client that unnecessarily pads values with multiple leading zeroes are seen as abusive here.
2. At most one overlapping pair. This is a spec-interpretation, it's optional to restrict it this way for the
recipient, spec gray-area. The spec could mean more than two ranges overlap the same given byte, it could also
say that more than two ranges overlap in total. E.g. the difference between `0-5,3-7,6-10` and `0-7,3-7,6-10`,
in this implementation, both alternatives are rejected, but the spec could be interpreted as only the second being
rejectable.

## Dev release checklist

1. Make sure CI passes
2. Run [cargo fuzz](https://rust-fuzz.github.io/book/cargo-fuzz.html)
`cargo +nightly fuzz run random_string_input`, at least a minute should be good enough. If it doesn't
error out it has passed.
3. Check msrv with for example [cargo msrv](https://github.com/foresterre/cargo-msrv),
   if a higher msrv is wanted/needed, bump it so that it's less than or equal to [tower-http's](https://github.com/tower-rs/tower-http)
4. Update changelog
5. Update version
6. Publish
