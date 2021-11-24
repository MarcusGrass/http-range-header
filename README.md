# Range header parsing

The main goal of this crate is to supply a stable parser with no dependencies that can accurately parse range headers, compliant with [RFC-7233](https://datatracker.ietf.org/doc/html/rfc7233), 
and [MDN](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Range).

Secondary goals are being fast and able to supply error information which could be propagated to the client if wanted.

The parser is strict. Any range where all parts are not syntactically correct and makes sense in the context of the underlying 
resource will be rejected.
