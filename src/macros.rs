#[cfg(feature = "with_error_cause")]
macro_rules! invalid {
    ($create:expr) => {
        Err(RangeMalformedError::new($create))
    };
}

#[cfg(not(feature = "with_error_cause"))]
macro_rules! invalid {
    ($create:expr) => {
        Err(RangeMalformedError)
    };
}

#[cfg(feature = "with_error_cause")]
macro_rules! unsatisfiable {
    ($create:expr) => {
        Err(RangeUnsatisfiableError::new($create))
    };
}

#[cfg(not(feature = "with_error_cause"))]
macro_rules! unsatisfiable {
    ($create:expr) => {
        Err(RangeUnsatisfiableError)
    };
}
