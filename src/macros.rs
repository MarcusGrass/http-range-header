#[macro_export]
#[cfg(feature = "with_error_cause")]
macro_rules! invalid {
    ($create:expr) => {
        Err(RangeMalformedError::new($create))
    };
}

#[macro_export]
#[cfg(not(feature = "with_error_cause"))]
macro_rules! invalid {
    ($create:expr) => {
        Err(RangeMalformedError)
    };
}

#[macro_export]
#[cfg(feature = "with_error_cause")]
macro_rules! unsatisfiable {
    ($create:expr) => {
        Err(RangeUnsatisfiableError::new($create))
    };
}

#[macro_export]
#[cfg(not(feature = "with_error_cause"))]
macro_rules! unsatisfiable {
    ($create:expr) => {
        Err(RangeUnsatisfiableError)
    };
}
