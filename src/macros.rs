#[macro_export]
#[cfg(feature = "with_error_cause")]
macro_rules! invalid {
    ($create:expr) => {
        ParsedRange::Invalid($create)
    };
}

#[macro_export]
#[cfg(not(feature = "with_error_cause"))]
macro_rules! invalid {
    ($create:expr) => {
        ParsedRange::Invalid
    };
}

#[macro_export]
#[cfg(feature = "with_error_cause")]
macro_rules! unsatisfiable {
    ($create:expr) => {
        ValidatedRange::Unsatisfiable($create)
    };
}

#[macro_export]
#[cfg(not(feature = "with_error_cause"))]
macro_rules! unsatisfiable {
    ($create:expr) => {
        ValidatedRange::Unsatisfiable
    };
}
