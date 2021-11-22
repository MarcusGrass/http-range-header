#[macro_export]
#[cfg(feature = "debug")]
macro_rules! invalid {
    ($create:expr) => {
        ParsedRange::Invalid($create)
    }
}

#[macro_export]
#[cfg(not(feature = "debug"))]
macro_rules! unsatisfiable {
    ($create:expr) => {
        ParsedRange::Invalid
    }
}
