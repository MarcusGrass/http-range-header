#[macro_export]
#[cfg(feature = "debug")]
macro_rules! unsatisfiable {
    ($create:expr) => {
        ParsedRangeHeader::Unsatisfiable($create)
    }
}

#[macro_export]
#[cfg(not(feature = "debug"))]
macro_rules! unsatisfiable {
    ($create:expr) => {
        ParsedRangeHeader::Unsatisfiable
    }
}


#[macro_export]
#[cfg(feature = "debug")]
macro_rules! malformed {
    ($create:expr) => {
        ParsedRangeHeader::Malformed($create)
    }
}

#[macro_export]
#[cfg(not(feature = "debug"))]
macro_rules! malformed {
    ($create:expr) => {
        ParsedRangeHeader::Malformed
    }
}
