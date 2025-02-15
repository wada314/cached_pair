[![Crates.io Version](https://img.shields.io/crates/v/cached_pair)](https://crates.io/crates/cached-pair)
[![docs.rs](https://img.shields.io/docsrs/cached-pair)](https://docs.rs/cached-pair/latest/cached_pair/)

# cached-pair

A simple library for caching pairs of values. Similar to `EitherOrBoth` in the [`itertools`] crate,
but with an extra assumption that both values are convertible to each other, and the conversion may be non-trivial or expensive.

For example, you can use this library to hold a pair of values that need to be kept in sync, such as a number and its string representation,
or a binary `Vec<u8>` and its base64 encoded `String`.

## Examples

### Basic Usage

```rust
use cached_pair::{Pair, fn_converter};
use std::convert::Infallible;
use std::num::ParseIntError;

let converter = fn_converter(
    |s: &String| s.parse::<i32>(),  // String -> i32 (may fail)
    |i: &i32| Ok(i.to_string()),    // i32 -> String (never fails)
);

// Create a pair from a left value
let pair = Pair::from_left_conv(42i32, converter);

// Access values
assert_eq!(pair.left_opt(), Some(&42));
assert_eq!(pair.try_right(), Ok(&"42".to_string()));

// The converted value is now cached
assert_eq!(pair.right_opt(), Some(&"42".to_string()));
```

### Using the `From` and `TryFrom` traits

For types that implement `TryFrom` traits, you can use the default `StdConverter`.

```rust
use cached_pair::Pair;
use std::convert::Infallible;

// Define types that implement TryFrom for each other
#[derive(Debug, PartialEq)]
struct Small(u8);

#[derive(Debug, PartialEq)]
struct Large(u32);

impl TryFrom<&Large> for Small {
    type Error = std::num::TryFromIntError;
    fn try_from(value: &Large) -> Result<Self, Self::Error> {
        value.0.try_into().map(Small)
    }
}

impl From<&Small> for Large {
    fn from(value: &Small) -> Self {
        Large(value.0 as u32)
    }
}

// Create a pair of `(Small, Large)` using the default StdConverter.
// Left (small) to right (large) conversion is infallible.
let pair = Pair::from_left(Small(42));
assert_eq!(pair.right(), &Large(42));

// Conversion from right (large) to left (small) may fail if the value is too large.
let pair = Pair::from_right(Large(300));
assert!(pair.try_left().is_err());
```

[`itertools`]: https://crates.io/crates/itertools
