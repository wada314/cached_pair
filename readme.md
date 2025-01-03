[![Crates.io Version](https://img.shields.io/crates/v/cached_pair)](https://crates.io/crates/cached-pair)
[![docs.rs](https://img.shields.io/docsrs/cached-pair)](https://docs.rs/once-list2/latest/cached_pair/)

# cached-pair

A simple library for caching pairs of values. Similar to `EitherOrBoth` in the [`itertools`] crate,
but with an extra assumption that the both values are convertible to each other, but the conversion is non-trivial.

For example, you can use this library to hold a pair of a binary `Vec<u8>` and its base64 encoded `String`.

## Example

```rust
use cached_pair::Pair;

// Initialize a pair with a binary value (`Vec<u8>`) on the left.
let pair: Pair<Vec<u8>, String> = Pair::from_left(vec![1, 2, 3]);

// Access the left value.
assert_eq!(pair.left_opt(), Some(&vec![1, 2, 3]));

// Access the right value, with giving a conversion function.
assert_eq!(pair.right_with(|v| base64::encode(v)), "AQID");

// Once you access the right value, it will be cached and be accessible without the conversion function.
assert_eq!(pair.right_opt(), Some(&"AQID".to_string()));
```

[`itertools`]: https://crates.io/crates/itertools
