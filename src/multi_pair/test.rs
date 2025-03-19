// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use ::std::alloc::Global;
use ::std::convert::Infallible;
use ::std::num::ParseIntError;

/// A converter implementation for testing that converts between integers and their string
/// representations in different bases (binary, decimal, hexadecimal).
struct IntegerConverter;

/// Represents different radixes for integer string representation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Radix {
    Binary = 2,
    Decimal = 10,
    Hexadecimal = 16,
}

impl Case<String> for Radix {
    fn matches(&self, target: &String) -> bool {
        // Check if the string matches the expected format for this radix
        match self {
            Self::Binary => target.starts_with("0b"),
            Self::Decimal => target.chars().all(|c| c.is_ascii_digit()),
            Self::Hexadecimal => target.starts_with("0x"),
        }
    }
}

impl MultiPairConverter<i32, String, Vec<String>> for IntegerConverter {
    type ToLeftError = ParseIntError;
    type ToRightError = Infallible;
    type Case = Radix;

    fn rights_to_left<'a>(
        &self,
        rights: impl IntoIterator<Item = &'a String>,
    ) -> Result<i32, Self::ToLeftError> {
        // Take the first right value and parse it according to its prefix
        let right = rights.into_iter().next().expect("at least one right value");
        if right.starts_with("0b") {
            i32::from_str_radix(&right[2..], 2)
        } else if right.starts_with("0x") {
            i32::from_str_radix(&right[2..], 16)
        } else {
            right.parse()
        }
    }

    fn left_to_right(&self, left: &i32, case: &Self::Case) -> Result<String, Self::ToRightError> {
        Ok(match case {
            Radix::Binary => format!("0b{:b}", left),
            Radix::Decimal => left.to_string(),
            Radix::Hexadecimal => format!("0x{:x}", left),
        })
    }
}

#[test]
fn test_left_to_right_conversion() {
    // Case 1: Target value already exists in right collection
    let mut pair = MultiPair::from_left_conv(42, IntegerConverter);
    let _ = pair.right(&Radix::Binary); // Create initial right value
    assert_eq!(*pair.right(&Radix::Binary), "0b101010");

    // Case 2: Target value doesn't exist but left value exists
    let pair = MultiPair::from_left_conv(42, IntegerConverter);
    assert_eq!(*pair.right(&Radix::Binary), "0b101010");
    assert_eq!(*pair.right(&Radix::Decimal), "42");
    assert_eq!(*pair.right(&Radix::Hexadecimal), "0x2a");

    // Case 3: Neither target value nor left value exists
    let pair = MultiPair::from_right_conv("0xff".to_string(), IntegerConverter);
    assert_eq!(*pair.right(&Radix::Binary), "0b11111111");
}

#[test]
fn test_right_to_left_conversion() {
    let pair = MultiPair::from_right_conv("0b101010".to_string(), IntegerConverter);
    assert_eq!(*pair.left(), 42);

    let pair = MultiPair::from_right_conv("42".to_string(), IntegerConverter);
    assert_eq!(*pair.left(), 42);

    let pair = MultiPair::from_right_conv("0x2a".to_string(), IntegerConverter);
    assert_eq!(*pair.left(), 42);
}

#[test]
fn test_left_to_right_mutation() {
    // Case 1: Target value already exists
    let mut pair = MultiPair::from_left_conv(42, IntegerConverter);
    let _ = pair.right(&Radix::Hexadecimal); // Create initial right value
    assert_eq!(*pair.right(&Radix::Hexadecimal), "0x2a");

    // Case 2: Target value doesn't exist but left value exists
    let mut pair = MultiPair::from_left_conv(42, IntegerConverter);
    assert_eq!(*pair.right(&Radix::Hexadecimal), "0x2a");
}

#[test]
fn test_right_to_left_mutation() {
    let mut pair = MultiPair::from_right_conv("0xff".to_string(), IntegerConverter);
    {
        let left = pair.left_mut();
        *left = 42;
    }

    // Verify both directions after mutation
    assert_eq!(*pair.left(), 42);
    assert_eq!(*pair.right(&Radix::Binary), "0b101010");
    assert_eq!(*pair.right(&Radix::Decimal), "42");
    assert_eq!(*pair.right(&Radix::Hexadecimal), "0x2a");
}

#[test]
fn test_left_to_right_into() {
    // Case 1: Target value already exists
    let mut pair = MultiPair::from_left_conv(255, IntegerConverter);
    let _ = pair.right(&Radix::Hexadecimal); // Create initial right value
    let hex = pair.clone().into_right(&Radix::Hexadecimal);
    assert_eq!(hex, "0xff");

    // Case 2: Target value doesn't exist but left value exists
    let pair = MultiPair::from_left_conv(255, IntegerConverter);
    let hex = pair.clone().into_right(&Radix::Hexadecimal);
    assert_eq!(hex, "0xff");

    // Case 3: Neither target value nor left value exists
    let pair = MultiPair::from_right_conv("0xff".to_string(), IntegerConverter);
    let bin = pair.into_right(&Radix::Binary);
    assert_eq!(bin, "0b11111111");
}

#[test]
fn test_right_to_left_into() {
    let pair = MultiPair::from_right_conv("0xff".to_string(), IntegerConverter);
    let left = pair.into_left();
    assert_eq!(left, 255);
}

#[test]
fn test_right_to_left_error_handling() {
    let pair = MultiPair::from_right_conv("invalid".to_string(), IntegerConverter);
    assert!(pair.try_left().is_err());

    let pair = MultiPair::from_right_conv("0b1234".to_string(), IntegerConverter);
    assert!(pair.try_left().is_err());
}

#[test]
fn test_left_to_right_error_handling() {
    // Define a converter that can fail in both directions
    struct FailingConverter;
    impl MultiPairConverter<i32, String, Vec<String>> for FailingConverter {
        type ToLeftError = ParseIntError;
        type ToRightError = &'static str;
        type Case = Radix;

        fn rights_to_left<'a>(
            &self,
            rights: impl IntoIterator<Item = &'a String>,
        ) -> Result<i32, Self::ToLeftError> {
            let right = rights.into_iter().next().expect("at least one right value");
            if right.starts_with("0x") {
                Err("Hexadecimal not supported".parse().unwrap_err())
            } else {
                right.parse()
            }
        }

        fn left_to_right(
            &self,
            left: &i32,
            case: &Self::Case,
        ) -> Result<String, Self::ToRightError> {
            match case {
                Radix::Binary => Err("Binary conversion not supported"),
                Radix::Decimal => Ok(left.to_string()),
                Radix::Hexadecimal => Ok(format!("0x{:x}", left)),
            }
        }
    }

    // Case 1: Target value already exists in right collection
    let mut pair = MultiPair::from_left_conv(42, FailingConverter);
    let _ = pair.right(&Radix::Decimal); // Create initial right value
    assert_eq!(*pair.right(&Radix::Decimal), "42");
    // Left-to-right conversion fails for binary (not supported)
    assert!(pair.try_right(&Radix::Binary).is_err());
    // Right-to-left conversion fails for hex (not supported)
    assert!(pair.try_right(&Radix::Hexadecimal).is_err());

    // Case 2: Target value doesn't exist but left value exists
    let pair = MultiPair::from_left_conv(42, FailingConverter);
    // Left-to-right conversion fails for binary (not supported)
    assert!(pair.try_right(&Radix::Binary).is_err());
    // Left-to-right conversion succeeds for decimal
    assert_eq!(*pair.try_right(&Radix::Decimal).unwrap(), "42");
    // Right-to-left conversion fails for hex (not supported)
    assert!(pair.try_right(&Radix::Hexadecimal).is_err());

    // Case 3: Neither target value nor left value exists
    let pair = MultiPair::from_right_conv("0xff".to_string(), FailingConverter);
    // Left-to-right conversion fails for binary (not supported)
    assert!(pair.try_right(&Radix::Binary).is_err());
    // Right-to-left conversion succeeds for decimal
    assert_eq!(*pair.try_right(&Radix::Decimal).unwrap(), "255");
    // Right-to-left conversion fails for hex (not supported)
    assert!(pair.try_right(&Radix::Hexadecimal).is_err());
}
