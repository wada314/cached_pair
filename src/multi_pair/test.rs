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
fn test_basic_conversion() {
    let pair = MultiPair::from_left_conv(42, IntegerConverter);

    // Test getting right values in different bases
    assert_eq!(*pair.try_right(&Radix::Binary).unwrap(), "0b101010");
    assert_eq!(*pair.try_right(&Radix::Decimal).unwrap(), "42");
    assert_eq!(*pair.try_right(&Radix::Hexadecimal).unwrap(), "0x2a");

    // Test getting left value
    assert_eq!(*pair.try_left().unwrap(), 42);
}

#[test]
fn test_mutable_operations() {
    let mut pair = MultiPair::from_right_conv("0xff".to_string(), IntegerConverter);

    // Test getting and modifying left value
    {
        let left = pair.try_left_mut().unwrap();
        *left = 42;
    }

    // Test that right values are updated after left modification
    assert_eq!(*pair.try_right(&Radix::Binary).unwrap(), "0b101010");
    assert_eq!(*pair.try_right(&Radix::Decimal).unwrap(), "42");
    assert_eq!(*pair.try_right(&Radix::Hexadecimal).unwrap(), "0x2a");
}

#[test]
fn test_into_operations() {
    let pair = MultiPair::from_left_conv(255, IntegerConverter);

    // Test converting into right value
    let hex = pair.clone().try_into_right(&Radix::Hexadecimal).unwrap();
    assert_eq!(hex, "0xff");

    // Test converting into left value
    let left = pair.try_into_left().unwrap();
    assert_eq!(left, 255);
}

#[test]
fn test_error_handling() {
    // Test parsing invalid number
    let pair = MultiPair::from_right_conv("invalid".to_string(), IntegerConverter);
    assert!(pair.try_left().is_err());

    // Test parsing valid number in wrong format
    let pair = MultiPair::from_right_conv("0b1234".to_string(), IntegerConverter);
    assert!(pair.try_left().is_err());
}
