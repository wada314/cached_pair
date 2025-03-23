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

#![cfg(feature = "multi_pair")]

use super::collections::std::VecCollection;
use super::*;
use ::allocator_api2::alloc::Global;
use ::std::convert::Infallible;
use ::std::fmt::Debug;
use ::std::num::ParseIntError;

/// A converter implementation that never fails for testing integer-string conversions
#[derive(Clone)]
struct NeverFailingConverter;

/// A converter implementation that can fail for testing error handling
#[derive(Clone)]
struct FailingConverter;

/// Represents different radixes for integer string representation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Radix {
    Binary = 2,
    Decimal = 10,
    Hexadecimal = 16,
}

impl Case<String> for Radix {
    fn matches(&self, target: &String) -> bool {
        match self {
            Self::Binary => target.starts_with("0b"),
            Self::Decimal => target.chars().all(|c| c.is_ascii_digit()),
            Self::Hexadecimal => target.starts_with("0x"),
        }
    }
}

impl MultiPairConverter<i32, String, VecCollection<String, Global>> for NeverFailingConverter {
    type ToLeftError = Infallible;
    type ToRightError = Infallible;
    type Case = Radix;

    fn rights_to_left<'a>(
        &self,
        first: &'a String,
        _rest: impl IntoIterator<Item = &'a String>,
    ) -> Result<i32, Self::ToLeftError> {
        let value = if first.starts_with("0b") {
            i32::from_str_radix(&first[2..], 2)
        } else if first.starts_with("0x") {
            i32::from_str_radix(&first[2..], 16)
        } else {
            first.parse()
        };
        Ok(value.unwrap()) // Safe because we only use this converter with valid strings
    }

    fn left_to_right(&self, left: &i32, case: &Self::Case) -> Result<String, Self::ToRightError> {
        Ok(match case {
            Radix::Binary => format!("0b{:b}", left),
            Radix::Decimal => left.to_string(),
            Radix::Hexadecimal => format!("0x{:x}", left),
        })
    }
}

/// Error type that can be converted from both ParseIntError and &'static str
#[derive(Debug)]
enum ConversionError {
    #[allow(unused)]
    Parse(ParseIntError),
    #[allow(unused)]
    Custom(&'static str),
}

impl From<ParseIntError> for ConversionError {
    fn from(err: ParseIntError) -> Self {
        ConversionError::Parse(err)
    }
}

impl From<&'static str> for ConversionError {
    fn from(err: &'static str) -> Self {
        ConversionError::Custom(err)
    }
}

impl MultiPairConverter<i32, String, VecCollection<String, Global>> for FailingConverter {
    type ToLeftError = ParseIntError;
    type ToRightError = &'static str;
    type Case = Radix;

    fn rights_to_left<'a>(
        &self,
        first: &'a String,
        _rest: impl IntoIterator<Item = &'a String>,
    ) -> Result<i32, Self::ToLeftError> {
        if first.starts_with("0b") {
            // Fail consistently for binary format
            Err("Binary not supported".parse::<i32>().unwrap_err())
        } else if first.starts_with("0x") {
            // Parse hexadecimal
            i32::from_str_radix(&first[2..], 16)
        } else {
            // Parse decimal
            first.parse()
        }
    }

    fn left_to_right(&self, left: &i32, case: &Self::Case) -> Result<String, Self::ToRightError> {
        match case {
            // Fail consistently for binary format
            Radix::Binary => Err("Binary conversion not supported"),
            Radix::Decimal => Ok(left.to_string()),
            Radix::Hexadecimal => Ok(format!("0x{:x}", left)),
        }
    }
}

#[test]
fn test_never_failing_conversion() {
    // Case 1: Target value already exists in right collection
    let pair = MultiPair::from_left_conv(42, NeverFailingConverter);
    assert_eq!(*pair.right(&Radix::Binary), "0b101010");

    // Case 2: Target value doesn't exist but left value exists
    let pair = MultiPair::from_left_conv(42, NeverFailingConverter);
    assert_eq!(*pair.right(&Radix::Binary), "0b101010");
    assert_eq!(*pair.right(&Radix::Decimal), "42");
    assert_eq!(*pair.right(&Radix::Hexadecimal), "0x2a");

    // Case 3: Neither target value nor left value exists
    let pair = MultiPair::from_right_conv("0xff".to_string(), NeverFailingConverter);
    assert_eq!(*pair.right(&Radix::Binary), "0b11111111");
}

#[test]
fn test_failing_conversion() {
    // Case 1: Target value already exists in right collection
    let pair = MultiPair::from_left_conv(42, FailingConverter);
    let _: Result<_, ConversionError> = pair.try_right(&Radix::Decimal); // Create initial right value
    let result: Result<_, ConversionError> = pair.try_right(&Radix::Decimal);
    assert_eq!(*result.unwrap(), "42");
    // Binary conversion fails as per FailingConverter's implementation
    assert!(pair.try_right::<ConversionError>(&Radix::Binary).is_err());
    // Right-to-left conversion succeeds for hex
    let result: Result<_, ConversionError> = pair.try_right(&Radix::Hexadecimal);
    assert_eq!(*result.unwrap(), "0x2a");

    // Case 2: Target value doesn't exist but left value exists
    let pair = MultiPair::from_left_conv(42, FailingConverter);
    // Binary conversion fails as per FailingConverter's implementation
    assert!(pair.try_right::<ConversionError>(&Radix::Binary).is_err());
    // Left-to-right conversion succeeds for decimal
    let result: Result<_, ConversionError> = pair.try_right(&Radix::Decimal);
    assert_eq!(*result.unwrap(), "42");
    // Right-to-left conversion succeeds for hex
    let result: Result<_, ConversionError> = pair.try_right(&Radix::Hexadecimal);
    assert_eq!(*result.unwrap(), "0x2a");

    // Case 3: Neither target value nor left value exists
    let pair = MultiPair::from_right_conv("0xff".to_string(), FailingConverter);
    // Binary conversion fails as per FailingConverter's implementation
    assert!(pair.try_right::<ConversionError>(&Radix::Binary).is_err());
    // Right-to-left conversion succeeds for decimal
    let result: Result<_, ConversionError> = pair.try_right(&Radix::Decimal);
    assert_eq!(*result.unwrap(), "255");
    // Right-to-left conversion succeeds for hex
    let result: Result<_, ConversionError> = pair.try_right(&Radix::Hexadecimal);
    assert_eq!(*result.unwrap(), "0xff");

    // Case 4: Test that binary conversion fails in both directions as implemented
    let pair = MultiPair::from_left_conv(42, FailingConverter);
    // Left-to-right conversion fails for binary
    assert!(pair.try_right::<ConversionError>(&Radix::Binary).is_err());

    let pair = MultiPair::from_right_conv("42".to_string(), FailingConverter);
    // Right-to-left conversion succeeds for decimal, but then binary conversion fails
    assert!(pair.try_right::<ConversionError>(&Radix::Binary).is_err());
}
