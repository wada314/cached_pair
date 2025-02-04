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

use crate::pair::{boxed_fn_converter, fn_converter, Converter, Pair, StdConverter};
use std::convert::{Infallible, TryFrom, TryInto};
use std::default::Default;
use std::num::TryFromIntError;

#[test]
fn test_basic_converter() {
    // Conversion from u8 to u32 is always successful, while u32 to u8 requires range checking
    #[derive(Debug, Clone, PartialEq, Default)]
    struct Small(u8);

    #[derive(Debug, Clone, PartialEq, Default)]
    struct Large(u32);

    impl TryFrom<&Large> for Small {
        type Error = TryFromIntError;

        fn try_from(value: &Large) -> Result<Self, Self::Error> {
            value.0.try_into().map(Small)
        }
    }

    impl TryFrom<&Small> for Large {
        type Error = Infallible;

        fn try_from(value: &Small) -> Result<Self, Self::Error> {
            Ok(Large(value.0 as u32))
        }
    }

    let converter = StdConverter::<Small, Large>::default();

    // Small -> Large (infallible)
    assert_eq!(converter.convert_to_right(&Small(42)), Ok(Large(42)));

    // Large -> Small (fallible, success case)
    assert_eq!(converter.convert_to_left(&Large(200)), Ok(Small(200)));

    // Large -> Small (fallible, error case)
    assert!(converter.convert_to_left(&Large(300)).is_err());
}

#[test]
fn test_fn_converter() {
    // Converting i32 to u8 subtracts 10, converting u8 to i32 adds 10
    let converter = fn_converter(
        |u: &u8| -> Result<i32, Infallible> { Ok((*u as i32).wrapping_add(10)) },
        |i: &i32| -> Result<u8, TryFromIntError> { i.wrapping_sub(10).try_into() },
    );

    // i32 -> u8 (subtract 10)
    assert_eq!(converter.convert_to_right(&42), Ok(32));

    // u8 -> i32 (add 10)
    assert_eq!(converter.convert_to_left(&32), Ok(42));

    // Error case: value out of range
    assert!(converter.convert_to_right(&300).is_err());
}

#[test]
fn test_boxed_fn_converter() {
    // Converting i32 to u8 subtracts 100, converting u8 to i32 adds 100
    let converter = boxed_fn_converter(
        |u: &u8| -> Result<i32, Infallible> { Ok((*u as i32).wrapping_add(100)) },
        |i: &i32| -> Result<u8, TryFromIntError> { i.wrapping_sub(100).try_into() },
    );

    // i32 -> u8 (subtract 100)
    assert_eq!(converter.convert_to_right(&150), Ok(50));

    // u8 -> i32 (add 100)
    assert_eq!(converter.convert_to_left(&50), Ok(150));

    // Error case: value out of range
    assert!(converter.convert_to_right(&50).is_err());
}
