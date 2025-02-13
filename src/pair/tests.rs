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

use crate::pair::{boxed_fn_converter, fn_converter, Converter, EitherOrBoth, Pair, StdConverter};
use std::convert::{Infallible, TryFrom, TryInto};
use std::default::Default;
use std::num::TryFromIntError;

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

#[test]
fn test_std_converter() {
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

#[test]
fn test_pair_basic() {
    // Test from_left constructor
    let pair = Pair::<Small, Large>::from_left(Small(42));
    assert_eq!(pair.left_opt(), Some(&Small(42)));
    assert_eq!(pair.right_opt(), None);

    // Test from_right constructor
    let pair = Pair::<Small, Large>::from_right(Large(100));
    assert_eq!(pair.left_opt(), None);
    assert_eq!(pair.right_opt(), Some(&Large(100)));
}

#[test]
fn test_pair_try_conversion() {
    // Test when pair has only left value
    let pair = Pair::<Small, Large>::from_left(Small(42));
    assert_eq!(pair.try_right(), Ok(&Large(42))); // Conversion succeeds
    assert_eq!(pair.try_left(), Ok(&Small(42))); // Already exists
    assert_eq!(pair.right_opt(), Some(&Large(42))); // Value is now cached

    // Test when pair has only right value (success case)
    let pair = Pair::<Small, Large>::from_right(Large(200));
    assert_eq!(pair.try_left(), Ok(&Small(200))); // Conversion succeeds
    assert_eq!(pair.try_right(), Ok(&Large(200))); // Already exists
    assert_eq!(pair.left_opt(), Some(&Small(200))); // Value is now cached

    // Test when pair has only right value (failure case)
    let pair = Pair::<Small, Large>::from_right(Large(300));
    assert!(pair.try_left().is_err()); // Conversion fails (value too large)
    assert_eq!(pair.try_right(), Ok(&Large(300))); // Already exists
    assert_eq!(pair.left_opt(), None); // No value is cached after failure

    // Test when pair has both values
    let pair = Pair::<Small, Large>::from_left(Small(42));
    let _ = pair.right(); // Fill the right value
    assert_eq!(pair.try_right(), Ok(&Large(42))); // Convert and cache right value
    assert_eq!(pair.try_left(), Ok(&Small(42))); // Left value exists
    assert_eq!(pair.try_right(), Ok(&Large(42))); // Right value is cached
}

#[test]
fn test_pair_try_into() {
    // Test try_into_right from left value
    let pair = Pair::<Small, Large>::from_left(Small(42));
    assert_eq!(pair.try_into_right::<TryFromIntError>(), Ok(Large(42)));

    // Test try_into_left from right value (success case)
    let pair = Pair::<Small, Large>::from_right(Large(200));
    assert_eq!(pair.try_into_left::<TryFromIntError>(), Ok(Small(200)));

    // Test try_into_left from right value (failure case)
    let pair = Pair::<Small, Large>::from_right(Large(300));
    assert!(pair.try_into_left::<TryFromIntError>().is_err());

    // Test try_into_right when both values exist
    let pair = Pair::<Small, Large>::from_left(Small(42));
    let _ = pair.try_right(); // Cache the right value
    assert_eq!(pair.try_into_right::<TryFromIntError>(), Ok(Large(42)));

    // Test try_into_left when both values exist
    let pair = Pair::<Small, Large>::from_right(Large(200));
    let _ = pair.try_left(); // Cache the left value
    assert_eq!(pair.try_into_left::<TryFromIntError>(), Ok(Small(200)));
}

#[test]
fn test_pair_try_mut() {
    // Test try_left_mut when pair has only left value
    let mut pair = Pair::<Small, Large>::from_left(Small(42));
    let left = pair.try_left_mut::<TryFromIntError>().unwrap();
    *left = Small(43);
    assert_eq!(pair.left_opt(), Some(&Small(43)));
    assert_eq!(pair.right_opt(), None);

    // Test try_right_mut when pair has only right value
    let mut pair = Pair::<Small, Large>::from_right(Large(200));
    let right = pair.try_right_mut::<TryFromIntError>().unwrap();
    *right = Large(201);
    assert_eq!(pair.right_opt(), Some(&Large(201)));
    assert_eq!(pair.left_opt(), None);

    // Test try_left_mut when pair has only right value (success case)
    let mut pair = Pair::<Small, Large>::from_right(Large(200));
    let left = pair.try_left_mut::<TryFromIntError>().unwrap();
    *left = Small(42);
    assert_eq!(pair.left_opt(), Some(&Small(42)));
    assert_eq!(pair.right_opt(), None); // Right value is cleared

    // Test try_left_mut when pair has only right value (failure case)
    let mut pair = Pair::<Small, Large>::from_right(Large(300));
    assert!(pair.try_left_mut::<TryFromIntError>().is_err());
    assert_eq!(pair.right_opt(), Some(&Large(300))); // Right value is preserved

    // Test try_right_mut when pair has both values
    let mut pair = Pair::<Small, Large>::from_left(Small(42));
    let _ = pair.try_right(); // Cache the right value
    assert_eq!(pair.right_opt(), Some(&Large(42)));
    let right = pair.try_right_mut::<TryFromIntError>().unwrap();
    *right = Large(43);
    assert_eq!(pair.right_opt(), Some(&Large(43)));
    assert_eq!(pair.left_opt(), None); // Left value is cleared

    // Test try_left_mut when pair has both values
    let mut pair = Pair::<Small, Large>::from_right(Large(200));
    let _ = pair.try_left(); // Cache the left value
    assert_eq!(pair.left_opt(), Some(&Small(200)));
    let left = pair.try_left_mut::<TryFromIntError>().unwrap();
    *left = Small(201);
    assert_eq!(pair.left_opt(), Some(&Small(201)));
    assert_eq!(pair.right_opt(), None); // Right value is cleared
}

#[test]
fn test_pair_opt_mut() {
    // Test left_opt_mut when pair has only left value
    let mut pair = Pair::<Small, Large>::from_left(Small(42));
    let left = pair.left_opt_mut().unwrap();
    *left = Small(43);
    assert_eq!(pair.left_opt(), Some(&Small(43)));
    assert_eq!(pair.right_opt(), None);

    // Test right_opt_mut when pair has only right value
    let mut pair = Pair::<Small, Large>::from_right(Large(200));
    let right = pair.right_opt_mut().unwrap();
    *right = Large(201);
    assert_eq!(pair.right_opt(), Some(&Large(201)));
    assert_eq!(pair.left_opt(), None);

    // Test left_opt_mut when pair has only right value
    let mut pair = Pair::<Small, Large>::from_right(Large(200));
    assert_eq!(pair.left_opt_mut(), None);
    assert_eq!(pair.right_opt(), Some(&Large(200))); // Right value is preserved

    // Test right_opt_mut when pair has only left value
    let mut pair = Pair::<Small, Large>::from_left(Small(42));
    assert_eq!(pair.right_opt_mut(), None);
    assert_eq!(pair.left_opt(), Some(&Small(42))); // Left value is preserved

    // Test left_opt_mut when pair has both values
    let mut pair = Pair::<Small, Large>::from_left(Small(42));
    let _ = pair.try_right(); // Cache the right value
    assert_eq!(pair.right_opt(), Some(&Large(42)));
    let left = pair.left_opt_mut().unwrap();
    *left = Small(43);
    assert_eq!(pair.left_opt(), Some(&Small(43)));
    assert_eq!(pair.right_opt(), None); // Right value is cleared

    // Test right_opt_mut when pair has both values
    let mut pair = Pair::<Small, Large>::from_right(Large(200));
    let _ = pair.try_left(); // Cache the left value
    assert_eq!(pair.left_opt(), Some(&Small(200)));
    let right = pair.right_opt_mut().unwrap();
    *right = Large(201);
    assert_eq!(pair.right_opt(), Some(&Large(201)));
    assert_eq!(pair.left_opt(), None); // Left value is cleared
}

#[test]
fn test_try_clear_left() {
    let mut pair = Pair::<Small, Large>::from_left(Small(42));

    // 左の値のみが存在する場合、右の値への変換が必要
    assert_eq!(
        pair.try_clear_left::<TryFromIntError>(),
        Ok(Some(Small(42)))
    );
    assert_eq!(pair.left_opt(), None);
    assert_eq!(pair.right_opt(), Some(&Large(42)));

    // 両方の値が存在する場合
    let mut pair = Pair::<Small, Large>::from_left(Small(42));
    assert_eq!(pair.try_right(), Ok(&Large(42))); // 右の値をキャッシュ
    assert_eq!(
        pair.try_clear_left::<TryFromIntError>(),
        Ok(Some(Small(42)))
    );
    assert_eq!(pair.left_opt(), None);
    assert_eq!(pair.right_opt(), Some(&Large(42)));

    // 左の値が存在しない場合
    let mut pair = Pair::<Small, Large>::from_right(Large(100));
    assert_eq!(pair.try_clear_left::<TryFromIntError>(), Ok(None));
    assert_eq!(pair.left_opt(), None);
    assert_eq!(pair.right_opt(), Some(&Large(100)));
}

#[test]
fn test_try_clear_right() {
    let mut pair = Pair::<Small, Large>::from_right(Large(200));

    // 右の値のみが存在する場合、左の値への変換が必要
    assert_eq!(
        pair.try_clear_right::<TryFromIntError>(),
        Ok(Some(Large(200)))
    );
    assert_eq!(pair.right_opt(), None);
    assert_eq!(pair.left_opt(), Some(&Small(200)));

    // 両方の値が存在する場合
    let mut pair = Pair::<Small, Large>::from_right(Large(200));
    assert_eq!(pair.try_left(), Ok(&Small(200))); // 左の値をキャッシュ
    assert_eq!(
        pair.try_clear_right::<TryFromIntError>(),
        Ok(Some(Large(200)))
    );
    assert_eq!(pair.right_opt(), None);
    assert_eq!(pair.left_opt(), Some(&Small(200)));

    // 右の値が存在しない場合
    let mut pair = Pair::<Small, Large>::from_left(Small(42));
    assert_eq!(pair.try_clear_right::<TryFromIntError>(), Ok(None));
    assert_eq!(pair.right_opt(), None);
    assert_eq!(pair.left_opt(), Some(&Small(42)));

    // 変換が失敗する場合
    let mut pair = Pair::<Small, Large>::from_right(Large(300));
    assert!(pair.try_clear_right::<TryFromIntError>().is_err());
}

#[test]
fn test_pair_method_existence() {
    // Define types with infallible conversions for testing
    #[derive(Debug, Clone, PartialEq, Default)]
    struct A(u32);

    #[derive(Debug, Clone, PartialEq, Default)]
    struct B(u32);

    impl TryFrom<&A> for B {
        type Error = Infallible;

        fn try_from(value: &A) -> Result<Self, Self::Error> {
            Ok(B(value.0))
        }
    }

    impl TryFrom<&B> for A {
        type Error = Infallible;

        fn try_from(value: &B) -> Result<Self, Self::Error> {
            Ok(A(value.0))
        }
    }

    let pair = Pair::<A, B>::from_left(A(42));
    let mut pair_mut = Pair::<A, B>::from_left(A(42));

    // Basic constructors
    let _: Pair<A, B> = Pair::from_left(A(42));
    let _: Pair<A, B> = Pair::from_right(B(100));
    let _: Pair<A, B> = Pair::from_left_conv(A(42), StdConverter::default());
    let _: Pair<A, B> = Pair::from_right_conv(B(100), StdConverter::default());

    // Reference getters
    let _: Option<&A> = pair.left_opt();
    let _: Option<&B> = pair.right_opt();
    let _: Result<&A, Infallible> = pair.try_left();
    let _: Result<&B, Infallible> = pair.try_right();
    let _: &A = Pair::<A, B>::from_left(A(42)).left();
    let _: &B = Pair::<A, B>::from_right(B(100)).right();
    let _: &A = unsafe { pair.left_with(|r| A(r.0)) };
    let _: &B = unsafe { pair.right_with(|l| B(l.0)) };
    let _: Result<&A, &str> = unsafe { pair.try_left_with(|r| Ok(A(r.0))) };
    let _: Result<&B, &str> = unsafe { pair.try_right_with(|l| Ok(B(l.0))) };

    // Mutable reference getters
    let _: Option<&mut A> = pair_mut.left_opt_mut();
    let _: Option<&mut B> = pair_mut.right_opt_mut();
    let _: Result<&mut A, Infallible> = pair_mut.try_left_mut();
    let _: Result<&mut B, Infallible> = pair_mut.try_right_mut();
    let _: Result<&mut A, &str> = unsafe { pair_mut.try_left_mut_with(|r| Ok(A(r.0))) };
    let _: Result<&mut B, &str> = unsafe { pair_mut.try_right_mut_with(|l| Ok(B(l.0))) };
    let _: &mut A = unsafe { pair_mut.left_mut_with(|r| A(r.0)) };
    let _: &mut B = unsafe { pair_mut.right_mut_with(|l| B(l.0)) };

    // Into variants (using infallible conversions)
    let pair = Pair::<A, B>::from_left(A(42));
    let _: Result<A, Infallible> = pair.try_into_left();
    let pair = Pair::<A, B>::from_left(A(42));
    let _: Result<B, Infallible> = pair.try_into_right();

    // Using a pair with infallible conversions for into_left/into_right
    let converter = fn_converter(
        |_: &B| -> Result<A, Infallible> { Ok(A(42)) },
        |_: &A| -> Result<B, Infallible> { Ok(B(42)) },
    );
    let pair = Pair::from_left_conv(A(42), converter.clone());
    let _: A = pair.into_left();
    let pair = Pair::from_left_conv(A(42), converter);
    let _: B = pair.into_right();

    // Testing with_* methods
    let pair = Pair::<A, B>::from_left(A(42));
    let _: Result<A, &str> = unsafe { pair.clone().try_into_left_with(|r| Ok(A(r.0))) };
    let _: Result<B, &str> = unsafe { pair.clone().try_into_right_with(|l| Ok(B(l.0))) };
    let _: A = unsafe { pair.clone().into_left_with(|r| A(r.0)) };
    let _: B = unsafe { pair.clone().into_right_with(|l| B(l.0)) };

    // Clear methods
    let _: Option<A> = pair_mut.clear_left();
    let _: Option<B> = pair_mut.clear_right();
    let _: Result<Option<A>, Infallible> = pair_mut.try_clear_left();
    let _: Result<Option<B>, Infallible> = pair_mut.try_clear_right();
    let _: Option<A> = unsafe { pair_mut.clear_left_with(|r| B(r.0)) };
    let _: Option<B> = unsafe { pair_mut.clear_right_with(|l| A(l.0)) };
    let _: Result<Option<A>, &str> = unsafe { pair_mut.try_clear_left_with(|r| Ok(B(r.0))) };
    let _: Result<Option<B>, &str> = unsafe { pair_mut.try_clear_right_with(|l| Ok(A(l.0))) };

    // Other methods
    let _: EitherOrBoth<&A, &B> = pair.as_ref();
}
