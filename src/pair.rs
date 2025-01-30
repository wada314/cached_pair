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

//! A pair (or an either) of values where one can be converted to the other.
//! This data structure caches the converted value to avoid redundant conversion.

use ::std::cell::OnceCell;
use ::std::convert::Infallible;
use ::std::fmt::Debug;
use ::std::hash::Hash;

/// Re-exporting from `itertools` crate.
pub use ::itertools::EitherOrBoth;

/// A pair of values where one can be converted to the other.
///
/// # Example
///
/// ```rust
/// use cached_pair::{Pair, Converter};
/// use std::convert::Infallible;
/// use std::num::ParseIntError;
///
/// // Define a converter between i32 and String
/// struct MyConverter;
///
/// impl Converter<i32, String> for MyConverter {
///     type ToLeftError = ParseIntError;
///     type ToRightError = Infallible;
///
///     fn convert_to_right(left: &i32) -> Result<String, Self::ToRightError> {
///         Ok(left.to_string())
///     }
///
///     fn convert_to_left(right: &String) -> Result<i32, Self::ToLeftError> {
///         right.parse()  // parse() returns Result<i32, ParseIntError>
///     }
/// }
///
/// impl Default for MyConverter {
///     fn default() -> Self {
///         MyConverter
///     }
/// }
///
/// // Construct a pair from a left value.
/// let pair: Pair<i32, String, MyConverter> = Pair::from_left(42);
///
/// // Left value is present, but right value is not.
/// assert_eq!(pair.left_opt(), Some(&42));
/// assert_eq!(pair.right_opt(), None);
///
/// // Get a right value by converting the left value.
/// assert_eq!(pair.right(), &"42".to_string());
///
/// // Once we get the right value, it is cached.
/// assert_eq!(pair.right_opt(), Some(&"42".to_string()));
///
/// // mutable access
/// let mut pair = pair;
///
/// // Get a mutable reference to the left value.
/// *pair.left_opt_mut().unwrap() = 123;
///
/// // ...then the right value is cleared.
/// assert_eq!(pair.right_opt(), None);
/// ```
#[derive(Clone)]
pub enum Pair<L, R, C = AutoConverter<L, R, Infallible>> {
    #[doc(hidden)]
    GivenLeft {
        left: L,
        right_cell: OnceCell<R>,
        converter: C,
    },
    #[doc(hidden)]
    GivenRight {
        left_cell: OnceCell<L>,
        right: R,
        converter: C,
    },
}

impl<L, R, C> Pair<L, R, C> {
    /// Returns the left value if it is available. Otherwise, returns `None`.
    pub fn left_opt(&self) -> Option<&L> {
        match self {
            Self::GivenLeft { left, .. } => Some(left),
            Self::GivenRight { left_cell, .. } => left_cell.get(),
        }
    }

    /// Returns the right value if it is available. Otherwise, returns `None`.
    pub fn right_opt(&self) -> Option<&R> {
        match self {
            Self::GivenLeft { right_cell, .. } => right_cell.get(),
            Self::GivenRight { right, .. } => Some(right),
        }
    }

    /// Returns a reference to the pair as `itertools::EitherOrBoth`.
    pub fn as_ref(&self) -> EitherOrBoth<&L, &R> {
        let (left, right) = match self {
            Self::GivenLeft {
                left, right_cell, ..
            } => (Some(left), right_cell.get()),
            Self::GivenRight {
                right, left_cell, ..
            } => (left_cell.get(), Some(right)),
        };
        match (left, right) {
            (Some(left), Some(right)) => EitherOrBoth::Both(left, right),
            (Some(left), None) => EitherOrBoth::Left(left),
            (None, Some(right)) => EitherOrBoth::Right(right),
            (None, None) => unreachable!(),
        }
    }

    /// Constructs a pair from a left value and a converter instance.
    pub fn from_left_conv(left: L, converter: C) -> Self {
        Self::GivenLeft {
            left,
            right_cell: OnceCell::new(),
            converter,
        }
    }

    /// Constructs a pair from a right value and a converter instance.
    pub fn from_right_conv(right: R, converter: C) -> Self {
        Self::GivenRight {
            left_cell: OnceCell::new(),
            right,
            converter,
        }
    }

    /// Returns a left value if it is available.
    /// Note: Obtaining a mutable reference will erase the right value.
    /// If the left value is available, this method clears the right value.
    /// If the left value is not available, it converts the right value and clears the original right value.
    pub fn left_opt_mut(&mut self) -> Option<&mut L> {
        match self {
            Self::GivenLeft {
                left, right_cell, ..
            } => {
                let _ = right_cell.take();
                Some(left)
            }
            Self::GivenRight {
                left_cell,
                right,
                converter,
            } => {
                let left = left_cell.take()?;
                // Take ownership of all fields using ptr::read
                let _ = unsafe { std::ptr::read(right) };
                let converter = unsafe { std::ptr::read(converter) };
                let new_self = Self::from_left_conv(left, converter);
                // Prevent double-free of the old fields
                std::mem::forget(std::mem::replace(self, new_self));
                let Self::GivenLeft { left, .. } = self else {
                    unreachable!()
                };
                Some(left)
            }
        }
    }

    /// Returns a right value if it is available.
    /// Note: Obtaining a mutable reference will erase the left value.
    /// If the right value is available, this method clears the left value.
    /// If the right value is not available, it converts the left value and clears the original left value.
    pub fn right_opt_mut(&mut self) -> Option<&mut R> {
        match self {
            Self::GivenLeft {
                right_cell,
                left,
                converter,
            } => {
                let right = right_cell.take()?;
                // Take ownership of all fields using ptr::read
                let _ = unsafe { std::ptr::read(left) };
                let converter = unsafe { std::ptr::read(converter) };
                let new_self = Self::from_right_conv(right, converter);
                // Prevent double-free of the old fields
                std::mem::forget(std::mem::replace(self, new_self));
                let Self::GivenRight { right, .. } = self else {
                    unreachable!()
                };
                Some(right)
            }
            Self::GivenRight {
                right, left_cell, ..
            } => {
                let _ = left_cell.take();
                Some(right)
            }
        }
    }
}

impl<L, R, C> Pair<L, R, C>
where
    C: Default,
{
    /// Constructs a pair from a left value.
    pub fn from_left(left: L) -> Self {
        Self::GivenLeft {
            left,
            right_cell: OnceCell::new(),
            converter: C::default(),
        }
    }

    /// Constructs a pair from a right value.
    pub fn from_right(right: R) -> Self {
        Self::GivenRight {
            left_cell: OnceCell::new(),
            right,
            converter: C::default(),
        }
    }
}

impl<L, R, C> Pair<L, R, C>
where
    C: Converter<L, R> + Default,
{
    /// Returns the left value. If the left value is not available, it converts the right value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_left_with<'a, F: FnOnce(&'a R) -> Result<L, E>, E>(
        &'a self,
        f: F,
    ) -> Result<&'a L, E> {
        match self {
            Self::GivenLeft { left, .. } => Ok(left),
            Self::GivenRight {
                left_cell, right, ..
            } => left_cell.get_or_try_init2(|| f(right)),
        }
    }

    /// Returns the right value. If the right value is not available, it converts the left value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_right_with<'a, F: FnOnce(&'a L) -> Result<R, E>, E>(
        &'a self,
        f: F,
    ) -> Result<&'a R, E> {
        match self {
            Self::GivenLeft {
                left, right_cell, ..
            } => right_cell.get_or_try_init2(|| f(left)),
            Self::GivenRight { right, .. } => Ok(right),
        }
    }

    /// Returns the left value as a mutable reference.
    /// Note: Obtaining a mutable reference will erase the right value.
    /// If the left value is not available, it converts the right value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_left_mut_with<F: for<'a> FnOnce(&'a R) -> Result<L, E>, E>(
        &mut self,
        f: F,
    ) -> Result<&mut L, E> {
        match self {
            Self::GivenLeft {
                left, right_cell, ..
            } => {
                let _ = right_cell.take();
                Ok(left)
            }
            Self::GivenRight {
                left_cell,
                right,
                converter,
            } => {
                let left = match left_cell.take() {
                    Some(left) => left,
                    None => f(right)?,
                };
                // Take ownership of converter
                let converter = unsafe { std::ptr::read(converter) };
                *self = Self::from_left_conv(left, converter);
                let Self::GivenLeft { left, .. } = self else {
                    unreachable!()
                };
                Ok(left)
            }
        }
    }

    /// Returns the right value as a mutable reference.
    /// Note: Obtaining a mutable reference will erase the left value.
    /// If the right value is not available, it converts the left value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_right_mut_with<F: for<'a> FnOnce(&'a L) -> Result<R, E>, E>(
        &mut self,
        f: F,
    ) -> Result<&mut R, E> {
        match self {
            Self::GivenLeft {
                left,
                right_cell,
                converter,
            } => {
                let right = match right_cell.take() {
                    Some(right) => right,
                    None => f(left)?,
                };
                // Take ownership of converter
                let converter = unsafe { std::ptr::read(converter) };
                *self = Self::from_right_conv(right, converter);
                let Self::GivenRight { right, .. } = self else {
                    unreachable!()
                };
                Ok(right)
            }
            Self::GivenRight {
                right, left_cell, ..
            } => {
                let _ = left_cell.take();
                Ok(right)
            }
        }
    }

    /// Returns a left value if it is available.
    /// If the left value is not available, it uses the converter to convert the right value.
    pub fn try_left<'a>(&'a self) -> Result<&'a L, C::ToLeftError> {
        unsafe { self.try_left_with(|r| C::convert_to_left(r)) }
    }

    /// Returns a right value if it is available.
    /// If the right value is not available, it uses the converter to convert the left value.
    pub fn try_right<'a>(&'a self) -> Result<&'a R, C::ToRightError> {
        unsafe { self.try_right_with(|l| C::convert_to_right(l)) }
    }

    /// Returns a left value as a mutable reference.
    /// Note: Obtaining a mutable reference will erase the right value.
    /// If the left value is not available, it uses the converter to convert the right value.
    pub fn try_left_mut(&mut self) -> Result<&mut L, C::ToLeftError> {
        unsafe { self.try_left_mut_with(|r| C::convert_to_left(r)) }
    }

    /// Returns a right value as a mutable reference.
    /// Note: Obtaining a mutable reference will erase the left value.
    /// If the right value is not available, it uses the converter to convert the left value.
    pub fn try_right_mut(&mut self) -> Result<&mut R, C::ToRightError> {
        unsafe { self.try_right_mut_with(|l| C::convert_to_right(l)) }
    }

    /// Consumes the pair and turn it into a left value.
    pub fn try_into_left(self) -> Result<L, C::ToLeftError> {
        unsafe { self.try_into_left_with(|r| C::convert_to_left(&r)) }
    }

    /// Consumes the pair and turn it into a right value.
    pub fn try_into_right(self) -> Result<R, C::ToRightError> {
        unsafe { self.try_into_right_with(|l| C::convert_to_right(&l)) }
    }

    /// Consumes the pair and turn it into a left value.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_into_left_with<F: FnOnce(R) -> Result<L, E>, E>(self, f: F) -> Result<L, E> {
        match self {
            Self::GivenLeft { left, .. } => Ok(left),
            Self::GivenRight {
                right,
                mut left_cell,
                ..
            } => left_cell.take().map_or_else(|| f(right), Ok),
        }
    }

    /// Consumes the pair and turn it into a right value.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_into_right_with<F: FnOnce(L) -> Result<R, E>, E>(self, f: F) -> Result<R, E> {
        match self {
            Self::GivenRight { right, .. } => Ok(right),
            Self::GivenLeft {
                left,
                mut right_cell,
                ..
            } => right_cell.take().map_or_else(|| f(left), Ok),
        }
    }

    /// Returns a left value if it is available.
    /// If the left value is not available, it uses the converter to convert the right value.
    pub fn left<'a>(&'a self) -> &'a L
    where
        C::ToLeftError: Into<Infallible>,
    {
        match self {
            Self::GivenLeft { left, .. } => left,
            Self::GivenRight {
                left_cell, right, ..
            } => left_cell
                .get_or_try_init2(|| C::convert_to_left(right).map_err(Into::into))
                .into_ok2(),
        }
    }

    /// Returns a right value if it is available.
    /// If the right value is not available, it uses the converter to convert the left value.
    pub fn right<'a>(&'a self) -> &'a R
    where
        C::ToRightError: Into<Infallible>,
    {
        match self {
            Self::GivenLeft {
                left, right_cell, ..
            } => right_cell
                .get_or_try_init2(|| C::convert_to_right(left).map_err(Into::into))
                .into_ok2(),
            Self::GivenRight { right, .. } => right,
        }
    }

    /// Returns a left value as a mutable reference.
    /// Note: Obtaining a mutable reference will erase the right value.
    /// If the left value is not available, it uses the converter to convert the right value.
    pub fn left_mut(&mut self) -> &mut L
    where
        C::ToLeftError: Into<Infallible>,
    {
        match self {
            Self::GivenLeft {
                left, right_cell, ..
            } => {
                let _ = right_cell.take();
                left
            }
            Self::GivenRight {
                left_cell,
                right,
                converter,
            } => {
                let left = match left_cell.take() {
                    Some(left) => left,
                    None => C::convert_to_left(right).map_err(Into::into).into_ok2(),
                };
                // Take ownership of converter
                let converter = unsafe { std::ptr::read(converter) };
                *self = Self::from_left_conv(left, converter);
                let Self::GivenLeft { left, .. } = self else {
                    unreachable!()
                };
                left
            }
        }
    }

    /// Returns a right value as a mutable reference.
    /// Note: Obtaining a mutable reference will erase the left value.
    /// If the right value is not available, it uses the converter to convert the left value.
    pub fn right_mut(&mut self) -> &mut R
    where
        C::ToRightError: Into<Infallible>,
    {
        match self {
            Self::GivenLeft {
                left,
                right_cell,
                converter,
            } => {
                let right = match right_cell.take() {
                    Some(right) => right,
                    None => C::convert_to_right(left).map_err(Into::into).into_ok2(),
                };
                // Take ownership of converter
                let converter = unsafe { std::ptr::read(converter) };
                *self = Self::from_right_conv(right, converter);
                let Self::GivenRight { right, .. } = self else {
                    unreachable!()
                };
                right
            }
            Self::GivenRight {
                right, left_cell, ..
            } => {
                let _ = left_cell.take();
                right
            }
        }
    }

    /// Consumes the pair and turn it into a left value.
    pub fn into_left(self) -> L
    where
        C::ToLeftError: Into<Infallible>,
    {
        match self {
            Self::GivenLeft { left, .. } => left,
            Self::GivenRight {
                right,
                mut left_cell,
                ..
            } => left_cell
                .take()
                .unwrap_or_else(|| C::convert_to_left(&right).map_err(Into::into).into_ok2()),
        }
    }

    /// Consumes the pair and turn it into a right value.
    pub fn into_right(self) -> R
    where
        C::ToRightError: Into<Infallible>,
    {
        match self {
            Self::GivenRight { right, .. } => right,
            Self::GivenLeft {
                left,
                mut right_cell,
                ..
            } => right_cell
                .take()
                .unwrap_or_else(|| C::convert_to_right(&left).map_err(Into::into).into_ok2()),
        }
    }
}

impl<L: Debug, R: Debug, C> Debug for Pair<L, R, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Pair")
            .field(&self.left_opt())
            .field(&self.right_opt())
            .finish()
    }
}

impl<L: PartialEq, R: PartialEq, C> PartialEq for Pair<L, R, C> {
    fn eq(&self, other: &Self) -> bool {
        (self.left_opt(), self.right_opt()) == (other.left_opt(), other.right_opt())
    }
}

impl<L: Eq, R: Eq, C> Eq for Pair<L, R, C> {}

impl<L: Hash, R: Hash, C> Hash for Pair<L, R, C> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.left_opt().hash(state);
        self.right_opt().hash(state);
    }
}

impl<L, R, C> From<Pair<L, R, C>> for EitherOrBoth<L, R> {
    fn from(pair: Pair<L, R, C>) -> Self {
        let (left, right) = match pair {
            Pair::GivenLeft {
                left,
                mut right_cell,
                ..
            } => (Some(left), right_cell.take()),
            Pair::GivenRight {
                mut left_cell,
                right,
                ..
            } => (left_cell.take(), Some(right)),
        };
        match (left, right) {
            (Some(left), Some(right)) => EitherOrBoth::Both(left, right),
            (Some(left), None) => EitherOrBoth::Left(left),
            (None, Some(right)) => EitherOrBoth::Right(right),
            (None, None) => unreachable!(),
        }
    }
}

// An extension for `OnceCell`.
// This is a workaround for the lack (unstableness) of `get_or_try_init` method in `OnceCell`.
trait OnceCellExt<T> {
    fn get_or_try_init2<E, F>(&self, init: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>;
}
impl<T> OnceCellExt<T> for OnceCell<T> {
    fn get_or_try_init2<E, F>(&self, init: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        match self.get() {
            Some(v) => Ok(v),
            None => {
                let v = init()?;
                let _ = self.set(v); // We are sure the `set` will succeed.
                Ok(unsafe { self.get().unwrap_unchecked() })
            }
        }
    }
}

/// A trait for converting between left and right types.
pub trait Converter<L, R> {
    /// The error type that may occur during right-to-left conversion.
    type ToLeftError;

    /// The error type that may occur during left-to-right conversion.
    type ToRightError;

    /// Convert from left type to right type.
    fn convert_to_right(left: &L) -> Result<R, Self::ToRightError>;

    /// Convert from right type to left type.
    fn convert_to_left(right: &R) -> Result<L, Self::ToLeftError>;
}

/// A converter implementation using standard Rust's type conversion traits.
pub struct AutoConverter<L, R, E = Infallible>(std::marker::PhantomData<(L, R, E)>);

impl<L, R, E> Default for AutoConverter<L, R, E> {
    fn default() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl<L, R, E> Converter<L, R> for AutoConverter<L, R, E>
where
    for<'a> &'a L: TryInto<R>,
    for<'a> &'a R: TryInto<L>,
    for<'a> <&'a L as TryInto<R>>::Error: Into<E>,
    for<'a> <&'a R as TryInto<L>>::Error: Into<E>,
{
    type ToLeftError = E;
    type ToRightError = E;

    fn convert_to_right(left: &L) -> Result<R, Self::ToRightError> {
        left.try_into().map_err(Into::into)
    }

    fn convert_to_left(right: &R) -> Result<L, Self::ToLeftError> {
        right.try_into().map_err(Into::into)
    }
}

// An extension trait for Result that provides functionality similar to nightly's into_ok
trait ResultExt<T, E> {
    fn into_ok2(self) -> T
    where
        E: Into<Infallible>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn into_ok2(self) -> T
    where
        E: Into<Infallible>,
    {
        match self {
            Ok(v) => v,
            Err(_) => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::Infallible;

    // Define a custom error type
    #[derive(Debug, PartialEq)]
    struct CustomError;

    // Test converter implementation
    #[derive(Clone)]
    struct TestConverter;

    impl Converter<i32, String> for TestConverter {
        type ToLeftError = CustomError;
        type ToRightError = Infallible;

        fn convert_to_right(left: &i32) -> Result<String, Self::ToRightError> {
            Ok(left.to_string())
        }

        fn convert_to_left(right: &String) -> Result<i32, Self::ToLeftError> {
            right.parse().map_err(|_| CustomError)
        }
    }

    impl Default for TestConverter {
        fn default() -> Self {
            TestConverter
        }
    }

    #[test]
    fn test_basic_conversion() {
        let pair: Pair<i32, String, TestConverter> = Pair::from_left(42);

        // Test basic conversion functionality
        assert_eq!(pair.left_opt(), Some(&42));
        assert_eq!(pair.right_opt(), None);
        assert_eq!(pair.right(), &"42".to_string());
        assert_eq!(pair.right_opt(), Some(&"42".to_string()));
    }

    #[test]
    fn test_mutable_access() {
        let mut pair: Pair<i32, String, TestConverter> = Pair::from_left(42);

        // Verify that obtaining a mutable reference erases the other side
        assert_eq!(pair.right(), &"42".to_string());
        if let Some(left) = pair.left_opt_mut() {
            *left = 123;
        }
        assert_eq!(pair.right_opt(), None);
        assert_eq!(pair.right(), &"123".to_string());
    }

    #[test]
    fn test_error_handling() {
        let pair: Pair<i32, String, TestConverter> = Pair::from_right("invalid".to_string());

        // Test conversion error handling
        assert_eq!(pair.try_left(), Err(CustomError));
        assert_eq!(pair.right_opt(), Some(&"invalid".to_string()));
    }

    #[test]
    fn test_either_or_both() {
        let pair: Pair<i32, String, TestConverter> = Pair::from_left(42);

        // Test conversion to EitherOrBoth
        match pair.as_ref() {
            EitherOrBoth::Left(left) => {
                assert_eq!(*left, 42);
            }
            _ => panic!("Expected Left variant"),
        }

        // After accessing right, both values should be available
        assert_eq!(pair.right(), &"42".to_string());
        match pair.as_ref() {
            EitherOrBoth::Both(left, right) => {
                assert_eq!(*left, 42);
                assert_eq!(right, "42");
            }
            _ => panic!("Expected Both variant"),
        }
    }

    #[test]
    fn test_into_conversion() {
        let pair: Pair<i32, String, TestConverter> = Pair::from_left(42);

        // Test into_right conversion
        let right: String = pair.into_right();
        assert_eq!(right, "42");
    }

    #[test]
    fn test_clone() {
        let pair: Pair<i32, String, TestConverter> = Pair::from_left(42);
        let cloned = pair.clone();

        // Verify clone equality
        assert_eq!(pair.left_opt(), cloned.left_opt());
        assert_eq!(pair.right_opt(), cloned.right_opt());
    }
}
