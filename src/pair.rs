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

#[cfg(test)]
mod tests;

use ::std::cell::OnceCell;
use ::std::convert::Infallible;
use ::std::fmt::Debug;
use ::std::hash::Hash;
use ::std::ptr;

/// Re-exporting from `itertools` crate.
pub use ::itertools::EitherOrBoth;

/// A pair of values where one can be converted to the other.
///
/// # Example
///
/// ```rust
/// use cached_pair::{Pair, fn_converter};
/// use std::convert::Infallible;
/// use std::num::ParseIntError;
///
/// // Define a converter between i32 and String using fn_converter
/// let converter = fn_converter(
///     |s: &String| s.parse::<i32>(),  // String -> i32 (may fail)
///     |i: &i32| Ok::<String, Infallible>(i.to_string()),    // i32 -> String (never fails)
/// );
///
/// // Construct a pair from a left value.
/// let pair = Pair::from_left_conv(42i32, converter);
///
/// // Left value is present, but right value is not.
/// assert_eq!(pair.left_opt(), Some(&42));
/// assert_eq!(pair.right_opt(), None);
///
/// // Get a right value by converting the left value.
/// assert_eq!(pair.try_right(), Ok(&"42".to_string()));
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
pub struct Pair<L, R, C = StdConverter> {
    inner: PairInner<L, R>,
    converter: C,
}

impl<L, R, C> Pair<L, R, C> {
    /// Creates a new pair from a left value.
    pub fn from_left(left: L) -> Self
    where
        C: Default,
    {
        Self {
            inner: PairInner::from_left(left),
            converter: C::default(),
        }
    }

    /// Creates a new pair from a right value.
    pub fn from_right(right: R) -> Self
    where
        C: Default,
    {
        Self {
            inner: PairInner::from_right(right),
            converter: C::default(),
        }
    }

    /// Creates a new pair from a left value with a custom converter.
    pub fn from_left_conv(left: L, converter: C) -> Self {
        Self {
            inner: PairInner::from_left(left),
            converter,
        }
    }

    /// Creates a new pair from a right value with a custom converter.
    pub fn from_right_conv(right: R, converter: C) -> Self {
        Self {
            inner: PairInner::from_right(right),
            converter,
        }
    }

    /// Returns the left value if it is available. Otherwise, returns `None`.
    pub fn left_opt(&self) -> Option<&L> {
        self.inner.left_opt()
    }

    /// Returns the right value if it is available. Otherwise, returns `None`.
    pub fn right_opt(&self) -> Option<&R> {
        self.inner.right_opt()
    }

    /// Returns a mutable reference to the left value if it is available.
    /// Note: Obtaining a mutable reference will erase the right value.
    pub fn left_opt_mut(&mut self) -> Option<&mut L> {
        self.inner.left_opt_mut()
    }

    /// Returns a mutable reference to the right value if it is available.
    /// Note: Obtaining a mutable reference will erase the left value.
    pub fn right_opt_mut(&mut self) -> Option<&mut R> {
        self.inner.right_opt_mut()
    }

    /// Returns a left value if it is available.
    /// If the left value is not available, converts the right value using the given closure.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn left_with<F: FnOnce(&R) -> L>(&self, f: F) -> &L {
        self.try_left_with(|r| Ok::<L, Infallible>(f(r))).into_ok2()
    }

    /// Returns a right value if it is available.
    /// If the right value is not available, converts the left value using the given closure.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn right_with<F: FnOnce(&L) -> R>(&self, f: F) -> &R {
        self.try_right_with(|l| Ok::<R, Infallible>(f(l)))
            .into_ok2()
    }

    /// Returns a left value if it is available.
    /// If the left value is not available, attempts to convert the right value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_left_with<F: FnOnce(&R) -> Result<L, E>, E>(&self, f: F) -> Result<&L, E> {
        self.inner.try_left_with(f)
    }

    /// Returns a right value if it is available.
    /// If the right value is not available, attempts to convert the left value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_right_with<F: FnOnce(&L) -> Result<R, E>, E>(&self, f: F) -> Result<&R, E> {
        self.inner.try_right_with(f)
    }

    /// Returns a mutable reference to the left value if it is available.
    /// Note: Obtaining a mutable reference will erase the right value.
    /// If the left value is not available, converts the right value using the given closure.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn left_mut_with<F: FnOnce(&R) -> L>(&mut self, f: F) -> &mut L {
        self.try_left_mut_with(|r| Ok::<L, Infallible>(f(r)))
            .into_ok2()
    }

    /// Returns a mutable reference to the right value if it is available.
    /// Note: Obtaining a mutable reference will erase the left value.
    /// If the right value is not available, converts the left value using the given closure.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn right_mut_with<F: FnOnce(&L) -> R>(&mut self, f: F) -> &mut R {
        self.try_right_mut_with(|l| Ok::<R, Infallible>(f(l)))
            .into_ok2()
    }

    /// Returns a mutable reference to the left value if it is available.
    /// Note: Obtaining a mutable reference will erase the right value.
    /// If the left value is not available, attempts to convert the right value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_left_mut_with<F: FnOnce(&R) -> Result<L, E>, E>(
        &mut self,
        f: F,
    ) -> Result<&mut L, E> {
        self.inner.try_left_mut_with(f)
    }

    /// Returns a mutable reference to the right value if it is available.
    /// Note: Obtaining a mutable reference will erase the left value.
    /// If the right value is not available, attempts to convert the left value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_right_mut_with<F: FnOnce(&L) -> Result<R, E>, E>(
        &mut self,
        f: F,
    ) -> Result<&mut R, E> {
        self.inner.try_right_mut_with(f)
    }

    /// Consumes the pair and returns the left value.
    /// If the left value is not available, converts the right value using the given closure.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn into_left_with<F: FnOnce(R) -> L>(self, f: F) -> L {
        self.try_into_left_with(|r| Ok::<L, Infallible>(f(r)))
            .into_ok2()
    }

    /// Consumes the pair and returns the right value.
    /// If the right value is not available, converts the left value using the given closure.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn into_right_with<F: FnOnce(L) -> R>(self, f: F) -> R {
        self.try_into_right_with(|l| Ok::<R, Infallible>(f(l)))
            .into_ok2()
    }

    /// Consumes the pair and attempts to return the left value.
    /// If the left value is not available, attempts to convert the right value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_into_left_with<F: FnOnce(R) -> Result<L, E>, E>(self, f: F) -> Result<L, E> {
        self.inner.try_into_left_with(f)
    }

    /// Consumes the pair and attempts to return the right value.
    /// If the right value is not available, attempts to convert the left value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_into_right_with<F: FnOnce(L) -> Result<R, E>, E>(self, f: F) -> Result<R, E> {
        self.inner.try_into_right_with(f)
    }

    /// Returns a reference to the pair as `itertools::EitherOrBoth`.
    pub fn as_ref(&self) -> EitherOrBoth<&L, &R> {
        match &self.inner {
            PairInner::GivenLeft { left, right_cell } => match right_cell.get() {
                Some(right) => EitherOrBoth::Both(left, right),
                None => EitherOrBoth::Left(left),
            },
            PairInner::GivenRight { right, left_cell } => match left_cell.get() {
                Some(left) => EitherOrBoth::Both(left, right),
                None => EitherOrBoth::Right(right),
            },
        }
    }

    /// Clears the left value if it exists and returns it.
    /// If the left value is the only value in the pair, converts it to a right value using the given closure before clearing.
    /// Returns None if the left value doesn't exist.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn extract_left_with<F: FnOnce(&L) -> R>(&mut self, f: F) -> Option<L> {
        self.try_extract_left_with(|l| Ok::<R, Infallible>(f(l)))
            .into_ok2()
    }

    /// Clears the right value if it exists and returns it.
    /// If the right value is the only value in the pair, converts it to a left value using the given closure before clearing.
    /// Returns None if the right value doesn't exist.
    /// The closure must not fail.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn extract_right_with<F: FnOnce(&R) -> L>(&mut self, f: F) -> Option<R> {
        self.try_extract_right_with(|r| Ok::<L, Infallible>(f(r)))
            .into_ok2()
    }

    /// Clears the left value if it exists and returns it.
    /// If the left value is the only value in the pair, attempts to convert it to a right value using the given closure before clearing.
    /// Returns None if the left value doesn't exist.
    /// Returns Err if conversion fails when needed.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_extract_left_with<F: FnOnce(&L) -> Result<R, E>, E>(
        &mut self,
        f: F,
    ) -> Result<Option<L>, E> {
        self.inner.try_extract_left_with(f)
    }

    /// Clears the right value if it exists and returns it.
    /// If the right value is the only value in the pair, attempts to convert it to a left value using the given closure before clearing.
    /// Returns None if the right value doesn't exist.
    /// Returns Err if conversion fails when needed.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_extract_right_with<F: FnOnce(&R) -> Result<L, E>, E>(
        &mut self,
        f: F,
    ) -> Result<Option<R>, E> {
        self.inner.try_extract_right_with(f)
    }

    /// Returns a reference to the converter used by this pair.
    pub fn converter(&self) -> &C {
        &self.converter
    }

    /// Returns a mutable reference to the converter used by this pair.
    pub fn converter_mut(&mut self) -> &mut C {
        &mut self.converter
    }
}

impl<L, R, C> Pair<L, R, C>
where
    C: Converter<L, R>,
{
    /// Returns a reference to the left value.
    /// If the left value is not available, converts the right value using the converter.
    /// This method is only available when the conversion is infallible.
    pub fn left(&self) -> &L
    where
        C: Converter<L, R, ToLeftError = Infallible>,
    {
        self.try_left().into_ok2()
    }

    /// Returns a reference to the right value.
    /// If the right value is not available, converts the left value using the converter.
    /// This method is only available when the conversion is infallible.
    pub fn right(&self) -> &R
    where
        C: Converter<L, R, ToRightError = Infallible>,
    {
        self.try_right().into_ok2()
    }

    /// Attempts to get a reference to the left value.
    /// If the left value is not available, attempts to convert the right value using the converter.
    pub fn try_left(&self) -> Result<&L, C::ToLeftError> {
        self.inner
            .try_left_with(|r| self.converter.convert_to_left(r))
    }

    /// Attempts to get a reference to the right value.
    /// If the right value is not available, attempts to convert the left value using the converter.
    pub fn try_right(&self) -> Result<&R, C::ToRightError> {
        self.inner
            .try_right_with(|l| self.converter.convert_to_right(l))
    }

    /// Returns a mutable reference to the left value.
    /// If the left value is not available, converts the right value using the converter.
    /// This method is only available when the conversion is infallible.
    /// Note: Obtaining a mutable reference will erase the right value.
    pub fn left_mut(&mut self) -> &mut L
    where
        C: Converter<L, R, ToLeftError = Infallible>,
    {
        self.try_left_mut().into_ok2()
    }

    /// Returns a mutable reference to the right value.
    /// If the right value is not available, converts the left value using the converter.
    /// This method is only available when the conversion is infallible.
    /// Note: Obtaining a mutable reference will erase the left value.
    pub fn right_mut(&mut self) -> &mut R
    where
        C: Converter<L, R, ToRightError = Infallible>,
    {
        self.try_right_mut().into_ok2()
    }

    /// Attempts to get a mutable reference to the left value.
    /// If the left value is not available, attempts to convert the right value using the converter.
    /// Note: Obtaining a mutable reference will erase the right value.
    pub fn try_left_mut(&mut self) -> Result<&mut L, C::ToLeftError> {
        self.inner
            .try_left_mut_with(|r| Ok(self.converter.convert_to_left(r)?))
    }

    /// Attempts to get a mutable reference to the right value.
    /// If the right value is not available, attempts to convert the left value using the converter.
    /// Note: Obtaining a mutable reference will erase the left value.
    pub fn try_right_mut(&mut self) -> Result<&mut R, C::ToRightError> {
        self.inner
            .try_right_mut_with(|l| Ok(self.converter.convert_to_right(l)?))
    }

    /// Consumes the pair and returns the left value.
    /// If the left value is not available, converts the right value using the converter.
    /// This method is only available when the conversion is infallible.
    pub fn into_left(self) -> L
    where
        C: Converter<L, R, ToLeftError = Infallible>,
    {
        self.try_into_left().into_ok2()
    }

    /// Consumes the pair and returns the right value.
    /// If the right value is not available, converts the left value using the converter.
    /// This method is only available when the conversion is infallible.
    pub fn into_right(self) -> R
    where
        C: Converter<L, R, ToRightError = Infallible>,
    {
        self.try_into_right().into_ok2()
    }

    /// Attempts to consume the pair and return the left value.
    /// If the left value is not available, attempts to convert the right value using the converter.
    pub fn try_into_left(self) -> Result<L, C::ToLeftError> {
        let converter = &self.converter;
        self.inner
            .try_into_left_with(|r| Ok(converter.convert_to_left(&r)?))
    }

    /// Attempts to consume the pair and return the right value.
    /// If the right value is not available, attempts to convert the left value using the converter.
    pub fn try_into_right(self) -> Result<R, C::ToRightError> {
        let converter = &self.converter;
        self.inner
            .try_into_right_with(|l| Ok(converter.convert_to_right(&l)?))
    }

    /// Clears the left value if it exists and returns it.
    /// If the left value is the only value in the pair, attempts to convert it to a right value before clearing.
    /// Returns None if the left value doesn't exist.
    /// This method is only available when the conversion is infallible.
    pub fn extract_left(&mut self) -> Option<L>
    where
        C: Converter<L, R, ToRightError = Infallible>,
    {
        self.try_extract_left().into_ok2()
    }

    /// Clears the right value if it exists and returns it.
    /// If the right value is the only value in the pair, attempts to convert it to a left value before clearing.
    /// Returns None if the right value doesn't exist.
    /// This method is only available when the conversion is infallible.
    pub fn extract_right(&mut self) -> Option<R>
    where
        C: Converter<L, R, ToLeftError = Infallible>,
    {
        self.try_extract_right().into_ok2()
    }

    /// Clears the left value if it exists and returns it.
    /// If the left value is the only value in the pair, attempts to convert it to a right value before clearing.
    /// Returns None if the left value doesn't exist.
    /// Returns Err if conversion fails when needed.
    pub fn try_extract_left(&mut self) -> Result<Option<L>, C::ToRightError> {
        self.inner
            .try_extract_left_with(|l| Ok(self.converter.convert_to_right(l)?))
    }

    /// Clears the right value if it exists and returns it.
    /// If the right value is the only value in the pair, attempts to convert it to a left value before clearing.
    /// Returns None if the right value doesn't exist.
    /// Returns Err if conversion fails when needed.
    pub fn try_extract_right(&mut self) -> Result<Option<R>, C::ToLeftError> {
        self.inner
            .try_extract_right_with(|r| Ok(self.converter.convert_to_left(r)?))
    }
}

#[derive(Clone)]
enum PairInner<L, R> {
    #[doc(hidden)]
    GivenLeft { left: L, right_cell: OnceCell<R> },
    #[doc(hidden)]
    GivenRight { left_cell: OnceCell<L>, right: R },
}

impl<L, R> PairInner<L, R> {
    fn from_left(left: L) -> Self {
        Self::GivenLeft {
            left,
            right_cell: OnceCell::new(),
        }
    }

    fn from_right(right: R) -> Self {
        Self::GivenRight {
            left_cell: OnceCell::new(),
            right,
        }
    }

    fn left_opt(&self) -> Option<&L> {
        match self {
            PairInner::GivenLeft { left, .. } => Some(left),
            PairInner::GivenRight { left_cell, .. } => left_cell.get(),
        }
    }

    fn right_opt(&self) -> Option<&R> {
        match self {
            PairInner::GivenLeft { right_cell, .. } => right_cell.get(),
            PairInner::GivenRight { right, .. } => Some(right),
        }
    }

    fn left_opt_mut(&mut self) -> Option<&mut L> {
        match self {
            PairInner::GivenLeft { left, right_cell } => {
                let _ = right_cell.take();
                Some(left)
            }
            PairInner::GivenRight { left_cell, .. } => {
                let left = left_cell.take()?;
                *self = Self::from_left(left);
                if let PairInner::GivenLeft { left, .. } = self {
                    Some(left)
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn right_opt_mut(&mut self) -> Option<&mut R> {
        match self {
            PairInner::GivenLeft { right_cell, .. } => {
                let right = right_cell.take()?;
                *self = Self::from_right(right);
                if let PairInner::GivenRight { right, .. } = self {
                    Some(right)
                } else {
                    unreachable!()
                }
            }
            PairInner::GivenRight { right, left_cell } => {
                let _ = left_cell.take();
                Some(right)
            }
        }
    }

    fn try_left_with<F: FnOnce(&R) -> Result<L, E>, E>(&self, f: F) -> Result<&L, E> {
        match self {
            PairInner::GivenLeft { left, .. } => Ok(left),
            PairInner::GivenRight { left_cell, right } => left_cell.get_or_try_init2(|| f(right)),
        }
    }

    fn try_right_with<F: FnOnce(&L) -> Result<R, E>, E>(&self, f: F) -> Result<&R, E> {
        match self {
            PairInner::GivenLeft { left, right_cell } => right_cell.get_or_try_init2(|| f(left)),
            PairInner::GivenRight { right, .. } => Ok(right),
        }
    }

    fn try_left_mut_with<F: FnOnce(&R) -> Result<L, E>, E>(&mut self, f: F) -> Result<&mut L, E> {
        match self {
            PairInner::GivenLeft { left, right_cell } => {
                let _ = right_cell.take();
                Ok(left)
            }
            PairInner::GivenRight { left_cell, right } => {
                let left = left_cell.take().map(Ok).unwrap_or_else(|| f(right))?;
                *self = Self::from_left(left);

                if let PairInner::GivenLeft { left, .. } = self {
                    Ok(left)
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn try_right_mut_with<F: FnOnce(&L) -> Result<R, E>, E>(&mut self, f: F) -> Result<&mut R, E> {
        match self {
            PairInner::GivenLeft { left, right_cell } => {
                let right = right_cell.take().map(Ok).unwrap_or_else(|| f(left))?;
                *self = Self::from_right(right);

                if let PairInner::GivenRight { right, .. } = self {
                    Ok(right)
                } else {
                    unreachable!()
                }
            }
            PairInner::GivenRight { right, left_cell } => {
                let _ = left_cell.take();
                Ok(right)
            }
        }
    }

    fn try_extract_left_with<F: FnOnce(&L) -> Result<R, E>, E>(
        &mut self,
        f: F,
    ) -> Result<Option<L>, E> {
        match self {
            PairInner::GivenLeft { left, right_cell } => {
                let right = right_cell.take().map(Ok).unwrap_or_else(|| f(left))?;
                let _ = unsafe { ptr::read(right_cell) };
                let old_left = unsafe { ptr::read(left) };
                unsafe {
                    ptr::write(self, Self::from_right(right));
                }
                Ok(Some(old_left))
            }
            PairInner::GivenRight { left_cell, .. } => Ok(left_cell.take()),
        }
    }

    fn try_extract_right_with<F: FnOnce(&R) -> Result<L, E>, E>(
        &mut self,
        f: F,
    ) -> Result<Option<R>, E> {
        match self {
            PairInner::GivenRight { right, left_cell } => {
                let left = left_cell.take().map(Ok).unwrap_or_else(|| f(right))?;
                let _ = unsafe { ptr::read(left_cell) };
                let old_right = unsafe { ptr::read(right) };
                unsafe {
                    ptr::write(self, Self::from_left(left));
                }
                Ok(Some(old_right))
            }
            PairInner::GivenLeft { right_cell, .. } => Ok(right_cell.take()),
        }
    }

    fn try_into_left_with<F: FnOnce(R) -> Result<L, E>, E>(self, f: F) -> Result<L, E> {
        match self {
            PairInner::GivenLeft { left, .. } => Ok(left),
            PairInner::GivenRight {
                right,
                mut left_cell,
            } => left_cell.take().map_or_else(|| f(right), Ok),
        }
    }

    fn try_into_right_with<F: FnOnce(L) -> Result<R, E>, E>(self, f: F) -> Result<R, E> {
        match self {
            PairInner::GivenRight { right, .. } => Ok(right),
            PairInner::GivenLeft {
                left,
                mut right_cell,
            } => right_cell.take().map_or_else(|| f(left), Ok),
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

impl<L: Hash, R: Hash, C> Hash for Pair<L, R, C> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.left_opt().hash(state);
        self.right_opt().hash(state);
    }
}

impl<L, R, C> From<Pair<L, R, C>> for EitherOrBoth<L, R> {
    fn from(pair: Pair<L, R, C>) -> Self {
        let (left, right) = match pair.inner {
            PairInner::GivenLeft {
                left,
                mut right_cell,
            } => (Some(left), right_cell.take()),
            PairInner::GivenRight {
                mut left_cell,
                right,
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

/// A trait for converting between two types.
/// This trait is used by [`Pair`] to convert between its left and right values.
///
/// # Example
///
/// ```rust
/// use cached_pair::Converter;
/// use std::convert::Infallible;
/// use std::num::ParseIntError;
///
/// struct MyConverter;
///
/// impl Converter<i32, String> for MyConverter {
///     type ToLeftError = ParseIntError;
///     type ToRightError = Infallible;
///
///     fn convert_to_left(&self, right: &String) -> Result<i32, Self::ToLeftError> {
///         right.parse()
///     }
///
///     fn convert_to_right(&self, left: &i32) -> Result<String, Self::ToRightError> {
///         Ok(left.to_string())
///     }
/// }
/// ```
pub trait Converter<L, R> {
    /// The error type returned when converting from right to left.
    type ToLeftError;

    /// The error type returned when converting from left to right.
    type ToRightError;

    /// Converts a reference to a right value into a left value.
    fn convert_to_left(&self, right: &R) -> Result<L, Self::ToLeftError>;

    /// Converts a reference to a left value into a right value.
    fn convert_to_right(&self, left: &L) -> Result<R, Self::ToRightError>;
}

/// A standard converter that uses the `TryFrom` trait for conversions.
/// This is the default converter used by [`Pair`] when no converter is specified.
/// Note that this converter requires the `TryFrom<&L> for R` and `TryFrom<&R> for L`
/// implementations, which are not typically implemented by the library authors.
#[derive(Default, Debug, Clone)]
pub struct StdConverter;

impl<L, R, EL, ER> Converter<L, R> for StdConverter
where
    for<'a> &'a L: TryInto<R, Error = ER>,
    for<'a> &'a R: TryInto<L, Error = EL>,
{
    type ToLeftError = EL;
    type ToRightError = ER;

    fn convert_to_left(&self, right: &R) -> Result<L, Self::ToLeftError> {
        right.try_into()
    }

    fn convert_to_right(&self, left: &L) -> Result<R, Self::ToRightError> {
        left.try_into()
    }
}

/// A converter that uses closures for conversions.
/// This is useful when you want to provide custom conversion logic without implementing the `TryFrom` trait.
#[derive(Clone)]
pub struct FnConverter<F, G> {
    to_left: F,
    to_right: G,
}

impl<F, G> Debug for FnConverter<F, G> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FnConverter")
            .field("to_left", &"<function>")
            .field("to_right", &"<function>")
            .finish()
    }
}

/// Creates a new [`FnConverter`] from two functions.
/// This is a convenience function for creating a converter that uses closures for conversions.
/// Note that the type of the converter is not descriptable if you use the closure as an argument.
/// Use [`boxed_fn_converter`] instead if you need a descriptable type.
///
/// # Example
///
/// ```rust
/// use cached_pair::{Pair, fn_converter};
/// use std::convert::Infallible;
/// use std::num::TryFromIntError;
///
/// let converter = fn_converter(
///     // Right to left
///     |i: &i32| -> Result<u8, TryFromIntError> { (*i - 10).try_into() },
///     // Left to right
///     |u: &u8| -> Result<i32, Infallible> { Ok((*u as i32) + 10) },
/// );
///
/// let pair = Pair::from_right_conv(52i32, converter);
/// assert_eq!(pair.try_left(), Ok(&42u8));
/// ```
pub fn fn_converter<F, G>(f: F, g: G) -> FnConverter<F, G> {
    FnConverter {
        to_left: f,
        to_right: g,
    }
}

impl<L, R, F, G, EL, ER> Converter<L, R> for FnConverter<F, G>
where
    for<'a> F: Fn(&'a R) -> Result<L, EL>,
    for<'a> G: Fn(&'a L) -> Result<R, ER>,
{
    type ToLeftError = EL;
    type ToRightError = ER;

    fn convert_to_left(&self, right: &R) -> Result<L, Self::ToLeftError> {
        (self.to_left)(right)
    }

    fn convert_to_right(&self, left: &L) -> Result<R, Self::ToRightError> {
        (self.to_right)(left)
    }
}

/// A converter that uses boxed closures for conversions.
/// This is similar to [`FnConverter`] but uses trait objects,
/// making its type always descriptable.
///
/// # Example
///
/// ```rust
/// use cached_pair::{Pair, boxed_fn_converter};
/// use std::convert::Infallible;
/// use std::num::TryFromIntError;
///
/// let converter = boxed_fn_converter(
///     // Right to left
///     |i: &i32| -> Result<u8, TryFromIntError> { (*i - 100).try_into() },
///     // Left to right
///     |u: &u8| -> Result<i32, Infallible> { Ok((*u as i32) + 100) },
/// );
///
/// let pair = Pair::from_right_conv(142i32, converter);
/// assert_eq!(pair.try_left(), Ok(&42u8));
/// ```
pub struct BoxedFnConverter<L, R, EL = Infallible, ER = Infallible> {
    to_left: Box<dyn for<'a> Fn(&'a R) -> Result<L, EL>>,
    to_right: Box<dyn for<'a> Fn(&'a L) -> Result<R, ER>>,
}

impl<L, R, EL, ER> Debug for BoxedFnConverter<L, R, EL, ER> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoxedFnConverter")
            .field("to_left", &"<boxed function>")
            .field("to_right", &"<boxed function>")
            .finish()
    }
}

/// Creates a new [`BoxedFnConverter`] from two closures.
/// This is a convenience function for creating a converter that uses boxed closures for conversions.
///
/// # Example
///
/// ```rust
/// use cached_pair::{Pair, boxed_fn_converter};
/// use std::convert::Infallible;
/// use std::num::TryFromIntError;
///
/// let converter = boxed_fn_converter(
///     |i: &i32| -> Result<u8, TryFromIntError> { (*i - 100).try_into() },
///     |u: &u8| -> Result<i32, Infallible> { Ok((*u as i32) + 100) },
/// );
///
/// let pair = Pair::from_right_conv(142i32, converter);
/// assert_eq!(pair.try_left(), Ok(&42u8));
/// ```
pub fn boxed_fn_converter<L, R, F, G, EL, ER>(f: F, g: G) -> BoxedFnConverter<L, R, EL, ER>
where
    for<'a> F: Fn(&'a R) -> Result<L, EL> + 'static,
    for<'a> G: Fn(&'a L) -> Result<R, ER> + 'static,
{
    BoxedFnConverter {
        to_left: Box::new(f),
        to_right: Box::new(g),
    }
}

impl<L, R, EL, ER> Converter<L, R> for BoxedFnConverter<L, R, EL, ER> {
    type ToLeftError = EL;
    type ToRightError = ER;

    fn convert_to_left(&self, right: &R) -> Result<L, Self::ToLeftError> {
        (self.to_left)(right)
    }

    fn convert_to_right(&self, left: &L) -> Result<R, Self::ToRightError> {
        (self.to_right)(left)
    }
}

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

trait ResultExt<T, E> {
    fn into_ok2(self) -> T
    where
        E: Into<Infallible>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    #[allow(unreachable_code)]
    fn into_ok2(self) -> T
    where
        E: Into<Infallible>,
    {
        match self {
            Ok(v) => v,
            Err(e) => match e.into() {},
        }
    }
}
