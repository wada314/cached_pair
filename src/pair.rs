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

    fn try_left_with<'a, F: FnOnce(&'a R) -> Result<L, E>, E>(&'a self, f: F) -> Result<&'a L, E> {
        match self {
            PairInner::GivenLeft { left, .. } => Ok(left),
            PairInner::GivenRight { left_cell, right } => left_cell.get_or_try_init2(|| f(right)),
        }
    }

    fn try_right_with<'a, F: FnOnce(&'a L) -> Result<R, E>, E>(&'a self, f: F) -> Result<&'a R, E> {
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
                let left = match left_cell.take() {
                    Some(left) => left,
                    None => f(right)?,
                };
                *self = PairInner::from_left(left);
                let PairInner::GivenLeft { left, .. } = self else {
                    unreachable!()
                };
                Ok(left)
            }
        }
    }

    fn try_right_mut_with<F: FnOnce(&L) -> Result<R, E>, E>(&mut self, f: F) -> Result<&mut R, E> {
        match self {
            PairInner::GivenLeft { left, right_cell } => {
                let right = match right_cell.take() {
                    Some(right) => right,
                    None => f(left)?,
                };
                *self = PairInner::from_right(right);
                let PairInner::GivenRight { right, .. } = self else {
                    unreachable!()
                };
                Ok(right)
            }
            PairInner::GivenRight { right, left_cell } => {
                let _ = left_cell.take();
                Ok(right)
            }
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

    fn try_left_opt_mut<E>(&mut self) -> Result<Option<&mut L>, E> {
        match self {
            PairInner::GivenLeft { left, right_cell } => {
                let _ = right_cell.take();
                Ok(Some(left))
            }
            PairInner::GivenRight { left_cell, .. } => {
                if left_cell.get().is_some() {
                    let left = left_cell.take().unwrap();
                    *self = Self::from_left(left);
                    if let PairInner::GivenLeft { left, .. } = self {
                        Ok(Some(left))
                    } else {
                        unreachable!()
                    }
                } else {
                    Ok(None)
                }
            }
        }
    }

    fn try_right_opt_mut<E>(&mut self) -> Result<Option<&mut R>, E> {
        match self {
            PairInner::GivenLeft { right_cell, .. } => {
                if right_cell.get().is_some() {
                    let right = right_cell.take().unwrap();
                    *self = Self::from_right(right);
                    if let PairInner::GivenRight { right, .. } = self {
                        Ok(Some(right))
                    } else {
                        unreachable!()
                    }
                } else {
                    Ok(None)
                }
            }
            PairInner::GivenRight { right, left_cell } => {
                let _ = left_cell.take();
                Ok(Some(right))
            }
        }
    }
}

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
/// #[derive(Clone)]
/// struct MyConverter;
///
/// impl Converter<i32, String> for MyConverter {
///     type ToLeftError = ParseIntError;
///     type ToRightError = Infallible;
///
///     fn convert_to_right(&self, left: &i32) -> Result<String, Self::ToRightError> {
///         Ok(left.to_string())
///     }
///
///     fn convert_to_left(&self, right: &String) -> Result<i32, Self::ToLeftError> {
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
pub struct Pair<L, R, C = AutoConverter<L, R>> {
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
        match &self.inner {
            PairInner::GivenLeft { left, .. } => Some(left),
            PairInner::GivenRight { left_cell, .. } => left_cell.get(),
        }
    }

    /// Returns the right value if it is available. Otherwise, returns `None`.
    pub fn right_opt(&self) -> Option<&R> {
        match &self.inner {
            PairInner::GivenLeft { right_cell, .. } => right_cell.get(),
            PairInner::GivenRight { right, .. } => Some(right),
        }
    }

    /// Returns a mutable reference to the left value if it is available.
    /// Note: Obtaining a mutable reference will erase the right value.
    pub fn left_opt_mut(&mut self) -> Option<&mut L> {
        match &mut self.inner {
            PairInner::GivenLeft { left, right_cell } => {
                let _ = right_cell.take();
                Some(left)
            }
            PairInner::GivenRight { left_cell, .. } => left_cell.get_mut(),
        }
    }

    /// Returns a mutable reference to the right value if it is available.
    /// Note: Obtaining a mutable reference will erase the left value.
    pub fn right_opt_mut(&mut self) -> Option<&mut R> {
        match &mut self.inner {
            PairInner::GivenLeft { right_cell, .. } => right_cell.get_mut(),
            PairInner::GivenRight { right, left_cell } => {
                let _ = left_cell.take();
                Some(right)
            }
        }
    }

    /// Returns a mutable reference to the left value if it is available.
    /// Note: Obtaining a mutable reference will erase the right value.
    pub fn try_left_opt_mut<E>(&mut self) -> Result<Option<&mut L>, E>
    where
        C: Converter<L, R>,
        for<'a> E: From<C::ToLeftError<'a>>,
    {
        self.inner.try_left_opt_mut()
    }

    /// Returns a mutable reference to the right value if it is available.
    /// Note: Obtaining a mutable reference will erase the left value.
    pub fn try_right_opt_mut<E>(&mut self) -> Result<Option<&mut R>, E>
    where
        C: Converter<L, R>,
        for<'a> E: From<C::ToRightError<'a>>,
    {
        self.inner.try_right_opt_mut()
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
}

impl<L, R, C> Pair<L, R, C>
where
    C: Converter<L, R>,
{
    /// Returns a left value if it is available. Otherwise, converts the right value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_left_with<'a, F: FnOnce(&'a R) -> Result<L, E>, E>(
        &'a self,
        f: F,
    ) -> Result<&'a L, E> {
        self.inner.try_left_with(f)
    }

    /// Returns a right value if it is available. Otherwise, converts the left value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_right_with<'a, F: FnOnce(&'a L) -> Result<R, E>, E>(
        &'a self,
        f: F,
    ) -> Result<&'a R, E> {
        self.inner.try_right_with(f)
    }

    pub fn try_left(&self) -> Result<&L, C::ToLeftError<'_>> {
        self.inner
            .try_left_with(|r| self.converter.convert_to_left(r))
    }

    pub fn try_right(&self) -> Result<&R, C::ToRightError<'_>> {
        self.inner
            .try_right_with(|l| self.converter.convert_to_right(l))
    }

    pub fn try_left_mut<E>(&mut self) -> Result<&mut L, E>
    where
        for<'a> E: From<C::ToLeftError<'a>>,
    {
        self.inner
            .try_left_mut_with(|r| Ok(self.converter.convert_to_left(r)?))
    }

    pub fn try_right_mut<E>(&mut self) -> Result<&mut R, E>
    where
        for<'a> E: From<C::ToRightError<'a>>,
    {
        self.inner
            .try_right_mut_with(|l| Ok(self.converter.convert_to_right(l)?))
    }

    pub fn try_into_left<E>(self) -> Result<L, E>
    where
        for<'a> E: From<<C as Converter<L, R>>::ToLeftError<'a>>,
    {
        let converter = &self.converter;
        self.inner
            .try_into_left_with(|r| Ok(converter.convert_to_left(&r)?))
    }

    pub fn try_into_right<E>(self) -> Result<R, E>
    where
        for<'a> E: From<<C as Converter<L, R>>::ToRightError<'a>>,
    {
        let converter = &self.converter;
        self.inner
            .try_into_right_with(|l| Ok(converter.convert_to_right(&l)?))
    }

    pub fn left<'a>(&'a self) -> &'a L
    where
        C::ToLeftError<'a>: Into<Infallible>,
    {
        self.try_left().map_err(Into::into).into_ok2()
    }

    pub fn right<'a>(&'a self) -> &'a R
    where
        C::ToRightError<'a>: Into<Infallible>,
    {
        self.try_right().map_err(Into::into).into_ok2()
    }

    pub fn left_mut(&mut self) -> &mut L
    where
        for<'a> Infallible: From<C::ToLeftError<'a>>,
    {
        self.try_left_mut::<Infallible>().into_ok2()
    }

    pub fn right_mut(&mut self) -> &mut R
    where
        for<'a> Infallible: From<<C as Converter<L, R>>::ToRightError<'a>>,
    {
        self.try_right_mut::<Infallible>().into_ok2()
    }

    pub fn into_left(self) -> L
    where
        for<'a> Infallible: From<<C as Converter<L, R>>::ToLeftError<'a>>,
    {
        self.try_into_left::<Infallible>().into_ok2()
    }

    pub fn into_right(self) -> R
    where
        for<'a> Infallible: From<<C as Converter<L, R>>::ToRightError<'a>>,
    {
        self.try_into_right::<Infallible>().into_ok2()
    }

    /// Returns a left value if it is available.
    /// If the left value is not available, converts the right value using the given closure.
    /// The closure must not fail.
    pub fn left_with<'a, F: FnOnce(&'a R) -> L>(&'a self, f: F) -> &'a L {
        unsafe { self.try_left_with(|r| Ok::<L, Infallible>(f(r))).into_ok2() }
    }

    /// Returns a right value if it is available.
    /// If the right value is not available, converts the left value using the given closure.
    /// The closure must not fail.
    pub fn right_with<'a, F: FnOnce(&'a L) -> R>(&'a self, f: F) -> &'a R {
        unsafe {
            self.try_right_with(|l| Ok::<R, Infallible>(f(l)))
                .into_ok2()
        }
    }

    /// Returns a left value as a mutable reference if it is available.
    /// Note: Obtaining a mutable reference will erase the right value.
    /// If the left value is not available, converts the right value using the given closure.
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

    /// Returns a right value as a mutable reference if it is available.
    /// Note: Obtaining a mutable reference will erase the left value.
    /// If the right value is not available, converts the left value using the given closure.
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

    /// Consumes the pair and turns it into a left value.
    /// If the left value is not available, converts the right value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_into_left_with<F: FnOnce(R) -> Result<L, E>, E>(self, f: F) -> Result<L, E> {
        self.inner.try_into_left_with(f)
    }

    /// Consumes the pair and turns it into a right value.
    /// If the right value is not available, converts the left value using the given closure.
    ///
    /// # Safety
    /// The conversion function must be consistent with the converter's behavior.
    /// Inconsistent conversions may lead to invalid state.
    pub unsafe fn try_into_right_with<F: FnOnce(L) -> Result<R, E>, E>(self, f: F) -> Result<R, E> {
        self.inner.try_into_right_with(f)
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
    type ToLeftError<'a>
    where
        R: 'a;

    /// The error type that may occur during left-to-right conversion.
    type ToRightError<'a>
    where
        L: 'a;

    /// Convert from left type to right type.
    fn convert_to_right<'a>(&self, left: &'a L) -> Result<R, Self::ToRightError<'a>>;

    /// Convert from right type to left type.
    fn convert_to_left<'a>(&self, right: &'a R) -> Result<L, Self::ToLeftError<'a>>;
}

/// A converter implementation using standard Rust's type conversion traits.
pub struct AutoConverter<L, R>(std::marker::PhantomData<(L, R)>);

impl<L, R> Default for AutoConverter<L, R> {
    fn default() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl<L, R> Converter<L, R> for AutoConverter<L, R>
where
    for<'a> &'a L: TryInto<R>,
    for<'a> &'a R: TryInto<L>,
{
    type ToLeftError<'a>
        = <&'a R as TryInto<L>>::Error
    where
        R: 'a;
    type ToRightError<'a>
        = <&'a L as TryInto<R>>::Error
    where
        L: 'a;

    fn convert_to_right<'a>(&self, left: &'a L) -> Result<R, Self::ToRightError<'a>> {
        left.try_into()
    }

    fn convert_to_left<'a>(&self, right: &'a R) -> Result<L, Self::ToLeftError<'a>> {
        right.try_into()
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
            Err(e) => match e.into() {},
        }
    }
}
