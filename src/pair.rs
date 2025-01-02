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

/// A pair of values where one can be converted to the other.
///
/// # Example
///
/// ```rust
/// use cached_pair::Pair;
///
/// // Construct a pair from a left value.
/// let pair: Pair<i32, String> = Pair::from_left(42);
///
/// // Left value is present, but right value is not.
/// assert_eq!(pair.left_opt(), Some(&42));
/// assert_eq!(pair.right_opt(), None);
///
/// // Get a right value by converting the left value.
/// assert_eq!(pair.right_with(|l| l.to_string()), "42");
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
pub enum Pair<L, R> {
    GivenLeft { left: L, right_cell: OnceCell<R> },
    GivenRight { left_cell: OnceCell<L>, right: R },
}

impl<L, R> Pair<L, R> {
    /// Constructs a pair from a left value.
    pub fn from_left(left: L) -> Self {
        Self::GivenLeft {
            left,
            right_cell: OnceCell::new(),
        }
    }

    /// Constructs a pair from a right value.
    pub fn from_right(right: R) -> Self {
        Self::GivenRight {
            left_cell: OnceCell::new(),
            right,
        }
    }

    /// Returns the left value. If the left value is not available, it converts the right value using the given closure.
    pub fn left_with<'a, F: FnOnce(&'a R) -> L>(&'a self, f: F) -> &'a L {
        match self {
            Self::GivenLeft { left, .. } => left,
            Self::GivenRight { left_cell, right } => left_cell.get_or_init(|| f(right)),
        }
    }

    /// Returns the right value. If the right value is not available, it converts the left value using the given closure.
    pub fn right_with<'a, F: FnOnce(&'a L) -> R>(&'a self, f: F) -> &'a R {
        match self {
            Self::GivenLeft { left, right_cell } => right_cell.get_or_init(|| f(left)),
            Self::GivenRight { right, .. } => right,
        }
    }

    /// Returns the left value. If the left value is not available, it converts the right value using the given closure.
    pub fn try_left_with<'a, F: FnOnce(&'a R) -> Result<L, E>, E>(
        &'a self,
        f: F,
    ) -> Result<&'a L, E> {
        match self {
            Self::GivenLeft { left, .. } => Ok(left),
            Self::GivenRight { left_cell, right } => left_cell.get_or_try_init2(|| f(right)),
        }
    }

    /// Returns the right value. If the right value is not available, it converts the left value using the given closure.
    pub fn try_right_with<'a, F: FnOnce(&'a L) -> Result<R, E>, E>(
        &'a self,
        f: F,
    ) -> Result<&'a R, E> {
        match self {
            Self::GivenLeft { left, right_cell } => right_cell.get_or_try_init2(|| f(left)),
            Self::GivenRight { right, .. } => Ok(right),
        }
    }

    /// Returns the left value as a mutable reference.
    /// If the left value is not available, it converts the right value using the given closure.
    pub fn left_mut_with<F: for<'a> FnOnce(&'a R) -> L>(&mut self, f: F) -> &mut L {
        self.try_left_mut_with(|r| -> Result<_, Infallible> { Ok(f(r)) })
            .unwrap()
    }

    /// Returns the right value as a mutable reference.
    /// If the right value is not available, it converts the left value using the given closure.
    pub fn right_mut_with<F: for<'a> FnOnce(&'a L) -> R>(&mut self, f: F) -> &mut R {
        self.try_right_mut_with(|l| -> Result<_, Infallible> { Ok(f(l)) })
            .unwrap()
    }

    /// Returns the left value as a mutable reference.
    /// If the left value is not available, it converts the right value using the given closure.
    pub fn try_left_mut_with<F: for<'a> FnOnce(&'a R) -> Result<L, E>, E>(
        &mut self,
        f: F,
    ) -> Result<&mut L, E> {
        match self {
            Self::GivenLeft { left, right_cell } => {
                let _ = right_cell.take();
                Ok(left)
            }
            Self::GivenRight { left_cell, right } => {
                let left = match left_cell.take() {
                    Some(left) => left,
                    None => f(right)?,
                };
                *self = Self::from_left(left);
                let Self::GivenLeft { left, .. } = self else {
                    unreachable!()
                };
                Ok(left)
            }
        }
    }

    /// Returns the right value as a mutable reference.
    /// If the right value is not available, it converts the left value using the given closure.
    pub fn try_right_mut_with<F: for<'a> FnOnce(&'a L) -> Result<R, E>, E>(
        &mut self,
        f: F,
    ) -> Result<&mut R, E> {
        match self {
            Self::GivenLeft { left, right_cell } => {
                let right = match right_cell.take() {
                    Some(right) => right,
                    None => f(left)?,
                };
                *self = Self::from_right(right);
                let Self::GivenRight { right, .. } = self else {
                    unreachable!()
                };
                Ok(right)
            }
            Self::GivenRight { right, left_cell } => {
                let _ = left_cell.take();
                Ok(right)
            }
        }
    }

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

    /// Returns a left value if it is available.
    /// If the left value is available, this method clears the right value.
    pub fn left_opt_mut(&mut self) -> Option<&mut L> {
        match self {
            Self::GivenLeft { left, right_cell } => {
                let _ = right_cell.take();
                Some(left)
            }
            Self::GivenRight { left_cell, .. } => {
                let left = left_cell.take()?;
                *self = Self::from_left(left);
                let Self::GivenLeft { left, .. } = self else {
                    unreachable!()
                };
                Some(left)
            }
        }
    }

    /// Returns a right value if it is available.
    /// If the right value is available, this method clears the left value.
    pub fn right_opt_mut(&mut self) -> Option<&mut R> {
        match self {
            Self::GivenLeft { right_cell, .. } => {
                let right = right_cell.take()?;
                *self = Self::from_right(right);
                let Self::GivenRight { right, .. } = self else {
                    unreachable!()
                };
                Some(right)
            }
            Self::GivenRight { right, left_cell } => {
                let _ = left_cell.take();
                Some(right)
            }
        }
    }

    /// Returns a left value if it is available.
    /// If the left value is not available, it uses the `Into` trait to convert the right value.
    pub fn left<'a>(&'a self) -> &'a L
    where
        &'a R: Into<L>,
    {
        self.left_with(<&R>::into)
    }

    /// Returns a right value if it is available.
    /// If the right value is not available, it uses the `Into` trait to convert the left value.
    pub fn right<'a>(&'a self) -> &'a R
    where
        &'a L: Into<R>,
    {
        self.right_with(|l| <&L>::into(l))
    }

    /// Returns a left value if it is available.
    /// If the left value is not available, it uses the `TryInto` trait to convert the right value.
    pub fn try_left<'a, E>(&'a self) -> Result<&'a L, E>
    where
        &'a R: TryInto<L, Error = E>,
    {
        self.try_left_with(|r| TryInto::try_into(r))
    }

    /// Returns a right value if it is available.
    /// If the right value is not available, it uses the `TryInto` trait to convert the left value.
    pub fn try_right<'a, E>(&'a self) -> Result<&'a R, E>
    where
        &'a L: TryInto<R, Error = E>,
    {
        self.try_right_with(|l| TryInto::try_into(l))
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
