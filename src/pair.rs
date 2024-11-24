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

pub enum Pair<L, R> {
    GivenLeft { left: L, right_cell: OnceCell<R> },
    GivenRight { left_cell: OnceCell<L>, right: R },
}

impl<L, R> Pair<L, R> {
    pub fn from_left(left: L) -> Self {
        Self::GivenLeft {
            left,
            right_cell: OnceCell::new(),
        }
    }
    pub fn from_right(right: R) -> Self {
        Self::GivenRight {
            left_cell: OnceCell::new(),
            right,
        }
    }

    pub fn left<F: FnOnce(&R) -> L>(&self, f: F) -> &L {
        match self {
            Self::GivenLeft { left, .. } => left,
            Self::GivenRight { left_cell, right } => left_cell.get_or_init(|| f(right)),
        }
    }

    pub fn right<F: FnOnce(&L) -> R>(&self, f: F) -> &R {
        match self {
            Self::GivenLeft { left, right_cell } => right_cell.get_or_init(|| f(left)),
            Self::GivenRight { right, .. } => right,
        }
    }

    pub fn try_left<F: FnOnce(&R) -> Result<L, E>, E>(&self, f: F) -> Result<&L, E> {
        match self {
            Self::GivenLeft { left, .. } => Ok(left),
            Self::GivenRight { left_cell, right } => left_cell.get_or_try_init2(|| f(right)),
        }
    }

    pub fn try_right<F: FnOnce(&L) -> Result<R, E>, E>(&self, f: F) -> Result<&R, E> {
        match self {
            Self::GivenLeft { left, right_cell } => right_cell.get_or_try_init2(|| f(left)),
            Self::GivenRight { right, .. } => Ok(right),
        }
    }

    pub fn left_mut<F: FnOnce(&R) -> L>(&mut self, f: F) -> &mut L {
        self.try_left_mut(|r| -> Result<_, Infallible> { Ok(f(r)) })
            .unwrap()
    }

    pub fn right_mut<F: FnOnce(&L) -> R>(&mut self, f: F) -> &mut R {
        self.try_right_mut(|l| -> Result<_, Infallible> { Ok(f(l)) })
            .unwrap()
    }

    pub fn try_left_mut<F: FnOnce(&R) -> Result<L, E>, E>(&mut self, f: F) -> Result<&mut L, E> {
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

    pub fn try_right_mut<F: FnOnce(&L) -> Result<R, E>, E>(&mut self, f: F) -> Result<&mut R, E> {
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

    pub fn left_opt(&self) -> Option<&L> {
        match self {
            Self::GivenLeft { left, .. } => Some(left),
            Self::GivenRight { left_cell, .. } => left_cell.get(),
        }
    }

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

// An extension for `Result<T, Infallible>`.
// This is a workaround for the lack (unstableness) of `into_ok` method in `Result`.
trait ResultExt<T> {
    fn into_ok2(self) -> T;
}
impl<T> ResultExt<T> for Result<T, Infallible> {
    fn into_ok2(self) -> T {
        match self {
            Ok(v) => v,
            Err(_) => unreachable!(),
        }
    }
}
