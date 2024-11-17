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

use crate::TryRefInto;
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
}

impl<L, R: TryRefInto<L>> Pair<L, R> {
    pub fn try_left(&self) -> Result<&L, R::Error> {
        match self {
            Pair::GivenLeft {
                left,
                right_cell: _,
            } => Ok(left),
            Pair::GivenRight {
                left_cell,
                ref right,
            } => left_cell.get_or_try_init2(|| R::try_ref_into(right)),
        }
    }

    pub fn try_left_mut(&mut self) -> Result<&mut L, R::Error> {
        match self {
            Pair::GivenLeft {
                left,
                right_cell: _,
            } => Ok(left),
            Pair::GivenRight {
                left_cell,
                ref mut right,
            } => {
                let left = if let Some(left) = left_cell.take() {
                    left
                } else {
                    R::try_ref_into(right)?
                };
                *self = Pair::from_left(left);
                let Pair::GivenLeft {
                    left: ref mut left_mut,
                    ..
                } = self
                else {
                    unreachable!();
                };
                Ok(left_mut)
            }
        }
    }
}

impl<L: TryRefInto<R>, R> Pair<L, R> {
    pub fn try_right(&self) -> Result<&R, L::Error> {
        match self {
            Pair::GivenLeft {
                ref left,
                right_cell,
            } => right_cell.get_or_try_init2(|| L::try_ref_into(left)),
            Pair::GivenRight {
                left_cell: _,
                ref right,
            } => Ok(right),
        }
    }

    pub fn try_right_mut(&mut self) -> Result<&mut R, L::Error> {
        match self {
            Pair::GivenLeft {
                ref left,
                right_cell,
            } => {
                let right = if let Some(right) = right_cell.take() {
                    right
                } else {
                    L::try_ref_into(left)?
                };
                *self = Pair::from_right(right);
                let Pair::GivenRight {
                    right: ref mut right_mut,
                    ..
                } = self
                else {
                    unreachable!();
                };
                Ok(right_mut)
            }
            Pair::GivenRight {
                left_cell,
                ref mut right,
            } => {
                let _ = left_cell.take();
                Ok(right)
            }
        }
    }
}

impl<L, R: TryRefInto<L, Error = Infallible>> Pair<L, R> {
    pub fn left(&self) -> &L {
        self.try_left().into_ok2()
    }

    pub fn left_mut(&mut self) -> &mut L {
        self.try_left_mut().into_ok2()
    }
}

impl<L: TryRefInto<R, Error = Infallible>, R> Pair<L, R> {
    pub fn right(&self) -> &R {
        self.try_right().into_ok2()
    }

    pub fn right_mut(&mut self) -> &mut R {
        self.try_right_mut().into_ok2()
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
