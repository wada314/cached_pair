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

use ::std::cell::OnceCell;
use ::std::convert::Infallible;

pub enum Cpcp<L, R> {
    GivenT { left: L, right_cell: OnceCell<R> },
    GivenU { left_cell: OnceCell<L>, right: R },
}

impl<L, R> Cpcp<L, R> {
    pub fn from_left(left: L) -> Self {
        Self::GivenT {
            left,
            right_cell: OnceCell::new(),
        }
    }
    pub fn from_right(right: R) -> Self {
        Self::GivenU {
            left_cell: OnceCell::new(),
            right,
        }
    }
}

impl<L: TryRefInto<R>, R> Cpcp<L, R> {
    pub fn try_left(&self) -> Result<&R, L::Error> {
        match self {
            Cpcp::GivenT {
                ref left,
                right_cell,
            } => right_cell.get_or_try_init2(|| L::try_ref_into(left)),
            Cpcp::GivenU {
                left_cell: _,
                ref right,
            } => Ok(right),
        }
    }
}

pub trait FromRef<T> {
    fn from_ref(t: &T) -> Self;
}
pub trait RefInto<T> {
    fn ref_into(&self) -> T;
}
impl<T, U> RefInto<U> for T
where
    U: FromRef<T>,
{
    fn ref_into(&self) -> U {
        U::from_ref(self)
    }
}

pub trait TryFromRef<T>: Sized {
    type Error;
    fn try_from_ref(t: &T) -> Result<Self, Self::Error>;
}
pub trait TryRefInto<T> {
    type Error;
    fn try_ref_into(&self) -> Result<T, Self::Error>;
}
impl<T, U> TryFromRef<U> for T
where
    U: RefInto<T>,
{
    type Error = Infallible;
    fn try_from_ref(u: &U) -> Result<T, Self::Error> {
        Ok(U::ref_into(u))
    }
}
impl<T, U> TryRefInto<U> for T
where
    U: TryFromRef<T>,
{
    type Error = U::Error;
    fn try_ref_into(&self) -> Result<U, Self::Error> {
        U::try_from_ref(self)
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
