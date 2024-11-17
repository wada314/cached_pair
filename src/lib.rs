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

mod pair;
#[cfg(feature = "star")]
mod star;
mod type_map;

pub use pair::Pair;
pub use star::Star;

use ::std::convert::Infallible;

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
