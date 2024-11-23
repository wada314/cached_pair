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

//! An extended version of the default `Pair`.
//! This data structure supports star-like shaped 1:N relation:
//! Supports values `t`, `u1`, `u2`, ... `un` where `t` is bidirectionary
//! convertible to each `u_i`s, but each `u_i`s are not convertible to each other.
//!
//! In this data structure, we call `t` the "center" and `u_i`s the "spokes".

use crate::pair::Pair;
use ::once_list2::OnceList;
use ::std::convert::Infallible;
use ::std::ops::{Deref, DerefMut};

pub struct Star<T, U>(Pair<Center<T>, Spokes<U>>);
struct Center<T>(T);
struct Spokes<T>(T, OnceList<T>);

impl<T, U> Star<T, U> {
    pub fn from_center(center: T) -> Self {
        Self(Pair::from_left(Center(center)))
    }
    pub fn from_spoke(spoke: U) -> Self {
        Self(Pair::from_right(Spokes::new(spoke)))
    }
    /// Constructs from multiple spoke items.
    /// Note this method does not allow an empty spoke list,
    /// so you need to provide at least one spoke.
    pub fn from_spokes(first: U, rest: impl Iterator<Item = U>) -> Self {
        Self(Pair::from_right(Spokes::from_spokes(first, rest)))
    }
}
impl<T> Center<T> {
    fn new(center: T) -> Self {
        Self(center)
    }
}
impl<T> Spokes<T> {
    fn new(spoke: T) -> Self {
        Self(spoke, OnceList::new())
    }
    fn from_spokes(first: T, rest: impl Iterator<Item = T>) -> Self {
        Self(first, rest.collect())
    }
}

impl<T, U> Star<T, U> {
    pub fn center<F: FnOnce(&U) -> T>(&self, f: F) -> &T {
        self.0.left(|center| &center.0)
    }

    pub fn try_center<F: FnOnce(&U) -> Result<T, E>, E>(&self, f: F) -> Result<&T, E> {
        self.0.try_left(|spokes| f(&spokes.0))
    }

    pub fn spoke<F: FnOnce(&T) -> U, P: Fn(&U) -> bool>(&self, f: F, predicate: P) -> &U {
        // No! Not optimized!
        self.0
            .right(|center| Spokes::new(f(&center.0)).find(predicate).unwrap())
    }
}

impl<T> Deref for Center<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T> DerefMut for Center<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, U: TryRefInto<T>> TryFromRef<Spokes<U>> for Center<T> {
    type Error = U::Error;
    fn try_from_ref(spokes: &Spokes<U>) -> Result<Self, Self::Error> {
        Ok(Center::new(U::try_ref_into(&spokes.0)?))
    }
}
impl<T: TryRefInto<U>, U> TryFromRef<Center<T>> for Spokes<U> {
    type Error = T::Error;
    fn try_from_ref(center: &Center<T>) -> Result<Self, Self::Error> {
        Ok(Spokes::new(T::try_ref_into(center)?))
    }
}
