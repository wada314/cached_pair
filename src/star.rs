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
//! In this data structure, we call `t` the "hub" and `u_i`s the "spokes".

use crate::pair::Pair;
use ::once_list2::OnceList;
use ::std::convert::Infallible;
use ::std::iter;
use ::std::ops::{Deref, DerefMut};

pub struct Star<H, S>(Pair<H, Spokes<S>>);
struct Spokes<T>(T, OnceList<T>);

impl<H, S> Star<H, S> {
    pub fn from_hub(hub: H) -> Self {
        Self(Pair::from_left(hub))
    }
    pub fn from_spoke(spoke: S) -> Self {
        Self(Pair::from_right(Spokes::new(spoke)))
    }
    /// Constructs from multiple spoke items.
    /// Note this method does not allow an empty spoke list,
    /// so you need to provide at least one spoke.
    pub fn from_spokes(first: S, rest: impl Iterator<Item = S>) -> Self {
        Self(Pair::from_right(Spokes::from_spokes(first, rest)))
    }
}

impl<T> Spokes<T> {
    fn new(spoke: T) -> Self {
        Self(spoke, OnceList::new())
    }
    fn from_spokes(first: T, rest: impl Iterator<Item = T>) -> Self {
        Self(first, rest.collect())
    }
    fn iter(&self) -> impl Iterator<Item = &T> {
        iter::once(&self.0).chain(self.1.iter())
    }
    pub fn select_spoke<L: SpokeSelector<T>>(&self, mut sel: L) -> &T {
        sel.select(&self.0, self.1.iter())
    }
}

pub trait SpokeSelector<T> {
    fn select<'a>(&mut self, first: &'a T, rest: impl Iterator<Item = &'a T>) -> &'a T;
}
pub use spoke_selector::FirstSpoke;
pub mod spoke_selector {
    pub struct FirstSpoke;
    impl<T> super::SpokeSelector<T> for FirstSpoke {
        fn select<'a>(&mut self, first: &'a T, _: impl Iterator<Item = &'a T>) -> &'a T {
            first
        }
    }
    pub fn from_reduce_fn<T, F>(f: F) -> impl super::SpokeSelector<T>
    where
        F: for<'a> FnMut(&'a T, &'a T) -> &'a T,
    {
        struct ReduceFn<F>(F);
        impl<T, F> super::SpokeSelector<T> for ReduceFn<F>
        where
            F: for<'a> FnMut(&'a T, &'a T) -> &'a T,
        {
            fn select<'a>(&mut self, first: &'a T, rest: impl Iterator<Item = &'a T>) -> &'a T {
                rest.fold(first, &mut self.0)
            }
        }
        ReduceFn(f)
    }
}

impl<H, S> Star<H, S>
where
    for<'a> &'a S: Into<H>,
{
    pub fn hub(&self) -> &H {
        self.hub_from_selected(self::spoke_selector::FirstSpoke)
    }

    pub fn hub_from_selected<L: SpokeSelector<S>>(&self, mut sel: L) -> &H {
        self.0.left(|spokes| {
            let spoke = sel.select(&spokes.0, spokes.1.iter());
            <&S>::into(spoke)
        })
    }

    pub fn spoke<L, T>(&self, sel: L) -> &T
    where
        L: SpokeSelector<S>,
        T: Into<S>,
        for<'a> &'a H: Into<T>,
        for<'a> &'a S: TryInto<&'a T>,
    {
        if let Some(spokes) = self.0.right_opt() {
            for spoke in spokes.iter() {
                if let Ok(typed_spoke) = spoke.try_into() {
                    // Found a matching spoke.
                    return typed_spoke;
                }
            }
            let hub = self.hub_from_selected(sel);
            let new_spoke = spokes.1.push(<T>::into(<&H>::into(hub)));
            // Safe because we are sure the new spoke is a `T` here... REALLY?
            // Needs:
            // - If a value `s` is generated from <T>::into(), then TryInto<&T>::try_into(s).is_ok()
            // This is not guaranteed by the current trait system.
            unsafe { new_spoke.try_into().unwrap_unchecked() }
        } else {
            let new_spokes = self.0.right(|hub| Spokes::new(<T>::into(<&H>::into(hub))));
            let new_spoke = (&new_spokes.0);
            // Same safetyness issue as above.
            unsafe { new_spoke.try_into().unwrap_unchecked() }
        }
    }
}

impl<H, S> Star<H, S> {}
