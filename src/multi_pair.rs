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

use crate::utils::OnceCellExt;
use ::std::{cell::OnceCell, iter};

pub struct MultiPair<L, R, RS, C, A> {
    inner: MultiPairInner<L, R, RS>,
    converter: C,
    allocator: A,
}

pub trait MultiPairConverter<L, R, RS> {
    type ToLeftError;
    type ToRightError;
    type Case;
    fn rights_to_left(&self, right: &R, rights_opt: Option<&RS>) -> Result<L, Self::ToLeftError>;
    fn left_to_right(&self, left: &L, context: &Self::Case) -> Result<R, Self::ToRightError>;
}

pub trait RightCollection {
    type Item;
    type Allocator;
    fn new_in(allocator: Self::Allocator) -> Self;
    fn insert(&self, item: Self::Item) -> &Self::Item;
    fn iter(&self) -> impl Iterator<Item = &Self::Item>;
}

pub trait Case {
    type Target: ?Sized;
    fn matches(&self, target: &Self::Target) -> bool;
}

impl<L, R, RS, C, A> MultiPair<L, R, RS, C, A> {
    pub fn from_left_conv_in(left: L, converter: C, allocator: A) -> Self {
        Self {
            inner: MultiPairInner::from_left(left),
            converter,
            allocator,
        }
    }

    pub fn from_right_conv_in(right: R, converter: C, allocator: A) -> Self {
        Self {
            inner: MultiPairInner::from_right(right),
            converter,
            allocator,
        }
    }
}

impl<L, R, RS, C, A> MultiPair<L, R, RS, C, A>
where
    RS: RightCollection<Item = R, Allocator = A>,
    C: MultiPairConverter<L, R, RS>,
    C::Case: Case<Target = R>,
    A: Clone,
{
    pub fn try_left(&self) -> Result<&L, C::ToLeftError> {
        self.inner
            .try_left_with(|right, rights_opt| self.converter.rights_to_left(right, rights_opt))
    }

    pub fn try_right<E>(&self, context: &C::Case) -> Result<&R, E>
    where
        E: From<C::ToLeftError> + From<C::ToRightError>,
    {
        self.inner.try_right_with(
            |right, rights_opt| Ok(self.converter.rights_to_left(right, rights_opt)?),
            |left| Ok(self.converter.left_to_right(left, context)?),
            |right, rights_opt| {
                iter::once(right)
                    .chain(rights_opt.into_iter().flat_map(|rs| rs.iter()))
                    .find(|v| context.matches(*v))
            },
            || RS::new_in(self.allocator.clone()),
            |rights, item| rights.insert(item),
        )
    }
}

#[derive(Debug, Clone)]
enum MultiPairInner<L, R, RS> {
    GivenLeft {
        left: L,
        rights_cell: OnceCell<RS>,
    },
    GivenRight {
        left_cell: OnceCell<L>,
        right: R,
        rights_cell: OnceCell<RS>,
    },
}

impl<L, R, RS> MultiPairInner<L, R, RS> {
    fn from_left(left: L) -> Self {
        Self::GivenLeft {
            left,
            rights_cell: OnceCell::new(),
        }
    }
    fn from_right(right: R) -> Self {
        Self::GivenRight {
            left_cell: OnceCell::new(),
            right,
            rights_cell: OnceCell::new(),
        }
    }
}

impl<L, R, RS> MultiPairInner<L, R, RS> {
    fn try_left_with<F: FnOnce(&R, Option<&RS>) -> Result<L, E>, E>(
        &self,
        rights_to_left: F,
    ) -> Result<&L, E> {
        match self {
            Self::GivenLeft { left, .. } => Ok(&left),
            Self::GivenRight {
                left_cell,
                right,
                rights_cell,
            } => left_cell.get_or_try_init2(|| rights_to_left(right, rights_cell.get())),
        }
    }

    // which methods belong to the right collection, and which belong to the converter?
    fn try_right_with<F, G, H, I, J, E>(
        &self,
        rights_to_left: F,
        left_to_right: G,
        search_rights: H,
        new_right_collection: I,
        insert_right: J,
    ) -> Result<&R, E>
    where
        F: FnOnce(&R, Option<&RS>) -> Result<L, E>,
        G: FnOnce(&L) -> Result<R, E>,
        H: for<'a> FnOnce(&'a R, Option<&'a RS>) -> Option<&'a R>,
        I: FnOnce() -> RS,
        J: FnOnce(&RS, R) -> &R,
    {
        let (left, rights_cell) = match self {
            Self::GivenRight {
                left_cell,
                right,
                rights_cell,
            } => {
                if let Some(right) = search_rights(right, rights_cell.get()) {
                    return Ok(right);
                } else {
                    let left =
                        left_cell.get_or_try_init2(|| rights_to_left(right, rights_cell.get()))?;
                    (left, rights_cell)
                }
            }
            Self::GivenLeft { left, rights_cell } => (left, rights_cell),
        };
        let new_right = left_to_right(left)?;
        let rights = rights_cell.get_or_init(new_right_collection);
        Ok(insert_right(rights, new_right))
    }
}
