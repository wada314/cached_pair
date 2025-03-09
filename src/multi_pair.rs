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

pub mod collections;

use crate::utils::{OnceCellExt, ResultExt};
use ::polonius_the_crab::prelude::*;
use ::std::alloc::Global;
use ::std::cell::OnceCell;
use ::std::convert::Infallible;
use ::std::fmt;
use ::std::fmt::Debug;
use ::std::iter;

/// A bidirectional mapping between a single left value and multiple right values.
///
/// *!!! this is super experimental and unstable API !!!*
///
/// `MultiPair` maintains a relationship between one left value and potentially multiple right values,
/// with automatic conversion between them using a provided converter.
/// The right `R` values should be distinguishable from the each other by the `Case` value.
/// Typically, `R` is an enum type, and the `Case` is a non-value enum type which has the same variants as `R`.
///
/// The converter should support bidirectional conversions between left and right values,
/// but it does not need right-to-right conversion.
///
/// # Type Parameters
///
/// * `L` - The type of the left value
/// * `R` - The type of the (scalar) right value
/// * `RS` - The collection type that stores multiple right values
/// * `C` - The converter type that implements [`MultiPairConverter`]
/// * `A` - The allocator type for the right values collection
///
/// # Caching Behavior
///
/// The structure caches conversions between left and right values to avoid redundant computations.
/// When a value is mutablly obtained from the structure, related cached values are automatically
/// invalidated (Even if the value is not modified actually).

#[derive(Clone)]
pub struct MultiPair<L, R, RS, C, A> {
    inner: MultiPairInner<L, R, RS>,
    converter: C,
    allocator: A,
}

pub trait MultiPairConverter<L, R, RS> {
    type ToLeftError;
    type ToRightError;
    type Case;

    /// Convert a sequence of right values to a left value.
    fn rights_to_left<'a>(
        &self,
        rights: impl IntoIterator<Item = &'a R>,
    ) -> Result<L, Self::ToLeftError>
    where
        R: 'a;
    fn left_to_right(&self, left: &L, case: &Self::Case) -> Result<R, Self::ToRightError>;
}

pub trait CellCollection {
    type Item;
    type Allocator;

    /// Creates a new collection with the given allocator.
    fn new_in(allocator: Self::Allocator) -> Self;

    /// Inserts an item into the collection and returns a reference to the item.
    ///
    /// The point is that this method is not `&mut self`, but `&self`.
    /// This is needed to implement the caching behavior.
    /// The returned reference does not lock the collection, so the collection
    /// can be modified even when the reference is alive, unless deleting the item.
    fn insert(&self, item: Self::Item) -> &Self::Item;

    /// Returns an iterator over the items in the collection.
    ///
    /// While the iterator is alive, the collection should be "locked"
    /// and not allow any modifications to the collection.
    /// On the other hand, the RESULT of the iterator does not lock the collection,
    /// it allows to modify the collection unless deleting the items.
    fn iter(&self) -> impl Iterator<Item = &Self::Item>;

    /// Searches for an item in the collection that satisfies the predicate,
    /// and if found, removes it from the collection and returns it.
    /// If no item is found, returns Err(self).
    fn extract_if<F>(self, f: F) -> Result<Self::Item, Self>
    where
        F: FnMut(&Self::Item) -> bool,
        Self: Sized;
}

pub trait Case<T: ?Sized> {
    fn matches(&self, target: &T) -> bool;
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

    pub fn allocator(&self) -> &A {
        &self.allocator
    }
}

impl<L, R, RS, C> MultiPair<L, R, RS, C, Global> {
    /// Creates a new `MultiPair` from a left value and a converter,
    /// using the global allocator.
    pub fn from_left_conv(left: L, converter: C) -> Self {
        Self::from_left_conv_in(left, converter, Global)
    }

    /// Creates a new `MultiPair` from a right value and a converter,
    /// using the global allocator.
    pub fn from_right_conv(right: R, converter: C) -> Self {
        Self::from_right_conv_in(right, converter, Global)
    }
}

impl<L, R, RS, C, A> MultiPair<L, R, RS, C, A>
where
    RS: CellCollection<Item = R, Allocator = A>,
    C: MultiPairConverter<L, R, RS, ToLeftError = Infallible>,
    C::Case: Case<R>,
    A: Clone,
{
    /// Gets a reference to the left value.
    /// This method is available when the left error type is `Infallible`.
    pub fn left(&self) -> &L {
        self.try_left().into_ok2()
    }

    /// Gets a mutable reference to the left value.
    /// This method is available when the left error type is `Infallible`.
    pub fn left_mut(&mut self) -> &mut L {
        self.try_left_mut().into_ok2()
    }
}

impl<L, R, RS, C, A> MultiPair<L, R, RS, C, A>
where
    RS: CellCollection<Item = R, Allocator = A>,
    C: MultiPairConverter<L, R, RS, ToLeftError = Infallible, ToRightError = Infallible>,
    C::Case: Case<R>,
    A: Clone,
{
    /// Gets a reference to the right value that matches the given case.
    /// This method is available when both error types are `Infallible`.
    pub fn right(&self, context: &C::Case) -> &R {
        let result: Result<&R, Infallible> = self.try_right(context);
        result.into_ok2()
    }

    /// Gets a mutable reference to the right value that matches the given case.
    /// This method is available when both error types are `Infallible`.
    pub fn right_mut(&mut self, context: &C::Case) -> &mut R {
        let result: Result<&mut R, Infallible> = self.try_right_mut(context);
        result.into_ok2()
    }
}

impl<L, R, RS, C, A> MultiPair<L, R, RS, C, A>
where
    RS: CellCollection<Item = R, Allocator = A>,
    C: MultiPairConverter<L, R, RS>,
    C::Case: Case<R>,
    A: Clone,
{
    pub fn try_left(&self) -> Result<&L, C::ToLeftError> {
        self.inner.try_left_with(|right, rights_opt| {
            let rights =
                std::iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
            self.converter.rights_to_left(rights)
        })
    }

    pub fn try_right<E>(&self, context: &C::Case) -> Result<&R, E>
    where
        E: From<C::ToLeftError> + From<C::ToRightError>,
    {
        self.inner.try_right_with(
            |right, rights_opt| {
                let rights =
                    std::iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
                Ok(self.converter.rights_to_left(rights)?)
            },
            |left| Ok(self.converter.left_to_right(left, context)?),
            |right| context.matches(right),
            || RS::new_in(self.allocator.clone()),
            |rights, item| rights.insert(item),
        )
    }

    pub fn try_left_mut(&mut self) -> Result<&mut L, C::ToLeftError> {
        let converter = &self.converter;
        self.inner.try_left_mut_with(|right, rights_opt| {
            let rights =
                std::iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
            converter.rights_to_left(rights)
        })
    }

    pub fn try_right_mut<E>(&mut self, context: &C::Case) -> Result<&mut R, E>
    where
        E: From<C::ToLeftError> + From<C::ToRightError>,
    {
        let converter = &self.converter;
        self.inner.try_right_mut_with(
            |right, rights_opt| {
                let rights =
                    std::iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
                converter.rights_to_left(rights).map_err(E::from)
            },
            |left| converter.left_to_right(left, context).map_err(E::from),
            |right| context.matches(right),
        )
    }
}

impl<L, R, RS, C, A> Debug for MultiPair<L, R, RS, C, A>
where
    L: Debug,
    R: Debug,
    RS: Debug,
    C: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MultiPair")
            .field("inner", &self.inner)
            .field("converter", &self.converter)
            .finish()
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
        matches: H,
        new_right_collection: I,
        insert_right: J,
    ) -> Result<&R, E>
    where
        F: FnOnce(&R, Option<&RS>) -> Result<L, E>,
        G: FnOnce(&L) -> Result<R, E>,
        H: Fn(&R) -> bool,
        I: FnOnce() -> RS,
        J: FnOnce(&RS, R) -> &R,
        RS: CellCollection<Item = R>,
    {
        let (left, rights_cell) = match self {
            Self::GivenRight {
                left_cell,
                right,
                rights_cell,
            } => {
                let mut all_rights =
                    iter::once(right).chain(rights_cell.get().into_iter().flat_map(|rs| rs.iter()));
                if let Some(right) = all_rights.find(|v| matches(v)) {
                    return Ok(right);
                } else {
                    let left =
                        left_cell.get_or_try_init2(|| rights_to_left(right, rights_cell.get()))?;
                    (left, rights_cell)
                }
            }
            Self::GivenLeft { left, rights_cell } => {
                if let Some(right) = rights_cell
                    .get()
                    .into_iter()
                    .flat_map(|rs| rs.iter())
                    .find(|v| matches(v))
                {
                    return Ok(right);
                } else {
                    (left, rights_cell)
                }
            }
        };
        let new_right = left_to_right(left)?;
        let rights = rights_cell.get_or_init(new_right_collection);
        Ok(insert_right(rights, new_right))
    }

    fn try_left_mut_with<G, E>(&mut self, rights_to_left: G) -> Result<&mut L, E>
    where
        G: FnOnce(&R, Option<&RS>) -> Result<L, E>,
    {
        match self {
            Self::GivenLeft { left, rights_cell } => {
                // Clear any cached rights as they become stale
                rights_cell.take();
                Ok(left)
            }
            Self::GivenRight {
                left_cell,
                right,
                rights_cell,
            } => {
                // Try to take existing left value or generate a new one
                let left_val = if let Some(left) = left_cell.take() {
                    left
                } else {
                    rights_to_left(right, rights_cell.get())?
                };

                // Transition to GivenLeft state
                *self = Self::GivenLeft {
                    left: left_val,
                    rights_cell: OnceCell::new(),
                };

                match self {
                    Self::GivenLeft { left, .. } => Ok(left),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn try_right_mut_with<F, G, H, E>(
        &mut self,
        rights_to_left: F,
        left_to_right: G,
        matches: H,
    ) -> Result<&mut R, E>
    where
        F: FnOnce(&R, Option<&RS>) -> Result<L, E>,
        G: FnOnce(&L) -> Result<R, E>,
        H: Fn(&R) -> bool,
        RS: CellCollection<Item = R>,
    {
        let mut this = self;

        polonius!(|this| -> Result<&'polonius mut R, E> {
            // Check if the matching value exists in the right field
            if let Self::GivenRight {
                right,
                left_cell,
                rights_cell,
            } = this
            {
                if matches(right) {
                    left_cell.take();
                    rights_cell.take();
                    polonius_return!(Ok(right));
                }
            }
        });

        polonius!(|this| -> Result<&'polonius mut R, E> {
            // Next check if the value exists in the rights collection
            match this {
                Self::GivenRight { rights_cell, .. } | Self::GivenLeft { rights_cell, .. } => {
                    if let Some(rights) = rights_cell.take() {
                        match rights.extract_if(|r| matches(r)) {
                            Ok(right) => {
                                polonius_return!(this.transition_to_right_mut(right));
                            }
                            Err(rights) => {
                                // We are sure the rights_cell is empty here because we took it above
                                let _ = rights_cell.set(rights);
                            }
                        }
                    }
                }
            }
        });

        // The value does not exist so we need to create it.
        // To create it, we need to obtain the left value. If it does not exist, make it.
        let left = match this {
            Self::GivenLeft { left, .. } => left,
            Self::GivenRight {
                left_cell,
                right,
                rights_cell,
            } => left_cell.get_or_try_init2(|| rights_to_left(right, rights_cell.get()))?,
        };

        // Now we can create the right value.
        let right = left_to_right(&left)?;

        return this.transition_to_right_mut(right);
    }

    /// Set the `MultiPairInner` to the state which is only having a right value,
    /// and return the mutable reference to the right value.
    fn transition_to_right_mut<E>(&mut self, right: R) -> Result<&mut R, E> {
        *self = Self::from_right(right);
        Ok(match self {
            Self::GivenRight { right, .. } => right,
            _ => unreachable!(),
        })
    }
}
