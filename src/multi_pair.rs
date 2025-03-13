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
use ::derive_more::Debug;
use ::polonius_the_crab::prelude::*;
use ::std::alloc::Global;
use ::std::cell::OnceCell;
use ::std::convert::Infallible;
use ::std::iter;

/// A bidirectional mapping between a left value and right values.
///
/// *!!! this is super experimental and unstable API !!!*
///
/// `MultiPair` maintains a relationship between one left value and right values,
/// with automatic conversion between them using a provided converter.
/// The right values are distinguishable by a `Case` value.
///
/// # Type Parameters
///
/// * `L` - The type of the left value
/// * `R` - The type of the right value
/// * `RS` - The collection type for right values
/// * `C` - The converter type that implements [`MultiPairConverter`]
/// * `A` - The allocator type
#[derive(Clone, Debug)]
pub struct MultiPair<L, R, RS, C, A> {
    inner: MultiPairInner<L, R, RS>,
    converter: C,
    #[debug(skip)]
    allocator: A,
}

/// Converter trait for bidirectional conversion between left and right values.
///
/// This trait defines the conversion methods needed by `MultiPair` to maintain
/// the relationship between left and right values.
pub trait MultiPairConverter<L, R, RS> {
    /// Error type returned when conversion from right values to a left value fails
    type ToLeftError;
    /// Error type returned when conversion from a left value to a right value fails
    type ToRightError;
    /// Type used to distinguish between different right values
    type Case;

    /// Convert right values to a left value.
    ///
    /// This method is called when a left value needs to be generated from
    /// the available right values.
    fn rights_to_left<'a>(
        &self,
        rights: impl IntoIterator<Item = &'a R>,
    ) -> Result<L, Self::ToLeftError>
    where
        R: 'a;

    /// Create a new right value from a left value.
    ///
    /// This method is called when a right value needs to be generated for
    /// a specific case from the left value.
    fn left_to_right(&self, left: &L, case: &Self::Case) -> Result<R, Self::ToRightError>;
}

/// Collection trait for storing right values with interior mutability.
///
/// This trait defines the operations needed by `MultiPair` to store and
/// manage right values in a thread-safe way.
pub trait CellCollection {
    /// The type of items stored in the collection
    type Item;
    /// The allocator type used by the collection
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

/// Trait for matching right values against a case.
///
/// This trait is used to find right values that match a specific case
/// when searching through the available right values.
pub trait Case<T: ?Sized> {
    /// Returns true if the target value matches this case.
    fn matches(&self, target: &T) -> bool;
}

impl<L, R, RS, C, A> MultiPair<L, R, RS, C, A> {
    /// Creates a new `MultiPair` from a left value and a converter.
    ///
    /// The pair will initially contain only the left value. Right values
    /// will be generated as needed using the converter.
    pub fn from_left_conv_in(left: L, converter: C, allocator: A) -> Self {
        Self {
            inner: MultiPairInner::from_left(left),
            converter,
            allocator,
        }
    }

    /// Creates a new `MultiPair` from a right value and a converter.
    ///
    /// The pair will initially contain only the right value. The left value
    /// and other right values will be generated as needed using the converter.
    pub fn from_right_conv_in(right: R, converter: C, allocator: A) -> Self {
        Self {
            inner: MultiPairInner::from_right(right),
            converter,
            allocator,
        }
    }

    /// Returns a reference to the allocator used by this pair.
    pub fn allocator(&self) -> &A {
        &self.allocator
    }
}

impl<L, R, RS, C> MultiPair<L, R, RS, C, Global> {
    /// Creates a new `MultiPair` from a left value and a converter,
    /// using the global allocator.
    ///
    /// This is a convenience method that uses the global allocator instead
    /// of requiring an explicit allocator.
    pub fn from_left_conv(left: L, converter: C) -> Self {
        Self::from_left_conv_in(left, converter, Global)
    }

    /// Creates a new `MultiPair` from a right value and a converter,
    /// using the global allocator.
    ///
    /// This is a convenience method that uses the global allocator instead
    /// of requiring an explicit allocator.
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
    /// This method is available when the right-to-left conversion cannot fail.
    pub fn left(&self) -> &L {
        self.try_left().into_ok2()
    }

    /// Gets a mutable reference to the left value.
    /// This method is available when the right-to-left conversion cannot fail.
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
    /// Gets a reference to a right value that matches the given case.
    /// This method is available when both conversion directions cannot fail.
    pub fn right(&self, context: &C::Case) -> &R {
        let result: Result<&R, Infallible> = self.try_right(context);
        result.into_ok2()
    }

    /// Gets a mutable reference to a right value that matches the given case.
    /// This method is available when both conversion directions cannot fail.
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
    /// Attempts to get a reference to the left value.
    ///
    /// If the left value is not present, converts from the available right values.
    /// This operation does not invalidate any cached values.
    pub fn try_left(&self) -> Result<&L, C::ToLeftError> {
        self.inner.try_left_with(|right, rights_opt| {
            let rights =
                std::iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
            self.converter.rights_to_left(rights)
        })
    }

    /// Attempts to get a reference to a right value that matches the given case.
    ///
    /// Searches through the available right values, and if no matching value exists,
    /// creates a new one from the left value.
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

    /// Attempts to get a mutable reference to the left value.
    ///
    /// If the left value is not present, converts from the available right values.
    /// This operation invalidates any cached right values.
    pub fn try_left_mut(&mut self) -> Result<&mut L, C::ToLeftError> {
        let converter = &self.converter;
        self.inner.try_left_mut_with(|right, rights_opt| {
            let rights =
                std::iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
            converter.rights_to_left(rights)
        })
    }

    /// Attempts to get a mutable reference to a right value that matches the given case.
    ///
    /// Searches through the available right values, and if no matching value exists,
    /// creates a new one from the left value.
    /// This operation may invalidate other cached values.
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

    /// Consumes the pair and converts it into a left value.
    ///
    /// If the left value is not present, converts from the available right values.
    pub fn try_into_left(self) -> Result<L, C::ToLeftError> {
        let converter = &self.converter;
        self.inner.try_into_left_with(|right, rights_opt| {
            let rights = iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
            converter.rights_to_left(rights)
        })
    }

    /// Consumes the pair and converts it into a right value that matches the given case.
    ///
    /// Searches through the available right values, and if no matching value exists,
    /// creates a new one from the left value.
    pub fn try_into_right<E>(self, context: &C::Case) -> Result<R, E>
    where
        E: From<C::ToLeftError> + From<C::ToRightError>,
    {
        let converter = &self.converter;
        self.inner.try_into_right_with(
            |right, rights_opt| {
                let rights =
                    iter::once(right).chain(rights_opt.into_iter().flat_map(|rs| rs.iter()));
                converter.rights_to_left(rights).map_err(E::from)
            },
            |left| converter.left_to_right(left, context).map_err(E::from),
            |right| context.matches(right),
        )
    }

    /// Consumes the pair and converts it into a left value.
    ///
    /// This method is available when the right-to-left conversion cannot fail.
    pub fn into_left(self) -> L
    where
        Infallible: From<C::ToLeftError>,
    {
        self.try_into_left().map_err(Infallible::from).into_ok2()
    }

    /// Consumes the pair and converts it into a right value that matches the given case.
    ///
    /// This method is available when both conversion directions cannot fail.
    pub fn into_right(self, context: &C::Case) -> R
    where
        Infallible: From<C::ToLeftError> + From<C::ToRightError>,
    {
        self.try_into_right::<Infallible>(context).into_ok2()
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
    /// Attempts to get a reference to the left value.
    /// If the left value is not present, converts from the available right values
    /// using the provided function.
    ///
    /// # Arguments
    /// * `rights_to_left` - A function that converts from right values to left value
    ///
    /// # Returns
    /// * `Ok(&L)` - A reference to the left value
    /// * `Err(E)` - If the conversion fails
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

    /// Attempts to get a reference to a right value that matches the given predicate.
    /// Searches through the available right values, and if no matching value exists,
    /// creates a new one from the left value.
    ///
    /// # Arguments
    /// * `rights_to_left` - Function to convert from right values to left
    /// * `left_to_right` - Function to create a new right value from left
    /// * `matches` - Predicate function to find matching right value
    /// * `new_right_collection` - Function to create a new collection
    /// * `insert_right` - Function to insert a right value into the collection
    ///
    /// # Returns
    /// * `Ok(&R)` - Reference to the matching or newly created right value
    /// * `Err(E)` - If any conversion fails
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

    /// Attempts to get a mutable reference to the left value.
    /// This operation invalidates any cached right values.
    /// If no left value is present, converts from the available right values.
    ///
    /// # Arguments
    /// * `rights_to_left` - Function to convert from right values to left if necessary
    ///
    /// # Returns
    /// * `Ok(&mut L)` - Mutable reference to the left value
    /// * `Err(E)` - If conversion fails
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

    /// Attempts to get a mutable reference to a right value that matches the predicate.
    /// Searches through the available right values, and if no matching value exists,
    /// creates a new one from the left value.
    /// This operation may invalidate other cached values.
    ///
    /// # Arguments
    /// * `rights_to_left` - Function to convert from right values to left
    /// * `left_to_right` - Function to create a new right value from left
    /// * `matches` - Predicate function to find matching right value
    ///
    /// # Returns
    /// * `Ok(&mut R)` - Mutable reference to the matching or newly created right value
    /// * `Err(E)` - If any conversion fails
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

    /// Updates the storage to contain only the specified right value,
    /// clearing all other stored values.
    ///
    /// # Arguments
    /// * `right` - The right value to store
    ///
    /// # Returns
    /// * `Ok(&mut R)` - Mutable reference to the stored right value
    /// * `Err(E)` - This is only for consistency with the type system, this function never fails
    fn transition_to_right_mut<E>(&mut self, right: R) -> Result<&mut R, E> {
        *self = Self::from_right(right);
        Ok(match self {
            Self::GivenRight { right, .. } => right,
            _ => unreachable!(),
        })
    }

    /// Consumes the pair and turn it into a left value.
    fn try_into_left_with<F: FnOnce(&R, Option<&RS>) -> Result<L, E>, E>(
        self,
        rights_to_left: F,
    ) -> Result<L, E> {
        match self {
            Self::GivenLeft { left, .. } => Ok(left),
            Self::GivenRight {
                mut left_cell,
                right,
                rights_cell,
            } => left_cell
                .take()
                .map_or_else(|| rights_to_left(&right, rights_cell.get()), Ok),
        }
    }

    /// Consumes the pair and turn it into a right value.
    fn try_into_right_with<F, G, H, E>(
        self,
        rights_to_left: F,
        left_to_right: G,
        matches: H,
    ) -> Result<R, E>
    where
        F: FnOnce(&R, Option<&RS>) -> Result<L, E>,
        G: FnOnce(&L) -> Result<R, E>,
        H: Fn(&R) -> bool,
        RS: CellCollection<Item = R>,
    {
        match self {
            Self::GivenRight {
                right, rights_cell, ..
            } => {
                // First check if the main right value matches
                if matches(&right) {
                    return Ok(right);
                }
                // Then check in the rights collection
                if let Some(rights) = rights_cell.into_inner() {
                    if let Ok(matching_right) = rights.extract_if(|r| matches(r)) {
                        return Ok(matching_right);
                    }
                }
                // If no matching right value found, create a new one from left
                let left = rights_to_left(&right, None)?;
                left_to_right(&left)
            }
            Self::GivenLeft { left, .. } => left_to_right(&left),
        }
    }
}
