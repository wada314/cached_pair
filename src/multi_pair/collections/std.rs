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

//! Example implementations of `CellCollection` using standard library types.

use ::std::alloc::Allocator;
use ::std::cell::{Ref, RefCell};

use super::CellCollection;

/// A collection that stores items in a Vec with boxed values.
/// This type provides interior mutability while maintaining reference safety.
pub struct VecCollection<T, A: Allocator>(RefCell<Vec<Box<T, A>, A>>);

impl<T, A: Allocator + Clone> CellCollection for VecCollection<T, A> {
    type Item = T;
    type Allocator = A;

    fn new_in(allocator: Self::Allocator) -> Self {
        Self(RefCell::new(Vec::new_in(allocator)))
    }

    fn insert(&self, item: Self::Item) -> &Self::Item {
        let mut vec = self.0.borrow_mut();
        let boxed = Box::new_in(item, vec.allocator().clone());
        vec.push(boxed);
        // Safety: The returned reference is valid because:
        // 1. The collection interface does not allow removing items
        // 2. The Box remains in the Vec until the collection is dropped
        // 3. The reference points to heap memory owned by the Box in Vec
        // 4. The lifetime is tied to self (the collection), not the temporary borrow
        let r = vec.last().unwrap().as_ref();
        unsafe { &*(r as *const T) }
    }

    fn iter(&self) -> impl Iterator<Item = &Self::Item> {
        struct RefIter<'a, T, A: Allocator> {
            _ref: Ref<'a, Vec<Box<T, A>, A>>,
            pos: usize,
        }

        impl<'a, T, A: Allocator> Iterator for RefIter<'a, T, A> {
            type Item = &'a T;

            fn next(&mut self) -> Option<Self::Item> {
                if self.pos >= self._ref.len() {
                    None
                } else {
                    // Safety: The returned reference is valid because:
                    // 1. The collection interface does not allow removing items
                    // 2. The collection itself owns all items until it is dropped
                    // 3. RefCell ensures no mutable access during iteration
                    // 4. The lifetime of the returned reference is tied to the collection (self),
                    //    not to the temporary Ref or iterator
                    let r = self._ref[self.pos].as_ref();
                    let item = unsafe { &*(r as *const T) };
                    self.pos += 1;
                    Some(item)
                }
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                let remaining = self._ref.len() - self.pos;
                (remaining, Some(remaining))
            }
        }

        RefIter {
            _ref: self.0.borrow(),
            pos: 0,
        }
    }

    fn extract_if<F>(self, mut f: F) -> Option<Self::Item>
    where
        F: FnMut(&Self::Item) -> bool,
    {
        // We can use into_inner() because we have ownership of self
        let mut vec = self.0.into_inner();

        // Find the first matching item
        let pos = vec.iter().position(|boxed| f(boxed.as_ref()))?;

        // Remove and unbox the item
        Some(*vec.remove(pos))
    }
}
