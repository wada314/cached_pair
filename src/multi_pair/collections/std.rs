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
use ::std::pin::Pin;

use super::CellCollection;

/// A collection that stores items in a Vec with pinned boxed values.
/// This type provides interior mutability while maintaining pinning guarantees.
pub struct VecCollection<T, A: Allocator>(RefCell<Vec<Pin<Box<T, A>>, A>>);

impl<T, A: Allocator + Clone> CellCollection for VecCollection<T, A> {
    type Item = T;
    type Allocator = A;

    fn new_in(allocator: Self::Allocator) -> Self {
        Self(RefCell::new(Vec::new_in(allocator)))
    }

    fn insert(&self, item: Self::Item) -> &Self::Item {
        let mut vec = self.0.borrow_mut();
        // First create a Box
        let boxed = Box::new_in(item, vec.allocator().clone());
        // Safety: This value is stored in Vec and only accessible by reference from outside.
        // The collection interface does not allow moving the value.
        let pinned = unsafe { Pin::new_unchecked(boxed) };
        vec.push(pinned);
        // Safety: The returned reference is valid as long as the value is not removed from Vec
        unsafe { &*(vec.last().unwrap().as_ref().get_ref() as *const T) }
    }

    fn iter(&self) -> impl Iterator<Item = &Self::Item> {
        struct RefIter<'a, T, A: Allocator> {
            _ref: Ref<'a, Vec<Pin<Box<T, A>>, A>>,
            pos: usize,
        }

        impl<'a, T, A: Allocator> Iterator for RefIter<'a, T, A> {
            type Item = &'a T;

            fn next(&mut self) -> Option<Self::Item> {
                if self.pos >= self._ref.len() {
                    None
                } else {
                    // Safety: This is safe because:
                    // 1. While Pin<Box<T>> itself can be moved within Vec,
                    //    the pointee (T) remains at a stable address due to Box's heap allocation
                    // 2. The collection does not provide any methods to delete items
                    // 3. The collection itself owns all items until it is dropped
                    // 4. RefCell ensures no mutable access during iteration
                    let item = unsafe { &*(self._ref[self.pos].as_ref().get_ref() as *const T) };
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
}
