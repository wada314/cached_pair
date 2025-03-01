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
use ::std::collections::LinkedList;
use ::std::iter;
use ::std::rc::Rc;

use super::CellCollection;

impl<T, A> CellCollection for RefCell<LinkedList<T, A>>
where
    A: Allocator + Clone,
{
    type Item = T;
    type Allocator = A;

    fn new_in(allocator: Self::Allocator) -> Self {
        RefCell::new(LinkedList::new_in(allocator))
    }

    fn insert(&self, item: Self::Item) -> &Self::Item {
        let mut list = self.borrow_mut();
        list.push_back(item);
        let borrowed = self.borrow();
        let back = borrowed.back().unwrap();
        // Allow to ignore the RefCell borrow checker because the immutable reference
        // to the LinkedList is always valid. This is not true for other collections like
        // Vec, HashMap, etc.
        unsafe { &*(back as *const Self::Item) }
    }

    fn iter(&self) -> impl Iterator<Item = &Self::Item> {
        iter::once(self.borrow()).flat_map(|list| list.iter())
    }
}
