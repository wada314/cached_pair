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
use ::std::ops::Deref;
use ::std::pin::Pin;
use ::std::rc::Rc;

use super::CellCollection;

impl<T, A> CellCollection for RefCell<Vec<Pin<Box<T, A>>, A>>
where
    A: Allocator + Clone,
{
    type Item = T;
    type Allocator = A;

    fn new_in(allocator: Self::Allocator) -> Self {
        RefCell::new(Vec::new_in(allocator))
    }

    fn insert(&self, item: Self::Item) -> &Self::Item {
        let mut vec = self.borrow_mut();
        vec.push(Box::pin_in(item, vec.allocator().clone()));
        let borrowed = self.borrow();
        let pinned_back = borrowed.last().unwrap();
        pinned_back.as_ref().get_ref()
    }

    fn iter(&self) -> impl Iterator<Item = impl Deref<Target = Self::Item>> {
        todo!()
    }
}
