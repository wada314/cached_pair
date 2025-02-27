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

use std::marker::PhantomData;

/// A container that holds multiple values where each value can be converted to another type.
///
/// This is similar to `Pair` but can hold multiple values instead of just two.
#[derive(Debug)]
pub struct MultiPair<T, U, const N: usize> {
    /// The first type of values
    t_values: Vec<T>,
    /// The second type of values
    u_values: Vec<U>,
    /// Phantom data to ensure proper type constraints
    _phantom: PhantomData<(T, U)>,
}

impl<T, U, const N: usize> MultiPair<T, U, N> {
    /// Creates a new empty MultiPair
    pub fn new() -> Self {
        Self {
            t_values: Vec::with_capacity(N),
            u_values: Vec::with_capacity(N),
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_empty_multipair() {
        let _pair: MultiPair<i32, String, 3> = MultiPair::new();
    }
}
