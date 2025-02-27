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

use ::std::cell::OnceCell;
use ::std::convert::Infallible;

/// A private trait for [`OnceCell`] to use an unstable method [`OnceCell::get_or_try_init()`] in stable code.
pub(crate) trait OnceCellExt<T> {
    fn get_or_try_init2<E, F>(&self, init: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>;
}

impl<T> OnceCellExt<T> for OnceCell<T> {
    fn get_or_try_init2<E, F>(&self, init: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        match self.get() {
            Some(v) => Ok(v),
            None => {
                let v = init()?;
                let _ = self.set(v); // We are sure the `set` will succeed.
                Ok(unsafe { self.get().unwrap_unchecked() })
            }
        }
    }
}

/// A private trait for [`Result`] to use an unstable method [`Result::into_ok()`] in stable code.
pub(crate) trait ResultExt<T, E> {
    fn into_ok2(self) -> T
    where
        E: Into<Infallible>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    #[allow(unreachable_code)]
    fn into_ok2(self) -> T
    where
        E: Into<Infallible>,
    {
        match self {
            Ok(v) => v,
            Err(e) => match e.into() {},
        }
    }
}
