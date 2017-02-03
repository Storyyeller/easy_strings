// Copyright 2017 Robert Grosse.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[macro_use]
extern crate lazy_static;

use std::collections::HashMap;
use std::sync::Mutex;

mod adapters;
mod ezstring;
pub use ezstring::EZString;

lazy_static! {
    static ref STATIC_STRINGS: Mutex<HashMap<&'static str, EZString>> = Mutex::default();
}

/// Creates an EZString from a string literal and interns the result so that calling it multiple times with the same string literal
/// won't result in multiple copies or allocations. (However, it still requires locking and querying the
/// interned string table each time.)
///
/// ```
/// # #![allow(unused_mut, unused_import)]
/// use easy_strings::{ez};
/// let s = ez("Hello, world!");
/// ```
pub fn ez(lit: &'static str) -> EZString {
    let mut map = STATIC_STRINGS.lock().unwrap();
    map.entry(lit).or_insert_with(|| EZString::from(lit)).clone()
}


