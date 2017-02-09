// Copyright 2017 Robert Grosse.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
use std::ops::{Deref, DerefMut};

extern crate owning_ref;
use self::owning_ref::{OwningHandle, StableAddress};

struct DerefNewtype<T>(T);
impl<T> Deref for DerefNewtype<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T> DerefMut for DerefNewtype<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
// impl<T: Clone> Clone for DerefNewtype<T> { fn clone(&self) -> Self { DerefNewtype(self.0.clone()) } }

pub struct OwnedIter<S: StableAddress, T>(OwningHandle<S, DerefNewtype<T>>);
impl<S: StableAddress + 'static, T> OwnedIter<S, T> {
    pub unsafe fn new<F>(o: S, f: F) -> Self
        where F: Fn(&'static S::Target) -> T
    {
        OwnedIter(OwningHandle::new(o, |ptr| DerefNewtype(f(&*ptr))))
    }

    pub fn wrapped(self) -> WrappedIter<S, T> {
        WrappedIter(self)
    }
}
impl<S: StableAddress, T: Iterator> Iterator for OwnedIter<S, T> {
    type Item = T::Item;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}
impl<S: StableAddress, T: DoubleEndedIterator> DoubleEndedIterator for OwnedIter<S, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}


pub trait Wrappable {
    type Target;
    fn wrap(self) -> Self::Target;
}
pub struct WrappedIter<S: StableAddress, T>(OwnedIter<S, T>);
impl<S: StableAddress, T: Iterator> Iterator for WrappedIter<S, T>
    where T::Item: Wrappable
{
    type Item = <T::Item as Wrappable>::Target;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|s| s.wrap())
    }
}
impl<S: StableAddress, T: DoubleEndedIterator> DoubleEndedIterator for WrappedIter<S, T>
    where T::Item: Wrappable
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|s| s.wrap())
    }
}



impl Wrappable for char {
    type Target = Self;
    fn wrap(self) -> Self::Target {
        self
    }
}
impl Wrappable for (usize, char) {
    type Target = Self;
    fn wrap(self) -> Self::Target {
        self
    }
}
impl Wrappable for u8 {
    type Target = Self;
    fn wrap(self) -> Self::Target {
        self
    }
}
