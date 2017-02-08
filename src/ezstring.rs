// Copyright 2017 Robert Grosse.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
use std;
use std::borrow::Borrow;

use std::ops::{Add, AddAssign, Deref, DerefMut, Index};
use std::sync::Arc;

use adapters;

impl<'a> adapters::Wrappable for &'a str {
    type Target = EZString;
    fn wrap(self) -> Self::Target { EZString::from(self) }
}

type WrappedIter<T> = adapters::WrappedIter<Arc<String>, T>;
type Chars = WrappedIter<std::str::Chars<'static>>;
type CharIndices = WrappedIter<std::str::CharIndices<'static>>;
type Bytes = WrappedIter<std::str::Bytes<'static>>;
type SplitWhitespace = WrappedIter<std::str::SplitWhitespace<'static>>;
type Lines = WrappedIter<std::str::Lines<'static>>;


type PatternIter<T> = WrappedIter<adapters::OwnedIter<String, T>>;
type Split = PatternIter<std::str::Split<'static, &'static str>>;
type RSplit = PatternIter<std::str::RSplit<'static, &'static str>>;
type SplitTerminator = PatternIter<std::str::SplitTerminator<'static, &'static str>>;
type RSplitTerminator = PatternIter<std::str::RSplitTerminator<'static, &'static str>>;
type SplitN = PatternIter<std::str::SplitN<'static, &'static str>>;
type RSplitN = PatternIter<std::str::RSplitN<'static, &'static str>>;


fn pattern_iter<F, T>(p: &str, f: F) -> adapters::OwnedIter<String, T>
    where F: Fn(&'static str) -> T
{
    // Unsafe invariant: f must not leak input reference or treat it as 'static (it's a fake lifetime)
    unsafe{adapters::OwnedIter::new(p.to_string(), f)}
}

/// An ergonomic, garbage collected string.
///
/// EZString is similar to the strings in high level languages such as
/// Python and Java. It is designed to as easy to use as possible by always returning owned values,
/// using reference counting and copy-on-write under the hood in order to make this efficient.
///
/// # Creation
/// The most common way to create an EZString is from a string literal, using the ez() helper
/// function. This interns the string so that calling it multiple times with the same string literal
/// won't result in multiple copies or allocations. (It still requires locking and querying the
/// interned string table each time.)
///
/// ```rust
/// use easy_strings::{ez};
/// let s = ez("Hello, world!");
/// ```
///
/// You can also create EZString from existing Strings or &strs.
///
/// ```rust
/// use easy_strings::{EZString};
/// let s = EZString::from("foo");
/// let s = EZString::from("foo".to_string());
/// ```
/// # Concatenation
/// To concatenate strings, write `&a + &b`. This syntax works regardless of the types of a and b,
/// whether they are EZString, &EZString, String, &String, or &str, as long as either a or b is
/// an EZString or &EZString.
///
/// ```rust
/// # use easy_strings::*;
/// let e = ez("E");
/// let re = &e;
/// let s = "s".to_string();
/// let rs = &s;
/// let lit = "lit";
/// assert_eq!(&e + &e, "EE");
/// assert_eq!(&e + &re, "EE");
/// assert_eq!(&e + &s, "Es");
/// assert_eq!(&e + &rs, "Es");
/// assert_eq!(&e + &lit, "Elit");
/// assert_eq!(&lit + &e, "litE");
/// assert_eq!(&lit + &re, "litE");
/// assert_eq!(&s + &re, "sE");
/// assert_eq!(&rs + &e, "sE");
/// ```
/// Note: If you're using Clippy, you should `#[allow(needless_borrow)]` or you'll get a lot of warnings.
///
/// You can also concatenate multiple strings this way, as long as at least one of the first two is EZString
/// or &EZString.
///
/// ```rust
/// # use easy_strings::*;
/// # let e = ez("E");
/// # let re = &e;
/// # let s = "s".to_string();
/// # let rs = &s;
/// # let lit = "lit";
/// assert_eq!(&lit + &re + &s + &e + &e + &rs, "litEsEEs");
/// ```
///
///
/// You can also use the += operator. This is optimized to only copy the left hand string when it is not
/// uniquely owned. This means that the following loop is O(n) rather than O(n^2 ) and there is no
/// need for a seperate StringBuilder type like there is in Java.
///
/// ```rust
/// # use easy_strings::*;
/// let mut s = ez("Some numbers: ");
/// for i in 0..5 {
///     s += &i.to_string();
///     s += &", ";
/// }
/// assert_eq!(s, "Some numbers: 0, 1, 2, 3, 4, ");
/// ```
///
/// # Slicing
/// Slicing is done via the substr() method. Note that the indices are by byte, not code point. If
/// the provided indices are not on a code point boundary, substr() will panic.
///
/// ```rust
/// # use easy_strings::{ez};
/// let mut a = ez("Hello, world!");
/// assert_eq!(a.substr(1..), "ello, world!");
/// assert_eq!(a.substr(..6), "Hello,");
/// assert_eq!(a.substr(1..6), "ello,");
/// assert_eq!(a.substr(1..a.len()-1), "ello, world");
///
/// let b = a.substr(1..3);
/// a += &b; // b is a copy, so we can freely mutate a
/// ```
///
/// substr() returns the substring as a new EZString. If you want a borrowed slice instead, you
/// can use []. This avoids the extra copy and allocation, at the expense of forcing you to worry
/// about lifetimes, which easy_strings was designed to avoid.
///
/// ```rust
/// # #![allow(unused_mut)]
/// # use easy_strings::*;
/// # let mut a = ez("Hello, world!");
/// let b = &a[1..3];
/// assert_eq!(b, "el");
/// // a += &b; // compile error because b borrowed a
/// ```
///
/// # Equality
/// Equality testing between multiple EZStrings or &EZStrings just works. If you want to compare to
/// a String or &str, the EZString should be on the left. If it is on the right, you'll have to
/// prefix it with * (or ** for &EZString).
///
/// ```rust
/// # use easy_strings::*;
/// let e = ez("AAA");
/// let er = &e;
/// let s = String::from("AAA");
/// let sr = &s;
/// let lit = "AAA";
/// assert!(e == e);
/// assert!(er == er);
/// assert!(e == er);
/// assert!(er == e);
/// assert!(e == s);
/// assert!(e == sr);
/// assert!(e == lit);
/// assert!(er == s);
/// assert!(er == sr);
/// assert!(er == lit);
/// assert!(s == *e);
/// assert!(*sr == *e);
/// assert!(lit == *e);
/// assert!(s == **er);
/// assert!(*sr == **er);
/// assert!(lit == **er);
/// ```
///
/// # Cloning
/// EZString is not Copy, which means you must clone it whenever you want to reuse it _by value_.
/// To work around this, it is recommended that your functions always take EZString parameters by
/// reference and return owned EZStrings. This provides maximum flexibility to the caller and avoids
/// requiring clone()s everywhere. EZString's own methods, such as trim() here, already do this.
///
/// ```rust
/// # use easy_strings::*;
/// // bad: requires caller to clone() argument
/// fn foo(s: EZString) -> EZString { s.trim() }
/// // good
/// fn bar(s: &EZString) -> EZString { s.trim() }
/// ```
/// That being said, sometimes taking by value is unavoidable. In this case, you need to clone your
/// string. Remember, this doesn't actually copy the string, it just increments the reference count.
///
/// The simplest and most standard way is to call .clone(). However, if this is too verbose for your
/// taste, there is also a shorthand .c() method. c() also has the advantage of always cloning the
/// underlying EZString, even if you call it on nested references (clone() clones the reference
/// instead in this case).
///
/// ```rust
/// # use easy_strings::*;
/// let mut v: Vec<EZString> = Vec::new();
/// let s = ez("foo");
/// let rs = &s;
/// let rrs = &rs;
///
/// v.push(s.clone());
/// v.push(s.c());
/// v.push(rs.clone());
/// v.push(rs.c());
/// // v.push(rrs.clone()); // compile error
/// v.push(rrs.c());
/// ```
/// # Coercions
/// Most libraries operate on Strings and &strs, rather than EZStrings. Luckily, EZString Derefs to
/// &str, so in most cases, you can pass &s in and it will just work,
///
/// ```rust
/// # use easy_strings::*;
/// fn take_str(_: &str) {}
/// let s = ez("");
/// let rs = &s;
///
/// take_str(&s);
/// take_str(&rs);
/// ```
/// In complicated cases, such as with generic functions, inference may not work. In that case, you
/// can explicitly get a &str via as_str().
///
/// ```rust
/// # use easy_strings::*;
/// # fn take_str(_: &str) {}
/// # let s = ez("");
/// # let rs = &s;
/// take_str(s.as_str());
/// take_str(rs.as_str());
/// ```
/// If a function requires an owned String, you can use the to_string() method.
///
/// ```rust
/// # use easy_strings::*;
/// fn take_string(_: String) {}
/// # let s = ez("");
/// take_string(s.to_string());
/// ```
/// # String searching
/// The contains(), starts_with(), ends_with(), find(), and rfind() methods are generic, meaning
/// that you'll get a confusing compile error if you naively pass in an EZString. The easiest
/// solution is to use as_str() as mentioned in the previous section. Alternatively, you can write
/// `&*s` for EZStrings and `&**s` for &EZStrings. No special syntax is required to pass in a literal.
///
/// ```rust
/// # use easy_strings::*;
/// let s = ez("Hello, world!");
///
/// assert!(s.contains("o, wo"));
/// assert!(s.starts_with("Hello"));
/// assert!(s.ends_with("world!"));
/// assert!(!s.ends_with("worl"));
/// assert_eq!(s.find("ld"), Some(10));
/// assert_eq!(s.find("l"), Some(2));
/// assert_eq!(s.rfind("l"), Some(10));
///
/// let p = ez("wor");
/// let r = &p;
/// assert!(s.contains(&*p));
/// assert!(s.contains(&**r));
/// assert!(s.contains(p.as_str()));
/// assert!(s.contains(r.as_str()));
/// ```
/// Note that find() and rfind() return an Option. To get behavior similar to Python's str.index(),
/// which throws if the substring isn't present, just call unwrap() on the result.
///
/// ```rust
/// # use easy_strings::*;
/// # let s = ez("Hello, world!");
/// assert_eq!(s.find("ld").unwrap(), 10);
/// ```
/// # String splitting
/// You can split by newlines, whitespace, or a provided substring. The returned iterators wrap
/// the results in new EZStrings.
///
/// ```rust
/// # use easy_strings::*;
/// let s = ez(" Hello,   world!\nLine two. ");
///
/// assert_eq!(s.lines().collect::<Vec<_>>(), vec![ez(" Hello,   world!"), ez("Line two. ")]);
/// assert_eq!(s.split_whitespace().collect::<Vec<_>>(),
///            vec![ez("Hello,"), ez("world!"), ez("Line"), ez("two.")]);
///
/// let s = ez("aaa-bbb-ccc");
/// assert_eq!(s.split("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"), ez("ccc")]);
/// assert_eq!(s.rsplit("-").collect::<Vec<_>>(), vec![ez("ccc"), ez("bbb"), ez("aaa")]);
/// ```
/// You can also limit the number of splits via splitn().
///
/// ```rust
/// # use easy_strings::*;
/// let s = ez("aaa-bbb-ccc");
/// assert_eq!(s.splitn(2, "-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb-ccc")]);
/// assert_eq!(s.rsplitn(2, "-").collect::<Vec<_>>(), vec![ez("ccc"), ez("aaa-bbb")]);
/// ```
/// split_terminator() and rsplit_terminator() are the same as split()/rsplit() except that
/// if the final substring is empty, it is skipped. This is useful if the string is
/// terminated, rather than seperated, by a seperator.
///
/// ```rust
/// # use easy_strings::*;
/// let s = ez("aaa-bbb-");
/// assert_eq!(s.split("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"),  ez("")]);
/// assert_eq!(s.split_terminator("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb")]);
/// assert_eq!(s.rsplit_terminator("-").collect::<Vec<_>>(), vec![ez("bbb"), ez("aaa")]);
///
/// let s = ez("aaa-bbb");
/// assert_eq!(s.split("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb")]);
/// assert_eq!(s.split_terminator("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb")]);
/// ```
/// Although the iterators are lazy, they hold a reference to a copy of the string at time of
/// creation. Therefore, if you later modify the string, the iteration results don't change.
///
/// ```rust
/// # use easy_strings::*;
/// let mut s = ez("aaa-bbb-ccc");
/// let it = s.split("-");
/// s += &"-ddd";
/// assert_eq!(it.collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"), ez("ccc")]);
/// let it2 = s.split("-");
/// assert_eq!(it2.collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"), ez("ccc"), ez("ddd")]);
/// ```
/// # Returning Iterators
/// Every iteration method returns a distinct type. If you want to return one of several iterators,
/// you need to either box them or eagerly evaluate them.
///
/// For example, suppose you wanted to emulate
/// Python's str.split() method, which splits on a substring if one is passed in and splits on
/// whitespace if no argument is passed. The naive approach doesn't work as EZString::split() and
/// EZString::split_whitespace() return distinct types. One solution is to eagerly evaluate them
/// and return a
/// list of strings.
///
/// ```rust
/// # use easy_strings::*;
/// fn split<'a, P: Into<Option<&'a str>>>(s: &EZString, sep: P) -> Vec<EZString> {
///     match sep.into() {
///         Some(sep) => s.split(sep).collect(),
///         None => s.split_whitespace().collect(),
///     }
/// }
///
/// let s = ez("x  x-x 77x");
/// assert_eq!(split(&s, "x"), vec![ez(""), ez("  "), ez("-"), ez(" 77"), ez("")]);
/// assert_eq!(split(&s, None), vec![ez("x"), ez("x-x"), ez("77x")]);
/// ```
/// Alternatively, you can box the iterators, thus preserving the laziness.
///
/// ```rust
/// # #![allow(unused_mut, unused_import)]
/// # use easy_strings::{ez, EZString};
/// fn split<'a, P: Into<Option<&'a str>>>(s: &EZString, sep: P) -> Box<Iterator<Item=EZString>> {
///     match sep.into() {
///         Some(sep) => Box::new(s.split(sep)),
///         None => Box::new(s.split_whitespace()),
///     }
/// }
/// ```
/// # Trimming
/// The trim(), trim_left(), and trim_right() methods trim whitespace from the ends of the string.
///
/// ```rust
/// # use easy_strings::*;
/// assert_eq!(ez("  hello \n ").trim(), "hello");
/// let s = ez("  hello \n ").trim_right();
/// assert_eq!(s, "  hello");
/// assert_eq!(s.trim_left(), "hello");
/// ```
/// trim_left_matches() and trim_right_matches() trim matches of a given substring from the ends of
/// the string. Note that unlike Python, they do not take a set of characters to trim, but a substring.
/// Note that trim_matches() is different from all of the other methods. It takes a char rather than
/// a substring.
///
/// ```rust
/// # use easy_strings::*;
/// assert_eq!(ez("  hello   ").trim_matches(' '), "hello");
/// let s = ez(" x xhello x x x").trim_right_matches(" x");
/// assert_eq!(s, " x xhello");
/// assert_eq!(s.trim_left_matches(" x"), "hello");
/// ```
/// # String replacement
/// You can replace one substring with another via .replace().
///
/// ```rust
/// # use easy_strings::*;
/// let s = ez("one fish two fish, old fish, new fish");
/// assert_eq!(s.replace("fish", "bush"), "one bush two bush, old bush, new bush");
/// assert_eq!(s.replace(&ez("fish"), &ez("bush")), "one bush two bush, old bush, new bush");
/// ```
/// # Other methods
/// to_lowercase(), to_uppercase(), and repeat() are pretty much self explanatory.
///
/// ```rust
/// # use easy_strings::*;
/// let s = ez("Hello, World!");
/// assert_eq!(s.to_lowercase(), "hello, world!");
/// assert_eq!(s.to_uppercase(), "HELLO, WORLD!");
/// assert_eq!(s.repeat(3), "Hello, World!Hello, World!Hello, World!");
/// ```
/// Note that to_lowercase and to_uppercase are Unicode aware, but locale independent.
/// i.e. there is no way to get Turkish capitalization for 'i'.
///
/// ```rust
/// # use easy_strings::*;
/// let s = ez("ὈΔΥΣΣΕΎΣ");
/// assert_eq!(s.to_lowercase(), "ὀδυσσεύς");
/// ```
///
/// # Pointer equality
/// The == operator tests for _value_ equality, that is whether the given strings contain the same
/// bytes. If you want to test whether two EZStrings share the same underlying buffer, you can use the
/// ptr_eq() method. Note that since EZString is copy-on-write, there is no observeable effect of
/// sharing buffers, apart from reduced memory usage. Therefore, this method is rarely useful.
///
/// ```rust
/// # use easy_strings::{ez};
/// let a = ez("xxx");
/// let mut b = a.clone();
/// let c = &ez("xx") + &ez("x");
/// assert!(a.ptr_eq(&b));
/// assert!(b == c && !b.ptr_eq(&c));
///
/// b += &"foo";
/// // += is copy on write, so b no longer points to a
/// assert!(!a.ptr_eq(&b));
/// assert!(a == "xxx");
/// assert!(b == "xxxfoo");
/// ```


#[derive(Clone, Default, PartialOrd, Ord, Eq, Hash, Debug)]
pub struct EZString(Arc<String>);
impl EZString {
    fn new(r: Arc<String>) -> Self { EZString(r) }
    fn from_slice<'a>(&self, s: &'a str) -> Self {
        if s.as_ptr() == self.as_ptr() && s.len() == self.len() { return self.clone(); }
        Self::from(s)
    }
    fn wrapped_iter<F, T>(&self, f: F) -> WrappedIter<T>
        where F: Fn(&'static String) -> T {
        // Unsafe invariant: f must not leak input reference or treat it as 'static (it's a fake lifetime)
        unsafe{adapters::OwnedIter::new(self.0.clone(), f)}.wrapped()
    }

    /// Shorthand for clone().
    ///
    /// This will derefence any number of references, unlike clone(), which only
    /// works on an EZString or &EZString.
    ///
    /// ```
    /// # use easy_strings::{ez, EZString};
    /// let r = &&&&&ez("");
    /// let s: EZString = r.c(); // works
    /// //let s: EZString = r.clone(); // doesn't work
    /// ```
    pub fn c(&self) -> Self { self.clone() }

    /// Returns whether two strings share the same underlying buffer.
    /// This is similar to the `is` operator in Python.
    ///
    /// ```
    /// # use easy_strings::{ez};
    /// let a = ez("xxx");
    /// let mut b = a.clone();
    /// let c = &ez("xx") + &ez("x");
    /// assert!(a.ptr_eq(&b));
    /// assert!(b == c && !b.ptr_eq(&c));
    ///
    /// b += &"foo";
    /// // += is copy on write, so b no longer points to a
    /// assert!(!a.ptr_eq(&b));
    /// ```
    pub fn ptr_eq(&self, other: &Self) -> bool { self.as_ptr() == other.as_ptr() }

    /// Returns a substring. This creates an independent EZString, which involves
    /// copying the sliced data. Panics if the given bounds are not at a code point
    /// boundary or are greater than the length of the string.
    ///
    /// ```
    /// # use easy_strings::{ez};
    /// let mut a = ez("Hello, world!");
    /// assert_eq!(a.substr(1..), "ello, world!");
    /// assert_eq!(a.substr(..6), "Hello,");
    /// assert_eq!(a.substr(1..6), "ello,");
    /// assert_eq!(a.substr(1..a.len()-1), "ello, world");
    ///
    /// let b = a.substr(1..3);
    /// a += &b; // b is a copy, so we can freely mutate a
    /// ```
    ///
    /// Note: If you want a borrowed slice instead, you can use []. This avoids the
    /// extra copy and allocation, at the expense of forcing you to worry about
    /// lifetimes, which easy_strings was designed to avoid.
    ///
    /// ```
    /// # #![allow(unused_mut, unused_import)]
    /// # use easy_strings::{ez, EZString};
    /// let mut a = ez("Hello, world!");
    /// let b = &a[1..3];
    /// assert_eq!(b, "el");
    /// // a += &b; // compile error because b borrowed a
    /// ```
    pub fn substr<I>(&self, ind: I) -> Self
        where String: Index<I, Output=str> {
        self.from_slice(self.0.index(ind))
    }

    /// Returns a reference to the underlying String.
    pub fn as_string(&self) -> &String { &*self.0 }
    /// Returns a copy of the underlying String.
    pub fn to_string(&self) -> String { (*self.0).clone() }


    /// Divide one string into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a UTF-8 code point.
    ///
    /// The two strings returned go from the start of the string to `mid`,
    /// and from `mid` to the end of the string.
    ///
    /// Panics if `mid` is not on a UTF-8 code point boundary, or if it is
    /// beyond the last code point of the string.
    pub fn split_at(&self, mid: usize) -> (Self, Self) {
        let (lhs, rhs) = self.0.split_at(mid);
        (Self::from(lhs), Self::from(rhs))
    }

    /// Returns an iterator over the `char`s of a string.
    ///
    /// As a string consists of valid UTF-8, we can iterate through a
    /// string by char. This method returns such an iterator.
    ///
    /// It's important to remember that char represents a Unicode Scalar
    /// Value, and may not match your idea of what a 'character' is. Iteration
    /// over grapheme clusters may be what you actually want.
    pub fn chars(&self) -> Chars { self.wrapped_iter(|s| s.chars()) }
    /// Returns an iterator over the chars of a string, and their
    /// positions.
    ///
    /// As a string consists of valid UTF-8, we can iterate through a
    /// string by char. This method returns an iterator of both
    /// these chars, as well as their byte positions.
    ///
    /// The iterator yields tuples. The position is first, the char is
    /// second.
    pub fn char_indices(&self) -> CharIndices { self.wrapped_iter(|s| s.char_indices()) }
    /// An iterator over the bytes of a string.
    ///
    /// As a string consists of a sequence of bytes, we can iterate
    /// through a string by byte. This method returns such an iterator.
    pub fn bytes(&self) -> Bytes { self.wrapped_iter(|s| s.bytes()) }
    /// Split a string by whitespace.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`.
    ///
    /// This iterator is double ended.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez(" Hello,   world!\nLine two. ");
    /// assert_eq!(s.split_whitespace().collect::<Vec<_>>(),
    ///            vec![ez("Hello,"), ez("world!"), ez("Line"), ez("two.")]);
    /// ```
    pub fn split_whitespace(&self) -> SplitWhitespace { self.wrapped_iter(|s| s.split_whitespace()) }
    /// An iterator over the lines of a string.
    ///
    /// Lines are ended with either a newline (`\n`) or a carriage return with
    /// a line feed (`\r\n`).
    ///
    /// The final line ending is optional.
    ///
    /// This iterator is double ended.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez(" Hello,   world!\nLine two. ");
    /// assert_eq!(s.lines().collect::<Vec<_>>(), vec![ez(" Hello,   world!"), ez("Line two. ")]);
    /// ```
    pub fn lines(&self) -> Lines { self.wrapped_iter(|s| s.lines()) }

    /// Split a string by substring
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("aaa-bbb-ccc");
    /// assert_eq!(s.split("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"), ez("ccc")]);
    /// ```
    pub fn split(&self, p: &str) -> Split { self.wrapped_iter(|s| pattern_iter(p, |p| s.split(p))) }
    /// Split a string by substring and return results in reverse order.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("aaa-bbb-ccc");
    /// assert_eq!(s.rsplit("-").collect::<Vec<_>>(), vec![ez("ccc"), ez("bbb"), ez("aaa")]);
    /// ```

    pub fn rsplit(&self, p: &str) -> RSplit { self.wrapped_iter(|s| pattern_iter(p, |p| s.rsplit(p))) }
    /// split_terminator() is the same as split() except that
    /// if the final substring is empty, it is skipped. This is useful if the string is
    /// terminated, rather than seperated, by a seperator.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("aaa-bbb-");
    /// assert_eq!(s.split("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"),  ez("")]);
    /// assert_eq!(s.split_terminator("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb")]);
    ///
    /// let s = ez("aaa-bbb");
    /// assert_eq!(s.split("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb")]);
    /// assert_eq!(s.split_terminator("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb")]);
    /// ```
    pub fn split_terminator(&self, p: &str) -> SplitTerminator { self.wrapped_iter(|s| pattern_iter(p, |p| s.split_terminator(p))) }
    /// Same as split_terminator, except it returns the results in reverse order.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("aaa-bbb-");
    /// assert_eq!(s.rsplit_terminator("-").collect::<Vec<_>>(), vec![ez("bbb"), ez("aaa")]);
    /// ```
    pub fn rsplit_terminator(&self, p: &str) -> RSplitTerminator { self.wrapped_iter(|s| pattern_iter(p, |p| s.rsplit_terminator(p))) }
    /// Split a string by substring, up to n-1 times (returning up to n results).
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("aaa-bbb-ccc");
    /// assert_eq!(s.splitn(2, "-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb-ccc")]);
    /// ```
    pub fn splitn(&self, n: usize, p: &str) -> SplitN { self.wrapped_iter(|s| pattern_iter(p, |p| s.splitn(n, p))) }
    /// Split a string by substring starting from the end, up to n-1 times (returning up to n results).
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("aaa-bbb-ccc");
    /// assert_eq!(s.rsplitn(2, "-").collect::<Vec<_>>(), vec![ez("ccc"), ez("aaa-bbb")]);
    /// ```
    pub fn rsplitn(&self, n: usize, p: &str) -> RSplitN { self.wrapped_iter(|s| pattern_iter(p, |p| s.rsplitn(n, p))) }

    /// Returns a string with leading and trailing whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`.
    ///
    /// ```
    /// # use easy_strings::*;
    /// assert_eq!(ez("  hello \n ").trim(), "hello");
    /// ```
    pub fn trim(&self) -> Self { self.from_slice(self.0.trim()) }
    /// Returns a string with leading whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`.
    ///
    /// ```
    /// # use easy_strings::*;
    /// assert_eq!(ez("  hello \n ").trim_left(), "hello \n ");
    /// ```
    pub fn trim_left(&self) -> Self { self.from_slice(self.0.trim_left()) }
    /// Returns a string with trailing whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`.
    ///
    /// ```
    /// # use easy_strings::*;
    /// assert_eq!(ez("  hello \n ").trim_right(), "  hello");
    /// ```
    pub fn trim_right(&self) -> Self { self.from_slice(self.0.trim_right()) }

    /// Returns a string with all instances of a given character removed from the beginning and end.
    ///
    /// ```
    /// # use easy_strings::*;
    /// assert_eq!(ez("  hello   ").trim_matches(' '), "hello");
    /// ```
    pub fn trim_matches(&self, p: char) -> Self { self.from_slice(self.0.trim_matches(p)) }
    /// Trim matches of a given substring from the beginning of
    /// the string. Note that unlike Python, it does not take a set of characters to trim, but a substring.
    /// Note that this differs from trim_matches(), which takes a char.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez(" x xhello x x x").trim_right_matches(" x");
    /// assert_eq!(s, " x xhello");
    /// assert_eq!(s.trim_left_matches(" x"), "hello");
    /// ```
    pub fn trim_left_matches(&self, p: &str) -> Self { self.from_slice(self.0.trim_left_matches(p)) }
    /// Trim matches of a given substring from the end of
    /// the string. Note that unlike Python, it does not take a set of characters to trim, but a substring.
    /// Note that this differs from trim_matches(), which takes a char.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez(" x xhello x x x").trim_right_matches(" x");
    /// assert_eq!(s, " x xhello");
    /// assert_eq!(s.trim_left_matches(" x"), "hello");
    /// ```
    pub fn trim_right_matches(&self, p: &str) -> Self { self.from_slice(self.0.trim_right_matches(p)) }

    /// Replaces all matches of a string with another string.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("one fish two fish, old fish, new fish");
    /// assert_eq!(s.replace("fish", "bush"), "one bush two bush, old bush, new bush");
    /// assert_eq!(s.replace(&ez("fish"), &ez("bush")), "one bush two bush, old bush, new bush");
    /// ```
    pub fn replace(&self, from: &str, to: &str) -> Self { Self::from(self.0.replace(from, to)) }
    /// Returns the lowercase equivalent of this string.
    ///
    /// 'Lowercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Lowercase`.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("Hello, World!");
    /// assert_eq!(s.to_lowercase(), "hello, world!");
    ///
    /// let s = ez("ὈΔΥΣΣΕΎΣ");
    /// assert_eq!(s.to_lowercase(), "ὀδυσσεύς");
    /// ```
    pub fn to_lowercase(&self) -> Self { Self::from(self.0.to_lowercase()) }
    /// Returns the uppercase equivalent of this string.
    ///
    /// 'Uppercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Uppercase`.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("Hello, World!");
    /// assert_eq!(s.to_uppercase(), "HELLO, WORLD!");
    /// ```
    pub fn to_uppercase(&self) -> Self { Self::from(self.0.to_uppercase()) }

    /// Create a new string by repeating a string `n` times.
    ///
    /// ```
    /// # use easy_strings::*;
    /// let s = ez("Hello, World!");
    /// assert_eq!(s.repeat(3), "Hello, World!Hello, World!Hello, World!");
    /// ```
    pub fn repeat(&self, n: usize) -> Self {
        match n {
            0 => Self::default(),
            1 => self.clone(),
            n => {
                //TODO: make more efficient?
                let a = n/2;
                self.repeat(a) + &self.repeat(n-a)
            },
        }
    }
}
impl Deref for EZString {
    type Target = String;
    fn deref(&self) -> &Self::Target { &*self.0 }
}
impl DerefMut for EZString {
    /// Returns a mutable reference to the underlying string, copying it if necessary.
    fn deref_mut(&mut self) -> &mut Self::Target { Arc::make_mut(&mut self.0) }
}
impl Borrow<String> for EZString { fn borrow(&self) -> &String { self.deref() } }
impl Borrow<str> for EZString { fn borrow(&self) -> &str { self.deref() } }
impl AsRef<String> for EZString { fn as_ref(&self) -> &String { self.deref() } }
impl AsRef<str> for EZString { fn as_ref(&self) -> &str { self.deref() } }
impl From<String> for EZString {
    fn from(s: String) -> Self { Self::new(Arc::new(s)) }
}
impl<'a> From<&'a str> for EZString {
    fn from(s: &'a str) -> Self { Self::from(String::from(s)) }
}




impl<'a, 'b> Add<&'a str> for &'b EZString {
    type Output = EZString;
    fn add(self, other: &str) -> Self::Output { Self::Output::from((*self.0).clone() + other) }
}
impl<'a, 'b, 'c> Add<&'a str> for &'c &'b EZString {
    type Output = EZString;
    fn add(self, other: &str) -> Self::Output { *self + other }
}

impl<'a, 'b> Add<&'a EZString> for &'b String {
    type Output = EZString;
    fn add(self, other: &EZString) -> Self::Output { Self::Output::from(self.clone()) + other }
}
impl<'a, 'b, 'c> Add<&'a EZString> for &'c &'b String {
    type Output = EZString;
    fn add(self, other: &EZString) -> Self::Output { *self + other }
}
impl<'a, 'b, 'c> Add<&'a EZString> for &'c &'b str {
    type Output = EZString;
    fn add(self, other: &EZString) -> Self::Output { Self::Output::from(*self) + other }
}

impl<'a> Add<&'a str> for EZString {
    type Output = EZString;
    fn add(mut self, other: &str) -> Self::Output { self += other; self }
}

impl<'a, T: AsRef<str> + ?Sized> AddAssign<&'a T> for EZString {
    fn add_assign(&mut self, other: &T) { *self.deref_mut() += &other.as_ref(); }
}
impl AddAssign<EZString> for EZString {
    fn add_assign(&mut self, other: EZString) { *self.deref_mut() += &other; }
}



// Should be Borrow instead of AsRef, but Rust won't allow it
impl<T: AsRef<str> + ?Sized> PartialEq<T> for EZString {
    fn eq(&self, other: &T) -> bool { *self.0 == other.as_ref() }
}
impl<'a> PartialEq<EZString> for &'a EZString {
    fn eq(&self, other: &EZString) -> bool { *self == other }
}
impl<'a> PartialEq<String> for &'a EZString {
    fn eq(&self, other: &String) -> bool { *self == other }
}

