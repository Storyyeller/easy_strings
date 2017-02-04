Ergonomic, garbage collected strings for Rust.

EZString is similar to the strings in high level languages such as
Python and Java. It is designed to as easy to use as possible by always returning owned values,
using reference counting and copy-on-write under the hood in order to make this efficient.

# Getting Started
[easy_strings is available on crates.io](https://crates.io/crates/easy_strings).
Add the following dependency to your Cargo manifest.

```toml
[dependencies]
easy_strings = "0.1"
```

Then import it in your code.
```rust
extern crate easy_strings;
use easy_strings::{EZString, ez};
```

# String Creation
The most common way to create an EZString is from a string literal, using the ez() helper
function. This interns the string so that calling it multiple times with the same string literal
won't result in multiple copies or allocations. (It still requires locking and querying the
interned string table each time.)

```rust
use easy_strings::{ez};
let s = ez("Hello, world!");
```

You can also create EZString from existing Strings or &strs.

```rust
use easy_strings::{EZString};
let s = EZString::from("foo");
let s = EZString::from("foo".to_string());
```
# Concatenation
To concatenate strings, write `&a + &b`. This syntax works regardless of the types of a and b,
whether they are EZString, &EZString, String, &String, or &str, as long as either a or b is
an EZString or &EZString.

```rust
let e = ez("E");
let re = &e;
let s = "s".to_string();
let rs = &s;
let lit = "lit";
assert_eq!(&e + &e, "EE");
assert_eq!(&e + &re, "EE");
assert_eq!(&e + &s, "Es");
assert_eq!(&e + &rs, "Es");
assert_eq!(&e + &lit, "Elit");
assert_eq!(&lit + &e, "litE");
assert_eq!(&lit + &re, "litE");
assert_eq!(&s + &re, "sE");
assert_eq!(&rs + &e, "sE");
```
Note: If you're using Clippy, you should `#[allow(needless_borrow)]` or you'll get a lot of warnings.

You can also concatenate multiple strings this way, as long as at least one of the first two is EZString
or &EZString.

```rust
assert_eq!(&lit + &re + &s + &e + &e + &rs, "litEsEEs");
```


You can also use the += operator. This is optimized to only copy the left hand string when it is not
uniquely owned. This means that the following loop is O(n) rather than O(n^2 ) and there is no
need for a seperate StringBuilder type like there is in Java.

```rust
let mut s = ez("Some numbers: ");
for i in 0..5 {
    s += &i.to_string();
    s += &", ";
}
assert_eq!(s, "Some numbers: 0, 1, 2, 3, 4, ");
```

# Slicing
Slicing is done via the substr() method. Note that the indices are by byte, not code point. If
the provided indices are not on a code point boundary, substr() will panic.

```rust
let mut a = ez("Hello, world!");
assert_eq!(a.substr(1..), "ello, world!");
assert_eq!(a.substr(..6), "Hello,");
assert_eq!(a.substr(1..6), "ello,");
assert_eq!(a.substr(1..a.len()-1), "ello, world");

let b = a.substr(1..3);
a += &b; // b is a copy, so we can freely mutate a
```

substr() returns the substring as a new EZString. If you want a borrowed slice instead, you
can use []. This avoids the extra copy and allocation, at the expense of forcing you to worry
about lifetimes, which easy_strings was designed to avoid.

```rust
let b = &a[1..3];
assert_eq!(b, "el");
// a += &b; // compile error because b borrowed a
```

# Equality
Equality testing between multiple EZStrings or &EZStrings just works. If you want to compare to
a String or &str, the EZString should be on the left. If it is on the right, you'll have to
prefix it with * (or ** for &EZString).

```rust
let e = ez("AAA");
let er = &e;
let s = String::from("AAA");
let sr = &s;
let lit = "AAA";
assert!(e == e);
assert!(er == er);
assert!(e == er);
assert!(er == e);
assert!(e == s);
assert!(e == sr);
assert!(e == lit);
assert!(er == s);
assert!(er == sr);
assert!(er == lit);
assert!(s == *e);
assert!(*sr == *e);
assert!(lit == *e);
assert!(s == **er);
assert!(*sr == **er);
assert!(lit == **er);
```

# Cloning
EZString is not Copy, which means you must clone it whenever you want to reuse it _by value_.
To work around this, it is recommended that your functions always take EZString parameters by
reference and return owned EZStrings. This provides maximum flexibility to the caller and avoids
requiring clone()s everywhere. EZString's own methods, such as trim() here, already do this.

```rust
// bad: requires caller to clone() argument
fn foo(s: EZString) -> EZString { s.trim() }
// good
fn bar(s: &EZString) -> EZString { s.trim() }
```
That being said, sometimes taking by value is unavoidable. In this case, you need to clone your
string. Remember, this doesn't actually copy the string, it just increments the reference count.

The simplest and most standard way is to call .clone(). However, if this is too verbose for your
taste, there is also a shorthand .c() method. c() also has the advantage of always cloning the
underlying EZString, even if you call it on nested references (clone() clones the reference
instead in this case).

```rust
let mut v: Vec<EZString> = Vec::new();
let s = ez("foo");
let rs = &s;
let rrs = &rs;

v.push(s.clone());
v.push(s.c());
v.push(rs.clone());
v.push(rs.c());
// v.push(rrs.clone()); // compile error
v.push(rrs.c());
```
# Coercions
Most libraries operate on Strings and &strs, rather than EZStrings. Luckily, EZString Derefs to
&str, so in most cases, you can pass &s in and it will just work,

```rust
fn take_str(_: &str) {}
let s = ez("");
let rs = &s;

take_str(&s);
take_str(&rs);
```
In complicated cases, such as with generic functions, inference may not work. In that case, you
can explicitly get a &str via as_str().

```rust
take_str(s.as_str());
take_str(rs.as_str());
```
If a function requires an owned String, you can use the to_string() method.

```rust
fn take_string(_: String) {}
take_string(s.to_string());
```
# String searching
The contains(), starts_with(), ends_with(), find(), and rfind() methods are generic, meaning
that you'll get a confusing compile error if you naively pass in an EZString. The easiest
solution is to use as_str() as mentioned in the previous section. Alternatively, you can write
`&*s` for EZStrings and `&**s` for &EZStrings. No special syntax is required to pass in a literal.

```rust
let s = ez("Hello, world!");

assert!(s.contains("o, wo"));
assert!(s.starts_with("Hello"));
assert!(s.ends_with("world!"));
assert!(!s.ends_with("worl"));
assert_eq!(s.find("ld"), Some(10));
assert_eq!(s.find("l"), Some(2));
assert_eq!(s.rfind("l"), Some(10));

let p = ez("wor");
let r = &p;
assert!(s.contains(&*p));
assert!(s.contains(&**r));
assert!(s.contains(p.as_str()));
assert!(s.contains(r.as_str()));
```
Note that find() and rfind() return an Option. To get behavior similar to Python's str.index(),
which throws if the substring isn't present, just call unwrap() on the result.

```rust
assert_eq!(s.find("ld").unwrap(), 10);
```
# String splitting
You can split by newlines, whitespace, or a provided substring. The returned iterators wrap
the results in new EZStrings.

```rust
let s = ez(" Hello,   world!\nLine two. ");

assert_eq!(s.lines().collect::<Vec<_>>(), vec![ez(" Hello,   world!"), ez("Line two. ")]);
assert_eq!(s.split_whitespace().collect::<Vec<_>>(),
           vec![ez("Hello,"), ez("world!"), ez("Line"), ez("two.")]);

let s = ez("aaa-bbb-ccc");
assert_eq!(s.split("-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"), ez("ccc")]);
assert_eq!(s.rsplit("-").collect::<Vec<_>>(), vec![ez("ccc"), ez("bbb"), ez("aaa")]);
```
You can also limit the number of splits via splitn().

```rust
let s = ez("aaa-bbb-ccc");
assert_eq!(s.splitn(2, "-").collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb-ccc")]);
assert_eq!(s.rsplitn(2, "-").collect::<Vec<_>>(), vec![ez("ccc"), ez("aaa-bbb")]);
```
Although the iterators are lazy, they hold a reference to the copy of the string at time of
creation. Therefore, if you later modify the string, the iteration results don't change.

```rust
let mut s = ez("aaa-bbb-ccc");
let it = s.split("-");
s += &"-ddd";
assert_eq!(it.collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"), ez("ccc")]);
let it2 = s.split("-");
assert_eq!(it2.collect::<Vec<_>>(), vec![ez("aaa"), ez("bbb"), ez("ccc"), ez("ddd")]);
```
# Returning Iterators
Every iteration method returns a distinct type. If you want to return one of several iterators,
you need to either box them or eagerly evaluate them.

For example, suppose you wanted to emulate
Python's str.split() method, which splits on a substring if one is passed in and splits on
whitespace if no argument is passed. The naive approach doesn't work as EZString::split() and
EZString::split_whitespace() return distinct types. One solution is to eagerly evaluate them
and return a
list of strings.

```rust
fn split<'a, P: Into<Option<&'a str>>>(s: &EZString, sep: P) -> Vec<EZString> {
    match sep.into() {
        Some(sep) => s.split(sep).collect(),
        None => s.split_whitespace().collect(),
    }
}

let s = ez("x  x-x 77x");
assert_eq!(split(&s, "x"), vec![ez(""), ez("  "), ez("-"), ez(" 77"), ez("")]);
assert_eq!(split(&s, None), vec![ez("x"), ez("x-x"), ez("77x")]);
```
Alternatively, you can box the iterators, thus preserving the laziness.

```rust
fn split<'a, P: Into<Option<&'a str>>>(s: &EZString, sep: P) -> Box<Iterator<Item=EZString>> {
    match sep.into() {
        Some(sep) => Box::new(s.split(sep)),
        None => Box::new(s.split_whitespace()),
    }
}
```
# Trimming
The trim(), trim_left(), and trim_right() methods trim whitespace from the ends of the string.

```rust
assert_eq!(ez("  hello \n ").trim(), "hello");
let s = ez("  hello \n ").trim_right();
assert_eq!(s, "  hello");
assert_eq!(s.trim_left(), "hello");
```
trim_left_matches() and trim_right_matches() trim matches of a given substring from the ends of
the string. Note that unlike Python, they do not take a set of characters to trim, but a substring.
Note that trim_matches() is different from all of the other methods. It takes a char rather than
a substring.

```rust
assert_eq!(ez("  hello   ").trim_matches(' '), "hello");
let s = ez(" x xhello x x x").trim_right_matches(" x");
assert_eq!(s, " x xhello");
assert_eq!(s.trim_left_matches(" x"), "hello");
```
# Other methods
to_lowercase(), to_uppercase(), and repeat() are pretty much self explanatory.

```rust
let s = ez("Hello, World!");
assert_eq!(s.to_lowercase(), "hello, world!");
assert_eq!(s.to_uppercase(), "HELLO, WORLD!");
assert_eq!(s.repeat(3), "Hello, World!Hello, World!Hello, World!");
```
# Pointer equality
The == operator tests for _value_ equality, that is whether the given strings contain the same
bytes. If you want to test whether two EZStrings share the same underlying buffer, you can use the
ptr_eq() method. Note that since EZString is copy-on-write, there is no observeable effect of
sharing buffers, apart from reduced memory usage. Therefore, this method is rarely useful.

```rust
let a = ez("xxx");
let mut b = a.clone();
let c = &ez("xx") + &ez("x");
assert!(a.ptr_eq(&b));
assert!(b == c && !b.ptr_eq(&c));

b += &"foo";
// += is copy on write, so b no longer points to a
assert!(!a.ptr_eq(&b));
assert!(a == "xxx");
assert!(b == "xxxfoo");
```
