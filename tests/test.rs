// Copyright 2017 Robert Grosse.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
use std::collections::HashMap;

extern crate easy_strings;
use easy_strings::{EZString, ez};

#[test]
fn literal() {
    let s = ez("Hello, world!");
    assert_eq!(*s, "Hello, world!");
}

fn consume(_: EZString) {}
fn consume_ref(_: &EZString) {}

#[test]
fn concat() {
    let ea = ez("AAA");
    let eb = ez("bbb");
    let erb = &eb;
    let sc: String = "CcC".into();
    let src = &sc;
    let ld: &str = "dDd";

    consume(&ea + &eb);
    consume(&ea + &erb);
    consume(&ea + &sc);
    consume(&ea + &src);
    consume(&ea + &ld);

    consume(&ea + &ea);
    consume(&erb + &ea);
    consume(&sc + &ea);
    consume(&src + &ea);
    consume(&ld + &ea);

    consume(&sc + &erb);
    consume(&src + &erb);
    consume(&ld + &erb);

    consume(&ea + &ea + &ea);
    consume(ez("") + &ea + &ea + &ea);
    consume(&ea + &erb + &sc + &src + &ld);
    consume(&ld + &erb + &ld);
}

#[test]
fn concat_inplace() {
    let ea = ez("AAA");
    let eb = ez("bbb");
    let erb = &eb;
    let sc: String = "CcC".into();
    let src = &sc;
    let ld: &str = "dDd";

    let mut s = ea.clone();
    s += &ea;
    s += &ea;
    s += &eb;
    s += &erb;
    s += &sc;
    s += &src;
    s += &ld;
    s += &ea + &eb;

    assert!(*s == "AAAAAAAAAbbbbbbCcCCcCdDdAAAbbb");
    assert!(*ea == "AAA");
}

#[test]
fn equality() {
    let e = ez("AAA");
    let er = &e;
    let s = String::from("AAA");
    let sr = &s;
    let lit = "AAA";

    let e2 = &ez("A") + &ez("AA");
    let er2 = &e2;

    assert!(e == e);
    assert!(er == er);
    assert!(e == e2);
    assert!(er == er2);

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
}

#[test]
fn comparisons() {
    let a = ez("a");
    let b = ez("b");
    let c = ez("c");
    assert!(a < b && b < c);
    assert!(a <= a);
    assert!(!(a >= b));
    assert!(c > b && c >= a);
}

#[test]
fn ref_comparisons() {
    let a = &ez("a");
    let b = &ez("b");
    let c = &ez("c");
    assert!(a < b && b < c);
    assert!(a <= a);
    assert!(!(a >= b));
    assert!(c > b && c >= a);
}

#[test]
fn hashmap() {
    let mut m = HashMap::new();
    let e1 = ez("a") + &ez("aa");
    let e2 = ez("aaa");

    m.insert(e1.clone(), 1);
    m.insert(ez(""), 9);

    assert!(m[&e1] == 1);
    assert!(m[&e2] == 1);

    m.insert(e2.clone(), 2);
    assert!(m["aaa"] == 2);

    let s = "aaa".to_string();
    assert!(m[&s] == 2);
}

#[test]
fn cloning() {
    let ea = ez("AAA");
    let eb = ez("bbb");
    let rc = &ez("ccc");
    let rr = &rc;
    let rrr = &rr;

    consume(ea.clone());
    consume(rc.clone());
    consume(rc.clone());
    consume((*rc).clone());

    consume_ref(rc);
    consume_ref(rc);
    consume_ref(*rr);

    // consume(rr.clone());
    consume(rr.c());
    consume(rc.c());
    consume(ea.c());
    consume(rr.c());
    consume(rrr.c());

    consume(ea);
    consume(eb);
}

#[test]
fn slicing() {
    let s = ez("0123456789");

    assert!(s.ptr_eq(&s.substr(..)));
    assert!(s.substr(..) == "0123456789");
    assert!(s.substr(1..) == "123456789");
    assert!(s.substr(1..4) == "123");
    assert!(s.substr(..4) == "0123");
    assert!(s.substr(..s.len() - 2) == "01234567");

    let s2 = s.substr(3..);
    assert!(s2.substr(..3) == "345");

    assert!(&s[1..4] == "123");
}

#[test]
fn iters() {
    let s = "0123456789".to_string();
    let s = EZString::from(s);

    for _ in s.chars() {}
    for _ in s.chars() {}

    for c in s.lines() {
        let _: EZString = c;
    }

    let s2: Vec<_> = s.bytes().collect();
    assert_eq!(s2, s.as_bytes());
}

#[test]
fn iter_lifetimes() {
    let mut s = ez("0 1 234 56789");
    let it = s.split_whitespace();
    s += &"Hello, world!";

    for c in it {
        let s: EZString = c;
        assert!(s != "world!");
    }

    let v = s.split_whitespace().collect::<Vec<_>>();
    assert_eq!(v.last().unwrap(), "world!");
}

#[test]
fn split_lifetimes() {
    let mut s = ez("0--1-1--2");
    let mut p = ez("-");

    let it = s.split(&p);
    s += &"--33";
    p += p.clone();

    let it2 = s.split(&p);

    let expected = vec![ez("0"), ez(""), ez("1"), ez("1"), ez(""), ez("2")];
    assert_eq!(expected, it.collect::<Vec<_>>());

    let expected = vec![ez("0"), ez("1-1"), ez("2"), ez("33")];
    assert_eq!(expected, it2.collect::<Vec<_>>());
}

#[test]
fn rsplit() {
    let mut s = ez("0-1-2-3");
    let p = ez("-");

    assert_eq!(s.split(&p).next().unwrap(), "0");
    assert_eq!(s.rsplit(&p).next().unwrap(), "3");

    s += &p;
    assert_eq!(s.split_terminator(&p).next().unwrap(), "0");
    assert_eq!(s.rsplit_terminator(&p).next().unwrap(), "3");

    assert_eq!(s.splitn(3, &p).collect::<Vec<_>>(),
               vec![ez("0"), ez("1"), ez("2-3-")]);
    assert_eq!(s.rsplitn(3, &p).collect::<Vec<_>>(),
               vec![ez(""), ez("3"), ez("0-1-2")]);
}

#[test]
fn trim() {
    assert_eq!(ez("  hello \n ").trim(), "hello");
    let s = ez("  hello \n ").trim_right();
    assert_eq!(s, "  hello");
    assert_eq!(s.trim_left(), "hello");

    assert_eq!(ez("  hello   ").trim_matches(' '), "hello");
    let s = ez(" x xhello x x x").trim_right_matches(" x");
    assert_eq!(s, " x xhello");
    assert_eq!(s.trim_left_matches(" x"), "hello");
}

#[test]
fn double_ended() {
    let s = "0\n1\n2\n3".to_string();
    let s = EZString::from(s);

    assert_eq!(s.chars().next_back().unwrap(), '3');
    assert_eq!(s.lines().next_back().unwrap(), "3");
}

#[test]
fn cases() {
    let s = ez("Hello, World!");
    assert_eq!(s.to_lowercase(), "hello, world!");
    assert_eq!(s.to_uppercase(), "HELLO, WORLD!");
    assert_eq!(s.repeat(3), "Hello, World!Hello, World!Hello, World!");
}

#[test]
fn repeat() {
    let s = ez("x");
    assert_eq!(s.repeat(0), "");
    assert_eq!(s.repeat(1), "x");
    assert_eq!(s.repeat(2), "xx");
    assert_eq!(s.repeat(3), "xxx");
    assert_eq!(s.repeat(4), "xxxx");
    assert_eq!(s.repeat(44), "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
}

#[test]
fn inherited_methods() {
    let s = ez("x");
    assert_eq!(s.len(), 1);
    assert!(!s.is_empty());
}

#[test]
fn searching() {
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
}

fn fstr(_: &str) {}
fn fstring(_: String) {}
fn fstringref(_: &String) {}

#[test]
fn conversions() {
    let s = ez("");
    let r = &s;

    fstr(&s);
    fstr(&r);
    fstringref(&s);
    fstringref(&r);

    fstr(s.as_str());
    fstr(r.as_str());
    fstring(s.to_string());
    fstring(r.to_string());
    fstringref(s.as_string());
    fstringref(r.as_string());
}

fn split<'a, P: Into<Option<&'a str>>>(s: &EZString, sep: P) -> Vec<EZString> {
    match sep.into() {
        Some(sep) => s.split(sep).collect(),
        None => s.split_whitespace().collect(),
    }
}
fn split2<'a, P: Into<Option<&'a str>>>(s: &EZString, sep: P) -> Box<Iterator<Item = EZString>> {
    match sep.into() {
        Some(sep) => Box::new(s.split(sep)),
        None => Box::new(s.split_whitespace()),
    }
}
#[test]
fn python_split_func() {
    let s = ez("x  x-x 77x");
    assert_eq!(split(&s, "x"),
               vec![ez(""), ez("  "), ez("-"), ez(" 77"), ez("")]);
    assert_eq!(split(&s, None), vec![ez("x"), ez("x-x"), ez("77x")]);
}
