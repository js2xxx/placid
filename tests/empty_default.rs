//! Regression tests for the empty `Default` impls of `Own` (issue #3).
//!
//! `Own::<str>::default()` and `Own::<[T]>::default()` fabricate an owned
//! reference to empty memory. Because `Own` exposes `DerefMut` (and drops via
//! `drop_in_place`), the fabricated pointer must never become a `&mut` into
//! read-only `'static` memory. These tests pin that down under Miri (run with
//! both Stacked and Tree Borrows).

// Explicitly forming `&mut *o` / `&*o` is the whole point of these tests.
#![allow(clippy::explicit_auto_deref)]

use placid::prelude::*;

// `Own` has an inherent `default(place)` that shadows the `Default` trait, so
// go through `Default::default` explicitly via these helpers.
fn str_default<'a>() -> Own<'a, str> {
    Default::default()
}
fn slice_default<'a>() -> Own<'a, [i32]> {
    Default::default()
}

#[test]
fn str_create_shared_drop() {
    let o = str_default();
    assert_eq!(&*o, "");
    drop(o);
}

#[test]
fn str_deref_mut() {
    let mut o = str_default();
    let m: &mut str = &mut *o;
    assert!(m.is_empty());
    // A real (zero-byte) mutation through the `&mut`.
    m.make_ascii_uppercase();
    drop(o);
}

#[test]
fn slice_create_shared_drop() {
    let o = slice_default();
    assert!(o.is_empty());
    drop(o);
}

#[test]
fn slice_deref_mut() {
    let mut o = slice_default();
    let m: &mut [i32] = &mut *o;
    m.iter_mut().for_each(|x| *x += 1);
    assert!(m.is_empty());
    drop(o);
}
