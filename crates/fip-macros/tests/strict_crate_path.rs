// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `crate = ..`: strict code generated against a re-export of `fip_strict` (as a
//! facade crate provides it) instead of `::fip_strict`. Every form of the argument
//! (`#[fip]`, `#[fip_impl]`, `fip_fn!`, path and string, inherited and overridden)
//! is used here; `tests/facade.rs` builds a consumer that has no `fip_strict` in
//! its extern prelude at all.

#![forbid(unsafe_code)] // generated code under a `crate = ..` path still compiles
#![allow(
    clippy::many_single_char_names,
    clippy::needless_pass_by_value,
    clippy::unnecessary_box_returns
)]

use fip_macros::{fip, fip_impl};
use fip_strict::FipFn;
use fip_testkit::{assert_fip, assert_fip_n};

fip_testkit::install!();

/// The items generated code names, re-exported as a facade crate root would.
mod shim {
    pub use fip_strict::{Cert, Certified, FipBound};
}

/// A facade that re-exports the whole crate.
mod facade {
    pub use fip_strict;
}

/// `fip_fn!` with the path filled in, as a facade's `macro_rules!` wrapper does it.
macro_rules! my_fip_fn {
    ($($t:tt)*) => { fip_macros::fip_fn!(crate = $crate::shim, $($t)*) };
}

#[fip(strict = true, crate = shim)]
fn swap2(a: &mut u8, b: &mut u8) {
    core::mem::swap(a, b);
}

#[fip(1, strict = true, crate = "facade::fip_strict")]
fn boxed(x: u8) -> Box<u8> {
    Box::new(x)
}

/// A `FipFn` parameter: the `FipBound` assertion goes through the path too.
#[fip(2, strict = true, param(g = 1), crate = crate::shim)]
fn apply<G: FipFn<(u8,), Output = Box<u8>>>(g: G, x: u8) -> (Box<u8>, Box<u8>) {
    (g.call((x,)), boxed(x))
}

/// Default path calling functions certified under another path: the certificates
/// are the same `fip_strict::Cert` type.
#[fip(strict = true)]
fn swap_twice(a: &mut u8, b: &mut u8) {
    swap2(a, b);
    swap2(a, b);
}

/// A slot whose strict methods are certified by `#[fip_impl(crate = ..)]`.
pub struct Slot<T> {
    v: T,
}

#[fip_impl(crate = self::facade::fip_strict)]
impl<T> Slot<T> {
    /// Inherits the block's path.
    #[fip(strict = true)]
    pub fn put(s: &mut Slot<T>, v: T) -> T {
        core::mem::replace(&mut s.v, v)
    }

    /// Its own path wins over the block's. Returns both old values (dropping a `T`
    /// here would be an implicit call).
    #[fip_macros::fip(strict = true, crate = shim)]
    pub fn put_twice(s: &mut Slot<T>, a: T, b: T) -> (T, T) {
        let first = Self::put(s, a);
        (first, Slot::put(s, b))
    }
}

fn allocs_of<G: fip_strict::FipBound>(_: &G) -> u64 {
    G::ALLOCS
}

#[test]
fn certificates_under_the_given_path() {
    assert_eq!(__fip_strict_swap2.allocs_for("swap2"), 0);
    assert_eq!(__fip_strict_boxed.allocs_for("boxed"), 1);
    assert_eq!(__fip_strict_apply.allocs_for("apply"), 2);
    assert_eq!(__fip_strict_swap_twice.allocs_for("swap_twice"), 0);
    assert_eq!(__fip_strict_Slot__put.allocs_for("Slot__put"), 0);
    assert_eq!(
        __fip_strict_Slot__put_twice.allocs_for("Slot__put_twice"),
        0
    );
}

#[test]
fn behaviour_is_unchanged() {
    let (mut a, mut b) = (1, 2);
    assert_fip!(swap2(&mut a, &mut b));
    assert_eq!((a, b), (2, 1));
    assert_fip!(swap_twice(&mut a, &mut b));
    assert_eq!((a, b), (2, 1));
    let mut s = Slot { v: 0_u8 };
    assert_eq!(assert_fip!(Slot::put_twice(&mut s, 5, 6)), (0, 5));
    assert_eq!(s.v, 6);
    // Called directly: `fip_testkit::summaries` does not follow a closure through a
    // user `macro_rules!`, so passing it to `apply` would be ⊤ for the checker.
    let g = my_fip_fn!(|x: u8| Box::new(x + 1));
    assert_eq!(allocs_of(&g), 1);
    let p = assert_fip_n!(1, g.call((3,)));
    assert_eq!(*p, 4);
    let h = fip_macros::fip_fn!(crate = facade::fip_strict, |x: u8| Box::new(x));
    let (p, q) = assert_fip_n!(2, apply(h, 7));
    assert_eq!((*p, *q), (7, 7));
}
