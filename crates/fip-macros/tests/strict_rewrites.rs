// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Strict forms that still compile after the rewrites and rejections added for the
//! 2026-11-04 audit of the strict mode, with their allocation behaviour measured:
//! constructors (rewritten to `Name { 0: .. }`), panicking macros (emitted as
//! `::core::..`), ghost macros (emptied), `param(..)` and contract calls (emitted as
//! type-checked path calls), `while` headers, statement blocks followed by a tuple,
//! `<Type as path::Trait>::m` with the impl's own trait, and certificate names that
//! used to collide (`f` / `check_f`).

#![forbid(unsafe_code)]
#![allow(
    clippy::many_single_char_names,
    clippy::needless_pass_by_value,
    clippy::unnecessary_box_returns,
    clippy::trivially_copy_pass_by_ref
)]

use fip_macros::{fip, fip_fn, fip_impl};
use fip_strict::FipFn;
use fip_testkit::{assert_fip, assert_fip_n};

fip_testkit::install!();

/// A tuple struct and an enum with tuple variants.
#[derive(Debug, PartialEq, Eq)]
pub struct Pair(pub u8, pub u8);

/// A tuple variant and a unit variant.
#[derive(Debug, PartialEq, Eq)]
pub enum Shape {
    /// With a side.
    Square(u8),
    /// Without data.
    Dot,
}

/// Constructors in expressions and patterns, nested, in `match` scrutinees, `if`
/// conditions and `let` patterns.
#[fip(strict = true)]
fn ctors(x: u8) -> (Pair, Option<Shape>) {
    let Pair(a, b) = Pair(x, x ^ 1);
    let s = if Some(a) == Some(b) {
        None
    } else {
        Some(Shape::Square(a))
    };
    let t = match Some(Pair(a, b)) {
        Some(Pair(p, _)) if p > 3 => Some(Shape::Square(p)),
        Some(Pair(..)) => s,
        None => Some(Shape::Dot),
    };
    (Pair(b, a), t)
}

/// `assert!` is emitted as `::core::assert!` (a shadowing `macro_rules! assert`
/// that allocates is measured in the crate documentation's runnable example: here it
/// would also shadow `assert!` for `fip_testkit`'s crate-wide check of these tests).
#[fip(strict = true)]
fn checked(x: u8) -> u8 {
    assert!(x < 200);
    x + 1
}

/// A local `proof!` that would keep its contents: they are not compiled.
macro_rules! proof {
    ($($t:tt)*) => {
        $($t)*
    };
}

/// The ghost block would allocate if it were compiled.
#[fip(strict = true)]
fn ghost(x: u8) -> u8 {
    proof! {
        let _b = Box::new(1_u8);
    }
    x
}

/// `#[fip]` without `strict`: the same.
#[fip]
fn ghost_plain(x: u8) -> u8 {
    proof! {
        let _b = Box::new(1_u8);
    }
    x
}

/// `g.call(..)` and `FipFn::call(&g, ..)` on a declared parameter.
#[fip(strict = true, param(g = 0))]
fn apply_twice<G: FipFn<(u8,), Output = u8>>(g: G, x: u8) -> u8 {
    let y = g.call((x,));
    FipFn::call(&g, (y,))
}

/// A `while` condition calling a bound-0 strict function, a range `for`, and a block
/// statement followed by a tuple expression.
#[fip(strict = true)]
fn below(i: u8, n: u8) -> bool {
    i < n
}

#[fip(strict = true)]
fn loops(n: u8) -> (u8, u8) {
    let mut i = 0;
    while below(i, n) {
        i += 1;
    }
    let mut s = 0_u8;
    for k in 0..n {
        s ^= k;
    }
    if n > 0 {
        s ^= 1;
    }
    (i, s)
}

/// `::std::vec![a, b]`: one allocation.
#[fip(1, strict = true)]
fn two(a: u8, b: u8) -> Vec<u8> {
    ::std::vec![a, b]
}

/// A strict function `f` and one named `check_f` (before: both emitted
/// `__fip_strict_check_f`, E0428).
#[fip(strict = true)]
fn f(x: u8) -> u8 {
    x
}

#[fip(strict = true)]
fn check_f(x: u8) -> u8 {
    f(x)
}

mod traits {
    use fip_macros::{fip, fip_impl};

    /// Implemented by `Foo` under `#[fip_impl]`.
    pub trait Tr {
        fn m(&self) -> u8;
    }

    /// A second trait named like the first, in another module.
    pub mod other {
        /// Not implemented strictly.
        pub trait Tr {
            fn m(&self) -> u8;
        }
    }

    pub struct Foo(pub u8);

    #[fip_impl]
    impl Tr for Foo {
        #[fip(strict = true)]
        fn m(&self) -> u8 {
            self.0
        }
    }

    impl other::Tr for Foo {
        fn m(&self) -> u8 {
            self.0 ^ 0x64
        }
    }

    /// A trait implemented with a raw-identifier method.
    pub trait Kind {
        fn r#type(&self) -> u8;
    }

    #[fip_impl]
    impl Kind for Foo {
        #[fip(strict = true)]
        fn r#type(&self) -> u8 {
            <Self as Tr>::m(self)
        }
    }
}

use traits::*;

/// `<Type as path::Trait>::m` with the trait of the `#[fip_impl]` block.
#[fip(strict = true)]
fn through_path(x: &Foo) -> u8 {
    <Foo as traits::Tr>::m(x) + <traits::Foo as Kind>::r#type(x)
}

/// A plain trait (no `#[fip_trait]`) and a trait that is not dyn-compatible
/// (`Clone`): `#[fip_impl]` certifies their strict methods and compares nothing
/// (before: "no associated function or constant named `__fip_strict_get` found for
/// trait `dyn Plain`", "the trait `Clone` is not dyn compatible").
pub trait Plain {
    /// The value.
    fn get(&self) -> u32;
}

/// Implements [`Plain`].
pub struct Sq(pub u32);

#[fip_impl]
impl Plain for Sq {
    #[fip(strict = true)]
    fn get(&self) -> u32 {
        self.0
    }
}

/// Implements `Clone` strictly.
#[derive(Debug, PartialEq, Eq)]
pub struct D(pub u8);

#[fip_impl]
impl Clone for D {
    #[fip(strict = true)]
    fn clone(&self) -> Self {
        D(self.0)
    }
}

#[test]
fn constructors_compile_and_do_not_allocate() {
    assert_eq!(assert_fip!(ctors(5)), (Pair(4, 5), Some(Shape::Square(5))));
    assert_eq!(assert_fip!(ctors(1)), (Pair(0, 1), Some(Shape::Square(1))));
}

#[test]
fn shadowing_macros_are_not_what_runs() {
    assert_eq!(assert_fip!(checked(3)), 4);
    assert_eq!(assert_fip!(ghost(3)), 3);
    assert_eq!(assert_fip!(ghost_plain(3)), 3);
}

#[test]
fn rewritten_calls_behave_as_written() {
    assert_eq!(assert_fip!(apply_twice(fip_fn!(|x: u8| x ^ 1), 6)), 6);
    assert_eq!(assert_fip!(loops(4)), (4, 1));
    assert_eq!(assert_fip_n!(1, two(1, 2)), vec![1, 2]);
    assert_eq!(assert_fip!(check_f(9)), 9);
    assert_eq!(__fip_strict_check_f.allocs_for("check_f"), 0);
}

#[test]
fn trait_impls_without_contracts() {
    assert_eq!(assert_fip!(through_path(&Foo(2))), 4);
    assert_eq!(<Foo as traits::other::Tr>::m(&Foo(1)), 101);
    assert_eq!(assert_fip!(Sq(3).get()), 3);
    assert_eq!(assert_fip!(D(7).clone()), D(7));
}
