// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `#[fip_impl]`: certificates for methods of generic types and for trait-impl
//! methods, called from strict code; allocation behaviour measured.

#![forbid(unsafe_code)] // generated certificates still compile
#![allow(clippy::unnecessary_box_returns)]

use fip_macros::fip;
use fip_testkit::{assert_fip, assert_fip_n};

fip_testkit::install!();

mod shapes {
    use fip_macros::{fip, fip_impl, fip_trait};

    /// A generic slot.
    pub struct Slot<T> {
        pub v: T,
    }

    #[fip_impl]
    impl<T> Slot<T> {
        /// Generic method on a generic type: certificate `__fip_strict_Slot__put`.
        #[fip(strict = true)]
        pub fn put(&mut self, v: T) -> T {
            core::mem::replace(&mut self.v, v)
        }

        /// Calls another method through `Self`.
        #[fip(strict = true)]
        pub fn put_twice(&mut self, a: T, b: T) -> T {
            Self::put(self, a);
            Self::put(self, b)
        }

        /// Boxes the value: one allocation, certified with bound 1.
        #[fip_macros::fip(1, strict = true)]
        pub fn boxed(self) -> Box<T> {
            Box::new(self.v)
        }

        /// Not strict: no certificate, so strict code cannot call it.
        pub fn peek(&self) -> &T {
            &self.v
        }
    }

    /// A trait with an in-place step.
    #[fip_trait]
    pub trait Step {
        /// Advances in place, returns the previous state.
        #[fip(strict = true)]
        fn step(&mut self) -> u32;
    }

    /// A non-generic type.
    pub struct Ticker {
        pub n: u32,
    }

    #[fip_impl]
    impl Step for Ticker {
        /// Trait-impl method: certificate `__fip_strict_Ticker__Step__step`.
        #[fip(strict = true)]
        fn step(&mut self) -> u32 {
            let old = core::mem::replace(&mut self.n, 0);
            self.n = old + 1;
            old
        }
    }

    /// A generic trait impl covering every instantiation.
    #[fip_impl]
    impl<T> Step for Slot<T> {
        #[fip(strict = true)]
        fn step(&mut self) -> u32 {
            7
        }
    }

    /// A contract with `panic_macros = false`: an implementation must be checked
    /// with `panic_macros = false` too (`#[fip_impl]` compares the certificates).
    #[fip_trait]
    pub trait Peek {
        #[fip(strict = true, panic_macros = false)]
        fn peek_n(&self) -> u32;
    }

    #[fip_impl]
    impl Peek for Ticker {
        #[fip(strict = true, panic_macros = false)]
        fn peek_n(&self) -> u32 {
            self.n
        }
    }

    /// An inherent method with the same name as the trait method: `Ticker::step`
    /// is this one, `<Ticker as Step>::step` the trait's.
    #[fip_impl]
    impl Ticker {
        /// Inherent `step`, certificate `__fip_strict_Ticker__step`.
        #[fip(strict = true)]
        pub fn step(&mut self) -> u32 {
            self.n += 10;
            self.n
        }

        /// Calls the trait method through `<Self as Step>`.
        #[fip(strict = true)]
        pub fn trait_step(&mut self) -> u32 {
            <Self as Step>::step(self)
        }
    }
}

use shapes::{Slot, Step, Ticker};

/// Calls generic methods by a module path; the certificate is read from
/// `shapes::__fip_strict_Slot__put`.
#[fip(strict = true)]
fn swap_in(s: &mut Slot<u8>, a: u8) -> u8 {
    shapes::Slot::put(s, a)
}

/// `<Type<..>>::m` names the same certificate.
#[fip(1, strict = true)]
fn box_it(s: Slot<u16>) -> Box<u16> {
    <shapes::Slot<u16>>::boxed(s)
}

/// `Type::<..>::m` is `<Type<..>>::m` (before: "generic arguments in a callee path
/// cannot be resolved").
#[fip(1, strict = true)]
fn box_it_turbofish(s: Slot<u16>) -> Box<u16> {
    shapes::Slot::<u16>::boxed(s)
}

/// Trait method through `<Type as Trait>::m`, inherent one through `Type::m`.
#[fip(strict = true)]
fn both_steps(t: &mut Ticker) -> (u32, u32) {
    let a = <shapes::Ticker as Step>::step(t);
    let b = shapes::Ticker::step(t);
    (a, b)
}

/// Trait method of a generic impl.
#[fip(strict = true)]
fn slot_step(s: &mut Slot<u8>) -> u32 {
    <shapes::Slot<u8> as Step>::step(s)
}

/// Strict caller through `dyn Step`.
#[fip(strict = true)]
fn step_dyn(s: &mut dyn Step) -> u32 {
    s.step()
}

/// Strict caller through generic `S: Step`.
#[fip(strict = true)]
fn step_gen<S: Step>(s: &mut S) -> u32 {
    s.step()
}

#[test]
fn generic_and_trait_methods_are_callable_from_strict_code() {
    let mut s = Slot { v: 1_u8 };
    assert_eq!(assert_fip!(swap_in(&mut s, 2)), 1);
    assert_eq!(assert_fip!(s.put_twice(3, 4)), 3);
    assert_eq!(*s.peek(), 4);
    assert_eq!(*assert_fip_n!(1, box_it(Slot { v: 9 })), 9);
    assert_eq!(*assert_fip_n!(1, box_it_turbofish(Slot { v: 10 })), 10);
    let mut t = Ticker { n: 5 };
    assert_eq!(assert_fip!(both_steps(&mut t)), (5, 16));
    assert_eq!(assert_fip!(t.trait_step()), 16);
    assert_eq!(Step::step(&mut t), 17);
    assert_eq!(assert_fip!(step_dyn(&mut t)), 18);
    assert_eq!(assert_fip!(step_gen(&mut t)), 19);
    assert_eq!(assert_fip!(slot_step(&mut s)), 7);
    assert_eq!(assert_fip!(shapes::Peek::peek_n(&t)), 20);
}

#[test]
fn certificates_are_named_after_type_trait_and_method() {
    assert_eq!(shapes::__fip_strict_Slot__put.name(), "Slot__put");
    assert_eq!(shapes::__fip_strict_Slot__boxed.allocs(), 1);
    assert_eq!(
        shapes::__fip_strict_Ticker__Step__step.name(),
        "Ticker__Step__step"
    );
    assert_eq!(shapes::__fip_strict_Ticker__step.name(), "Ticker__step");
    assert_eq!(shapes::__fip_strict_Slot__Step__step.allocs(), 0);
    assert_eq!(__fip_strict_box_it.allocs_for("box_it"), 1);
    assert_eq!(shapes::__fip_strict_Step__step.name(), "Step__step");
    assert_eq!(<dyn Step>::__fip_strict_step.allocs(), 0);
    // Panic strictness is part of the certificate.
    assert!(!<dyn Step>::__fip_strict_step.no_panic_macros());
    assert!(<dyn shapes::Peek>::__fip_strict_peek_n.no_panic_macros());
    assert!(shapes::__fip_strict_Ticker__Peek__peek_n.no_panic_macros_for("Ticker__Peek__peek_n"));
    assert!(!shapes::__fip_strict_Ticker__step.no_panic_macros());
}
