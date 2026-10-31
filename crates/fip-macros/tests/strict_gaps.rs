// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! What `strict = true` does not see, measured: these functions are accepted with
//! bound 0, and the counting allocator shows what they actually do. Each test pins a
//! gap recorded in `TODOs/strict-open-items.md` (items 5 and 6); if one starts to
//! fail, the gap has changed and the record must be updated.

#![allow(
    clippy::needless_pass_by_value,
    clippy::boxed_local,
    reason = "the measured functions take owned values on purpose"
)]

use fip_macros::fip;

fip_testkit::install!();

/// Implicit `Drop`: the `Box` argument is freed at the end of the body.
#[fip(strict = true)]
fn consume(b: Box<u8>) -> u8 {
    *b
}

/// A user type whose `+` allocates.
pub struct Big(Box<u64>);

impl core::ops::Add for Big {
    type Output = Big;
    fn add(self, o: Big) -> Big {
        Big(Box::new(*self.0 + *o.0))
    }
}

/// Overloaded operator: the call to `Add::add` is not visible to the macro.
#[fip(strict = true)]
fn sum(a: Big, b: Big) -> Big {
    a + b
}

/// A panicking macro (allowed unless `panic_macros = false`).
#[fip(strict = true)]
fn checked_dec(x: u8) -> u8 {
    assert!(x > 0, "x must be positive, got {x}");
    x - 1
}

#[test]
fn implicit_drop_is_accepted_and_counted_as_a_free() {
    let b = Box::new(3);
    let (v, s) = fip_testkit::measure(|| consume(b));
    assert_eq!(v, 3);
    assert_eq!((s.allocs, s.frees), (0, 1), "{s:?}");
}

#[test]
fn overloaded_operator_is_accepted_and_counted() {
    let (a, b) = (Big(Box::new(1)), Big(Box::new(2)));
    let (r, s) = fip_testkit::measure(|| sum(a, b));
    assert_eq!(*r.0, 3);
    assert_eq!((s.allocs, s.frees), (1, 2), "{s:?}");
}

#[test]
fn panic_path_allocates() {
    std::panic::set_hook(Box::new(|_| {}));
    let (r, s) = fip_testkit::measure(|| std::panic::catch_unwind(|| checked_dec(0)));
    let _ = std::panic::take_hook();
    assert!(r.is_err());
    assert!(s.allocs > 0, "{s:?}");
    assert_eq!(checked_dec(1), 0);
}
