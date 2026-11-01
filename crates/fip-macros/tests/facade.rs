// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! End to end: a facade crate re-exports the macros and `fip_strict`, and a consumer
//! depends on the facade only, so `::fip_strict` does not exist for it. The two
//! crates are written to `CARGO_TARGET_TMPDIR` and built with a nested `cargo`
//! (offline; the workspace has no crates.io dependencies).
//!
//! - `crate = facade::fip_strict` on `#[fip]`, `#[fip_impl]` and `fip_fn!`, and the
//!   facade's `fip_fn!` wrapper (`macro_rules!`, fills in `$crate::fip_strict`);
//! - `extern crate facade as fip_strict;` once in the consumer: the default
//!   `::fip_strict` then names the facade, whose root re-exports `Cert`, `Certified`
//!   and `FipBound`, and no argument is needed;
//! - control: neither, and the build fails because `fip_strict` is not found.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const FACADE: &str = r"
pub use fip_macros::{fbip, fip, fip_impl};
pub use fip_strict;

/// What generated strict code names under `::fip_strict` / `crate = facade`.
#[doc(hidden)]
pub use fip_strict::{Cert, Certified, FipBound};

#[doc(hidden)]
pub use fip_macros::fip_fn as __fip_fn;

/// `fip_fn!` with this crate's `fip_strict` path filled in.
#[macro_export]
macro_rules! fip_fn {
    ($($t:tt)*) => { $crate::__fip_fn!(crate = $crate::fip_strict, $($t)*) };
}
";

/// Consumer with explicit `crate = ..` arguments.
const EXPLICIT: &str = r#"
#![forbid(unsafe_code)]
use facade::fip_strict::FipFn;
use facade::{fip, fip_impl};

pub struct Slot { v: u8 }

#[fip_impl(crate = facade::fip_strict)]
impl Slot {
    #[facade::fip(strict = true)]
    pub fn put(s: &mut Slot, v: u8) -> u8 { core::mem::replace(&mut s.v, v) }
}

#[fip(strict = true, crate = facade::fip_strict)]
fn swap2(a: &mut u8, b: &mut u8) { core::mem::swap(a, b) }

#[fip(1, strict = true, crate = "facade::fip_strict")]
fn boxed(x: u8) -> Box<u8> { Box::new(x) }

#[fip(2, strict = true, param(g = 1), crate = ::facade::fip_strict)]
fn apply<G: FipFn<(u8,), Output = u8>>(g: G, x: u8) -> (u8, Box<u8>) {
    let mut s = Slot { v: 0 };
    let old = Slot::put(&mut s, x);
    (g.call((old,)), boxed(s.v))
}

fn main() {
    let (mut a, mut b) = (1, 2);
    swap2(&mut a, &mut b);
    let (r, bx) = apply(facade::fip_fn!(|x: u8| x + 1), 5);
    let (r2, _) = apply(facade::__fip_fn!(crate = facade::fip_strict, |x: u8| x + 2), 5);
    println!("{a} {b} {r} {} {r2} {}", *bx, __fip_strict_apply.allocs_for("apply"));
}
"#;

/// Consumer with one `extern crate` alias and no arguments.
const ALIAS: &str = r#"
#![forbid(unsafe_code)]
extern crate facade as fip_strict;
use facade::{fip, fip_impl};

pub struct Slot { v: u8 }

#[fip_impl]
impl Slot {
    #[fip(strict = true)]
    pub fn put(s: &mut Slot, v: u8) -> u8 { core::mem::replace(&mut s.v, v) }
}

#[fip(strict = true)]
fn swap2(a: &mut u8, b: &mut u8) { core::mem::swap(a, b) }

#[fip(1, strict = true)]
fn boxed(x: u8) -> Box<u8> { Box::new(x) }

mod inner {
    #[facade::fip(2, strict = true, param(g = 1))]
    pub fn apply<G: facade::fip_strict::FipFn<(u8,), Output = u8>>(g: G, x: u8) -> (u8, Box<u8>) {
        let mut s = super::Slot { v: 0 };
        let old = super::Slot::put(&mut s, x);
        (g.call((old,)), super::boxed(s.v))
    }
}

fn main() {
    let (mut a, mut b) = (1, 2);
    swap2(&mut a, &mut b);
    let (r, bx) = inner::apply(facade::__fip_fn!(|x: u8| x + 1), 5);
    let (r2, _) = inner::apply(facade::fip_fn!(|x: u8| x + 2), 5);
    println!("{a} {b} {r} {} {r2} {}", *bx, inner::__fip_strict_apply.allocs_for("apply"));
}
"#;

/// Control: no argument, no alias.
const NEITHER: &str = r"
use facade::fip;
#[fip(strict = true)]
fn swap2(a: &mut u8, b: &mut u8) { core::mem::swap(a, b) }
fn main() { let (mut a, mut b) = (1, 2); swap2(&mut a, &mut b); }
";

fn crates_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/")
        .to_path_buf()
}

/// Writes the consumer `consumer-<name>` (with `facade/` inside it) and returns its
/// dir. The fixtures share a target dir, so each consumer needs its own package name:
/// cargo fingerprints path packages by their path relative to the workspace root, and
/// same-named consumers would be taken for one another (measured: the control was
/// reported built from another fixture's artifacts).
fn fixture(name: &str, main: &str) -> PathBuf {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join("facade-fixture");
    let consumer = root.join(name);
    let facade = consumer.join("facade");
    fs::create_dir_all(facade.join("src")).expect("mkdir facade");
    fs::create_dir_all(consumer.join("src")).expect("mkdir consumer");
    let crates = crates_dir();
    let dep = |c: &str| crates.join(c).display().to_string().replace('\\', "/");
    fs::write(
        facade.join("Cargo.toml"),
        format!(
            "[package]\nname = \"facade\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [dependencies]\nfip-macros = {{ path = \"{}\" }}\nfip-strict = {{ path = \"{}\" }}\n",
            dep("fip-macros"),
            dep("fip-strict")
        ),
    )
    .expect("write facade manifest");
    fs::write(facade.join("src/lib.rs"), FACADE).expect("write facade");
    fs::write(
        consumer.join("Cargo.toml"),
        format!(
            "[package]\nname = \"consumer-{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [dependencies]\nfacade = {{ path = \"facade\" }}\n\n[workspace]\n"
        ),
    )
    .expect("write consumer manifest");
    fs::write(consumer.join("src/main.rs"), main).expect("write consumer");
    consumer
}

fn cargo(dir: &Path, cmd: &str) -> Output {
    let target = Path::new(env!("CARGO_TARGET_TMPDIR")).join("facade-fixture/target");
    Command::new(env!("CARGO"))
        .args([cmd, "-q", "--offline", "--target-dir"])
        .arg(target)
        .current_dir(dir)
        .output()
        .expect("run cargo")
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// The consumer really has no `fip_strict`: the dependency graph lists only the facade.
fn assert_only_facade(dir: &Path) {
    let manifest = fs::read_to_string(dir.join("Cargo.toml")).expect("read manifest");
    assert!(!manifest.contains("fip-strict") && !manifest.contains("fip-macros"));
}

#[test]
fn explicit_crate_path() {
    let dir = fixture("explicit", EXPLICIT);
    assert_only_facade(&dir);
    let o = cargo(&dir, "run");
    assert!(o.status.success(), "{}", stderr(&o));
    assert_eq!(String::from_utf8_lossy(&o.stdout).trim(), "2 1 1 5 2 2");
}

#[test]
fn extern_crate_alias() {
    let dir = fixture("alias", ALIAS);
    assert_only_facade(&dir);
    let o = cargo(&dir, "run");
    assert!(o.status.success(), "{}", stderr(&o));
    assert_eq!(String::from_utf8_lossy(&o.stdout).trim(), "2 1 1 5 2 2");
}

#[test]
fn neither_fails_without_fip_strict() {
    let dir = fixture("neither", NEITHER);
    assert_only_facade(&dir);
    let o = cargo(&dir, "build");
    assert!(
        !o.status.success(),
        "built without a `fip_strict` path: {}",
        stderr(&o)
    );
    assert!(
        stderr(&o).contains("could not find `fip_strict`"),
        "{}",
        stderr(&o)
    );
}
