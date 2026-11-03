// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Runs `cargo fip-prelint --message-format short` on every workspace under
//! `tests/fixtures/` and compares its diagnostics with `expected.txt` there (or
//! `expected-<variant>.txt` for a run with extra environment variables).
//!
//! Compared: every line mentioning `fip-prelint` and every rustc error code line
//! (`error[E..]`), sorted and deduplicated (cargo checks `lib` and `lib test`), plus
//! the exit status (`exit: success` / `exit: failure`, first line). Lines starting with
//! `#` in `expected.txt` are comments. `FIP_PRELINT_BLESS=1` rewrites the files.

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

fn run(name: &str, variant: &str, envs: &[(&str, std::ffi::OsString)]) -> Vec<String> {
    run_args(name, variant, envs, &["--message-format", "short"])
}

fn run_args(
    name: &str,
    variant: &str,
    envs: &[(&str, std::ffi::OsString)],
    args: &[&str],
) -> Vec<String> {
    let dir = fixtures_dir().join(name);
    let target = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("fixtures")
        .join(format!("{name}{variant}"));
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-fip-prelint"));
    cmd.arg("fip-prelint")
        .args(args)
        .current_dir(&dir)
        .env("FIP_PRELINT_TARGET_DIR", &target)
        .env("FIP_PRELINT_DRIVER_PATH", env!("CARGO_BIN_EXE_fip-prelint"))
        .env_remove("FIP_PRELINT_WARN_ONLY")
        .env_remove("FIP_PRELINT_DUMP")
        .env_remove("FIP_PRELINT_DUMP_MIR")
        .env_remove("FIP_PRELINT_STD_SUMMARIES")
        .env_remove("FIP_PRELINT_STD_SUMMARIES_OUT")
        .env_remove("FIP_PRELINT_STACK")
        .env_remove("FIP_MACROS_MARK_ONLY")
        .env_remove("CARGO_TARGET_DIR");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("run cargo-fip-prelint");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let mut lines: Vec<String> = stderr
        .lines()
        .filter(|l| l.contains("fip-prelint") || l.contains("error[E"))
        .filter(|l| {
            !l.trim_start().starts_with("Checking") && !l.trim_start().starts_with("Compiling")
        })
        .map(|l| l.trim_end().to_string())
        .collect();
    lines.sort();
    lines.dedup();
    let status = if out.status.success() {
        "exit: success"
    } else {
        "exit: failure"
    };
    let mut v = vec![status.to_string()];
    v.extend(lines);
    v
}

fn check(name: &str) {
    check_with(name, "", &[]);
}

/// `check` with extra environment variables, compared with `expected{variant}.txt`.
fn check_with(name: &str, variant: &str, envs: &[(&str, std::ffi::OsString)]) {
    compare(name, variant, &run(name, variant, envs));
}

/// Compares (or blesses) `got` with `expected{variant}.txt`.
fn compare(name: &str, variant: &str, got: &[String]) {
    let got = got.to_vec();
    let path = fixtures_dir()
        .join(name)
        .join(format!("expected{variant}.txt"));
    if std::env::var("FIP_PRELINT_BLESS").is_ok_and(|v| v == "1") {
        let mut text = String::from(
            "# Expected `cargo fip-prelint --message-format short` diagnostics (tests/fixtures.rs).\n",
        );
        for l in &got {
            text.push_str(l);
            text.push('\n');
        }
        std::fs::write(&path, text).expect("write the expected file");
        return;
    }
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: {e} (run with FIP_PRELINT_BLESS=1)", path.display()));
    let want: Vec<String> = text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| l.trim_end().to_string())
        .collect();
    if got != want {
        let missing: Vec<&String> = want.iter().filter(|l| !got.contains(l)).collect();
        let extra: Vec<&String> = got.iter().filter(|l| !want.contains(l)).collect();
        panic!(
            "fixture `{name}` differs from expected{variant}.txt\nmissing:\n{}\nunexpected:\n{}",
            missing
                .iter()
                .map(|s| format!("  {s}"))
                .collect::<Vec<_>>()
                .join("\n"),
            extra
                .iter()
                .map(|s| format!("  {s}"))
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
}

/// `Box::new` directly, through an exported callee, through a non-exported one (`⊤`),
/// through a `use` alias.
#[test]
fn cross_crate() {
    check("cross_crate");
}

/// Implicit `Drop` (accepted by the token-level `#[fip]`), an allocating `Add` used
/// via `+`, indexing panics under `panic_macros = false`, method resolution.
#[test]
fn implicit() {
    check("implicit");
}

/// Bounds, overflow and division checks behind guards (value analysis): guarded
/// index, `while i < xs.len()` and `for i in 0..xs.len()` loops, a second counter
/// bounded by the first, `x - 1` after `x == 0` returns, `d != 0` division pass;
/// unguarded, off-by-one, guards on another variable, a local changed through
/// `&mut`, a replaced slice, `0..=len`, signed `i - 1` under `i < 0` are reported.
/// Values returned by calls (return summaries): `usize::from(u8)`, a wrapper's
/// `len`/`get`/`is_empty` over a `Vec` field, `len() - 1` after `is_empty()`,
/// `count_ones` (intrinsic table) pass; `usize::from(u16)`, a `Cell`-backed `len`, a
/// replaced reference, a `&mut` wrapper changed in between are reported. Iterator
/// contracts: `(0..len).rev()`, `0..=len - 1` after `is_empty`, `enumerate` indexing
/// a longer slice, a counter of `zip`'s items pass; off-by-one controls of each are
/// reported.
#[test]
fn guards() {
    check("guards");
}

/// Generic instantiation, closure arguments, higher-order roots, `fip(N)` bounds and
/// the loop rule, recursion through two functions; drops of generic values through
/// their glue (`Vec<T>`, `Box<T>` may free; `Option<T>`, `T` are the term `drop(T)`;
/// a glue rustc cannot build for the generic type is `⊤`, without aborting).
#[test]
fn generics() {
    check("generics");
}

/// `fip::exprot`, `fip::mrak` and a malformed mark are rejected.
#[test]
fn bad_attr() {
    check("bad_attr");
}

/// Defence in depth: a dependency whose `fip::export` is active (injected by RUSTFLAGS)
/// although it was compiled without `-Zalways-encode-mir`: a hard error naming the
/// crate, and the call is unresolved, never 0.
#[test]
fn export_unencoded() {
    check("export_unencoded");
}

/// Path dependencies that are not workspace members, as other projects consume
/// portable-fip: the one declaring `fip::export` is compiled with the driver's flags
/// and analysed (allocation found, allocation-free callee passes); the other is ⊤.
#[test]
fn nonmember_export() {
    check("nonmember_export");
}

/// Export detection from the crate root's parsed inner attributes (limits plan L10c):
/// `fip::export` in a `cfg_attr` with several attributes, with a comment inside, and
/// nested under a combined predicate is found (the dependencies are analysed); the
/// attribute's text in comments and a raw string is not (the dependency is passed
/// through to the real rustc, and calls into it are `⊤`).
#[test]
fn export_detection() {
    check("export_detection");
}

/// Declared parameter bounds at call sites (`param(g = K)`): the reproducer of
/// `TODOs/fip-prelint.md` (a non-root caller, a `#[fip]` and a `#[fip(1)]` root passing
/// an allocating `fip_fn!` for `param(g = 0)`), and the argument kinds: allocation-free
/// and allocating closures, a named function, a function pointer (`⊤`), a generic
/// forwarder instantiated from a root, a root's own `param(h = K)` forwarded, a call
/// inside a closure. Function pointers and `&dyn Fn` with a declared bound (limits plan
/// L4): the call through the parameter costs `K`; a function reified or a closure
/// unsized at the call site is checked (passes or is reported), a pointer loaded from
/// data or an undeclared parameter is `⊤` at the call site, a declared one passed on is
/// checked against its own bound; an argument that frees or recurses under a `fip`
/// callee is reported, and a `fip` root calling an `fbip` callee with a bound argument
/// gets what that argument does (top plan B). A generic `G` instantiated with a
/// function pointer (top plan T3): its `Fn` shim is bound to a local reification or a
/// declared parameter (passes; an allocating one is reported at the call site).
/// Private functions passing an undeclared parameter on (top plan T4.3): not reported
/// on their own; each call site checks them with what it passes (an allocating or
/// unknown argument is reported at the private function's call); `pub` and reified
/// ones keep the report.
#[test]
fn param_bounds() {
    check("param_bounds");
}

/// Allocation and free sources (limits plan L7), from the allocator probe: marked
/// arena and slab in an exported crate (one allocation, `∞` in a loop, a free,
/// `alloc_source(n = 2)`, `fbip`), the unmarked arena as the pinned residue (passes),
/// a source whose body loops, recurses and allocates (counts 1, nothing from its body),
/// a source declared on a trait method (an implementation and a generic call),
/// `GlobalAlloc` methods called directly, by default body and through `dyn`, the
/// system allocator, foreign `malloc`/`free`, a marked foreign function, an unknown
/// one (`⊤`), a Rust function named `malloc`; rejected: a FIP mark on a source or on
/// a `GlobalAlloc` method, `n = 0`, unknown keys, a misplaced source mark.
#[test]
fn alloc_sources() {
    check("alloc_sources");
}

/// Declared preconditions and callee contexts (limits plan L1): `fip::requires`
/// established by guards or constants passes, a root is checked under its own; a
/// call site that does not establish it, a function with a precondition used as a
/// value, `split_at_mut` without `j < len`, and a callee whose context is too weak
/// are reported; an allocation hidden behind a broken precondition is counted;
/// malformed and unsatisfiable preconditions are errors.
#[test]
fn preconditions() {
    check("preconditions");
}

/// Drops are frees only when their drop glue deallocates (limits plan L12): `Cell`,
/// a `RefMut` store and a user guard pass; dropping an `Rc` may free. Interior
/// mutability and dynamic uniqueness are out of scope (limits plan L8); pinned:
/// `Cell::replace`, two aliasing `&Cell`, an `UnsafeCell` write, `try_borrow_mut`,
/// `Rc::get_mut` and `Rc::clone` pass; a `Box` taken out of a `Cell` and dropped
/// frees; `Rc::new` allocates; `RefCell::borrow`/`borrow_mut` are panic paths (errors
/// under `strict = true, panic_macros = false`, allowed otherwise).
#[test]
fn cells() {
    check("cells");
}

/// Function pointers and trait objects (limits plan L4): resolved from one origin on
/// every path of the body (a reified function or closure, an unsized concrete type),
/// `⊤` for two origins, data or an unknown receiver; contracts on trait methods: a
/// dynamic call costs the contract (`n`, panic paths of a non-strict contract), every
/// implementation is checked in its crate (a default body for each impl keeping it),
/// one in a crate without `fip::export` is `⊤`, `param(..)` and `fip::requires(..)`
/// in a contract are rejected. Contracts are written with `#[fip]` (`Shape::area`, the
/// default body `Scaled::scaled`) or by hand (`Grow::grow`, the strict `Pick::pick`):
/// the same mark. An implementation's own mark weaker than the contract is rejected;
/// an implementation is checked against a contract without its own precondition.
/// `&Box<dyn Fn>` parameters (top plan T2): with `param(g = 0)` the call through the
/// box passes and call sites are checked (a box of an allocating function is
/// reported); undeclared, and `Rc<dyn Fn>`, stay `⊤`.
#[test]
fn indirect() {
    check("indirect");
}

/// Function pointers loaded from immutable data (top plan T1.1–T1.3): a constant, an
/// immutable static, static tables (every element a candidate, the maximum counted;
/// a constant index selects one), a field of a static struct, a constant slice, a
/// dependency's static table, fields of local aggregates; the same at call sites of a
/// callee with `param(p = 0)`. Interior mutability, `static mut`, an atomic, a local
/// written in part and a parameter's field stay `⊤`. Crate `certs` (top plan T1.4):
/// calls through `fip_strict::Certified<N, fn(..)>` fields cost `N` (and a panic
/// path); every analysed `Certified::assume` is checked against `N` (an allocating or
/// freeing function is an error there, a pointer of unknown origin or a generic
/// callable type `⊤`, a declared parameter passes and its callers are checked).
#[test]
fn indirect_data() {
    check("indirect_data");
}

/// Callable parameters bound at their call sites (top plan B): callees without
/// `param(..)` analysed with the function, table candidates, trait object type or
/// declared parameter the call site passes; three nested bound callees pass, a fourth
/// falls back to no binding (`⊤`); an undeclared parameter passed on stays `⊤`.
#[test]
fn callable_binds() {
    check("callable_binds");
}

/// A dependency declaring `fip::export` (not a workspace member, compiled without
/// roots) whose implementation breaks a trait method's contract: rejected where it
/// is compiled (limits plan L4).
#[test]
fn contract_dep() {
    check("contract_dep");
}

/// Generated std summaries (limits plan L6, sidecar of L10e): `write!` into a fixed
/// buffer through a local `fmt::Write` impl (integers, strings, a user `Display`
/// writing through the `Formatter`) passes; `format!` is a violation (allocations,
/// a free) without `⊤`; `{:?}` of a derived `Debug` (`&dyn Debug` inside `core`) stays
/// `⊤`; under `strict = true` the bounds checks inside `core`'s integer formatting
/// are panic paths.
#[test]
fn std_summaries() {
    check("std_summaries");
}

/// The same crate with a std summaries file stamped for another compiler: not used,
/// every function without MIR stays `⊤` (never a silent pass).
#[test]
fn std_summaries_stale() {
    let stale = fixtures_dir()
        .join("std_summaries")
        .join("stale-summaries.txt");
    check_with(
        "std_summaries",
        "-stale",
        &[("FIP_PRELINT_STD_SUMMARIES", stale.into_os_string())],
    );
}

/// The same crate for `wasm32-unknown-unknown` with that target's sidecar (top plan
/// T7j): the formatting results equal the host's; the `std::sys` paths differ by
/// platform (no OS random source, no foreign calls, no thread-local destructors), so
/// `hashmap_new`, the thread locals and the FFI marks have their own expectations.
/// Skipped if the target's `std` is not installed.
#[test]
fn std_summaries_wasm32() {
    let triple = "wasm32-unknown-unknown";
    let out = Command::new("rustc")
        .env(
            "RUSTUP_TOOLCHAIN",
            std::env::var("FIP_PRELINT_TOOLCHAIN").unwrap_or_else(|_| "1.99.1".to_string()),
        )
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc --print sysroot");
    let sysroot = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    if !sysroot.join("lib").join("rustlib").join(triple).is_dir() {
        eprintln!("std_summaries_wasm32: `{triple}` not installed, skipped");
        return;
    }
    compare(
        "std_summaries",
        "-wasm32",
        &run_args(
            "std_summaries",
            "-wasm32",
            &[],
            &["--message-format", "short", "--target", triple],
        ),
    );
}

/// The analysis cache is keyed on the std summaries' content, not only on their
/// modification time. Fixture `sidecar_cache`, one target directory, one
/// `FIP_PRELINT_STD_SUMMARIES` path: first the real sidecar (the root passes, so cargo
/// caches the result), then the stale one with the same (old) modification time. The
/// second run must re-check (`⊤`), not replay the first run's success from the cache.
/// Without the content key in `FIP_PRELINT_INPUTS_ID` the second run passed (measured).
#[test]
fn std_summaries_cache_key() {
    if !cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        eprintln!("std_summaries_cache_key: x86_64 Linux only (the host sidecar)");
        return;
    }
    let real = std::fs::read_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("std-summaries"))
        .expect("std-summaries directory")
        .flatten()
        .map(|e| e.path())
        .find(|p| {
            p.file_name().is_some_and(|n| {
                n.to_string_lossy()
                    .ends_with("-x86_64-unknown-linux-gnu.txt")
            })
        })
        .expect("the x86_64 Linux sidecar");
    let stale = fixtures_dir()
        .join("std_summaries")
        .join("stale-summaries.txt");
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("sidecar-cache");
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(
        Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("fixtures")
            .join("sidecar_cache"),
    );
    std::fs::create_dir_all(&dir).expect("create the sidecar directory");
    let path = dir.join("summaries.txt");
    let old = std::time::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000_000);
    let put = |from: &Path| {
        std::fs::copy(from, &path).expect("copy the sidecar");
        std::fs::File::options()
            .write(true)
            .open(&path)
            .and_then(|f| f.set_modified(old))
            .expect("set the sidecar's modification time");
    };
    let envs = [("FIP_PRELINT_STD_SUMMARIES", path.clone().into_os_string())];
    put(&real);
    compare("sidecar_cache", "-real", &run("sidecar_cache", "", &envs));
    put(&stale);
    compare("sidecar_cache", "-stale", &run("sidecar_cache", "", &envs));
}

/// The profile's semantics (top plan T14.1): the driver analyses with the overflow
/// checks and debug assertions of the profile, not those `-Copt-level=0` implies. In
/// dev both crates have an overflow check and a `debug_assert!` panic path; under
/// `--release` only `checked` (`[profile.release.package.checked] overflow-checks =
/// true`) keeps its overflow check, and neither has the debug assertion.
#[test]
fn profiles() {
    for (variant, extra) in [("-dev", &[][..]), ("-release", &["--release"][..])] {
        let mut args = vec!["--message-format", "short"];
        args.extend_from_slice(extra);
        compare(
            "profiles",
            variant,
            &run_args("profiles", variant, &[], &args),
        );
    }
}

/// Stack bounds (limits plan L9, top plan T8): `cargo fip-prelint --stack` in the dev
/// profile (opt-level 0) and with `--release` (opt-level 3), target
/// x86_64-unknown-linux-gnu, rustc 1.99.1; the expected bounds hold for these builds
/// only. A three-level chain with arrays, an index (its panic path excluded) and a
/// slice iterator (through the `precondition_check` functions codegen calls) are
/// bounded; recursion, a dynamic call, a function pointer, a foreign function, a
/// precompiled std function, `memcpy`, an allocation and a generic root without an
/// instance are `⊤` with the reason, where the build has them (at opt-level 3 the
/// recursion became a loop and `labs` an instruction; with
/// `-Zcross-crate-inline-threshold=never` every root has a symbol, T8d). Crate `leafy`
/// declares `memcpy` a stack leaf (T8b) and instantiates `chain::generic::<u32>`
/// (bounded per instance, T8e). Variants: `-tests` (`--lib --tests`: the test target's
/// objects add `chain::generic::<u8>`, T8f), `-aarch64` (`--target
/// aarch64-unknown-linux-gnu`, AArch64 ELF, return address 0, T8a; skipped if not
/// installed), `-buildstd` (`--build-std`: the std functions are built and bounded,
/// down to the foreign `getpid`/`memcpy`, T8c). If the system `llvm-readobj` exists,
/// each bound of `chain_top` (dev, release, aarch64) is checked to be at least the sum
/// of its chain's frame sizes as `llvm-readobj --stack-sizes` reads them.
#[test]
fn stack() {
    if !cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        eprintln!("stack fixture: x86_64 Linux only (the expected bounds are for that build)");
        return;
    }
    let out = Command::new("rustc")
        .env(
            "RUSTUP_TOOLCHAIN",
            std::env::var("FIP_PRELINT_TOOLCHAIN").unwrap_or_else(|_| "1.99.1".to_string()),
        )
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc --print sysroot");
    let sysroot = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    let aarch64 = "aarch64-unknown-linux-gnu";
    let has_aarch64 = sysroot.join("lib").join("rustlib").join(aarch64).is_dir();
    let variants: [(&str, &[&str], Option<&str>); 5] = [
        ("-dev", &[], Some("debug")),
        ("-release", &["--release"], Some("release")),
        ("-tests", &["--lib", "--tests"], None),
        (
            "-aarch64",
            &["--target", aarch64],
            Some("aarch64-unknown-linux-gnu/debug"),
        ),
        ("-buildstd", &["--build-std"], None),
    ];
    for (variant, extra, cross_check) in variants {
        if variant == "-aarch64" && !has_aarch64 {
            eprintln!("stack fixture{variant}: `{aarch64}` not installed, skipped");
            continue;
        }
        let mut args = vec!["--stack"];
        args.extend_from_slice(extra);
        let got = run_args("stack", variant, &[], &args);
        compare("stack", variant, &got);
        let Some(profile) = cross_check else {
            continue;
        };
        let bound: u64 = got
            .iter()
            .find_map(|l| {
                l.split("`chain_top` uses at most ")
                    .nth(1)?
                    .split(' ')
                    .next()?
                    .parse()
                    .ok()
            })
            .expect("a bound for chain_top");
        let rlib = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("fixtures")
            .join(format!("stack{variant}"))
            .join(profile)
            .join("libchain.rlib");
        match Command::new("llvm-readobj")
            .args(["--stack-sizes"])
            .arg(&rlib)
            .output()
        {
            Ok(out) if out.status.success() => {
                let text = String::from_utf8_lossy(&out.stdout);
                let mut sum = 0u64;
                let mut current: Option<String> = None;
                for line in text.lines() {
                    let line = line.trim();
                    if let Some(f) = line.strip_prefix("Functions: [") {
                        current = Some(f.trim_end_matches(']').to_string());
                    } else if let Some(size) = line.strip_prefix("Size: 0x")
                        && let Some(f) = current.take()
                        && ["5chain9chain_top", "5chain3mid", "5chain4leaf"]
                            .iter()
                            .any(|n| f.ends_with(n))
                    {
                        sum += u64::from_str_radix(size, 16).expect("a hex size");
                    }
                }
                assert!(sum > 0, "llvm-readobj found no frame of the chain");
                assert!(
                    bound >= sum,
                    "bound {bound} of chain_top{variant} below the llvm-readobj frame sum {sum}"
                );
                eprintln!("stack fixture{variant}: bound {bound} >= llvm-readobj frame sum {sum}");
            }
            _ => {
                eprintln!("stack fixture{variant}: llvm-readobj not available, cross-check skipped")
            }
        }
    }
}

/// Pool hints (top plan T17): the default run has no hint; with `--pool-hints` the
/// unmarked `Pool::alloc` and `Bump::alloc` of the exported crate get a heuristic note,
/// the marked arena, the stack, the cursor and the unexported crate's arena do not.
/// Without the hint lines, the `--pool-hints` output equals the default output (same
/// verdicts, counts and exit status).
#[test]
fn pool_hints() {
    let default = run("pool_hints", "", &[]);
    compare("pool_hints", "", &default);
    let hints = run_args(
        "pool_hints",
        "-hints",
        &[],
        &["--message-format", "short", "--pool-hints"],
    );
    compare("pool_hints", "-hints", &hints);
    let without: Vec<String> = hints
        .iter()
        .filter(|l| !l.contains("fip-prelint: heuristic: "))
        .cloned()
        .collect();
    assert_eq!(without, default, "--pool-hints changed more than its notes");
    assert!(
        hints.iter().any(|l| l.contains("heuristic: ")),
        "--pool-hints printed no hint"
    );
    assert!(
        !default.iter().any(|l| l.contains("heuristic")),
        "a hint without --pool-hints"
    );
}

#[test]
fn clean() {
    check("clean");
}

/// Foreign functions: certified, excluded, neither, both.
#[test]
fn ffi() {
    check("ffi");
}

/// Constructor spellings the token rule cannot resolve (inferred type, type alias)
/// are decided by the driver; the audited non-allocating spellings pass.
#[test]
fn ctor_spellings() {
    check("ctor_spellings");
}

/// The error of `fip_fn!(prelint, ..)` outside a checking driver run (`fip-macros`).
const PRELINT_UNCHECKED: &str = "fip_fn!(prelint, ..) is checked only by `cargo fip-prelint`";

/// The driver-checked `fip_fn!(prelint, N, ..)`
/// (`docs/decisions/2026-11-03-fip-fn-driver-mode.md`). Check run: in crate `checked`
/// a method call, an inferred local, two parameters and an honest bound pass; a lie
/// about the allocations, a recursion, a freed argument and a box dropped inside the
/// closure are reported at the construction; in a generic function the allocating
/// closure is reported by the same check, and both constructions there also get the
/// existing `Certified::assume` check's `⊤` for a generic callable type (as the
/// default `fip_fn!` does in a generic function). The three driver runs that
/// compile without checking must not accept the mode (`FIP_PRELINT_CHECKS` unset by
/// the driver): the non-member dependency `drvdep` declaring `fip::export`
/// (`Role::ExportedDependency`, in the check run), stack mode (`-stack`) and
/// std-summary generation (`-generate`, `FIP_PRELINT_STD_SUMMARIES_OUT` set) all fail
/// with the `fip-macros` error; stack mode with `FIP_PRELINT_CHECKS=1` inherited from
/// the environment fails the same way (the driver removes it).
#[test]
fn driver_checked() {
    let unchecked_at = |got: &[String], file: &str| {
        got.iter()
            .any(|l| l.contains(file) && l.contains(PRELINT_UNCHECKED))
    };
    let check_run = run("driver_checked", "", &[]);
    compare("driver_checked", "", &check_run);
    assert!(
        unchecked_at(&check_run, "drvdep/src/lib.rs"),
        "an exported dependency accepted fip_fn!(prelint, ..): {check_run:#?}"
    );
    assert!(
        !unchecked_at(&check_run, "checked/src/lib.rs")
            && check_run
                .iter()
                .any(|l| l.contains("note: fip-prelint: crate `checked`:")),
        "the checked primary package rejected fip_fn!(prelint, ..) or was not analysed: {check_run:#?}"
    );

    let stack = run_args("driver_checked", "-stack", &[], &["--stack"]);
    compare("driver_checked", "-stack", &stack);
    assert!(
        stack[0] == "exit: failure" && stack.iter().any(|l| l.contains(PRELINT_UNCHECKED)),
        "stack mode accepted fip_fn!(prelint, ..): {stack:#?}"
    );
    // An inherited `FIP_PRELINT_CHECKS=1` is removed by the driver: the same result.
    let forged = run_args(
        "driver_checked",
        "-stack-forged",
        &[("FIP_PRELINT_CHECKS", "1".into())],
        &["--stack"],
    );
    compare("driver_checked", "-stack", &forged);

    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join("driver_checked-summaries.txt");
    let generate = run(
        "driver_checked",
        "-generate",
        &[("FIP_PRELINT_STD_SUMMARIES_OUT", out.into_os_string())],
    );
    compare("driver_checked", "-generate", &generate);
    assert!(
        generate[0] == "exit: failure" && generate.iter().any(|l| l.contains(PRELINT_UNCHECKED)),
        "std-summary generation accepted fip_fn!(prelint, ..): {generate:#?}"
    );
}
