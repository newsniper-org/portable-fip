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
    run_at(
        &fixtures_dir().join(name),
        &format!("{name}{variant}"),
        envs,
        args,
    )
}

/// `run_args` on the workspace at `dir`, into the target directory `target_key`.
fn run_at(
    dir: &Path,
    target_key: &str,
    envs: &[(&str, std::ffi::OsString)],
    args: &[&str],
) -> Vec<String> {
    let target = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("fixtures")
        .join(target_key);
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-fip-prelint"));
    cmd.arg("fip-prelint")
        .args(args)
        .current_dir(dir)
        .env("FIP_PRELINT_TARGET_DIR", &target)
        .env("FIP_PRELINT_DRIVER_PATH", env!("CARGO_BIN_EXE_fip-prelint"))
        .env_remove("FIP_PRELINT_WARN_ONLY")
        .env_remove("FIP_PRELINT_DUMP")
        .env_remove("FIP_PRELINT_DUMP_MIR")
        .env_remove("FIP_PRELINT_STD_SUMMARIES")
        .env_remove("FIP_PRELINT_STD_SUMMARIES_OUT")
        .env_remove("FIP_PRELINT_STACK")
        .env_remove("FIP_MACROS_MARK_ONLY")
        .env_remove("FIP_PRELINT_NO_VERUS")
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
/// objects add `chain::generic::<u8>`, T8f; the allocator shim is named
/// `__rustc::__rust_alloc`), `-aarch64` (`--target aarch64-unknown-linux-gnu`, AArch64
/// ELF, return address 0, T8a), `-i686` (ELF32 i386, return address 4, 4 more bytes
/// for a function without callees) and `-armv7` (ELF32 ARM, return address 0)
/// (cross targets skipped if not installed), `-buildstd` (`--build-std`: the std functions are built and bounded,
/// down to the foreign `getpid`/`memcpy`, T8c). If the system `llvm-readobj` exists,
/// each bound of `chain_top` (dev, release and the cross targets) is checked to be at least the sum
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
    let installed = |t: &str| sysroot.join("lib").join("rustlib").join(t).is_dir();
    let variants: [(&str, &[&str], Option<&str>); 7] = [
        ("-dev", &[], Some("debug")),
        ("-release", &["--release"], Some("release")),
        ("-tests", &["--lib", "--tests"], None),
        (
            "-aarch64",
            &["--target", "aarch64-unknown-linux-gnu"],
            Some("aarch64-unknown-linux-gnu/debug"),
        ),
        (
            "-i686",
            &["--target", "i686-unknown-linux-gnu"],
            Some("i686-unknown-linux-gnu/debug"),
        ),
        (
            "-armv7",
            &["--target", "armv7-unknown-linux-gnueabihf"],
            Some("armv7-unknown-linux-gnueabihf/debug"),
        ),
        ("-buildstd", &["--build-std"], None),
    ];
    for (variant, extra, cross_check) in variants {
        if let ["--target", t] = extra
            && !installed(t)
        {
            eprintln!("stack fixture{variant}: `{t}` not installed, skipped");
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
/// unmarked `Pool::alloc` and `Bump::alloc` of the exported crate and the `Bump::alloc`
/// of the member without `fip::export` get a heuristic note, the marked arena, the
/// stack and the cursor do not.
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
/// closure is reported by the same check, the allocation-free one and a default
/// `fip_fn!` there pass (a closure type generic through the enclosing function's
/// parameters is analysed through its body, not a generic callable type), and a
/// closure calling `T::make` is `⊤` (a term left: the certificate claims its bound
/// for every instantiation). The three driver runs that
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

/// Std-summary generation (`FIP_PRELINT_STD_SUMMARIES_OUT` set) of a crate that
/// depends on a proc-macro crate (`fip-macros`) and on `fip-strict` writes the
/// summaries. It was an ICE (`rustc_metadata` `def_key`, `Option::unwrap` on `None`):
/// generation listed the functions of every dependency, the proc-macro crate
/// included, whose metadata has none.
#[test]
fn generate_deps() {
    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join("generate_deps-summaries.txt");
    let _ = std::fs::remove_file(&out);
    // A fresh build: cargo would not rerun the driver on an unchanged crate.
    let _ = std::fs::remove_dir_all(
        Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("fixtures")
            .join("generate_deps-generate"),
    );
    let got = run(
        "generate_deps",
        "-generate",
        &[(
            "FIP_PRELINT_STD_SUMMARIES_OUT",
            out.clone().into_os_string(),
        )],
    );
    assert_eq!(got[0], "exit: success", "generation failed: {got:#?}");
    assert!(
        got.iter()
            .any(|l| l.contains("std summaries: 0 functions from 1 seed roots")),
        "no summary note: {got:#?}"
    );
    let text = std::fs::read_to_string(&out).expect("the summaries were written");
    assert!(text.starts_with("fip-prelint std summaries\n"), "{text}");
}

/// Copies the fixture `name` to a fresh directory under the test's temporary
/// directory (without `target`), for mutations.
fn copy_fixture(name: &str, to: &str) -> PathBuf {
    fn copy(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).expect("create the copy");
        for e in std::fs::read_dir(from).expect("read the fixture").flatten() {
            let p = e.path();
            if e.file_name() == "target" {
                continue;
            }
            if p.is_dir() {
                copy(&p, &to.join(e.file_name()));
            } else {
                std::fs::copy(&p, to.join(e.file_name())).expect("copy a fixture file");
            }
        }
    }
    let dest = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("copies")
        .join(to);
    let _ = std::fs::remove_dir_all(&dest);
    copy(&fixtures_dir().join(name), &dest);
    dest
}

/// Replaces `from` by `to` (exactly once) in `file`.
fn edit(file: &Path, from: &str, to: &str) {
    let text = std::fs::read_to_string(file).expect("read the file to edit");
    assert_eq!(
        text.matches(from).count(),
        1,
        "`{from}` once in {}",
        file.display()
    );
    std::fs::write(file, text.replace(from, to)).expect("write the edited file");
}

/// Verus as an oracle for panic freedom (top plan T13.4). Fixture `verus_sidecar`: the
/// crate `vside` declares the sidecar `vside/verus-verified.txt` written by a
/// `--no-cheating` Verus run (`just verify-sidecar` regenerates it and fails if it
/// differs). With it, the body-local overflow and bounds sites of the listed `mul`,
/// `pick`, `halves` and of the impl methods `Acc::add`, `Acc::three_quarters` are
/// discharged (5, stated in the crate summary with the stamp; the methods are matched
/// by `{impl}` path, file and line, since a plain-only impl block shifts rustc's impl
/// numbers against Verus's); the Verus caller `square_small` has no note; the calls of
/// `mul` from `plain::use_mul` and of `Acc::add` from `plain::use_add`, which Verus did
/// not check, carry the callee's precondition; the non-verified `plain::mul` (same
/// name), `Acc::add_plain` and the unannotated `halves_unannotated` (not in the VIR, so
/// not listed) keep their notes, with the reason. With `--no-verus` every site is
/// reported as before (12 notes).
#[test]
fn verus_sidecar() {
    check("verus_sidecar");
    compare(
        "verus_sidecar",
        "-off",
        &run_args(
            "verus_sidecar",
            "-off",
            &[],
            &["--message-format", "short", "--no-verus"],
        ),
    );
}

/// Stale or foreign sidecars are never used (top plan T13.4): a body edited after the
/// verification run (every note back, the sidecar refused: its source hash differs);
/// the same edit with the sidecar's source hash forged to match (only the edited
/// function's item hash differs: its notes are back, the other two functions keep
/// theirs discharged); a sidecar stamped with another Verus version; a missing one; an
/// impl method's body edited (its notes back); an impl method's entry moved to another
/// line; the impl block's header configured differently for Verus.
#[test]
fn verus_sidecar_refused() {
    let body_from = "pub fn mul(a: u32, b: u32) -> u32 {\n    a * b\n}";
    let body_to = "pub fn mul(a: u32, b: u32) -> u32 {\n    b * a\n}";

    let d = copy_fixture("verus_sidecar", "verus_mutant");
    edit(&d.join("vside/src/lib.rs"), body_from, body_to);
    compare(
        "verus_sidecar",
        "-mutant",
        &run_at(
            &d,
            "verus_sidecar-mutant",
            &[],
            &["--message-format", "short"],
        ),
    );

    let d = copy_fixture("verus_sidecar", "verus_item");
    let sidecar = d.join("vside/verus-verified.txt");
    let old = sha256_file(&d.join("vside/src/lib.rs"));
    edit(&d.join("vside/src/lib.rs"), body_from, body_to);
    let new = sha256_file(&d.join("vside/src/lib.rs"));
    edit(
        &sidecar,
        &format!("source src/lib.rs {old}"),
        &format!("source src/lib.rs {new}"),
    );
    compare(
        "verus_sidecar",
        "-item",
        &run_at(
            &d,
            "verus_sidecar-item",
            &[],
            &["--message-format", "short"],
        ),
    );

    let d = copy_fixture("verus_sidecar", "verus_stamp");
    edit(
        &d.join("vside/verus-verified.txt"),
        "verus 0.2026.10.18.7d82994 ",
        "verus 0.2026.10.31.559ac52 ",
    );
    compare(
        "verus_sidecar",
        "-stamp",
        &run_at(
            &d,
            "verus_sidecar-stamp",
            &[],
            &["--message-format", "short"],
        ),
    );

    let d = copy_fixture("verus_sidecar", "verus_missing");
    std::fs::remove_file(d.join("vside/verus-verified.txt")).expect("remove the sidecar");
    compare(
        "verus_sidecar",
        "-missing",
        &run_at(
            &d,
            "verus_sidecar-missing",
            &[],
            &["--message-format", "short"],
        ),
    );

    // Impl methods (top plan item 8): the body of the verified `Acc::add` edited, the
    // source hash forged: only `add`'s item hash differs, its note is back (and its
    // caller's precondition note becomes the plain chain); `three_quarters` stays
    // discharged.
    let d = copy_fixture("verus_sidecar", "verus_impl");
    let lib = d.join("vside/src/lib.rs");
    let old = sha256_file(&lib);
    edit(
        &lib,
        "pub fn add(&self, a: u32) -> u32 {\n        self.n + a\n    }",
        "pub fn add(&self, a: u32) -> u32 {\n        a + self.n\n    }",
    );
    let new = sha256_file(&lib);
    edit(
        &d.join("vside/verus-verified.txt"),
        &format!("source src/lib.rs {old}"),
        &format!("source src/lib.rs {new}"),
    );
    compare(
        "verus_sidecar",
        "-impl",
        &run_at(
            &d,
            "verus_sidecar-impl",
            &[],
            &["--message-format", "short"],
        ),
    );

    // An impl method is matched by path, file and line, never by its impl number:
    // `add`'s entry moved to the line of `three_quarters` is not used for `add`.
    let d = copy_fixture("verus_sidecar", "verus_line");
    let sidecar = d.join("vside/verus-verified.txt");
    let text = std::fs::read_to_string(&sidecar).expect("read the sidecar");
    let line_of = |name: &str| {
        text.lines()
            .find(|l| l.starts_with(&format!("fn vside::{{impl}}::{name} ")))
            .and_then(|l| l.split_whitespace().nth(2))
            .expect("an impl entry")
            .to_string()
    };
    let (add_at, tq_at) = (line_of("add"), line_of("three_quarters"));
    edit(
        &sidecar,
        &format!("fn vside::{{impl}}::add {add_at} "),
        &format!("fn vside::{{impl}}::add {tq_at} "),
    );
    compare(
        "verus_sidecar",
        "-line",
        &run_at(
            &d,
            "verus_sidecar-line",
            &[],
            &["--message-format", "short"],
        ),
    );

    // The impl block's header configured differently for Verus (an attribute under
    // `cfg_attr(not(verus_keep_ghost), ..)` on the same line, source hash forged):
    // neither method of the block is used.
    let d = copy_fixture("verus_sidecar", "verus_header");
    let lib = d.join("vside/src/lib.rs");
    let old = sha256_file(&lib);
    edit(
        &lib,
        "\nimpl Acc {\n    /// Verified under",
        "\n#[cfg_attr(not(verus_keep_ghost), allow(unused))] impl Acc {\n    /// Verified under",
    );
    let new = sha256_file(&lib);
    edit(
        &d.join("vside/verus-verified.txt"),
        &format!("source src/lib.rs {old}"),
        &format!("source src/lib.rs {new}"),
    );
    compare(
        "verus_sidecar",
        "-header",
        &run_at(
            &d,
            "verus_sidecar-header",
            &[],
            &["--message-format", "short"],
        ),
    );
}

/// SHA-256 of a file with `sha256sum` (the driver's own implementation is checked
/// against the FIPS vectors in its unit tests).
fn sha256_file(p: &Path) -> String {
    let out = Command::new("sha256sum")
        .arg(p)
        .output()
        .expect("run sha256sum");
    String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .next()
        .expect("a hash")
        .to_string()
}
