# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

# Upstream Verus (verus-lang/verus) with Singular for `by (integer_ring)`.
verus := env_var_or_default("VERUS", "verus")
singular := env_var_or_default("SINGULAR", "/usr/bin/Singular")
# Lowest supported toolchain (workspace `rust-version`).
msrv := "1.97.1"
# Toolchain of `fip-prelint` (the installed Verus toolchain; decision 2026-11-01-fip-prelint).
prelint_tc := "1.99.1"

# Every gate; a change merges only when this passes.
ci: fmt-check lint test msrv nostd cross arch-override verify compile-fail-reasons prelint

# Formatting.
fmt-check:
    cargo fmt --all -- --check

# Clippy, warnings are errors (workspace lints: all = deny, pedantic = warn).
lint:
    cargo clippy --workspace --all-targets -- -D warnings

# Unit, integration and doc tests (allocation-count tests run in parallel).
test:
    cargo test --workspace

# Builds and tests on the lowest supported toolchain.
msrv:
    cargo +{{msrv}} test --workspace --target-dir target/msrv

# Real no_std evidence: this target ships only core/alloc, so any std use fails to link.
nostd:
    cargo +{{msrv}} build --release --target x86_64-unknown-none -p fip-core -p fip-alloc -p fip-arch -p fip-strict

# Other ISAs the arch module realises (incl. Apple aarch64, whose default line is 128 B).
cross:
    cargo check -p fip-core -p fip-alloc -p fip-arch -p fip-strict --target aarch64-unknown-linux-gnu
    cargo check -p fip-core -p fip-alloc -p fip-arch -p fip-strict --target riscv64gc-unknown-linux-gnu
    cargo check -p fip-arch --target aarch64-apple-darwin

# All Verus gates: proofs, composition with #[fip], and negative controls.
verify: verify-strict verify-core verify-alloc verify-compose verify-negative

# Verus metadata and library of fip-strict, imported where `FipFn` specs are needed.
verus_strict := "--import fip_strict=target/verus-strict/fip_strict.vir --extern fip_strict=target/verus-strict/libfip_strict.rlib"

# fip-strict proofs (`FipFn` with `pre`/`post`, `Certified`), no trusted items;
# exports the Verus metadata that fip-core and verify-compose import.
verify-strict:
    rm -rf target/verus-strict && mkdir -p target/verus-strict
    VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --crate-name fip_strict --no-cheating crates/fip-strict/src/lib.rs --export target/verus-strict/fip_strict.vir --compile --out-dir target/verus-strict

# Verus metadata and library of fip-core (needs fip-strict's on the library path),
# imported by verified callers in `verify/`.
verus_core := "--import fip_core=target/verus-core/fip_core.vir --extern fip_core=target/verus-core/libfip_core.rlib -L target/verus-strict"

# fip-core proofs, no trusted items (--no-cheating); imports fip-strict's Verus build
# and exports fip-core's for `verify/compose_state.rs`.
verify-core: verify-strict
    rm -rf target/verus-core && mkdir -p target/verus-core
    VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --crate-name fip_core --no-cheating crates/fip-core/src/lib.rs {{verus_strict}} --export target/verus-core/fip_core.vir --compile --out-dir target/verus-core

# fip-alloc proofs, no trusted items (--no-cheating).
verify-alloc:
    VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating crates/fip-alloc/src/lib.rs

# `#[fip]` above `verus_spec` verifies; below it, or with an allocation, it is rejected.
# Strict functions with `FipFn` parameters verify against fip-strict's Verus build.
# Callers of the state-passing combinators verify against fip-core's Verus build.
verify-compose: verify-strict verify-core
    #!/usr/bin/env bash
    set -euo pipefail
    tc=$({{verus}} --version | awk '/Toolchain/ {print $2}')
    cargo +"$tc" build -q -p fip-macros --target-dir target/verus-macros
    deps=target/verus-macros/debug/deps
    so=$(ls -t $deps/libfip_macros-*.so | head -1)
    run() { VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating --extern fip_macros="$so" {{verus_strict}} -L "$deps" "$1"; }
    run verify/compose.rs
    run verify/compose_strict.rs
    VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating {{verus_strict}} {{verus_core}} verify/compose_state.rs
    out=target/verify-compose; mkdir -p "$out"
    sed 's/^#\[fip\]$//; s/^pub fn count/#[fip]\npub fn count/' verify/compose.rs > "$out/below.rs"
    if run "$out/below.rs" 2> "$out/below.err"; then echo "FAIL: #[fip] below verus_spec was accepted"; exit 1; fi
    grep -q "write FIP attributes above" "$out/below.err"
    sed 's/^extern crate alloc;$//' verify/compose.rs \
      | sed 's/#!\[no_std\]/#![no_std]/' \
      | awk '{print} /feature\(proc_macro_hygiene\)/ {print "extern crate alloc;"} /^        i \+= 1;$/ {print "        let _b = alloc::boxed::Box::new(i);"}' > "$out/alloc.rs"
    if run "$out/alloc.rs" 2> "$out/alloc.err"; then echo "FAIL: allocation inside #[fip] was accepted"; exit 1; fi
    grep -q "allocation site \`Box::new\`" "$out/alloc.err"
    # strict + Verus: an uncertified callee is still rejected under `verus`.
    sed 's/^    swap2(a, b);$/    plain(a, b);/' verify/compose_strict.rs > "$out/strict_bad.rs"
    printf 'pub fn plain(a: &mut u32, b: &mut u32) { core::mem::swap(a, b) }\n' >> "$out/strict_bad.rs"
    if run "$out/strict_bad.rs" 2> "$out/strict_bad.err"; then echo "FAIL: uncertified callee accepted under verus"; exit 1; fi
    grep -q "__fip_strict_plain" "$out/strict_bad.err"
    # A `FipFn` parameter promises only its `post`: claiming the negation must fail.
    sed 's/^    keep.call((&x,))$/    !keep.call((\&x,))/' verify/compose_strict.rs > "$out/strict_post.rs"
    if cmp -s verify/compose_strict.rs "$out/strict_post.rs"; then echo "FAIL: mutation strict_post did not apply"; exit 1; fi
    if run "$out/strict_post.rs" 2> "$out/strict_post.err" > "$out/strict_post.out"; then echo "FAIL: wrong FipFn result accepted under verus"; exit 1; fi
    grep -q "postcondition not satisfied" "$out/strict_post.err" "$out/strict_post.out"
    echo "verify-compose: ok"

# Mutated copies must FAIL; a gate that cannot fail proves nothing.
# Each mutation is scoped to one function with a sed address range.
verify-negative: verify-strict verify-core
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/verify-negative; rm -rf "$out"; mkdir -p "$out"
    mutate() {  # name, crate dir, file, sed script -> prints mutant dir
      local d="$out/$1"; cp -r "crates/$2" "$d"
      sed -i "$4" "$d/src/$3"
      if cmp -s "crates/$2/src/$3" "$d/src/$3"; then echo "FAIL: mutation $1 did not apply" >&2; exit 1; fi
      echo "$d"
    }
    expect_verus_fail() {  # name, crate, file, sed script, expected log regex
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating "$d/src/lib.rs" {{verus_strict}} > "$d/log" 2>&1; then
        echo "FAIL: mutant $1 verified"; exit 1
      fi
      grep -Eq "$5" "$d/log" || { echo "FAIL: mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected by Verus"
    }
    errs='verification results:: .* [1-9][0-9]* errors'
    # Functional specs.
    expect_verus_fail compact-no-swap      fip-core  slice.rs '/^pub fn compact</,/^}/ s/^                swap_lt(xs, w, r);$//' "$errs"
    expect_verus_fail compact-order        fip-core  slice.rs '/^pub fn compact</,/^}/ s/idx = idx.push(r as int);/idx = idx.push(0);/' "$errs"
    expect_verus_fail map-skips-store      fip-core  slice.rs '/^pub fn map_in_place</,/^}/ s/^        spare = crate::slot::replace(&mut xs\[i\], next);$/        spare = next;/' "$errs"
    expect_verus_fail update-keeps-old     fip-core  slot.rs  's/^    let next = f(prev);$/    let next = prev; let _ = f;/' "$errs"
    expect_verus_fail dedup-no-swap        fip-core  slice.rs '/^pub fn dedup_by</,/^}/ s/^                swap_lt(xs, w, r);$//' "$errs"
    expect_verus_fail dedup-wrong-compare  fip-core  slice.rs '/^pub fn dedup_by</,/^}/ s/same(&xs\[w - 1\], &xs\[r\])/same(\&xs[r - 1], \&xs[r])/' "$errs"
    expect_verus_fail compact-map-no-swap  fip-core  slice.rs '/^pub fn compact_map</,/^}/ s/^                swap_lt(xs, w, r);$//' "$errs"
    expect_verus_fail compact-map-invert   fip-core  slice.rs '/^pub fn compact_map</,/^}/ s/^        if keep {$/        if !keep {/' "$errs"
    expect_verus_fail refill-no-swap       fip-alloc lib.rs   's/^    core::mem::swap(&mut \*cell, &mut prev);$//' "$errs"
    # Strict variants (`FipFn` callables), same mutations.
    expect_verus_fail strict-compact-no-swap     fip-core strict.rs '/^pub fn compact</,/^}/ s/^                crate::slice::swap_lt(xs, w, r);$//' "$errs"
    expect_verus_fail strict-map-skips-store     fip-core strict.rs '/^pub fn map_in_place</,/^}/ s/^        spare = crate::slot::replace(&mut xs\[i\], next);$/        spare = next;/' "$errs"
    expect_verus_fail strict-update-keeps-old    fip-core strict.rs '/^pub fn update</,/^}/ s/^    let next = f.call((prev,));$/    let next = prev; let _ = \&f;/' "$errs"
    expect_verus_fail strict-dedup-wrong-compare fip-core strict.rs '/^pub fn dedup_by</,/^}/ s/same.call((&xs\[w - 1\], &xs\[r\]))/same.call((\&xs[r - 1], \&xs[r]))/' "$errs"
    expect_verus_fail strict-compact-map-invert  fip-core strict.rs '/^pub fn compact_map</,/^}/ s/^        if keep {$/        if !keep {/' "$errs"
    # State-passing variants: the state must be threaded once per element, in index
    # order. Each must fail on the state-chain invariant or assertion, not elsewhere.
    chain='\(ss\[[jk]\], old\(xs\)@\[[jk]\]\), \(ss\[[jk] \+ 1\]'
    expect_verus_fail map-st-reverse-order              fip-core slice.rs  '/^pub fn map_in_place_st</,/^}/ s/&mut xs\[i\]/\&mut xs[n - 1 - i]/g' "$chain"
    expect_verus_fail map-st-not-threaded               fip-core slice.rs  '/^pub fn map_in_place_st</,/^}/ { s/^pub fn map_in_place_st<S, /pub fn map_in_place_st<S: Copy, /; s/^        s = s1;$/        let _ = s1;/ }' "$chain"
    expect_verus_fail compact-map-st-not-threaded       fip-core slice.rs  '/^pub fn compact_map_st</,/^}/ { s/^pub fn compact_map_st<S, /pub fn compact_map_st<S: Copy, /; s/^        s = s1;$/        let _ = s1;/ }' "$chain"
    expect_verus_fail strict-map-st-reverse-order       fip-core strict.rs '/^pub fn map_in_place_st</,/^}/ s/&mut xs\[i\]/\&mut xs[n - 1 - i]/g' "$chain"
    expect_verus_fail strict-compact-map-st-not-threaded fip-core strict.rs '/^pub fn compact_map_st</,/^}/ { s/^pub fn compact_map_st<S, /pub fn compact_map_st<S: Copy, /; s/^        s = s1;$/        let _ = s1;/ }' "$chain"
    # Pre-verified state spec: without the state chain, the rejecting lemmas fail.
    expect_verus_fail spec-st-no-chain fip-core spec.rs '/^    pub open spec fn map_st_post</,/^    }/ s/^        &&& forall|k: int| 0 <= k < old.len() ==> step(.*$/        \&\&\& true/' "$errs"
    # Verified callers (verify/compose_state.rs): a wrong final state must be rejected.
    for c in 's/^        r == 13,$/        r == 14,/' 's/^        r == 2,$/        r == 3,/'; do
      sed "$c" verify/compose_state.rs > "$out/state_wrong.rs"
      if cmp -s verify/compose_state.rs "$out/state_wrong.rs"; then echo "FAIL: control $c did not apply"; exit 1; fi
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating {{verus_strict}} {{verus_core}} "$out/state_wrong.rs" > "$out/state_wrong.log" 2>&1; then
        echo "FAIL: wrong final state accepted ($c)"; exit 1
      fi
      grep -q "postcondition not satisfied" "$out/state_wrong.log" || { echo "FAIL: control $c failed for another reason"; cat "$out/state_wrong.log"; exit 1; }
      echo "control $c rejected by Verus"
    done
    # Pre-verified spec of the strict variants: a wrong relation breaks the lemmas.
    expect_verus_fail spec-fip-wrong-relation    fip-core spec.rs   '/^pub open spec fn compact_fip_post</,/^}/ s/keep.post((&a,), r)/keep.post((\&a,), !r)/' "$errs"
    # fip-strict: `Certified::pre` must be the closure's `requires`.
    expect_verus_fail certified-pre-true         fip-strict lib.rs  's/^                self.inner().requires(args)$/                true/' "$errs"
    # Stack bound: recursion without `decreases` is rejected.
    expect_verus_fail swap-recursive       fip-core  slice.rs '/^pub fn swap</,/^}/ s/^        swap_lt(xs, lo, hi);$/        swap_lt(xs, lo, hi);\n        swap(xs, lo, lo);/' 'recursive function must have a decreases clause'
    # Source gates (fip_testkit::surface) must fail on mutated sources.
    expect_test_fail() {  # name, crate, file, sed script, test name
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      if FIP_SURFACE_SRC="$PWD/$d/src" cargo test -q -p "$2" --test verified_surface "$5" > "$d/log" 2>&1; then
        echo "FAIL: surface mutant $1 passed"; exit 1
      fi
      grep -q "test result: FAILED" "$d/log" || { echo "FAIL: surface mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected by the surface gate"
    }
    expect_test_fail surface-unspecified fip-core slot.rs '0,/^#\[cfg_attr(verus_keep_ghost, verus_spec(r =>$/{/^#\[cfg_attr(verus_keep_ghost, verus_spec(r =>$/,/^))\]$/d}' every_function_is_specified
    expect_test_fail surface-decreases   fip-core slot.rs '0,/^    ensures$/ s/^    ensures$/    decreases 0nat,\n    ensures/' no_function_may_recurse
    # Drift gate (fip-strict): the Verus `FipFn::call` must match the plain one.
    d=$(mutate drift-call fip-strict lib.rs 's/^    fn call(&self, args: Args) -> (r: Self::Output)$/    fn call(\&self, args: Args, extra: u8) -> (r: Self::Output)/')
    if FIP_DRIFT_SRC="$PWD/$d/src/lib.rs" cargo test -q -p fip-strict --test verus_drift > "$d/log" 2>&1; then
      echo "FAIL: drift mutant passed"; exit 1
    fi
    grep -q "test result: FAILED" "$d/log" || { echo "FAIL: drift mutant failed for another reason"; cat "$d/log"; exit 1; }
    echo "mutant drift-call rejected by the drift test"
    echo "verify-negative: ok"

# CACHE_LINE override: supported values take effect, others are rejected.
arch-override:
    #!/usr/bin/env bash
    set -euo pipefail
    for v in 32 128; do
      RUSTFLAGS="--cfg fip_cache_line=\"$v\"" cargo test -q -p fip-arch --target-dir "target/cl$v"
    done
    for bad in '--cfg fip_cache_line="256"' '--cfg fip_cache_line' '--cfg fip_cache_line="64" --cfg fip_cache_line="128"'; do
      if RUSTFLAGS="$bad" cargo build -q -p fip-arch --target-dir target/cl-bad 2>/dev/null; then
        echo "FAIL: accepted $bad"; exit 1
      fi
    done
    echo "arch-override: ok"

# Every compile_fail doctest of fip-macros fails for its stated reason, not another error.
# Own target dir: the script needs exactly one build of each crate, by the ambient rustc.
compile-fail-reasons:
    rm -rf target/compile-fail
    cargo build -q -p fip-macros -p fip-strict --target-dir target/compile-fail
    uv run --no-project python verify/compile_fail_reasons.py target/compile-fail

# MIR-level checker `fip-prelint` (tools/fip-prelint, a rustc driver on the Verus toolchain
# with `rustc-dev`): builds the driver, runs the fixture workspaces and the workspace
# self-check against `tools/fip-prelint/tests/*.expected`. Report-only run on the
# workspace: `tools/fip-prelint/target/debug/cargo-fip-prelint --warn-only`.
prelint:
    cd tools/fip-prelint && cargo +{{prelint_tc}} fmt --check
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 FIP_PRELINT_TOOLCHAIN={{prelint_tc}} cargo +{{prelint_tc}} test
