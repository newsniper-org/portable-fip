# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

# Upstream Verus (verus-lang/verus) with Singular for `by (integer_ring)`.
verus := env_var_or_default("VERUS", "verus")
singular := env_var_or_default("SINGULAR", "/usr/bin/Singular")
# Lowest supported toolchain (workspace `rust-version`).
msrv := "1.97.1"

# Every gate; a change merges only when this passes.
ci: fmt-check lint test msrv nostd cross arch-override verify compile-fail-reasons

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
    cargo +{{msrv}} test --workspace

# Real no_std evidence: this target ships only core/alloc, so any std use fails to link.
nostd:
    cargo +{{msrv}} build --release --target x86_64-unknown-none -p fip-core -p fip-alloc -p fip-arch

# Other ISAs the arch module realises (incl. Apple aarch64, whose default line is 128 B).
cross:
    cargo check -p fip-core -p fip-alloc -p fip-arch --target aarch64-unknown-linux-gnu
    cargo check -p fip-core -p fip-alloc -p fip-arch --target riscv64gc-unknown-linux-gnu
    cargo check -p fip-arch --target aarch64-apple-darwin

# All Verus gates: proofs, composition with #[fip], and negative controls.
verify: verify-core verify-alloc verify-compose verify-negative

# fip-core proofs, no trusted items (--no-cheating).
verify-core:
    VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating crates/fip-core/src/lib.rs

# fip-alloc proofs, no trusted items (--no-cheating).
verify-alloc:
    VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating crates/fip-alloc/src/lib.rs

# `#[fip]` above `verus_spec` verifies; below it, or with an allocation, it is rejected.
verify-compose:
    #!/usr/bin/env bash
    set -euo pipefail
    tc=$({{verus}} --version | awk '/Toolchain/ {print $2}')
    cargo +"$tc" build -q -p fip-macros --target-dir target/verus-macros
    so=$(ls -t target/verus-macros/debug/deps/libfip_macros-*.so | head -1)
    run() { VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating --extern fip_macros="$so" "$1"; }
    run verify/compose.rs
    out=target/verify-compose; mkdir -p "$out"
    sed 's/^#\[fip\]$//; s/^pub fn count/#[fip]\npub fn count/' verify/compose.rs > "$out/below.rs"
    if run "$out/below.rs" 2> "$out/below.err"; then echo "FAIL: #[fip] below verus_spec was accepted"; exit 1; fi
    grep -q "write FIP attributes above" "$out/below.err"
    sed 's/^extern crate alloc;$//' verify/compose.rs \
      | sed 's/#!\[no_std\]/#![no_std]/' \
      | awk '{print} /feature\(proc_macro_hygiene\)/ {print "extern crate alloc;"} /^        i \+= 1;$/ {print "        let _b = alloc::boxed::Box::new(i);"}' > "$out/alloc.rs"
    if run "$out/alloc.rs" 2> "$out/alloc.err"; then echo "FAIL: allocation inside #[fip] was accepted"; exit 1; fi
    grep -q "allocation site \`Box::new\`" "$out/alloc.err"
    echo "verify-compose: ok"

# Mutated copies must FAIL; a gate that cannot fail proves nothing.
# Each mutation is scoped to one function with a sed address range.
verify-negative:
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
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating "$d/src/lib.rs" > "$d/log" 2>&1; then
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

# Every compile_fail doctest of fip-macros fails because of the lint, not another error.
compile-fail-reasons:
    cargo build -q -p fip-macros
    uv run --no-project python verify/compile_fail_reasons.py "$(ls -t target/debug/deps/libfip_macros-*.so | head -1)"
