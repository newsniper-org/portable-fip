# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

# Upstream Verus (verus-lang/verus) with Singular for `by (integer_ring)`.
verus := env_var_or_default("VERUS", "verus")
singular := env_var_or_default("SINGULAR", "/usr/bin/Singular")
# Lowest supported toolchain (workspace `rust-version`).
msrv := "1.97.1"

# Every gate; a change merges only when this passes.
ci: fmt-check lint test msrv nostd cross verify compile-fail-reasons

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

# Other ISAs the arch module realises.
cross:
    cargo check -p fip-core -p fip-alloc -p fip-arch --target aarch64-unknown-linux-gnu
    cargo check -p fip-core -p fip-alloc -p fip-arch --target riscv64gc-unknown-linux-gnu

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

# Mutated copies must FAIL verification; a gate that cannot fail proves nothing.
verify-negative:
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/verify-negative; rm -rf "$out"; mkdir -p "$out"
    expect_fail() {  # name, crate dir, file, sed expression
      local d="$out/$1"; cp -r "crates/$2" "$d"
      sed -i "$4" "$d/src/$3"
      if cmp -s "crates/$2/src/$3" "$d/src/$3"; then echo "FAIL: mutation $1 did not apply"; exit 1; fi
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib --no-cheating "$d/src/lib.rs" > "$d/log" 2>&1; then
        echo "FAIL: mutant $1 verified"; exit 1
      fi
      grep -q "verification results:: .* [1-9][0-9]* errors" "$d/log" || { echo "FAIL: mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected"
    }
    expect_fail compact-no-swap   fip-core  slice.rs 's/^                swap_lt(xs, w, r);$//'
    expect_fail compact-order     fip-core  slice.rs 's/^            proof! { idx = idx.push(r as int); }$/            proof! { idx = idx.push(0); }/'
    expect_fail map-skips-store   fip-core  slice.rs 's/^        spare = crate::slot::replace(&mut xs\[i\], next);$/        spare = next;/'
    expect_fail update-keeps-old  fip-core  slot.rs  's/^    let next = f(prev);$/    let next = prev; let _ = f;/'
    expect_fail refill-no-swap    fip-alloc lib.rs   's/^    core::mem::swap(&mut \*cell, &mut prev);$//'
    echo "verify-negative: ok"

# Every compile_fail doctest of fip-macros fails because of the lint, not another error.
compile-fail-reasons:
    cargo build -q -p fip-macros
    uv run --no-project python verify/compile_fail_reasons.py "$(ls -t target/debug/deps/libfip_macros-*.so | head -1)"
