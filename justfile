# SPDX-License-Identifier: MIT OR Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

# Pins (decision 2026-11-06-redesign-verus-allocates): each is written in one file and
# read from there, so a re-pin edits only that file.
#   - trusted Verus (version, commit) and Z3: tools/fip-prelint/verus-trusted.txt,
#     checked against the binary `VERUS` by `verus-pin` before every Verus gate;
#   - toolchain of `fip-prelint` (= the Verus toolchain, checked by `verus-pin`):
#     tools/fip-prelint/rust-toolchain.toml (also read by the driver's build.rs);
#   - MSRV: `rust-version` in Cargo.toml;
#   - upstream Verus of the strip gate: `verus_upstream_pin` below.
#
# The Verus fork with `allocates` (branch `fip`, the pin in verus-trusted.txt), with
# Singular for `by (integer_ring)`. `VERUS` must name that build (`just verus-pin` fails
# otherwise); its Z3 is `VERUS_Z3_PATH`, else the `z3` next to the binary.
verus := env_var_or_default("VERUS", "verus")
# Flags of every Verus run of the gates: no trusted items, and `allocates` bounds checked
# (the fork's `-V alloc-check`; an importing crate needs the imported crate's export
# from a run with it).
verus_flags := "--no-cheating -V alloc-check"
singular := env_var_or_default("SINGULAR", "/usr/bin/Singular")
# Upstream Verus for the strip gate `verify-upstream` (decision D5): unset or empty skips
# the gate with a message; set, it must report `verus_upstream_pin`.
verus_upstream := env_var_or_default("VERUS_UPSTREAM", "")
verus_upstream_pin := "0.2026.11.02.8bf68ee"
# Lowest supported toolchain (workspace `rust-version`).
msrv := `sed -n 's/^rust-version = "\(.*\)"$/\1/p' Cargo.toml`
# Toolchain of `fip-prelint` (the Verus toolchain; decision 2026-11-01-fip-prelint).
prelint_tc := `sed -n 's/^channel = "\(.*\)"$/\1/p' tools/fip-prelint/rust-toolchain.toml`

# Every gate; a change merges only when this passes. A driver test skipped for a
# missing target, tool or host fails here (`FIP_PRELINT_REQUIRE_TARGETS=1`).
ci:
    FIP_PRELINT_REQUIRE_TARGETS=1 just ci-gates

# The gates of `ci`, without turning skipped driver tests into failures.
ci-gates: fmt-check lint test msrv nostd cross arch-override verify verify-upstream compile-fail-reasons prelint

# Formatting.
fmt-check:
    cargo fmt --all -- --check

# Clippy, warnings are errors (workspace lints: all = deny, pedantic = warn).
lint:
    cargo clippy --locked --workspace --all-targets -- -D warnings

# Unit, integration and doc tests (allocation-count tests run in parallel).
test:
    cargo test --locked --workspace

# Builds and tests on the lowest supported toolchain.
msrv:
    cargo +{{msrv}} test --locked --workspace --target-dir target/msrv

# Real no_std evidence: this target ships only core/alloc, so any std use fails to link.
nostd:
    cargo +{{msrv}} build --locked --release --target x86_64-unknown-none -p fip-core -p fip-alloc -p fip-arch -p fip-strict -p fip-lint-rules

# Linker flags for the musl targets without a C cross toolchain (`rust-lld`, static).
musl_lld := "-C linker=rust-lld -C linker-flavor=ld.lld -C link-self-contained=yes -C target-feature=+crt-static"

# Other ISAs the arch module realises (incl. Apple aarch64, whose default line is 128 B).
# `cargo check` does not assemble `asm!` templates, and `prefetch_read` is generic and
# `#[inline(always)]`, so only `fip-arch`'s unit tests instantiate it: they are built
# (not run) for aarch64 and riscv64 musl, linked by `rust-lld`, which assembles the
# `prfm` and `ori` templates (needs both musl targets for the ambient toolchain).
cross:
    cargo check --locked -p fip-core -p fip-alloc -p fip-arch -p fip-strict --target aarch64-unknown-linux-gnu
    cargo check --locked -p fip-core -p fip-alloc -p fip-arch -p fip-strict --target riscv64gc-unknown-linux-gnu
    cargo check --locked -p fip-arch --target riscv64gc-unknown-linux-musl
    cargo check --locked -p fip-arch --target riscv64gc-unknown-none-elf
    cargo check --locked -p fip-arch --target aarch64-apple-darwin
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUSTFLAGS="{{musl_lld}}" cargo test --locked -q --no-run -p fip-arch --lib --target aarch64-unknown-linux-musl --target-dir target/cross-asm
    CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_MUSL_RUSTFLAGS="{{musl_lld}}" cargo test --locked -q --no-run -p fip-arch --lib --target riscv64gc-unknown-linux-musl --target-dir target/cross-asm

# All Verus gates: proofs, composition with #[fip], and negative controls.
verify: verus-pin verify-strict verify-core verify-alloc verify-compose verify-negative verify-sidecar

# `VERUS` must be the trusted build (tools/fip-prelint/verus-trusted.txt: version, commit
# and Z3) on the toolchain of `fip-prelint`; every Verus gate depends on this check.
verus-pin:
    #!/usr/bin/env bash
    set -euo pipefail
    pin=tools/fip-prelint/verus-trusted.txt
    want_v=$(awk '$1 == "verus" {print $2}' $pin); want_c=$(awk '$1 == "verus" {print $3}' $pin)
    want_z3=$(awk '$1 == "z3" {print $2}' $pin)
    hint="set VERUS to a build of the pinned Verus ($want_v, commit $want_c; $pin)"
    json=$({{verus}} --version --output-json 2> /dev/null) || { echo "FAIL: cannot run \`{{verus}} --version\`: $hint"; exit 1; }
    field() { printf '%s\n' "$json" | sed -n "s/^ *\"$1\": \"\(.*\)\",\{0,1\}$/\1/p" | head -1; }
    got_v=$(field version); got_c=$(field commit); got_tc=$(field toolchain)
    if [ "$got_v" != "$want_v" ] || [ "$got_c" != "$want_c" ]; then
      echo "FAIL: \`{{verus}}\` is Verus $got_v (commit $got_c): $hint"; exit 1
    fi
    if [ "${got_tc%%-*}" != "{{prelint_tc}}" ]; then
      echo "FAIL: Verus $got_v is built on toolchain $got_tc, fip-prelint on {{prelint_tc}} (tools/fip-prelint/rust-toolchain.toml)"; exit 1
    fi
    if [ -n "${VERUS_Z3_PATH:-}" ]; then z3=$VERUS_Z3_PATH; else z3=$(dirname "$(readlink -f "$(command -v {{verus}})")")/z3; fi
    got_z3=$("$z3" --version 2> /dev/null | awk '/Z3 version/ {print $3}') || true
    if [ "$got_z3" != "$want_z3" ]; then
      echo "FAIL: Z3 \`$z3\` is ${got_z3:-unreadable}, the pin is $want_z3 ($pin; set VERUS_Z3_PATH)"; exit 1
    fi
    echo "verus-pin: Verus $got_v ($got_c), Z3 $got_z3, toolchain $got_tc"

# Verus metadata and library of fip-strict, imported where `FipFn` specs are needed.
verus_strict := "--import fip_strict=target/verus-strict/fip_strict.vir --extern fip_strict=target/verus-strict/libfip_strict.rlib"

# fip-strict proofs (`FipFn` with `pre`/`post`, `Certified`), no trusted items;
# exports the Verus metadata that fip-core and verify-compose import. The run goes
# through the sidecar generator (top plan T13.4); its sidecar must equal
# crates/fip-strict/verus-verified.txt (2 functions listed, `Certified::assume` and
# `Certified::assume_no_panic_macros`; every other verified method is a Verus-only twin
# or macro-generated, each skipped with the reason).
verify-strict: verus-pin sidecar-gen
    rm -rf target/verus-strict && mkdir -p target/verus-strict
    VERUS_SINGULAR_PATH="{{singular}}" {{sidecar_gen}} --crate-name fip_strict --crate-dir crates/fip-strict --out target/verus-strict/verus-verified.txt -- {{verus}} --crate-type=lib --crate-name fip_strict {{verus_flags}} crates/fip-strict/src/lib.rs --export target/verus-strict/fip_strict.vir --compile --out-dir target/verus-strict
    just verus-sidecar-check target/verus-strict/verus-verified.txt crates/fip-strict/verus-verified.txt

# Verus metadata and library of fip-core (needs fip-strict's on the library path),
# imported by verified callers in `verify/`.
verus_core := "--import fip_core=target/verus-core/fip_core.vir --extern fip_core=target/verus-core/libfip_core.rlib -L target/verus-strict"

# Generator of Verus sidecars (top plan T13.4): `cargo fip-prelint --verus-sidecar`, a
# plain binary of tools/fip-prelint (no rustc-dev needed to run it).
sidecar_gen := "tools/fip-prelint/target/debug/cargo-fip-prelint --verus-sidecar"

# Builds the sidecar generator (`--target-dir target`: an exported `CARGO_TARGET_DIR`
# would put it elsewhere, and the recipes would run a stale `sidecar_gen`).
sidecar-gen:
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 cargo +{{prelint_tc}} build --locked -q --bin cargo-fip-prelint --target-dir target

# fip-core proofs, no trusted items (--no-cheating); imports fip-strict's Verus build
# and exports fip-core's for `verify/compose_state.rs`. The run goes through the
# sidecar generator, which writes the verified bodies (top plan T13.4) to
# target/verus-core/verus-verified.txt; it must equal crates/fip-core/verus-verified.txt.
# The import is accepted only with fip-strict's committed sidecar (trusted stamp,
# --no-cheating, unchanged sources) and a VIR file exported by the generator run of
# `verify-strict` (its `.fip-run` record).
verify-core: verify-strict
    rm -rf target/verus-core && mkdir -p target/verus-core
    VERUS_SINGULAR_PATH="{{singular}}" {{sidecar_gen}} --crate-name fip_core --crate-dir crates/fip-core --out target/verus-core/verus-verified.txt --import-sidecar fip_strict=crates/fip-strict/verus-verified.txt -- {{verus}} --crate-type=lib --crate-name fip_core {{verus_flags}} crates/fip-core/src/lib.rs {{verus_strict}} --export target/verus-core/fip_core.vir --compile --out-dir target/verus-core
    just verus-sidecar-check target/verus-core/verus-verified.txt crates/fip-core/verus-verified.txt

# A regenerated Verus sidecar must equal the committed one, so a stale sidecar fails
# `just ci` here (and, in `prelint`, the driver refuses it: the self-check changes).
# Compared only when the run's stamp is the driver's trusted pin
# (tools/fip-prelint/verus-trusted.txt): another Verus build writes its own sidecar,
# which the driver would refuse anyway (the gates' `verus-pin` already refuses such a
# build; this recipe is also run by hand).
# `FIP_VERUS_BLESS=1` copies the regenerated file over the committed one.
verus-sidecar-check generated committed:
    #!/usr/bin/env bash
    set -euo pipefail
    pin_verus=$(awk '$1 == "verus" {print $2, $3}' tools/fip-prelint/verus-trusted.txt)
    pin_z3=$(awk '$1 == "z3" {print $2}' tools/fip-prelint/verus-trusted.txt)
    got_verus=$(awk '$1 == "verus" {print $2, $3}' "{{generated}}")
    got_z3=$(awk '$1 == "z3" {print $2}' "{{generated}}")
    if [ "$got_verus" != "$pin_verus" ] || [ "$got_z3" != "$pin_z3" ]; then
      echo "verus sidecar: stamp Verus $got_verus / Z3 $got_z3 is not the trusted pin ($pin_verus / Z3 $pin_z3): {{committed}} not compared"
      exit 0
    fi
    if [ "${FIP_VERUS_BLESS:-}" = 1 ]; then cp "{{generated}}" "{{committed}}"; echo "verus sidecar: blessed {{committed}}"; exit 0; fi
    if ! cmp -s "{{generated}}" "{{committed}}"; then
      diff -u "{{committed}}" "{{generated}}" || true
      echo "FAIL: {{committed}} is stale (review the diff, then FIP_VERUS_BLESS=1 just verify)"
      exit 1
    fi
    echo "verus sidecar: {{committed}} is up to date"

# fip-alloc proofs, no trusted items (--no-cheating), through the sidecar generator;
# imports fip-strict's Verus build (`fip_strict::AllocFreeDrop` bounds `refill`); the
# sidecar must equal crates/fip-alloc/verus-verified.txt.
verify-alloc: verify-strict
    rm -rf target/verus-alloc && mkdir -p target/verus-alloc
    VERUS_SINGULAR_PATH="{{singular}}" {{sidecar_gen}} --crate-name fip_alloc --crate-dir crates/fip-alloc --out target/verus-alloc/verus-verified.txt --import-sidecar fip_strict=crates/fip-strict/verus-verified.txt -- {{verus}} --crate-type=lib --crate-name fip_alloc {{verus_flags}} crates/fip-alloc/src/lib.rs {{verus_strict}}
    just verus-sidecar-check target/verus-alloc/verus-verified.txt crates/fip-alloc/verus-verified.txt

# `#[fip]` above `verus_spec` verifies; below it, or with an allocation, it is rejected.
# Strict functions with `FipFn` parameters verify against fip-strict's Verus build.
# Callers of the state-passing combinators (incl. a strict one, so with fip-macros)
# verify against fip-core's Verus build.
verify-compose: verify-strict verify-core
    #!/usr/bin/env bash
    set -euo pipefail
    tc=$({{verus}} --version | awk '/Toolchain/ {print $2}')
    cargo +"$tc" build --locked -q -p fip-macros --target-dir target/verus-macros
    deps=target/verus-macros/debug/deps
    so=$(ls -t $deps/libfip_macros-*.so | head -1)
    run() { VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" {{verus_strict}} -L "$deps" "$1"; }
    run verify/compose.rs
    run verify/compose_strict.rs
    run_state() { VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" -L "$deps" {{verus_strict}} {{verus_core}} "$1"; }
    run_state verify/compose_state.rs
    run_state verify/alloc_callers.rs
    out=target/verify-compose; mkdir -p "$out"
    # `fip_fn!` values have one type in both builds: verify/fip_fn_types.rs is compiled
    # by plain rustc and verified by Verus; a wrong `N` in any annotation fails both.
    cargo +"$tc" build --locked -q -p fip-strict --target-dir target/verus-macros
    rl=$(ls -t $deps/libfip_strict-*.rlib | head -1)
    plain() { rustc +"$tc" --edition 2024 --crate-type lib --crate-name fip_fn_types --extern fip_macros="$so" --extern fip_strict="$rl" -L "$deps" --out-dir "$out" "$1"; }
    plain verify/fip_fn_types.rs
    run verify/fip_fn_types.rs
    for m in 's/let boxing: Certified<1, _>/let boxing: Certified<0, _>/' 's/let limited: Certified<2, _>/let limited: Certified<0, _>/' 's/step: Certified<1, C>/step: Certified<0, C>/'; do
      sed "$m" verify/fip_fn_types.rs > "$out/types.rs"
      if cmp -s verify/fip_fn_types.rs "$out/types.rs"; then echo "FAIL: mutation $m did not apply"; exit 1; fi
      if plain "$out/types.rs" 2> "$out/types-plain.err"; then echo "FAIL: plain build accepted $m"; exit 1; fi
      if run "$out/types.rs" 2> "$out/types-verus.err"; then echo "FAIL: Verus accepted $m"; exit 1; fi
      grep -q "E0308" "$out/types-plain.err" && grep -q "E0308" "$out/types-verus.err" || { echo "FAIL: $m rejected for another reason"; cat "$out/types-plain.err" "$out/types-verus.err"; exit 1; }
    done
    # A closure calling a certified function has no literal bound: rejected under Verus.
    cp verify/fip_fn_types.rs "$out/types.rs"
    printf '\n#[cfg_attr(verus_keep_ghost, verus_spec())]\npub fn calls() {\n    let _f = fip_fn!(|x: u32| halve(x));\n}\n' >> "$out/types.rs"
    plain "$out/types.rs"
    if run "$out/types.rs" 2> "$out/types-verus.err"; then echo "FAIL: Verus accepted a fip_fn! closure without a literal bound"; exit 1; fi
    grep -q "has no literal allocation bound" "$out/types-verus.err" || { echo "FAIL: closure with calls rejected for another reason"; cat "$out/types-verus.err"; exit 1; }
    sed 's/^#\[fip\]$//; s/^pub fn count/#[fip]\npub fn count/' verify/compose.rs > "$out/below.rs"
    if run "$out/below.rs" 2> "$out/below.err"; then echo "FAIL: #[fip] below verus_spec was accepted"; exit 1; fi
    grep -q "write FIP attributes above" "$out/below.err"
    sed 's/^extern crate alloc;$//' verify/compose.rs \
      | sed 's/#!\[no_std\]/#![no_std]/' \
      | awk '{print} /feature\(proc_macro_hygiene\)/ {print "extern crate alloc;"} /^        i \+= 1;$/ {print "        let _b = alloc::boxed::Box::new(i);"}' > "$out/alloc.rs"
    if run "$out/alloc.rs" 2> "$out/alloc.err"; then echo "FAIL: allocation inside #[fip] was accepted"; exit 1; fi
    grep -q "allocation site \`Box::new\`" "$out/alloc.err"
    # `requires(..)` of `#[fip]` that is not in the `verus_spec` requires: rejected.
    sed 's/^#\[fip(requires(i < xs.len()))\]$/#[fip(requires(i <= xs.len()))]/' verify/compose.rs > "$out/drift.rs"
    if cmp -s verify/compose.rs "$out/drift.rs"; then echo "FAIL: mutation drift did not apply"; exit 1; fi
    if run "$out/drift.rs" 2> "$out/drift.err"; then echo "FAIL: requires(..) drifting from verus_spec was accepted"; exit 1; fi
    grep -q "is not in the \`requires\` of \`verus_spec\`" "$out/drift.err"
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
    tc=$({{verus}} --version | awk '/Toolchain/ {print $2}')
    cargo +"$tc" build --locked -q -p fip-macros --target-dir target/verus-macros
    deps=target/verus-macros/debug/deps
    so=$(ls -t $deps/libfip_macros-*.so | head -1)
    mutate() {  # name, crate dir, file, sed script -> prints mutant dir
      local d="$out/$1"; cp -r "crates/$2" "$d"
      sed -i "$4" "$d/src/$3"
      if cmp -s "crates/$2/src/$3" "$d/src/$3"; then echo "FAIL: mutation $1 did not apply" >&2; exit 1; fi
      echo "$d"
    }
    # `--multiple-errors 8`: report up to 8 failing checks per function (default 2), so the
    # regex finds the intended failure even when an earlier check fails too (e.g. a
    # reversed loop now fails `f`'s indexed precondition before the state chain).
    # A mutant that hits the resource limit fails the gate: a timeout says nothing
    # about the spec. Optional sixth argument: extra Verus flags (e.g. `--rlimit 100`).
    expect_verus_fail() {  # name, crate, file, sed script, expected log regex[, verus flags]
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --multiple-errors 8 ${6:-} "$d/src/lib.rs" {{verus_strict}} > "$d/log" 2>&1; then
        echo "FAIL: mutant $1 verified"; exit 1
      fi
      if grep -q "rlimit" "$d/log"; then echo "FAIL: mutant $1 hit the resource limit (rlimit)"; cat "$d/log"; exit 1; fi
      grep -Eq "$5" "$d/log" || { echo "FAIL: mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected by Verus"
    }
    errs='verification results:: .* [1-9][0-9]* errors'
    # Functional mutants must break a loop invariant or the postcondition (the spec),
    # not a proof step left behind: where the mutation strands a proof assertion about
    # the removed code, the sed script deletes that assertion too (the unmutated
    # function verifies without it, measured 2026-11-04 for `dedup_by`). The `dedup_by`
    # mutants hit the default resource limit on the loop before the invariant fails, so
    # they run with a larger one (1000 for both: measured at 100 and 300 still rlimit
    # for the strict one, and on the Verus fork `ca33b04` for the plain one too, with and
    # without `-V alloc-check`, 2026-11-06; on 10.18 the plain one needed 100).
    spec='postcondition not satisfied|invariant not satisfied'
    # `compact_map` without the swap: the kept element at `w` is not the mapped value,
    # which `lemma_prefix_push` requires (`new_s[w] == ys[r]`); its asserts about the
    # swap are deleted. Measured: the unmutated function with the same asserts deleted
    # fails only a loop invariant, never this precondition.
    cmap_order='new_s\[w\] == ys\[r\]'
    no_swap_asserts='/^                    assert(xs@.subrange(0, r as int + 1) =~= p.update(w as int, p\[r as int\]).update(r as int, p\[w as int\]));$/d; /^                assert(xs@\[w as int\] == mapped);$/d'
    # Functional specs.
    expect_verus_fail compact-no-swap      fip-core  slice.rs '/^pub fn compact</,/^}/ s/^                swap_lt(xs, w, r);$//' "$spec"
    expect_verus_fail compact-order        fip-core  slice.rs '/^pub fn compact</,/^}/ s/idx = idx.push(r as int);/idx = idx.push(0);/' "$spec"
    expect_verus_fail map-skips-store      fip-core  slice.rs '/^pub fn map_in_place</,/^}/ s/^        spare = crate::slot::replace(&mut xs\[i\], next);$/        spare = next;/' "$spec"
    expect_verus_fail update-keeps-old     fip-core  slot.rs  's/^    let next = f(prev);$/    let next = prev; let _ = f;/' "$spec"
    expect_verus_fail dedup-no-swap        fip-core  slice.rs '/^pub fn dedup_by</,/^}/ { s/^                swap_lt(xs, w, r);$//; /^                assert(xs@\[ow\] == old(xs)@\[r as int\]);$/d }' "$spec" "--rlimit 1000"
    expect_verus_fail dedup-wrong-compare  fip-core  slice.rs '/^pub fn dedup_by</,/^}/ s/same(&xs\[w - 1\], &xs\[r\])/same(\&xs[r - 1], \&xs[r])/' "$spec"
    expect_verus_fail compact-map-no-swap  fip-core  slice.rs "/^pub fn compact_map</,/^}/ { s/^                swap_lt(xs, w, r);\$//; $no_swap_asserts }" "$cmap_order"
    expect_verus_fail compact-map-invert   fip-core  slice.rs '/^pub fn compact_map</,/^}/ s/^        if keep {$/        if !keep {/' "$spec"
    expect_verus_fail refill-no-swap       fip-alloc lib.rs   's/^    ::core::mem::swap(&mut \*cell, &mut prev);$//' "$spec"
    # Allocation bounds (`allocates`, decision 2026-11-06-redesign-verus-allocates, phase 2):
    # each mutant must fail a verification condition whose reported span is the
    # allocation layer (an `allocates` clause, an `allocated()` invariant or a
    # `call_allocates` requirement), not a functional one.
    expect_alloc_fail() {  # name, crate, file, sed script, regex expected in the failing span
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --multiple-errors 8 "$d/src/lib.rs" {{verus_strict}} > "$d/log" 2>&1; then
        echo "FAIL: mutant $1 verified"; exit 1
      fi
      if grep -q "rlimit" "$d/log"; then echo "FAIL: mutant $1 hit the resource limit (rlimit)"; cat "$d/log"; exit 1; fi
      grep -A12 -E "^error: (postcondition|precondition|invariant) not satisfied" "$d/log" | grep -Eq "$5" \
        || { echo "FAIL: mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected by Verus"
    }
    # A `Box::new` in an `allocates 0` body (fip-core links no `alloc`, so the mutant
    # adds `extern crate alloc;` to the module) and in a loop bounded by the callbacks' sum.
    ext_alloc='0,/^#\[cfg(verus_keep_ghost)\]$/ s//extern crate alloc;\n&/'
    expect_alloc_fail swap-allocates        fip-core  slice.rs "$ext_alloc"'; /^pub fn swap</,/^}/ s/^        swap_lt(xs, lo, hi);$/        swap_lt(xs, lo, hi);\n        let _b = alloc::boxed::Box::new(0u8);/' 'allocates 0'
    expect_alloc_fail map-allocates         fip-core  slice.rs "$ext_alloc"'; /^pub fn map_in_place</,/^}/ s/^        i += 1;$/        let _b = alloc::boxed::Box::new(0u8);\n        i += 1;/' 'allocated\(\) <= crate::spec::map_allocs'
    expect_alloc_fail refill-allocates      fip-alloc lib.rs   's/^    ::core::mem::swap(&mut \*cell, &mut prev);$/    ::core::mem::swap(\&mut *cell, \&mut prev);\n    let _b = Box::new(0u8);/' 'allocates 0'
    # A sum spec that forgets the last call cannot bound the loop.
    expect_alloc_fail map-sum-drops-call    fip-core  spec.rs  's/^    if n <= 0 { 0 } else { map_allocs(f, s, n - 1) + call_allocates(f, (s\[n - 1\],)) }$/    if n <= 0 { 0 } else { map_allocs(f, s, n - 1) }/' 'allocated\(\) <= crate::spec::map_allocs'
    expect_alloc_fail compact-sum-drops-call fip-core spec.rs  's/^    if n <= 0 { 0 } else { compact_allocs(keep, s, n - 1) + call_allocates(keep, (&s\[n - 1\],)) }$/    if n <= 0 { 0 } else { compact_allocs(keep, s, n - 1) }/' 'allocated\(\) <= crate::spec::compact_allocs'
    # `map_in_place_st` is `allocates 0` only because every call is required to be.
    expect_alloc_fail map-st-alloc-unrequired fip-core slice.rs '/^        map_st_by_ok(old(xs)@, f, s0),$/ { n; /call_allocates/d; }' 'call_allocates\(f, \(s, x\)\) <= 0'
    # Strict callables (phase 3): `FipFn::call` allocates at most `allocs()`. A strict
    # combinator calling its callable twice per element breaks `len * f.allocs()`;
    # `Compose` claiming one allocation less than its parts, and `Certified` without
    # the `call_allocates(..) <= ALLOCS` conjunct of `pre`, break `call`'s bound.
    expect_alloc_fail strict-compact-calls-twice fip-core strict.rs '/^pub fn compact</,/^}/ s/^        if keep.call((&xs\[r\],)) {$/        let _again = keep.call((\&xs[r],));\n        if keep.call((\&xs[r],)) {/' 'allocated\(\) <= r \* keep\.allocs\(\)'
    expect_alloc_fail compose-sum-minus-one   fip-strict lib.rs '/^macro_rules! compose_fip_fn/,/^}/ s/^                self.0.allocs() + self.1.allocs()$/                (self.0.allocs() + self.1.allocs() - 1) as nat/' 'allocates self\.allocs\(\)'
    expect_alloc_fail certified-pre-no-alloc  fip-strict lib.rs '/^                &&& call_allocates(self.inner(), args) <= ALLOCS as int$/d' 'allocates self\.allocs\(\)'
    # Strict variants (`FipFn` callables), same mutations.
    expect_verus_fail strict-compact-no-swap     fip-core strict.rs '/^pub fn compact</,/^}/ s/^                crate::slice::swap_lt(xs, w, r);$//' "$spec"
    expect_verus_fail strict-compact-order       fip-core strict.rs '/^pub fn compact</,/^}/ s/idx = idx.push(r as int);/idx = idx.push(0);/' "$spec"
    expect_verus_fail strict-map-skips-store     fip-core strict.rs '/^pub fn map_in_place</,/^}/ s/^        spare = crate::slot::replace(&mut xs\[i\], next);$/        spare = next;/' "$spec"
    expect_verus_fail strict-update-keeps-old    fip-core strict.rs '/^pub fn update</,/^}/ s/^    let next = f.call((prev,));$/    let next = prev; let _ = \&f;/' "$spec"
    expect_verus_fail strict-dedup-no-swap       fip-core strict.rs '/^pub fn dedup_by</,/^}/ { s/^                crate::slice::swap_lt(xs, w, r);$//; /^                assert(xs@\[ow\] == old(xs)@\[r as int\]);$/d }' "$spec" "--rlimit 1000"
    expect_verus_fail strict-dedup-wrong-compare fip-core strict.rs '/^pub fn dedup_by</,/^}/ s/same.call((&xs\[w - 1\], &xs\[r\]))/same.call((\&xs[r - 1], \&xs[r]))/' "$spec"
    expect_verus_fail strict-compact-map-no-swap fip-core strict.rs "/^pub fn compact_map</,/^}/ { s/^                crate::slice::swap_lt(xs, w, r);\$//; $no_swap_asserts }" "$cmap_order"
    expect_verus_fail strict-compact-map-invert  fip-core strict.rs '/^pub fn compact_map</,/^}/ s/^        if keep {$/        if !keep {/' "$spec"
    # State-passing variants: the state must be threaded once per element, in index
    # order. Each must fail on the state-chain invariant or assertion, not elsewhere.
    chain='\(ss\[[jk]\], old\(xs\)@\[[jk]\]\), \(ss\[[jk] \+ 1\]'
    expect_verus_fail map-st-reverse-order              fip-core slice.rs  '/^pub fn map_in_place_st</,/^}/ s/&mut xs\[i\]/\&mut xs[n - 1 - i]/g' "$chain"
    expect_verus_fail map-st-not-threaded               fip-core slice.rs  '/^pub fn map_in_place_st</,/^}/ { s/^    S: crate::AllocFreeDrop,$/    S: crate::AllocFreeDrop + Copy,/; s/^        s = s1;$/        let _ = s1;/ }' "$chain"
    expect_verus_fail compact-map-st-not-threaded       fip-core slice.rs  '/^pub fn compact_map_st</,/^}/ { s/^    S: crate::AllocFreeDrop,$/    S: crate::AllocFreeDrop + Copy,/; s/^        s = s1;$/        let _ = s1;/ }' "$chain"
    expect_verus_fail compact-map-st-reverse-order      fip-core slice.rs  '/^pub fn compact_map_st</,/^}/ s/&mut xs\[r\]/\&mut xs[len - 1 - r]/g' "$chain"
    expect_verus_fail strict-map-st-reverse-order       fip-core strict.rs '/^pub fn map_in_place_st</,/^}/ s/&mut xs\[i\]/\&mut xs[n - 1 - i]/g' "$chain"
    expect_verus_fail strict-map-st-not-threaded        fip-core strict.rs '/^pub fn map_in_place_st</,/^}/ { s/^    S: crate::AllocFreeDrop,$/    S: crate::AllocFreeDrop + Copy,/; s/^        s = s1;$/        let _ = s1;/ }' "$chain"
    expect_verus_fail strict-compact-map-st-not-threaded fip-core strict.rs '/^pub fn compact_map_st</,/^}/ { s/^    S: crate::AllocFreeDrop,$/    S: crate::AllocFreeDrop + Copy,/; s/^        s = s1;$/        let _ = s1;/ }' "$chain"
    # Pre-verified state spec: without the state chain, the rejecting lemmas fail.
    expect_verus_fail spec-st-no-chain fip-core spec.rs '/^    pub open spec fn map_st_post</,/^    }/ s/^        &&& forall|k: int| 0 <= k < old.len() ==> step(.*$/        \&\&\& true/' "$errs"
    # State invariants and named traces (`spec::state`). A weakened invariant spec must
    # fail the pre-verification lemma that rejects the case it no longer excludes; a trace
    # chosen for another run must fail the postcondition that names it; an
    # implementation that stops carrying the invariants must fail `f`'s precondition at
    # the call.
    expect_verus_fail spec-st-inv-no-preserve           fip-core spec.rs   '/^    pub open spec fn map_st_by_inv</,/^    }/ s/(s2, y)) ==> inv(k + 1, s2)$/(s2, y)) ==> true/' '!map_st_by_inv\(seq!\[0u8, 0u8, 0u8\], f, 10u8, \|k: int, c: u8\| c < 13\)'
    expect_verus_fail spec-st-fip-inv-no-start          fip-core spec.rs   '/^    pub open spec fn map_st_fip_inv</,/^    }/ s/^        &&& inv(0, s0)$/        \&\&\& true/' 'assert\(inv\(3, 13u8\)\)'
    expect_verus_fail spec-compact-st-inv-no-require    fip-core spec.rs   '/^    pub open spec fn compact_map_st_by_inv</,/^    }/ s/==> #\[trigger\] f.requires((s, old\[k\]))$/==> #[trigger] f.requires((s, old[k])) || true/' '!compact_map_st_by_inv\(old4, f, 10u8, inv\)'
    expect_verus_fail spec-compact-st-fip-inv-no-preserve fip-core spec.rs '/^    pub open spec fn compact_map_st_fip_inv</,/^    }/ s/(s2, y, b)) ==> inv(k + 1, s2)$/(s2, y, b)) ==> true/' '!compact_map_st_fip_inv\(seq!\[1u8, 2u8, 3u8\], c, 10u8, \|k: int, c: u8\| c < 13\)'
    expect_verus_fail spec-st-ok-vacuous                fip-core spec.rs   '/^    pub open spec fn map_st_by_ok</,/^    }/ s/#\[trigger\] map_st_by_inv(old, f, s0, inv)$/#[trigger] map_st_by_inv(old, f, s0, inv) || true/' '!map_st_by_ok\(seq!\[0u8, 0u8, 0u8, 0u8\], f, 10u8\)'
    expect_verus_fail spec-st-trace-inv-drops-last      fip-core spec.rs   '/^    pub open spec fn st_trace_inv</,/^    }/ s/0 <= k < ss.len() ==>/0 <= k < ss.len() - 1 ==>/' '!st_trace_inv\(seq!\[10u8, 11u8, 12u8, 14u8\]'
    expect_verus_fail spec-st-trace-other-run           fip-core spec.rs   '/^    pub open spec fn map_st_by_trace</,/^    }/ s/map_st_by_post(old, new, f, s0, s, ss)$/map_st_by_post(old, old, f, s0, s, ss)/' 'map_st_by_post\(old\(xs\)@, final\(xs\)@, f, s0, r.0, map_st_by_trace'
    expect_verus_fail spec-compact-st-fip-witnesses-other-run fip-core spec.rs '/^    pub open spec fn compact_map_st_fip_witnesses</,/^    }/ s/compact_map_st_fip_post(old, new, w, f, s0, s, ss, ys, ks, idx, pos)$/compact_map_st_fip_post(old, old, w, f, s0, s, ss, ys, ks, idx, pos)/' 'compact_map_st_fip_witnesses\(old\(xs\)@, final\(xs\)@'
    expect_verus_fail map-st-inv-not-carried            fip-core slice.rs  '/^pub fn map_in_place_st</,/^}/ { /^            forall|inv: spec_fn(int, S) -> bool| #\[trigger\] map_st_by_inv(old(xs)@, f, s0, inv) ==> st_trace_inv(ss, inv),$/d }' 'let \(s1, next\) = f\(s, prev\);'
    expect_verus_fail strict-compact-map-st-inv-not-carried fip-core strict.rs '/^pub fn compact_map_st</,/^}/ { /^            forall|inv: spec_fn(int, S) -> bool| #\[trigger\] compact_map_st_fip_inv(old(xs)@, f, s0, inv) ==> st_trace_inv(ss, inv),$/d }' 'let \(s1, mapped, keep\) = f\.call\(\(s, item\)\);'
    # Verified callers (verify/compose_state.rs): wrong final claims, a missing
    # invariant and an invariant the step does not preserve must be rejected.
    state_fail() {  # name, sed script, expected log regex
      local f="$out/state_$1.rs"
      sed "$2" verify/compose_state.rs > "$f"
      if cmp -s verify/compose_state.rs "$f"; then echo "FAIL: control $1 did not apply"; exit 1; fi
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" -L "$deps" {{verus_strict}} {{verus_core}} "$f" > "$out/state_$1.log" 2>&1; then
        echo "FAIL: control $1 verified"; exit 1
      fi
      if grep -q "rlimit" "$out/state_$1.log"; then echo "FAIL: control $1 hit the resource limit (rlimit)"; cat "$out/state_$1.log"; exit 1; fi
      grep -Eq "$3" "$out/state_$1.log" || { echo "FAIL: control $1 failed for another reason"; cat "$out/state_$1.log"; exit 1; }
      echo "control $1 rejected by Verus"
    }
    state_fail wrong-final-map      's/^        r == 13,$/        r == 14,/' 'postcondition not satisfied'
    state_fail wrong-final-compact  's/^        r == 2,$/        r == 3,/' 'postcondition not satisfied'
    state_fail inv-missing          '/^pub fn number_from_11(/,/^}/ { /^    proof! { assert(map_st_by_inv(/d }' 'precondition not satisfied'
    state_fail inv-not-preserved    '/^pub fn number_from_11(/,/^}/ s/|k: int, c: u32| c == 10 + k)); }$/|k: int, c: u32| c < 1000)); }/' 'c: u32\| c < 1000\)\); \}'
    state_fail strict-inv-missing   '/^pub fn number_from_11_strict(/,/^}/ { /^    proof! { assert(map_st_fip_inv(/d }' 'precondition not satisfied'
    state_fail strict-wrong-final   '/^\/\/\/ `number_from_11` through/,/^}/ s/^        r == 10 + old(xs)@.len(),$/        r == 11 + old(xs)@.len(),/' 'postcondition not satisfied'
    state_fail keep-odd-inv-missing '/^pub fn keep_odd(/,/^}/ { /^    proof! { assert(compact_map_st_by_inv(/d }' 'precondition not satisfied'
    # A `fip_fn!` closure without its `verus_spec` attribute promises nothing, so the
    # invariant cannot be shown preserved; a closure body breaking its `ensures` fails.
    state_fail closure-spec-missing '/^pub fn number_from_11_closure(/,/^}/ { /^        #\[cfg_attr(verus_keep_ghost, verus_spec(r: (u32, u32) =>$/,/^        ))\]$/d; }' 'map_st_fip_inv\(old\(xs\)@, f, 10u32, \|k: int, c: u32\| c == 10 \+ k\)\); \}'
    state_fail closure-wrong-ensures '/^pub fn number_from_11_closure(/,/^}/ s/^                r.0 == c + 1,$/                r.0 == c + 2,/' 'unable to prove post-condition of closure'
    # Adapters: `Stateless` / `Compose` promise only what the wrapped closures do.
    state_fail stateless-wrong-final '/^\/\/\/ Doubles every element through/,/^}/ s/final(xs)@\[k\] == 2 \* old(xs)@\[k\],$/final(xs)@[k] == 3 * old(xs)@[k],/' 'postcondition not satisfied'
    state_fail compose-wrong-final   '/^\/\/\/ Multiplies every element by 4/,/^}/ s/final(xs)@\[k\] == 4 \* old(xs)@\[k\],$/final(xs)@[k] == 5 * old(xs)@[k],/' 'postcondition not satisfied'
    state_fail compose-pre-missing   '/^\/\/\/ Multiplies every element by 4/,/^}/ s/old(xs)@\[k\] < 250,$/old(xs)@[k] < 1000,/' 'precondition not satisfied'
    # `Then` promises only what both steps do: a wrong final claim, and a counter step
    # whose output breaks the doubling step's `requires`.
    state_fail then-wrong-final      '/^\/\/\/ Numbers from 11 and doubles/,/^}/ s/final(xs)@\[k\] == 2 \* (11 + k),$/final(xs)@[k] == 2 * (12 + k),/' 'postcondition not satisfied'
    state_fail then-pre-missing      '/^\/\/\/ Numbers from 11 and doubles/,/^}/ s/^        old(xs)@.len() < 990,$/        old(xs)@.len() < 1990,/' 'precondition not satisfied|assertion failed'
    # `allocates 0` (Verus fork, `-V alloc-check`): a `Box::new` in a step function or
    # in a `fip_fn!` closure carrying `allocates 0` must fail that clause. Also shows
    # that the gate runs with `-V alloc-check` (without it both mutants verify).
    alloc_fail() {  # name, sed script
      local f="$out/state_$1.rs"
      sed 's/^use fip_macros::fip;$/use fip_macros::fip;\nextern crate alloc;/'"; $2" verify/compose_state.rs > "$f"
      if ! grep -q "alloc::boxed::Box::new" "$f"; then echo "FAIL: control $1 did not apply"; exit 1; fi
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" -L "$deps" {{verus_strict}} {{verus_core}} "$f" > "$out/state_$1.log" 2>&1; then
        echo "FAIL: control $1 verified"; exit 1
      fi
      grep -A3 -E "postcondition not satisfied|unable to prove post-condition of closure" "$out/state_$1.log" | grep -q "allocates 0" \
        || { echo "FAIL: control $1 failed for another reason"; cat "$out/state_$1.log"; exit 1; }
      echo "control $1 rejected by Verus"
    }
    alloc_fail step-allocates    '/^pub fn tick(/,/^}/ s/^    (n, n)$/    let _b = alloc::boxed::Box::new(n);\n    (n, n)/'
    alloc_fail closure-allocates '/^pub fn doubled_stateless(/,/^}/ s/^        |x: u32| x \* 2$/        |x: u32| { let _b = alloc::boxed::Box::new(x); x * 2 }/'
    # Verified callers of fip-core's `allocates` bounds (verify/alloc_callers.rs): an
    # allocating closure fails its own bound; a closure without a bound fails the
    # caller's `allocates 0` (sum-bounded callee) or the callee's requirement
    # (`dedup_by`); without the zero-sum lemmas the sum-bounded callers fail.
    callers_fail() {  # name, sed script, expected error, regex expected in the failing span
      local f="$out/callers_$1.rs"
      sed "$2" verify/alloc_callers.rs > "$f"
      if cmp -s verify/alloc_callers.rs "$f"; then echo "FAIL: control $1 did not apply"; exit 1; fi
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" -L "$deps" {{verus_strict}} {{verus_core}} "$f" > "$out/callers_$1.log" 2>&1; then
        echo "FAIL: control $1 verified"; exit 1
      fi
      grep -A12 -E "^error: $3" "$out/callers_$1.log" | grep -Eq "$4" \
        || { echo "FAIL: control $1 failed for another reason"; cat "$out/callers_$1.log"; exit 1; }
      echo "control callers-$1 rejected by Verus"
    }
    callers_fail closure-allocates '/^pub fn evens(/,/^}/ s/allocates 0 { \*v % 2 == 0 }/allocates 0 { let _b = Box::new(0u8); *v % 2 == 0 }/' 'unable to prove post-condition of closure' 'Box::new'
    callers_fail closure-unbounded '/^pub fn evens(/,/^}/ s/-> (r: bool) allocates 0 {/-> (r: bool) {/' 'postcondition not satisfied' 'allocates 0'
    callers_fail dedup-unbounded   '/^pub fn deduped(/,/^}/ s/-> (r: bool) allocates 0 {/-> (r: bool) {/' 'precondition not satisfied' 'call_allocates\(same'
    callers_fail no-zero-lemmas    '/^broadcast use fip_core::spec::group_allocs_zero;$/d' 'postcondition not satisfied' 'allocates 0'
    # A `Certified<0, _>` wrapping a closure that allocates once: `Certified::pre`
    # (`call_allocates(closure, args) <= 0`; the closure has no `requires`) fails.
    callers_fail certified0-allocating '/^pub fn boxed_once(/,/^}/ s/Certified::<1, _, false>/Certified::<0, _, false>/' 'precondition not satisfied' 'self\.pre\(args\)'
    # `fip_fn!(path)` without `bound` is a `Certified<0, _>` under Verus (it reads no
    # certificate): for the allocating `boxed` (verify/fip_fn_types.rs) the verified
    # caller fails `Certified::pre` (`boxed` has no `requires`, so the failing part is
    # `call_allocates(boxed, (x,)) <= 0`).
    f="$out/types_path_no_bound.rs"
    sed 's/^    let f = fip_fn!(bound <= 1, boxed);$/    let f = fip_fn!(boxed);/' verify/fip_fn_types.rs > "$f"
    if cmp -s verify/fip_fn_types.rs "$f"; then echo "FAIL: control types-path-no-bound did not apply"; exit 1; fi
    if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" -L "$deps" {{verus_strict}} "$f" > "$out/types_path_no_bound.log" 2>&1; then
      echo "FAIL: control types-path-no-bound verified"; exit 1
    fi
    grep -A12 -E "^error: precondition not satisfied" "$out/types_path_no_bound.log" | grep -Eq 'self\.pre\(args\)' \
      || { echo "FAIL: control types-path-no-bound failed for another reason"; cat "$out/types_path_no_bound.log"; exit 1; }
    echo "control types-path-no-bound rejected by Verus"
    # Pre-verified spec of the strict variants: a wrong relation breaks the lemmas.
    expect_verus_fail spec-fip-wrong-relation    fip-core spec.rs   '/^pub open spec fn compact_fip_post</,/^}/ s/keep.post((&a,), r)/keep.post((\&a,), !r)/' "$errs"
    # fip-strict: `Certified::pre` must be the closure's `requires`.
    expect_verus_fail certified-pre-true         fip-strict lib.rs  's/^                &&& self.inner().requires(args)$/                \&\&\& true/' "$errs"
    # Stack bound: recursion without `decreases` is rejected.
    expect_verus_fail swap-recursive       fip-core  slice.rs '/^pub fn swap</,/^}/ s/^        swap_lt(xs, lo, hi);$/        swap_lt(xs, lo, hi);\n        swap(xs, lo, lo);/' 'recursive function must have a .?decreases.? clause'
    # Source gates (fip_testkit::surface) must fail on mutated sources.
    expect_test_fail() {  # name, crate, file, sed script, test name
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      if FIP_SURFACE_SRC="$PWD/$d/src" cargo test --locked -q -p "$2" --test verified_surface "$5" > "$d/log" 2>&1; then
        echo "FAIL: surface mutant $1 passed"; exit 1
      fi
      grep -q "test result: FAILED" "$d/log" || { echo "FAIL: surface mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected by the surface gate"
    }
    expect_test_fail surface-unspecified fip-core slot.rs '0,/^#\[cfg_attr(verus_keep_ghost, verus_spec(r =>$/{/^#\[cfg_attr(verus_keep_ghost, verus_spec(r =>$/,/^))\]$/d}' every_function_is_specified
    expect_test_fail surface-decreases   fip-core slot.rs '0,/^    ensures$/ s/^    ensures$/    decreases 0nat,\n    ensures/' no_function_may_recurse
    expect_test_fail surface-no-decreases-attr fip-core slot.rs '0,/^#\[cfg_attr(verus_keep_ghost, verus_spec(r =>$/ s/^#\[cfg_attr(verus_keep_ghost, verus_spec(r =>$/#[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]\n&/' no_unlisted_verifier_attribute
    # Drift gate (fip-strict): the Verus `FipFn::call` must match the plain one.
    d=$(mutate drift-call fip-strict lib.rs 's/^    fn call(&self, args: Args) -> (r: Self::Output)$/    fn call(\&self, args: Args, extra: u8) -> (r: Self::Output)/')
    if FIP_DRIFT_SRC="$PWD/$d/src/lib.rs" cargo test --locked -q -p fip-strict --test verus_drift > "$d/log" 2>&1; then
      echo "FAIL: drift mutant passed"; exit 1
    fi
    grep -q "test result: FAILED" "$d/log" || { echo "FAIL: drift mutant failed for another reason"; cat "$d/log"; exit 1; }
    echo "mutant drift-call rejected by the drift test"
    # The per-arity Verus `Compose` impls must match the plain generic one.
    d=$(mutate drift-compose fip-strict lib.rs '/^macro_rules! compose_fip_fn/,/^}/ s/^                self.1.call((y,))$/                self.1.call((y,)); self.1.call((y,))/')
    if FIP_DRIFT_SRC="$PWD/$d/src/lib.rs" cargo test --locked -q -p fip-strict --test verus_drift > "$d/log" 2>&1; then
      echo "FAIL: drift mutant drift-compose passed"; exit 1
    fi
    grep -q "test result: FAILED" "$d/log" || { echo "FAIL: drift mutant drift-compose failed for another reason"; cat "$d/log"; exit 1; }
    echo "mutant drift-compose rejected by the drift test"
    echo "verify-negative: ok"

# The Verus sidecar of the driver fixture (tools/fip-prelint/tests/fixtures/verus_sidecar)
# is regenerated and compared like fip-core's; the generator refuses a run without
# `--no-cheating`; an `external_body` function makes the `--no-cheating` run fail, so no
# sidecar lists it (the VIR filter is unit-tested in src/verusgen.rs). The soundness
# audit's probes (2026-11-04): an item whose text deletes code for Verus only is
# skipped; a crate testing `fip_prelint` gets no sidecar; an `--import` without the
# imported crate's committed sidecar, or of a VIR file no generator run exported, is
# refused. The re-audit's probes (N3, N4): a crate with a macro-built `cfg!`, an
# `option_env!` or a `#[path]` module outside `src/` testing `fip_prelint` gets no
# sidecar; a caller of a function skipped for its cfg is skipped.
verify-sidecar: verify-strict
    #!/usr/bin/env bash
    set -euo pipefail
    (cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 cargo +{{prelint_tc}} build --locked -q --bin cargo-fip-prelint --target-dir target)
    gen="$PWD/tools/fip-prelint/target/debug/cargo-fip-prelint --verus-sidecar"
    out="$PWD/target/verify-sidecar"; rm -rf "$out"; mkdir -p "$out"
    fx=tools/fip-prelint/tests/fixtures/verus_sidecar
    (cd "$fx" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name vside --crate-dir vside --out "$out/vside.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs)
    just verus-sidecar-check "$out/vside.txt" "$fx/vside/verus-verified.txt"
    # Without --no-cheating: refused before Verus runs, nothing written.
    if (cd "$fx" && $gen --crate-name vside --crate-dir vside --out "$out/cheat.txt" -- {{verus}} --crate-type=lib --crate-name vside vside/src/lib.rs) 2> "$out/cheat.err"; then
      echo "FAIL: a sidecar was generated without --no-cheating"; exit 1
    fi
    grep -q "must use \`--no-cheating\`" "$out/cheat.err"
    test ! -e "$out/cheat.txt"
    # An `external_body` function: Verus rejects the --no-cheating run, nothing written.
    cp -r "$fx" "$out/ext"
    printf '\n#[cfg_attr(verus_keep_ghost, verifier::external_body)]\npub fn ext() -> u32 { 2 }\n' >> "$out/ext/vside/src/lib.rs"
    if (cd "$out/ext" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name vside --crate-dir vside --out "$out/ext.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs) > "$out/ext.log" 2>&1; then
      echo "FAIL: a sidecar was generated for a crate with external_body"; exit 1
    fi
    grep -q "Verus failed: no sidecar written" "$out/ext.log"
    test ! -e "$out/ext.txt"
    # A Verus-only `cfg_attr` deleting a bounds check: verified, but not listed.
    cp -r "$fx" "$out/cfgitem"
    printf '\n#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]\n#[cfg_attr(verus_keep_ghost, verus_spec(\n    requires\n        i < xs@.len(),\n))]\npub fn probe2(xs: &[u8], i: usize) -> u8 {\n    #[cfg_attr(verus_keep_ghost, cfg(any()))]\n    let _x = xs[i + 1];\n    xs[i]\n}\n' >> "$out/cfgitem/vside/src/lib.rs"
    (cd "$out/cfgitem" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name vside --crate-dir vside --out "$out/cfgitem.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs) > "$out/cfgitem.log" 2>&1
    if grep -q "^fn vside::probe2 " "$out/cfgitem.txt"; then echo "FAIL: an item with a Verus-only cfg was listed"; exit 1; fi
    grep -q "^skip vside::probe2 the item text has \`cfg_attr(verus_keep_ghost, cfg(any()))\`" "$out/cfgitem.txt"
    # A crate whose code tests `fip_prelint` (set by the driver, not by Verus): refused.
    cp -r "$fx" "$out/cfgcrate"
    printf '\npub fn probe_cfg(a: u32, b: u32) -> u32 {\n    if cfg!(fip_prelint) { a / b } else { 0 }\n}\n' >> "$out/cfgcrate/vside/src/lib.rs"
    if (cd "$out/cfgcrate" && $gen --crate-name vside --crate-dir vside --out "$out/cfgcrate.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs) 2> "$out/cfgcrate.err"; then
      echo "FAIL: a sidecar was generated for a crate testing fip_prelint"; exit 1
    fi
    grep -q "tests \`fip_prelint\`.*no sidecar is written" "$out/cfgcrate.err"
    test ! -e "$out/cfgcrate.txt"
    # Re-audit probes (N3, N4): a macro-built `cfg!`, `option_env!` and a `#[path]`
    # module outside `src/` testing `fip_prelint` get no sidecar.
    refused_probe() {  # name, text appended to lib.rs, expected stderr regex[, file, its text]
      cp -r "$fx" "$out/$1"
      printf '%b' "$2" >> "$out/$1/vside/src/lib.rs"
      if [ $# -ge 5 ]; then printf '%b' "$5" > "$out/$1/$4"; fi
      if (cd "$out/$1" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name vside --crate-dir vside --out "$out/$1.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs) > "$out/$1.log" 2>&1; then
        echo "FAIL: a sidecar was generated for probe $1"; exit 1
      fi
      grep -q "$3" "$out/$1.log" || { echo "FAIL: probe $1 refused for another reason"; cat "$out/$1.log"; exit 1; }
      test ! -e "$out/$1.txt"
    }
    refused_probe mac '\nmacro_rules! gate {\n    ($c:ident, $p:ident) => {\n        $c!($p)\n    };\n}\n\npub fn probe_mac(a: u32, b: u32) -> u32 {\n    if gate!(cfg, fip_prelint) { a / b } else { 0 }\n}\n' 'a macro named by a metavariable.*no sidecar is written'
    refused_probe env '\npub fn probe_env(a: u32, b: u32) -> u32 {\n    match option_env!("CARGO_PKG_NAME") {\n        Some(_) => a / b,\n        None => 0,\n    }\n}\n' 'option_env!(..).*no sidecar is written'
    refused_probe path '\n#[path = "../../shared.rs"]\npub mod shared;\n\npub fn probe_path(a: u32, b: u32) -> u32 {\n    if shared::on() { a / b } else { 0 }\n}\n' 'shared.rs: `cfg!(fip_prelint)` tests `fip_prelint`.*no sidecar is written' shared.rs '#[cfg(verus_keep_ghost)]\nuse vstd::prelude::*;\n\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        !r,\n))]\npub fn on() -> bool {\n    cfg!(fip_prelint)\n}\n'
    # A caller verified against the `ensures` of a function skipped for a Verus-only
    # `cfg_attr`: skipped too.
    cp -r "$fx" "$out/taint"
    printf '\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        !r,\n))]\npub fn on() -> bool {\n    #[cfg_attr(verus_keep_ghost, cfg(any()))]\n    return true;\n    false\n}\n\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        true,\n))]\npub fn probe_taint(a: u32, b: u32) -> u32 {\n    if on() { a / b } else { 0 }\n}\n' >> "$out/taint/vside/src/lib.rs"
    (cd "$out/taint" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name vside --crate-dir vside --out "$out/taint.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs) > "$out/taint.log" 2>&1
    if grep -q "^fn vside::probe_taint " "$out/taint.txt"; then echo "FAIL: a caller of a cfg-skipped function was listed"; exit 1; fi
    grep -q "^skip vside::probe_taint relies on the specification of \`vside::on\`" "$out/taint.txt"
    # Imports: the imported crate's committed sidecar is required, and the VIR file must
    # come from a generator run (fip-strict's, copied without its `.fip-run` record).
    root="$PWD"; vir="$root/target/verus-strict/fip_strict.vir"
    if (cd "$fx" && $gen --crate-name vside --crate-dir vside --out "$out/imp.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs --import fip_strict="$vir") 2> "$out/imp.err"; then
      echo "FAIL: an import without its committed sidecar was accepted"; exit 1
    fi
    grep -q "needs \`--import-sidecar fip_strict=" "$out/imp.err"
    cp "$vir" "$out/plain.vir"
    if (cd "$fx" && $gen --crate-name vside --crate-dir vside --out "$out/imp.txt" --import-sidecar fip_strict="$root/crates/fip-strict/verus-verified.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs --import fip_strict="$out/plain.vir") 2> "$out/imp.err"; then
      echo "FAIL: an import of a VIR file no generator run exported was accepted"; exit 1
    fi
    grep -q "was not exported by a generator run" "$out/imp.err"
    test ! -e "$out/imp.txt"
    echo "verify-sidecar: ok"

# Strip gate (decision 2026-11-06-redesign-verus-allocates, D5): upstream Verus
# (`VERUS_UPSTREAM`, version `verus_upstream_pin`) verifies the sources with the fork's
# allocation layer removed (`verify/strip_alloc.py`: `allocates` clauses, `allocated()`
# invariants, `call_allocates`, adapter-bound hints, `AllocFreeDrop` impls; it fails on
# any spelling it does not know), so the functional proofs do not depend on the fork's
# allocation pass. The fork's `.vir` files cannot be imported by upstream, so every
# crate is re-verified, with `--no-cheating` and the fork-only flags left out. In `ci`;
# without `VERUS_UPSTREAM` it is skipped with a message (the fork remains the gate).
verify-upstream:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ -z "{{verus_upstream}}" ]; then
      echo "verify-upstream: SKIPPED: VERUS_UPSTREAM is not set (a build of upstream Verus {{verus_upstream_pin}})"
      exit 0
    fi
    got=$({{verus_upstream}} --version --output-json 2> /dev/null | sed -n 's/^ *"version": "\(.*\)",\{0,1\}$/\1/p' | head -1) || true
    if [ "$got" != "{{verus_upstream_pin}}" ]; then
      echo "FAIL: VERUS_UPSTREAM is Verus ${got:-unreadable}, the strip gate's pin is {{verus_upstream_pin}} (justfile verus_upstream_pin)"; exit 1
    fi
    out=target/verify-upstream; rm -rf "$out"; mkdir -p "$out/strict" "$out/core" "$out/alloc"
    src="$out/src"
    uv run --no-project python verify/strip_alloc.py "$src" crates/fip-strict crates/fip-core crates/fip-alloc verify/compose.rs verify/compose_strict.rs verify/compose_state.rs verify/fip_fn_types.rs
    tc=$({{verus_upstream}} --version | awk '/Toolchain/ {print $2}')
    cargo +"$tc" build --locked -q -p fip-macros --target-dir target/verus-macros
    deps=target/verus-macros/debug/deps
    so=$(ls -t $deps/libfip_macros-*.so | head -1)
    up() {  # name, Verus arguments
      local name=$1; shift
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus_upstream}} --crate-type=lib --no-cheating "$@" > "$out/$name.log" 2>&1; then
        echo "verify-upstream: $name: $(grep -h 'verification results' "$out/$name.log")"
      else
        cat "$out/$name.log"; echo "FAIL: upstream Verus rejects the stripped $name"; exit 1
      fi
    }
    strict="--import fip_strict=$out/strict/fip_strict.vir --extern fip_strict=$out/strict/libfip_strict.rlib"
    core="--import fip_core=$out/core/fip_core.vir --extern fip_core=$out/core/libfip_core.rlib -L $out/strict"
    up fip-strict --crate-name fip_strict "$src/fip-strict/src/lib.rs" --export "$out/strict/fip_strict.vir" --compile --out-dir "$out/strict"
    up fip-core --crate-name fip_core "$src/fip-core/src/lib.rs" $strict --export "$out/core/fip_core.vir" --compile --out-dir "$out/core"
    up fip-alloc --crate-name fip_alloc "$src/fip-alloc/src/lib.rs"
    up compose.rs --extern fip_macros="$so" -L "$deps" $strict "$src/compose.rs"
    up compose_strict.rs --extern fip_macros="$so" -L "$deps" $strict "$src/compose_strict.rs"
    up compose_state.rs --extern fip_macros="$so" -L "$deps" $strict $core "$src/compose_state.rs"
    up fip_fn_types.rs --extern fip_macros="$so" -L "$deps" $strict "$src/fip_fn_types.rs"
    echo "verify-upstream: ok"

# `fip-arch`'s unit tests on riscv64 under qemu-user, with and without Zicbop
# (decision 2026-10-31-arch-prefetch-asm, amendment 2026-11-04). Not in `ci`: needs
# `qemu-riscv64` and the `riscv64gc-unknown-linux-musl` target (linked by `rust-lld`).
arch-qemu-riscv64:
    #!/usr/bin/env bash
    set -euo pipefail
    export CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_MUSL_RUSTFLAGS="{{musl_lld}}"
    for cpu in rv64,zicbop=false rv64,zicbop=true max; do
      for profile in "" --release; do
        QEMU_CPU="$cpu" CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_MUSL_RUNNER=qemu-riscv64 \
          cargo test --locked -q $profile -p fip-arch --lib --target riscv64gc-unknown-linux-musl --target-dir target/rv64-qemu
      done
    done
    echo "arch-qemu-riscv64: ok"

# CACHE_LINE override: supported values take effect, others are rejected.
arch-override:
    #!/usr/bin/env bash
    set -euo pipefail
    for v in 32 128; do
      RUSTFLAGS="--cfg fip_cache_line=\"$v\"" cargo test --locked -q -p fip-arch --target-dir "target/cl$v"
    done
    for bad in '--cfg fip_cache_line="256"' '--cfg fip_cache_line' '--cfg fip_cache_line="64" --cfg fip_cache_line="128"'; do
      if RUSTFLAGS="$bad" cargo build --locked -q -p fip-arch --target-dir target/cl-bad 2> target/cl-bad.err; then
        echo "FAIL: accepted $bad"; exit 1
      fi
      grep -q "fip_cache_line must be exactly one of" target/cl-bad.err || { echo "FAIL: $bad rejected for another reason"; cat target/cl-bad.err; exit 1; }
    done
    echo "arch-override: ok"

# Every compile_fail doctest of fip-macros fails for its stated reason, not another error.
# Own target dir: the script needs exactly one build of each crate, by the ambient rustc.
compile-fail-reasons:
    rm -rf target/compile-fail
    cargo build --locked -q -p fip-macros -p fip-strict --target-dir target/compile-fail
    uv run --no-project python verify/compile_fail_reasons.py target/compile-fail
    uv run --no-project python verify/ctor_spellings.py target/compile-fail

# MIR-level checker `fip-prelint` (tools/fip-prelint, a rustc driver on the Verus toolchain
# with `rustc-dev`): rustfmt and clippy (`-D warnings`) on the driver, builds it, runs the fixture workspaces and the workspace
# self-check against `tools/fip-prelint/tests/*.expected`. Report-only run on the
# workspace: `tools/fip-prelint/target/debug/cargo-fip-prelint --warn-only`.
# Network: the `-Zbuild-std` runs (the stack fixture's `-buildstd` variant, the
# generation-mode tests) resolve the standard library's own crates.io dependencies
# (`cfg-if`, `hashbrown`, ..) into the cargo registry cache; on a cold cache they need
# crates.io (measured offline with an empty `CARGO_HOME`: "no matching package named
# `cfg-if`"). Kept in the gate: they are the only test of `--stack --build-std` and of
# generation mode. The workspace itself has no crates.io dependency.
prelint:
    cd tools/fip-prelint && cargo +{{prelint_tc}} fmt --check
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 cargo +{{prelint_tc}} clippy --locked --all-targets -- -D warnings
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 FIP_PRELINT_TOOLCHAIN={{prelint_tc}} cargo +{{prelint_tc}} test --locked

# Moves `fip-prelint` to another rustc (limits plan L10a): toolchain and components,
# driver build, the decision record's probes, the allocator entry-point dump, the std
# summaries (regenerated; for the pinned version they must equal the committed file),
# every driver test, then the pin sites and the trusted tables to re-audit by hand.
# Not in `ci`. `INSTALL=1` installs the toolchain, `APPLY=1` rewrites the driver's pins.
# Logs under /tmp/fip-prelint-repin-<version>.
prelint-repin version:
    tools/fip-prelint/repin.sh {{version}}

# Regenerates the std summaries of `fip-prelint` (limits plan L6, a sidecar stamped with
# the rustc version and target): `cargo check -Zbuild-std` of the seed crate
# `tools/fip-prelint/std-summaries/seed` with the release settings of the shipped std,
# analysed by the driver; writes `tools/fip-prelint/std-summaries/<release>-<target>.txt`.
# Maintainer-run after a repin or a seed change (measured 2026-11-02: 94-131 s cold in 3 runs,
# 32-45 s of it the analysis); the result is committed. Build directory under /tmp.
prelint-std-summaries target="x86_64-unknown-linux-gnu":
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 cargo +{{prelint_tc}} build --locked
    cd tools/fip-prelint && FIP_PRELINT_TOOLCHAIN={{prelint_tc}} FIP_PRELINT_TARGET_DIR=/tmp/fip-prelint-std-summaries target/debug/cargo-fip-prelint fip-prelint --std-summaries --target {{target}}

# The std summaries for every installed target with `std` (top plan T7j), one after
# the other, into one build directory under /tmp (measured 2026-11-03: 3.8-12.4
# min per target with three in parallel at load average ~34).
prelint-std-summaries-all:
    #!/usr/bin/env bash
    set -euo pipefail
    sysroot=$(rustc +{{prelint_tc}} --print sysroot)
    for d in "$sysroot"/lib/rustlib/*/lib; do
      if ls "$d"/libstd-*.rlib > /dev/null 2>&1; then
        t=$(basename "$(dirname "$d")")
        just prelint-std-summaries "$t"
      fi
    done
