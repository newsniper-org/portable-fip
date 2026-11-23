# SPDX-License-Identifier: MIT OR Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

# Pins (decision 2026-11-06-redesign-verus-allocates): each is written in one file and
# read from there, so a re-pin edits only that file.
#   - trusted Verus (version, commit) and Z3: tools/fip-prelint/verus-trusted.txt,
#     checked against the binary `VERUS` by `verus-pin` before every Verus gate;
#   - toolchain of `fip-prelint` (= the Verus toolchain, checked by `verus-pin`):
#     tools/fip-prelint/rust-toolchain.toml (also read by the driver's build.rs);
#   - MSRV: `rust-version` in Cargo.toml; the toolchain of the plain `cargo` gates
#     (fmt, clippy, tests, cross, no_std): `rust-toolchain.toml`, currently the same;
#   - upstream Verus of the strip gate: `verus_upstream_pin` below.
#
# The Verus fork with `allocates` (branch `fip`, the pin in verus-trusted.txt), with
# Singular for `by (integer_ring)`. `VERUS` must name that build (`just verus-pin` fails
# otherwise); its Z3 is `VERUS_Z3_PATH`, else the `z3` next to the binary.
verus := env_var_or_default("VERUS", "verus")
# Flags of every Verus run of the gates: no trusted items, and `allocates` bounds checked
# (the fork's `-V alloc-check`; an importing crate needs the imported crate's export
# from a run with it).
verus_flags := "--no-cheating -V alloc-check --edition 2024"
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
# missing target, tool or host fails here (`FIP_PRELINT_REQUIRE_TARGETS=1`), and so does
# the upstream strip gate when `VERUS_UPSTREAM` is unset (`FIP_REQUIRE_UPSTREAM=1`).
ci:
    FIP_PRELINT_REQUIRE_TARGETS=1 FIP_REQUIRE_UPSTREAM=1 just ci-gates

# The gates of `ci`, without turning skipped driver tests or a skipped strip gate
# into failures.
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
# `prfm` and `ori` templates (needs both musl targets for the toolchain of `rust-toolchain.toml`).
cross:
    cargo check --locked -p fip-core -p fip-alloc -p fip-arch -p fip-strict --target aarch64-unknown-linux-gnu
    cargo check --locked -p fip-core -p fip-alloc -p fip-arch -p fip-strict --target riscv64gc-unknown-linux-gnu
    cargo check --locked -p fip-arch --target riscv64gc-unknown-linux-musl
    cargo check --locked -p fip-arch --target riscv64gc-unknown-none-elf
    cargo check --locked -p fip-arch --target aarch64-apple-darwin
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUSTFLAGS="{{musl_lld}}" cargo test --locked -q --no-run -p fip-arch --lib --target aarch64-unknown-linux-musl --target-dir target/cross-asm
    CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_MUSL_RUSTFLAGS="{{musl_lld}}" cargo test --locked -q --no-run -p fip-arch --lib --target riscv64gc-unknown-linux-musl --target-dir target/cross-asm

# All Verus gates: proofs, composition with #[fip], and negative controls.
verify: verus-pin verify-flags verify-strict verify-core verify-alloc verify-compose verify-negative verify-sidecar

# Every Verus run of this justfile uses `--no-cheating` and none verifies a crate as a
# standard-library crate (`--is-vstd`, ..): `verify/no_cheating_flags.py`, the fork
# audit (2026-11-09). Mutated copies of the justfile (the flag dropped from
# `verus_flags`, from the upstream runs or from the mutant runs; `--is-vstd` added)
# must fail the check.
verify-flags:
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/verify-flags; rm -rf "$out"; mkdir -p "$out"
    uv run --no-project python verify/no_cheating_flags.py justfile
    flags_mutant() {  # name, sed script, expected message
      sed "$2" justfile > "$out/$1"
      if cmp -s justfile "$out/$1"; then echo "FAIL: flags mutant $1 did not apply"; exit 1; fi
      if uv run --no-project python verify/no_cheating_flags.py "$out/$1" > "$out/$1.log" 2>&1; then
        echo "FAIL: flags mutant $1 passed"; exit 1
      fi
      grep -q "$3" "$out/$1.log" || { echo "FAIL: flags mutant $1 failed for another reason"; cat "$out/$1.log"; exit 1; }
      echo "flags mutant $1 rejected"
    }
    flags_mutant verus-flags 's/^verus_flags := "--no-cheating -V alloc-check --edition 2024"$/verus_flags := "-V alloc-check --edition 2024"/' 'lacks --no-cheating'
    flags_mutant verus-edition 's/^verus_flags := "--no-cheating -V alloc-check --edition 2024"$/verus_flags := "--no-cheating -V alloc-check"/' 'lacks --edition 2024'
    flags_mutant upstream-edition 's/ --crate-type=lib --no-cheating --edition 2024 "\$@"/ --crate-type=lib --no-cheating "\$@"/' 'Verus run without --edition 2024'
    flags_mutant upstream-run 's/ --crate-type=lib --no-cheating --edition 2024 "\$@"/ --crate-type=lib --edition 2024 "\$@"/' 'Verus run without --no-cheating'
    flags_mutant mutant-run 's/ [{][{]verus_flags[}][}] --multiple-errors 8 / --multiple-errors 8 /' 'Verus run without --no-cheating'
    flags_mutant is-vstd 's/^verus_flags := "--no-cheating -V alloc-check --edition 2024"$/verus_flags := "--no-cheating --is-vstd -V alloc-check --edition 2024"/' 'a standard-library crate flag' # negative probe
    echo "verify-flags: ok"

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
    # `toolchain` is `<channel>-<host triple>`. The channel itself may contain `-`
    # (e.g. `beta-2026-11-05`), so compare the whole string against the pinned channel and
    # this host's triple; a floating channel (`beta`) does not match a dated build.
    host=$(rustc +{{prelint_tc}} -vV 2> /dev/null | awk '/^host:/ {print $2}') || true
    if [ -z "$host" ]; then
      echo "FAIL: cannot run \`rustc +{{prelint_tc}} -vV\` (install the fip-prelint toolchain, tools/fip-prelint/rust-toolchain.toml)"; exit 1
    fi
    if [ "$got_tc" != "{{prelint_tc}}-$host" ]; then
      echo "FAIL: Verus $got_v is built on toolchain $got_tc, fip-prelint on {{prelint_tc}}-$host (tools/fip-prelint/rust-toolchain.toml)"; exit 1
    fi
    if [ -n "${VERUS_Z3_PATH:-}" ]; then z3=$VERUS_Z3_PATH; else z3=$(dirname "$(readlink -f "$(command -v {{verus}})")")/z3; fi
    got_z3=$("$z3" --version 2> /dev/null | awk '/Z3 version/ {print $3}') || true
    if [ "$got_z3" != "$want_z3" ]; then
      echo "FAIL: Z3 \`$z3\` is ${got_z3:-unreadable}, the pin is $want_z3 ($pin; set VERUS_Z3_PATH)"; exit 1
    fi
    echo "verus-pin: Verus $got_v ($got_c), Z3 $got_z3, toolchain $got_tc"

# Verus metadata and library of fip-strict, imported where `FipFn` specs are needed.
verus_strict := "--import fip_strict=target/verus-strict/fip_strict.vir --extern fip_strict=target/verus-strict/libfip_strict.rlib"

# Shell function `one_artifact <target dir> <crate> <ext>`: the one cargo artifact
# `lib<crate>-<hash>.<ext>` of a debug build into <target dir>, in cargo's layout up
# to 1.99 (`debug/deps/`) or the build-dir layout of cargo 1.100 (`debug/build/<package>/<hash>/out/`,
# measured with cargo 1.100.0-beta.10, 2026-11-09). Zero or several candidates fail
# (no guess); the recipes build into a fresh directory, so a second one is a stale
# or foreign build.
one_artifact := 'one_artifact() { local c=() f; shopt -s nullglob; for f in "$1"/debug/deps/lib"$2"-*."$3" "$1"/debug/build/*/*/out/lib"$2"-*."$3"; do c+=("$f"); done; shopt -u nullglob; if [ "${#c[@]}" -ne 1 ]; then echo "FAIL: expected exactly one lib$2-*.$3 under $1, found ${#c[@]}: ${c[*]:-none}" >&2; return 1; fi; printf "%s\n" "${c[0]}"; }'

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
verify-core: verify-strict verus-lib-macros
    #!/usr/bin/env bash
    set -euo pipefail
    rm -rf target/verus-core && mkdir -p target/verus-core
    {{one_artifact}}
    so=$(one_artifact target/verus-lib-macros fip_macros so)
    VERUS_SINGULAR_PATH="{{singular}}" {{sidecar_gen}} --crate-name fip_core --crate-dir crates/fip-core --out target/verus-core/verus-verified.txt --import-sidecar fip_strict=crates/fip-strict/verus-verified.txt -- {{verus}} --crate-type=lib --crate-name fip_core {{verus_flags}} crates/fip-core/src/lib.rs {{verus_strict}} --extern fip_macros="$so" -L "$(dirname "$so")" --export target/verus-core/fip_core.vir --compile --out-dir target/verus-core
    just verus-sidecar-check target/verus-core/verus-verified.txt crates/fip-core/verus-verified.txt

# `fip-macros` built with the Verus toolchain, for the crates whose functions carry
# `#[fip_macros::fip(strict ..)]`/`(total)` in both builds (phase 5: under Verus the
# macro generates their `requires`/`allocates`/`no_unwind`/`#[verifier::fip(strict)]`).
verus-lib-macros: verus-pin
    #!/usr/bin/env bash
    set -euo pipefail
    tc=$({{verus}} --version | awk '/Toolchain/ {print $2}')
    rm -rf target/verus-lib-macros
    cargo +"$tc" build --locked -q -p fip-macros --target-dir target/verus-lib-macros

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
verify-alloc: verify-strict verus-lib-macros
    #!/usr/bin/env bash
    set -euo pipefail
    rm -rf target/verus-alloc && mkdir -p target/verus-alloc
    {{one_artifact}}
    so=$(one_artifact target/verus-lib-macros fip_macros so)
    VERUS_SINGULAR_PATH="{{singular}}" {{sidecar_gen}} --crate-name fip_alloc --crate-dir crates/fip-alloc --out target/verus-alloc/verus-verified.txt --import-sidecar fip_strict=crates/fip-strict/verus-verified.txt -- {{verus}} --crate-type=lib --crate-name fip_alloc {{verus_flags}} crates/fip-alloc/src/lib.rs {{verus_strict}} --extern fip_macros="$so" -L "$(dirname "$so")"
    just verus-sidecar-check target/verus-alloc/verus-verified.txt crates/fip-alloc/verus-verified.txt

# `#[fip]` above `verus_spec` verifies; below it, or with an allocation, it is rejected.
# Strict functions with `FipFn` parameters verify against fip-strict's Verus build.
# Callers of the state-passing combinators (incl. a strict one, so with fip-macros)
# verify against fip-core's Verus build.
verify-compose: verify-strict verify-core
    #!/usr/bin/env bash
    set -euo pipefail
    tc=$({{verus}} --version | awk '/Toolchain/ {print $2}')
    m=target/verus-macros; rm -rf "$m"
    cargo +"$tc" build --locked -q -p fip-macros -p fip-strict --target-dir "$m"
    {{one_artifact}}
    so=$(one_artifact "$m" fip_macros so); rl=$(one_artifact "$m" fip_strict rlib)
    deps=$(dirname "$so")
    run() { VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" {{verus_strict}} -L "$deps" "$1"; }
    run verify/compose.rs
    run verify/compose_strict.rs
    # Phase 5: `strict`/`total` generate the Verus contract (verify/total.rs).
    run verify/total.rs
    run_state() { VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" -L "$deps" {{verus_strict}} {{verus_core}} "$1"; }
    run_state verify/compose_state.rs
    run_state verify/alloc_callers.rs
    out=target/verify-compose; mkdir -p "$out"
    # `fip_fn!` values have one type in both builds: verify/fip_fn_types.rs is compiled
    # by plain rustc and verified by Verus; a wrong `N` in any annotation fails both.
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
    m=target/verus-macros; rm -rf "$m"
    cargo +"$tc" build --locked -q -p fip-macros --target-dir "$m"
    {{one_artifact}}
    so=$(one_artifact "$m" fip_macros so)
    deps=$(dirname "$so")
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
    # about the spec. Optional sixth argument: extra Verus flags (e.g. `--rlimit 100`);
    # a `--multiple-errors N` among them replaces the 8 (Verus refuses the flag twice).
    expect_verus_fail() {  # name, crate, file, sed script, expected log regex[, verus flags]
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      local me="--multiple-errors 8"; case "${6:-}" in *--multiple-errors*) me="";; esac
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} $me ${6:-} "$d/src/lib.rs" {{verus_strict}} --extern fip_macros="$so" -L "$deps" > "$d/log" 2>&1; then
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
    # (`--multiple-errors 1`, 2026-11-22: on the fork `ac9642e` the first error is the
    # intended one, the broken invariant, and Verus's search for a second one exceeds
    # the limit, which the previous pin's did not.)
    expect_verus_fail dedup-no-swap        fip-core  slice.rs '/^pub fn dedup_by</,/^}/ { s/^                swap_lt(xs, w, r);$//; /^                assert(xs@\[ow\] == old(xs)@\[r as int\]);$/d }' "$spec" "--rlimit 1000 --multiple-errors 1"
    expect_verus_fail dedup-wrong-compare  fip-core  slice.rs '/^pub fn dedup_by</,/^}/ s/same(&xs\[w - 1\], &xs\[r\])/same(\&xs[r - 1], \&xs[r])/' "$spec"
    expect_verus_fail compact-map-no-swap  fip-core  slice.rs "/^pub fn compact_map</,/^}/ { s/^                swap_lt(xs, w, r);\$//; $no_swap_asserts }" "$cmap_order"
    expect_verus_fail compact-map-invert   fip-core  slice.rs '/^pub fn compact_map</,/^}/ s/^        if keep {$/        if !keep {/' "$spec"
    expect_verus_fail refill-no-swap       fip-alloc lib.rs   's/^    ::core::mem::swap(&mut \*cell, &mut prev);$//' "$spec"
    # Phase 5: the macro merges generated clauses into the hand-written `verus_spec`;
    # these show the hand-written `ensures` of every `strict`/`total` function still
    # binds after the merge, and that the generated `requires` is really emitted.
    expect_verus_fail swap-lt-no-swap      fip-core  slice.rs '/^pub(crate) fn swap_lt</,/^}/ { s/^    ::core::mem::swap(&mut a\[i\], &mut b\[0\]);$//; /^        assert(final(xs)@ =~= /d }' "$spec"
    expect_verus_fail swap-no-op           fip-core  slice.rs '/^pub fn swap</,/^}/ { /^        swap_lt(xs, [ij], [ij]);$/d; /^        assert(final(xs)@ =~= /d }' "$spec"
    expect_verus_fail replace-keeps-slot   fip-core  slot.rs  '/^pub fn replace</,/^}/ s/^    ::core::mem::swap(slot, &mut v);$//' "$spec"
    expect_verus_fail swap-lt-requires-dropped fip-core slice.rs 's/#\[fip_macros::fip(total, requires(i < j, j < xs.len()))\]/#[fip_macros::fip(total, requires(j < xs.len()))]/' 'precondition not met: index in bounds'
    # Allocation bounds (`allocates`, decision 2026-11-06-redesign-verus-allocates, phase 2):
    # each mutant must fail a verification condition whose reported span is the
    # allocation layer (an `allocates` clause, an `allocated()` invariant or a
    # `call_allocations` requirement), not a functional one.
    expect_alloc_fail() {  # name, crate, file, sed script, regex expected in the failing span
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --multiple-errors 8 "$d/src/lib.rs" {{verus_strict}} --extern fip_macros="$so" -L "$deps" > "$d/log" 2>&1; then
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
    # `swap` (`strict`) and `refill` (`total`) carry `#[fip_macros::fip(..)]` in the
    # Verus build too (phase 5): a visible `Box::new` is rejected by its token scan,
    # before Verus; an allocation hidden from the scan fails the generated `allocates 0`
    # (control `total-hidden-alloc` below).
    expect_scan_fail() {  # name, crate, file, sed script
      local d; d=$(mutate "$1" "$2" "$3" "$4")
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} "$d/src/lib.rs" {{verus_strict}} --extern fip_macros="$so" -L "$deps" > "$d/log" 2>&1; then
        echo "FAIL: mutant $1 verified"; exit 1
      fi
      grep -q "allocation site \`Box::new\` in the body" "$d/log" || { echo "FAIL: mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected by the fip-macros token scan"
    }
    expect_scan_fail swap-allocates         fip-core  slice.rs "$ext_alloc"'; /^pub fn swap</,/^}/ s/^        swap_lt(xs, i, j);$/        swap_lt(xs, i, j);\n        let _b = alloc::boxed::Box::new(0u8);/'
    expect_alloc_fail map-allocates         fip-core  slice.rs "$ext_alloc"'; /^pub fn map_in_place</,/^}/ s/^        i += 1;$/        let _b = alloc::boxed::Box::new(0u8);\n        i += 1;/' 'allocated\(\) <= crate::spec::map_allocs'
    expect_scan_fail refill-allocates       fip-alloc lib.rs   's/^    ::core::mem::swap(&mut \*cell, &mut prev);$/    ::core::mem::swap(\&mut *cell, \&mut prev);\n    let _b = Box::new(0u8);/'
    # A free in `total` `refill` (an `Option<Box<u8>>` dropped on the normal return):
    # the generated `#[verifier::fip(strict)]` rejects it (the fork words its error for both forms as "a `#[verifier::fip]` function must not deallocate") (no `allocates`/token check sees it).
    d=$(mutate refill-frees fip-alloc lib.rs 's/^    ::core::mem::swap(&mut \*cell, &mut prev);$/    ::core::mem::swap(\&mut *cell, \&mut prev);\n    let _spare: Option<Box<u8>> = None;/')
    if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} "$d/src/lib.rs" {{verus_strict}} --extern fip_macros="$so" -L "$deps" > "$d/log" 2>&1; then
      echo "FAIL: mutant refill-frees verified"; exit 1
    fi
    grep -q "a \`#\[verifier::fip\]\` function must not deallocate" "$d/log" || { echo "FAIL: mutant refill-frees failed for another reason"; cat "$d/log"; exit 1; }
    echo "mutant refill-frees rejected by Verus (#[verifier::fip(strict)])"
    # A sum spec that forgets the last call cannot bound the loop.
    expect_alloc_fail map-sum-drops-call    fip-core  spec.rs  's/^    if n <= 0 { 0 } else { map_allocs(f, s, n - 1) + call_allocations(f, (s\[n - 1\],)) }$/    if n <= 0 { 0 } else { map_allocs(f, s, n - 1) }/' 'allocated\(\) <= crate::spec::map_allocs'
    expect_alloc_fail compact-sum-drops-call fip-core spec.rs  's/^    if n <= 0 { 0 } else { compact_allocs(keep, s, n - 1) + call_allocations(keep, (&s\[n - 1\],)) }$/    if n <= 0 { 0 } else { compact_allocs(keep, s, n - 1) }/' 'allocated\(\) <= crate::spec::compact_allocs'
    # Deallocation bounds (the fork's `deallocates`, 2026-11-22): the sums of the
    # callbacks' `call_deallocations`, and `update`'s one call.
    expect_alloc_fail map-dealloc-sum-drops-call fip-core dealloc_spec.rs 's/^    if n <= 0 { 0 } else { map_deallocs(f, s, n - 1) + call_deallocations(f, (s\[n - 1\],)) }$/    if n <= 0 { 0 } else { map_deallocs(f, s, n - 1) }/' 'deallocated\(\) <= crate::dealloc_spec::map_deallocs'
    expect_alloc_fail compact-dealloc-sum-drops-call fip-core dealloc_spec.rs 's/^    if n <= 0 { 0 } else { compact_deallocs(keep, s, n - 1) + call_deallocations(keep, (&s\[n - 1\],)) }$/    if n <= 0 { 0 } else { compact_deallocs(keep, s, n - 1) }/' 'deallocated\(\) <= crate::dealloc_spec::compact_deallocs'
    expect_alloc_fail compact-map-dealloc-sum-drops-call fip-core dealloc_spec.rs 's/^    if n <= 0 { 0 } else { compact_map_deallocs(f, s, n - 1) + call_deallocations(f, (s\[n - 1\],)) }$/    if n <= 0 { 0 } else { compact_map_deallocs(f, s, n - 1) }/' 'deallocated\(\) <= crate::dealloc_spec::compact_map_deallocs'
    expect_alloc_fail update-dealloc-zero fip-core slot.rs 's/^    deallocates call_deallocations(f, (\*old(slot),))$/    deallocates 0/' 'deallocates 0'
    # `map_in_place_st` is `allocates 0` only because every call is required to be.
    expect_alloc_fail map-st-alloc-unrequired fip-core slice.rs '/^        map_st_by_ok(old(xs)@, f, s0),$/ { n; /call_allocations/d; }' 'call_allocations\(f, \(s, x\)\) <= 0'
    # Strict callables (phase 3): `FipFn::call` allocates at most `allocs()`. A strict
    # combinator calling its callable twice per element breaks `len * f.allocs()`;
    # `Compose` claiming one allocation less than its parts, and `Certified` without
    # the `call_allocations(..) <= ALLOCS` conjunct of `pre`, break `call`'s bound.
    expect_alloc_fail strict-compact-calls-twice fip-core strict.rs '/^pub fn compact</,/^}/ s/^        if keep.call((&xs\[r\],)) {$/        let _again = keep.call((\&xs[r],));\n        if keep.call((\&xs[r],)) {/' 'allocated\(\) <= r \* keep\.allocs\(\)'
    expect_alloc_fail compose-sum-minus-one   fip-strict lib.rs '/^macro_rules! compose_fip_fn/,/^}/ s/^                self.0.allocs() + self.1.allocs()$/                (self.0.allocs() + self.1.allocs() - 1) as nat/' 'allocates self\.allocs\(\)'
    expect_alloc_fail certified-pre-no-alloc  fip-strict lib.rs '/^                &&& call_allocations(self.inner(), args) <= ALLOCS as int$/d' 'allocates self\.allocs\(\)'
    # (2026-11-22) `FipFn::call` is `deallocates 0`: without the conjunct of `pre`,
    # `Certified`'s `call` cannot show it; without the requirement, neither can the
    # `_st` combinators and `dedup_by`.
    expect_alloc_fail certified-pre-no-dealloc fip-strict lib.rs '/^                &&& call_deallocations(self.inner(), args) == 0$/d' 'deallocates 0'
    expect_alloc_fail map-st-dealloc-unrequired fip-core slice.rs '/^        map_st_by_ok(old(xs)@, f, s0),$/ { n; n; /call_deallocations/d; }' 'call_deallocations\(f, \(s, x\)\) == 0'
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
    callers_fail dedup-unbounded   '/^pub fn deduped(/,/^}/ s/-> (r: bool) allocates 0 deallocates 0 {/-> (r: bool) deallocates 0 {/' 'precondition not satisfied' 'call_allocations\(same'
    # (2026-11-22) `dedup_by`, `map_in_place_st` and `compact_map_st` also require
    # callbacks that deallocate nothing, and a `Certified` checks it in `pre`.
    callers_fail dedup-dealloc-unbounded '/^pub fn deduped(/,/^}/ s/-> (r: bool) allocates 0 deallocates 0 {/-> (r: bool) allocates 0 {/' 'precondition not satisfied' 'call_deallocations\(same'
    callers_fail st-dealloc-unbounded '/^pub fn kept_state(/,/^}/ s/allocates 0 deallocates 0 { (s, x) }/allocates 0 { (s, x) }/' 'precondition not satisfied' 'call_deallocations\(f, \(s, x\)\) == 0'
    callers_fail certified-dealloc-unbounded '/^pub fn incremented_strict(/,/^}/ s/requires v < 100 allocates 0 deallocates 0 { v + 1 }/requires v < 100 allocates 0 { v + 1 }/' 'precondition not satisfied' 'f\.pre\(\(old\(xs\)@\[i\],\)\)'
    callers_fail no-zero-lemmas    's/^broadcast use fip_core::spec::group_allocs_zero, fip_core::dealloc_spec::group_deallocs_zero;$/broadcast use fip_core::dealloc_spec::group_deallocs_zero;/' 'postcondition not satisfied' 'allocates 0'
    # Deallocation bounds (2026-11-22): a closure without a `deallocates` bound, one
    # that frees, the zero-sum lemmas left out, a bound one too low, and a freeing
    # closure under a `#[verifier::fip]` caller.
    callers_fail dealloc-closure-unbounded '/^pub fn evens_no_free(/,/^}/ s/allocates 0 deallocates 0 { \*v % 2 == 0 }/allocates 0 { *v % 2 == 0 }/' 'postcondition not satisfied' 'deallocates 0'
    callers_fail dealloc-closure-frees '/^pub fn bumped_no_free(/,/^}/ s/allocates 0 deallocates 0 { v + 1 }/allocates 1 deallocates 1 { let b = Box::new(v + 1); *b }/' 'postcondition not satisfied' 'deallocates 0'
    callers_fail no-dealloc-zero-lemmas 's/^broadcast use fip_core::spec::group_allocs_zero, fip_core::dealloc_spec::group_deallocs_zero;$/broadcast use fip_core::spec::group_allocs_zero;/' 'postcondition not satisfied' 'deallocates 0'
    callers_fail dealloc-bound-low '/^pub fn reboxed_pair(/,/^}/ s/^    deallocates 2$/    deallocates 1/' 'postcondition not satisfied' 'deallocates 1'
    callers_fail fip-caller-closure-frees '/^pub fn evens_fip(/,/^}/ s/#\[verifier::fip\] |v: &u32| -> (r: bool) { \*v % 2 == 0 }/|v: \&u32| -> (r: bool) allocates 1 deallocates 1 { let b = Box::new(*v); *b % 2 == 0 }/' 'this call may deallocate memory' 'fip_core::compact'
    # A `Certified<0, _>` wrapping a closure that allocates once: `Certified::pre`
    # (`call_allocations(closure, args) <= 0`; the closure has no `requires`) fails.
    callers_fail certified0-allocating '/^pub fn boxed_once(/,/^}/ s/Certified::<1, _, false>/Certified::<0, _, false>/' 'precondition not satisfied' 'self\.pre\(args\)'
    # `fip_fn!(path)` without `bound` is a `Certified<0, _>` under Verus (it reads no
    # certificate): for the allocating `boxed` (verify/fip_fn_types.rs) the verified
    # caller fails `Certified::pre` (`boxed` has no `requires`, so the failing part is
    # `call_allocations(boxed, (x,)) <= 0`).
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
    # Stack bound: recursion without `decreases` is rejected (in `compact`, which has no
    # `#[fip]` attribute, so Verus is the check; on a `strict`/`total` function the
    # macro's direct-recursion check rejects it first).
    expect_verus_fail compact-recursive    fip-core  slice.rs '/^pub fn compact</,/^}/ s/^    let n = xs.len();$/    let _again = compact(xs, keep);\n    let n = xs.len();/' 'recursive function must have a .?decreases.? clause'
    # Termination (P4 of `total`): a loop without `decreases` in verified code is
    # rejected by Verus (`exec_allows_no_decreases_clause` is refused by the surface
    # gate, mutant `surface-no-decreases-attr`).
    expect_verus_fail compact-loop-no-decreases fip-core slice.rs '/^pub fn compact</,/^}/ { /^        decreases n - r,$/d }' 'loop must have a .?decreases.? clause'
    # Phase 5 (`total`, verify/total.rs): a `total` caller of a callee that may unwind
    # fails the generated `no_unwind`; an allocation hidden from the token scan behind a
    # hand-written certificate fails a `strict` caller's generated `allocates 0`; a free
    # in a `total` function fails the generated `#[verifier::fip(strict)]`.
    total_fail() {  # name, sed script or `append:<text>`, expected regex
      local f="$out/total_$1.rs"
      case "$2" in
        append:*) cp verify/total.rs "$f"; printf '%b' "${2#append:}" >> "$f" ;;
        *) sed "$2" verify/total.rs > "$f" ;;
      esac
      if cmp -s verify/total.rs "$f"; then echo "FAIL: control total-$1 did not apply"; exit 1; fi
      if VERUS_SINGULAR_PATH="{{singular}}" {{verus}} --crate-type=lib {{verus_flags}} --extern fip_macros="$so" -L "$deps" {{verus_strict}} "$f" > "$out/total_$1.log" 2>&1; then
        echo "FAIL: control total-$1 verified"; exit 1
      fi
      grep -Eq "$3" "$out/total_$1.log" || { echo "FAIL: control total-$1 failed for another reason"; cat "$out/total_$1.log"; exit 1; }
      echo "control total-$1 rejected by Verus"
    }
    total_fail unwind 's/^    inc(same_total(x))$/    inc(same_fip(x))/' 'cannot show this call will not unwind'
    total_fail hidden-alloc 'append:\n/// Claims 0 allocations, allocates one.\npub const __fip_strict_claim: fip_strict::Cert = unsafe { fip_strict::Cert::assume("claim", 0) };\n\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        r == 1,\n    allocates 1\n    deallocates 1\n))]\npub fn claim() -> u32 {\n    let b = alloc::boxed::Box::new(1u32);\n    *b\n}\n\n#[fip(strict)]\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        r == 1,\n))]\npub fn calls_claim() -> u32 {\n    claim()\n}\n' 'postcondition not satisfied'
    grep -A3 "postcondition not satisfied" "$out/total_hidden-alloc.log" | grep -q '#\[fip(strict)\]' || { echo "FAIL: control total-hidden-alloc failed elsewhere than the generated bound"; cat "$out/total_hidden-alloc.log"; exit 1; }
    # Since fork c716c2bfd `total` emits `#[verifier::fip(strict)]` (constant stack): a
    # `total` caller of a callee that is `#[verifier::fip]`, `no_unwind` and
    # `allocates 0` but not strict fails the fork's strict call check.
    total_fail nonstrict-callee 'append:\n/// Certified for the token scan (0, no panicking macro); not strict for Verus.\npub const __fip_strict_plain_fip: fip_strict::Cert = unsafe { fip_strict::Cert::assume_no_panic_macros("plain_fip", 0) };\n\n#[cfg_attr(verus_keep_ghost, verifier::fip)]\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        r == x,\n    no_unwind allocates 0\n))]\npub fn plain_fip(x: u32) -> u32 {\n    x\n}\n\n#[fip(total)]\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        r == x,\n))]\npub fn calls_plain_fip(x: u32) -> u32 {\n    plain_fip(x)\n}\n' 'must use constant stack space, but it calls .plain_fip., which is not .#\[verifier::fip\(strict\)\]'
    total_fail free 'append:\n#[fip(total)]\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures\n        r == x,\n))]\npub fn frees(x: u32) -> u32 {\n    let _spare: Option<alloc::boxed::Box<u32>> = None;\n    x\n}\n' 'function must not deallocate'
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
    # The fork audit (2026-11-09): a `trusted_call` block and an allocator trait
    # implementation in a verified crate (fip-core, fip-alloc, fip-strict) are rejected.
    expect_test_fail surface-trusted-call fip-alloc lib.rs 's/^    ::core::mem::swap(&mut \*cell, &mut prev);$/    #[verifier::trusted_call]\n    {\n        ::core::mem::swap(\&mut *cell, \&mut prev);\n    }/' no_trusted_call
    expect_test_fail surface-allocator-impl fip-core slot.rs '$ s/$/\nunsafe impl<T> core::alloc::GlobalAlloc for Pool<T> {}/' no_allocator_impl
    expect_test_fail surface-strict-trusted-call fip-strict lib.rs '$ s/$/\nfn t() {\n    #[cfg_attr(verus_keep_ghost, verifier::trusted_call)]\n    {}\n}/' no_trusted_call
    expect_test_fail surface-strict-internal-attr fip-strict lib.rs '$ s/$/\nmacro_rules! glue { ($t:ident, $i:ident) => { #[$t::$i(x)] fn t() {} } }\nglue!(verus, internal);/' no_internal_identifier
    expect_test_fail surface-strict-allocator-impl fip-strict lib.rs '$ s/$/\nunsafe impl core::alloc::Allocator for Arena {}/' no_allocator_impl
    # The same gates on the verified callers in `verify/` (fip-testkit's
    # `verified_sources` test).
    verify_surface_fail() {  # name, file, sed script, test name
      local d="$out/$1"; mkdir -p "$d"; cp verify/*.rs "$d/"
      sed -i "$3" "$d/$2"
      if cmp -s "verify/$2" "$d/$2"; then echo "FAIL: mutation $1 did not apply"; exit 1; fi
      if FIP_SURFACE_SRC="$PWD/$d" cargo test --locked -q -p fip-testkit --test verified_sources "$4" > "$d/log" 2>&1; then
        echo "FAIL: surface mutant $1 passed"; exit 1
      fi
      grep -q "test result: FAILED" "$d/log" || { echo "FAIL: surface mutant $1 failed for another reason"; cat "$d/log"; exit 1; }
      echo "mutant $1 rejected by the surface gate"
    }
    verify_surface_fail surface-verify-trusted-call compose.rs '$ s/$/\n#[verifier::trusted_call]\nfn t() {}/' no_trusted_call
    # `verus::internal(..)` in any spelling (raw identifier, put together by a macro).
    verify_surface_fail surface-verify-internal-attr compose.rs '$ s/$/\n#[verus::r#internal(x)]\nfn t() {}/' no_internal_identifier
    verify_surface_fail surface-verify-allocator-impl alloc_callers.rs '$ s/$/\nunsafe impl std::alloc::GlobalAlloc for Arena {}/' no_allocator_impl
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
# sidecar; a caller of a function skipped for its cfg is skipped. Phase 4: callers of a
# method of a trait with a plain-only implementation are skipped.
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
    if (cd "$fx" && $gen --crate-name vside --crate-dir vside --out "$out/cheat.txt" -- {{verus}} --crate-type=lib --crate-name vside --edition 2024 vside/src/lib.rs) 2> "$out/cheat.err"; then # negative probe
      echo "FAIL: a sidecar was generated without --no-cheating"; exit 1
    fi
    grep -q "must use \`--no-cheating\`" "$out/cheat.err"
    test ! -e "$out/cheat.txt"
    # Without -V alloc-check (required since sidecar format 5): refused before Verus runs, nothing written.
    if (cd "$fx" && $gen --crate-name vside --crate-dir vside --out "$out/noalloc.txt" -- {{verus}} --crate-type=lib --crate-name vside --no-cheating --edition 2024 vside/src/lib.rs) 2> "$out/noalloc.err"; then
      echo "FAIL: a sidecar was generated without -V alloc-check"; exit 1
    fi
    grep -q "must use \`-V alloc-check\`" "$out/noalloc.err"
    test ! -e "$out/noalloc.txt"
    # Without --edition (required since sidecar format 7): refused before Verus runs, nothing written.
    if (cd "$fx" && $gen --crate-name vside --crate-dir vside --out "$out/noedition.txt" -- {{verus}} --crate-type=lib --crate-name vside --no-cheating -V alloc-check vside/src/lib.rs) 2> "$out/noedition.err"; then # negative probe
      echo "FAIL: a sidecar was generated without --edition"; exit 1
    fi
    grep -q "names no \`--edition\`" "$out/noedition.err"
    test ! -e "$out/noedition.txt"
    # `#[verifier::fip]` on a function that Verus does not verify (outside `verus!`
    # without `#[verus_spec(..)]`, or `#[verifier::external]`): an error of the fork since
    # `62f2a9400` (before, a warning and a successful run, also for a function that
    # allocates; the generator matched the warning until the re-pin to `d633cde`). No
    # sidecar is written, with or without the flags that hid the warning. The control
    # with `#[verus_spec]` beside the attribute is refused by the verification.
    mkdir -p "$out/ignored/src" "$out/ignext/src" "$out/ignctl/src"
    printf '%s\n' '#![allow(unused_imports)]' 'use vstd::prelude::*;' '#[verifier::fip]' 'pub fn boxed(x: u64) -> Box<u64> {' '    Box::new(x)' '}' > "$out/ignored/src/lib.rs"
    printf '%s\n' '#![allow(unused_imports)]' 'use vstd::prelude::*;' '#[verifier::external]' '#[verifier::fip]' 'pub fn boxed(x: u64) -> Box<u64> {' '    Box::new(x)' '}' > "$out/ignext/src/lib.rs"
    printf '%s\n' '#![feature(proc_macro_hygiene)]' 'use vstd::prelude::*;' '#[verus_spec]' '#[verifier::fip]' 'pub fn boxed(x: u64) -> Box<u64> {' '    Box::new(x)' '}' > "$out/ignctl/src/lib.rs"
    ign() {  # crate, expected regex in Verus's output, extra Verus flags
      local c="$1" want="$2"; shift 2
      if (cd "$out" && $gen --crate-name "$c" --crate-dir "$c" --out "$out/$c.txt" -- {{verus}} --crate-type=lib --crate-name "$c" {{verus_flags}} "$@" "$c/src/lib.rs") > "$out/$c.log" 2>&1; then # negative probe
        echo "FAIL: a sidecar was generated for the crate $c ($*)"; exit 1
      fi
      grep -Eq "$want" "$out/$c.log" || { echo "FAIL: the crate $c ($*) failed for another reason"; cat "$out/$c.log"; exit 1; }
      grep -q "Verus failed: no sidecar written" "$out/$c.log" || { echo "FAIL: the crate $c ($*): the generator did not report Verus's failure"; cat "$out/$c.log"; exit 1; }
      test ! -e "$out/$c.txt"
    }
    ign ignored 'alloc-check: `#\[verifier::fip\]` is on a function that Verus is ignoring'
    ign ignored 'alloc-check: `#\[verifier::fip\]` is on a function that Verus is ignoring' -A warnings
    ign ignored 'alloc-check: `#\[verifier::fip\]` is on a function that Verus is ignoring' --cap-lints allow
    ign ignext 'alloc-check: `#\[verifier::fip\]` is on a function that is marked external'
    ign ignctl 'postcondition not satisfied'
    # A body that differs between Verus's verification and the compiled program
    # (`verus_keep_ghost_body` is set for the verification only): the generator refuses
    # the crate for the cfg it tests, before Verus runs; and since the fork `66c6c2b`
    # Verus itself refuses a crate whose source names that cfg (before, it verified
    # `allocates 0` for this function, whose compiled body allocates).
    mkdir -p "$out/cfgbody/src"
    printf '%s\n' '#![feature(proc_macro_hygiene)]' '#![allow(unexpected_cfgs)]' 'use vstd::prelude::*;' '#[verus_spec(r => allocates 0)]' 'pub fn quiet(x: u64) -> u64 {' '    #[cfg(not(verus_keep_ghost_body))]' '    let _b = Box::new(x);' '    x' '}' > "$out/cfgbody/src/lib.rs"
    if (cd "$out" && $gen --crate-name cfgbody --crate-dir cfgbody --out "$out/cfgbody.txt" -- {{verus}} --crate-type=lib --crate-name cfgbody {{verus_flags}} cfgbody/src/lib.rs) > "$out/cfgbody.log" 2>&1; then # negative probe
      echo "FAIL: a sidecar was generated for a crate whose body tests verus_keep_ghost_body"; exit 1
    fi
    grep -q 'tests `verus_keep_ghost_body`' "$out/cfgbody.log" || { echo "FAIL: the crate cfgbody failed for another reason"; cat "$out/cfgbody.log"; exit 1; }
    test ! -e "$out/cfgbody.txt"
    if (cd "$out" && {{verus}} --crate-type=lib --crate-name cfgbody {{verus_flags}} cfgbody/src/lib.rs) > "$out/cfgbody-verus.log" 2>&1; then # negative probe
      echo "FAIL: Verus verified a crate whose compiled body differs from the verified one"; exit 1
    fi
    grep -q 'alloc-check: Verus sets `verus_keep_ghost_body` only when it verifies the crate' "$out/cfgbody-verus.log" || { echo "FAIL: Verus refused the crate cfgbody for another reason"; cat "$out/cfgbody-verus.log"; exit 1; }
    # A standard-library crate run (`--is-vstd`; the fork audit, 2026-11-09): refused
    # before Verus runs, nothing written (the driver also refuses a sidecar recording it).
    if (cd "$fx" && $gen --crate-name vside --crate-dir vside --out "$out/isvstd.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} --is-vstd vside/src/lib.rs) 2> "$out/isvstd.err"; then # negative probe
      echo "FAIL: a sidecar was generated for a run with --is-vstd"; exit 1
    fi
    grep -q "refused Verus flag \`--is-vstd\`" "$out/isvstd.err"
    test ! -e "$out/isvstd.txt"
    # Allocation bounds (phase 4): the fixture verus_alloc's sidecar records each listed
    # function's proved `allocates` bound.
    fa=tools/fip-prelint/tests/fixtures/verus_alloc
    (cd "$fa" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name valloc --crate-dir valloc --out "$out/valloc.txt" -- {{verus}} --crate-type=lib --crate-name valloc {{verus_flags}} valloc/src/lib.rs)
    just verus-sidecar-check "$out/valloc.txt" "$fa/valloc/verus-verified.txt"
    # Declared sources of another crate (amendment 2026-11-19): `ypool` is exported and
    # compiled by its generator run, `yuser` imports it with its committed sidecar.
    fxs=tools/fip-prelint/tests/fixtures/verus_xsource; mkdir -p "$out/xsource"
    (cd "$fxs" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name ypool --crate-dir ypool --out "$out/ypool.txt" -- {{verus}} --crate-type=lib --crate-name ypool {{verus_flags}} ypool/src/lib.rs --export "$out/xsource/ypool.vir" --compile --out-dir "$out/xsource")
    just verus-sidecar-check "$out/ypool.txt" "$fxs/ypool/verus-verified.txt"
    (cd "$fxs" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name yuser --crate-dir yuser --out "$out/yuser.txt" --import-sidecar ypool=ypool/verus-verified.txt -- {{verus}} --crate-type=lib --crate-name yuser {{verus_flags}} yuser/src/lib.rs --import ypool="$out/xsource/ypool.vir" --extern ypool="$out/xsource/libypool.rlib")
    just verus-sidecar-check "$out/yuser.txt" "$fxs/yuser/verus-verified.txt"
    # An imported crate outside the tree, as a git or registry dependency is (its sources
    # are in cargo's checkout, at a path that differs from machine to machine): the
    # importer's sidecar names it by the hash of its sidecar (`import ..`), lists no
    # source of it, and the driver accepts the sidecar wherever the dependency lies.
    oot="$out/oot"; mkdir -p "$oot/depA" "$oot/proj" "$oot/o"
    cp -r "$fxs/ypool" "$oot/depA/"; cp -r "$fxs/yuser" "$oot/proj/"
    printf '[workspace]\nmembers = ["yuser"]\nresolver = "3"\n' > "$oot/proj/Cargo.toml"
    sed -i "s|ypool = { path = \"../ypool\" }|ypool = { path = \"$oot/depA/ypool\" }|" "$oot/proj/yuser/Cargo.toml"
    grep -q "$oot/depA/ypool" "$oot/proj/yuser/Cargo.toml"
    (cd "$oot/depA" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name ypool --crate-dir ypool --out "$oot/o/ypool.txt" -- {{verus}} --crate-type=lib --crate-name ypool {{verus_flags}} ypool/src/lib.rs --export "$oot/o/ypool.vir" --compile --out-dir "$oot/o")
    cmp "$oot/o/ypool.txt" "$fxs/ypool/verus-verified.txt"
    (cd "$oot/proj" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name yuser --crate-dir yuser --out "$oot/o/yuser.txt" --import-sidecar ypool="$oot/depA/ypool/verus-verified.txt" -- {{verus}} --crate-type=lib --crate-name yuser {{verus_flags}} yuser/src/lib.rs --import ypool="$oot/o/ypool.vir" --extern ypool="$oot/o/libypool.rlib")
    [ "$(grep -c '^source ' "$oot/o/yuser.txt")" = 1 ] && grep -q '^source src/lib.rs ' "$oot/o/yuser.txt" || { echo "FAIL: the out-of-tree importer's sidecar lists a source outside its crate"; grep '^source ' "$oot/o/yuser.txt"; exit 1; }
    grep -Eq '^import ypool [0-9a-f]{64} 2024$' "$oot/o/yuser.txt" || { echo "FAIL: no import line for ypool"; exit 1; }
    cp "$oot/o/yuser.txt" "$oot/proj/yuser/verus-verified.txt"
    (cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 cargo +{{prelint_tc}} build --locked -q --bin fip-prelint --target-dir target)
    drv="$PWD/tools/fip-prelint/target/debug"
    oot_run() {  # name: the driver on the out-of-tree project; Verus's bounds must be taken
      (cd "$oot/proj" && rm -f Cargo.lock && cargo +{{prelint_tc}} generate-lockfile -q \
        && { RUSTC_BOOTSTRAP=1 FIP_PRELINT_TARGET_DIR="$oot/target-$1" FIP_PRELINT_DRIVER_PATH="$drv/fip-prelint" "$drv/cargo-fip-prelint" fip-prelint --message-format short --locked > "$oot/o/run-$1.txt" 2>&1 || true; })
      grep -Eq 'crate `yuser`: 7 roots, 4 passed, 3 errors.*4 allocation bounds taken from Verus.*2 deallocation bounds taken from Verus' "$oot/o/run-$1.txt" \
        || { echo "FAIL: out-of-tree import ($1): the importer's sidecar was not used"; cat "$oot/o/run-$1.txt"; exit 1; }
      echo "out-of-tree import ($1): sidecar used"
    }
    oot_run at-a
    mv "$oot/depA" "$oot/depB"; sed -i "s|$oot/depA/ypool|$oot/depB/ypool|" "$oot/proj/yuser/Cargo.toml"
    oot_run moved
    # `total` marks (phase 5): the fixture verus_total's sidecar lists the functions the
    # driver discharges or refuses as `total` (tests/fixtures.rs `verus_total_marks`).
    ft=tools/fip-prelint/tests/fixtures/verus_total
    (cd "$ft" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name vtotal --crate-dir vtotal --out "$out/vtotal.txt" -- {{verus}} --crate-type=lib --crate-name vtotal {{verus_flags}} vtotal/src/lib.rs)
    just verus-sidecar-check "$out/vtotal.txt" "$ft/vtotal/verus-verified.txt"
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
    # Phase 4 (cfg twins, decision 2026-11-06-redesign-verus-allocates): a trait with
    # a plain-only implementation (returning 0 under the Verus declaration's
    # `ensures r > 0`): the generic caller `run`, its caller `run_s` and the concrete
    # caller `direct` are skipped and the trait is recorded as `divergent`. Before, all
    # three were listed and both divisions discharged.
    cp -r "$fx" "$out/twin"
    printf '%b' '\n#[cfg(verus_keep_ghost)]\nverus! {\npub trait Step {\n    fn step(&self) -> (r: u32)\n        ensures r > 0,\n        allocates 0;\n}\n\nimpl Step for S {\n    fn step(&self) -> (r: u32) { 1 }\n}\n}\n\n#[cfg(not(verus_keep_ghost))]\npub trait Step {\n    fn step(&self) -> u32;\n}\n\n#[cfg(not(verus_keep_ghost))]\nimpl Step for S {\n    fn step(&self) -> u32 {\n        let b = Box::new(0u32);\n        *b\n    }\n}\n\n#[cfg_attr(verus_keep_ghost, verifier::verify)]\npub struct S;\n\n#[cfg_attr(verus_keep_ghost, verus_spec(allocates 0))]\npub fn run<T: Step>(t: &T, a: u32) -> u32 {\n    a / t.step()\n}\n\n#[cfg_attr(verus_keep_ghost, verus_spec(allocates 0))]\npub fn run_s(a: u32) -> u32 {\n    run(&S, a)\n}\n\n#[cfg_attr(verus_keep_ghost, verus_spec(allocates 0))]\npub fn direct(a: u32) -> u32 {\n    a / S.step()\n}\n' >> "$out/twin/vside/src/lib.rs"
    (cd "$out/twin" && VERUS_SINGULAR_PATH="{{singular}}" $gen --crate-name vside --crate-dir vside --out "$out/twin.txt" -- {{verus}} --crate-type=lib --crate-name vside {{verus_flags}} vside/src/lib.rs) > "$out/twin.log" 2>&1
    for f in run run_s direct; do
      if grep -q "^fn vside::$f " "$out/twin.txt"; then echo "FAIL: $f, relying on a divergent trait, was listed"; exit 1; fi
    done
    grep -q "^skip vside::run relies on the specification of \`vside::Step::step\`, a method of trait \`Step\`" "$out/twin.txt"
    grep -q "^skip vside::direct relies on the specification of \`vside::Step::step\`, a method of trait \`Step\`" "$out/twin.txt"
    grep -q "^skip vside::run_s relies on the specification of \`vside::run\`" "$out/twin.txt"
    grep -q "^divergent Step src/lib.rs:" "$out/twin.txt"
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
# invariants, `call_allocations`, adapter-bound hints, `AllocFreeDrop` impls; it fails on
# any spelling it does not know), so the functional proofs do not depend on the fork's
# allocation pass. The fork's `.vir` files cannot be imported by upstream, so every
# crate is re-verified, with `--no-cheating` and the fork-only flags left out. In `ci`
# a missing `VERUS_UPSTREAM` is a failure (`FIP_REQUIRE_UPSTREAM=1`); run alone or in
# `ci-gates` it is skipped with a message (the fork remains the gate).
verify-upstream:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ -z "{{verus_upstream}}" ]; then
      if [ "${FIP_REQUIRE_UPSTREAM:-}" = 1 ]; then
        echo "FAIL: verify-upstream: VERUS_UPSTREAM is not set (a build of upstream Verus {{verus_upstream_pin}}); \`just ci\` requires the strip gate"; exit 1
      fi
      echo "verify-upstream: SKIPPED: VERUS_UPSTREAM is not set (a build of upstream Verus {{verus_upstream_pin}})"
      exit 0
    fi
    got=$({{verus_upstream}} --version --output-json 2> /dev/null | sed -n 's/^ *"version": "\(.*\)",\{0,1\}$/\1/p' | head -1) || true
    if [ "$got" != "{{verus_upstream_pin}}" ]; then
      echo "FAIL: VERUS_UPSTREAM is Verus ${got:-unreadable}, the strip gate's pin is {{verus_upstream_pin}} (justfile verus_upstream_pin)"; exit 1
    fi
    out=target/verify-upstream; rm -rf "$out"; mkdir -p "$out/strict" "$out/core" "$out/alloc"
    src="$out/src"
    uv run --no-project python verify/strip_alloc.py "$src" crates/fip-strict crates/fip-core crates/fip-alloc verify/compose.rs verify/compose_strict.rs verify/compose_state.rs verify/fip_fn_types.rs verify/total.rs
    # The proc-macro is loaded by the upstream Verus's rustc: built with its toolchain
    # (not the fork's), into its own directory.
    tc=$({{verus_upstream}} --version | awk '/Toolchain/ {print $2}')
    if [ -z "$tc" ]; then echo "FAIL: cannot read the toolchain of \`{{verus_upstream}}\`"; exit 1; fi
    m=target/verus-macros-upstream; rm -rf "$m"
    # `--ignore-rust-version`: upstream Verus is on an older rustc (1.99.1 at the pin)
    # than the workspace MSRV (1.100.0 since 2026-11-17). The proc-macro must be built
    # by the compiler that loads it, so this one build is exempt from the MSRV; it
    # fails here, visibly, the day `fip-macros` uses something that compiler lacks.
    cargo +"$tc" build --locked -q -p fip-macros --ignore-rust-version --target-dir "$m"
    {{one_artifact}}
    so=$(one_artifact "$m" fip_macros so)
    deps=$(dirname "$so")
    # `#[fip_macros::fip(strict ..)]`/`(total)` emit fork-only clauses under Verus
    # (phase 5), which the script cannot strip: `FIP_MACROS_UPSTREAM=1` makes the macro
    # leave out `allocates` and `#[verifier::fip(strict)]` (never `requires` or `no_unwind`,
    # which upstream verifies).
    up() {  # name, Verus arguments
      local name=$1; shift
      if FIP_MACROS_UPSTREAM=1 VERUS_SINGULAR_PATH="{{singular}}" {{verus_upstream}} --crate-type=lib --no-cheating --edition 2024 "$@" > "$out/$name.log" 2>&1; then
        echo "verify-upstream: $name: $(grep -h 'verification results' "$out/$name.log")"
      else
        cat "$out/$name.log"; echo "FAIL: upstream Verus rejects the stripped $name"; exit 1
      fi
    }
    strict="--import fip_strict=$out/strict/fip_strict.vir --extern fip_strict=$out/strict/libfip_strict.rlib"
    core="--import fip_core=$out/core/fip_core.vir --extern fip_core=$out/core/libfip_core.rlib -L $out/strict"
    up fip-strict --crate-name fip_strict "$src/fip-strict/src/lib.rs" --export "$out/strict/fip_strict.vir" --compile --out-dir "$out/strict"
    up fip-core --crate-name fip_core "$src/fip-core/src/lib.rs" $strict --extern fip_macros="$so" -L "$deps" --export "$out/core/fip_core.vir" --compile --out-dir "$out/core"
    up fip-alloc --crate-name fip_alloc "$src/fip-alloc/src/lib.rs" $strict --extern fip_macros="$so" -L "$deps"
    up compose.rs --extern fip_macros="$so" -L "$deps" $strict "$src/compose.rs"
    up compose_strict.rs --extern fip_macros="$so" -L "$deps" $strict "$src/compose_strict.rs"
    up compose_state.rs --extern fip_macros="$so" -L "$deps" $strict $core "$src/compose_state.rs"
    up fip_fn_types.rs --extern fip_macros="$so" -L "$deps" $strict "$src/fip_fn_types.rs"
    up total.rs --extern fip_macros="$so" -L "$deps" $strict "$src/total.rs"
    # Control: without the switch the macro emits `allocates` (at the `strict`/`total`
    # key of the attribute), which upstream does not parse, so the switch is what makes
    # the stripped `total.rs` pass.
    if VERUS_SINGULAR_PATH="{{singular}}" {{verus_upstream}} --crate-type=lib --no-cheating --edition 2024 --extern fip_macros="$so" -L "$deps" $strict "$src/total.rs" > "$out/total-noswitch.log" 2>&1; then
      echo "FAIL: upstream Verus accepted total.rs without FIP_MACROS_UPSTREAM=1"; exit 1
    fi
    grep -A3 "^error: unexpected token" "$out/total-noswitch.log" | grep -q "#\[fip(total" || { echo "FAIL: upstream rejected total.rs without the switch for another reason"; cat "$out/total-noswitch.log"; exit 1; }
    echo "verify-upstream: control: without FIP_MACROS_UPSTREAM=1 the stripped total.rs is rejected"
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

# `fip-testkit`'s tests on a target without 64-bit atomics, under qemu-user: there the
# process-wide counters are a `Mutex<[u64; 4]>` locked inside the global allocator
# (`cfg(not(target_has_atomic = "64"))`), and only running them shows that the lock
# neither allocates nor deadlocks (`tests/all_threads.rs` counts across threads).
# Not in `ci`: needs `qemu-arm` and the `armv5te-unknown-linux-musleabi` target
# (linked by `rust-lld`).
testkit-qemu-armv5te:
    #!/usr/bin/env bash
    set -euo pipefail
    t=armv5te-unknown-linux-musleabi
    rustc --print cfg --target $t | grep -q '^target_has_atomic="64"$' && { echo "FAIL: $t has 64-bit atomics; this recipe would not run the Mutex counters"; exit 1; }
    export CARGO_TARGET_ARMV5TE_UNKNOWN_LINUX_MUSLEABI_RUSTFLAGS="{{musl_lld}}"
    for profile in "" --release; do
      CARGO_TARGET_ARMV5TE_UNKNOWN_LINUX_MUSLEABI_RUNNER=qemu-arm \
        cargo test --locked $profile -p fip-testkit --target $t --target-dir target/armv5te-qemu
    done
    echo "testkit-qemu-armv5te: ok"

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
# Own target dir: the script needs exactly one build of each crate, by the rustc of `rust-toolchain.toml`.
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

# The per-target self-check of `fip-prelint` (tests/targets.rs) on the RECORDED targets:
# those with a section in `tools/fip-prelint/tests/targets.expected`. This is the set
# `just ci` gates on (through `prelint`); a recorded target that is not installed fails
# here. Installed targets without a section are named in a note and not built.
prelint-targets:
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 FIP_PRELINT_TOOLCHAIN={{prelint_tc}} FIP_PRELINT_TARGETS=recorded FIP_PRELINT_REQUIRE_TARGETS=1 cargo +{{prelint_tc}} test --locked --test targets -- --nocapture

# The same self-check on EVERY target installed in the driver's toolchain (one workspace
# build per target, four at a time). An installed target without a section fails: review
# its output, then record it with `FIP_PRELINT_BLESS=1 just prelint-targets-all`. Not in
# `ci`: its result depends on what is installed on the host.
prelint-targets-all:
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 FIP_PRELINT_TOOLCHAIN={{prelint_tc}} FIP_PRELINT_TARGETS=all cargo +{{prelint_tc}} test --locked --test targets -- --nocapture

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
# 32-45 s of it the analysis); the result is committed. Build directory
# `FIP_PRELINT_TARGET_DIR`, else under /tmp.
prelint-std-summaries target="x86_64-unknown-linux-gnu":
    cd tools/fip-prelint && RUSTC_BOOTSTRAP=1 cargo +{{prelint_tc}} build --locked
    cd tools/fip-prelint && FIP_PRELINT_TOOLCHAIN={{prelint_tc}} FIP_PRELINT_TARGET_DIR="${FIP_PRELINT_TARGET_DIR:-/tmp/fip-prelint-std-summaries}" target/debug/cargo-fip-prelint fip-prelint --std-summaries --target {{target}}

# The std summaries for the RECORDED targets with `std` (the `std` sections of
# `tools/fip-prelint/tests/targets.expected`): the set that is committed and gated.
prelint-std-summaries-recorded:
    #!/usr/bin/env bash
    set -euo pipefail
    for t in $(sed -n 's/^== \(.*\) std$/\1/p' tools/fip-prelint/tests/targets.expected); do
      just prelint-std-summaries "$t"
    done

# The std summaries for every installed target with `std` (top plan T7j), one after
# the other, into one build directory (`FIP_PRELINT_TARGET_DIR`, else under /tmp; measured 2026-11-03: 3.8-12.4
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
