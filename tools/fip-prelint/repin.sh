#!/usr/bin/env bash
# SPDX-License-Identifier: MIT OR Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
#
# Moves fip-prelint to another rustc (limits plan L10a; `just prelint-repin <version>`).
#
# The driver links `rustc_private` crates and reads MIR, both unstable: every rustc
# release may change the API, the shipped MIR (entry points, inlining) and the
# standard library the trusted tables were audited against. This script runs every
# check that a repin needs, in order, and stops at the first failure:
#
#   1. toolchain <version> with rustc-dev, rust-src and llvm-tools (INSTALL=1 installs it);
#   2. build the driver with it, ignoring the workspace MSRV (a failure here is an
#      API change: fix the driver);
#   3. the decision record's probes (tools/fip-prelint/probes): MIR of a non-inline
#      function readable downstream only with -Zalways-encode-mir; crate-root
#      `fip::export` and function `fip::mark` readable from a dependency; E0514 when
#      another rustc reads the metadata;
#   4. the allocator entry-point dump (FIP_PRELINT_DUMP=1) of Box::new, vec!,
#      Vec::with_capacity, String::from, format!, Vec::push and a Box drop: each must
#      still reach an allocation (or free) leaf; the leaves are printed for comparison
#      with TODOs/fip-prelint.md "Allocator entry points";
#   5. the std summaries sidecars (`--std-summaries`) for every installed target with
#      `std` (top plan T7j; TARGETS="<triple> .." restricts the list): for the pinned
#      version each is regenerated under /tmp and must equal the committed file byte
#      for byte; for a new version they are written to
#      std-summaries/<release>-<target>.txt (commit them after review);
#   6. the driver's tests (unit tests, every fixture, the self-check, every installed
#      target, the compile_fail examples) with the new toolchain; their diffs must be
#      reviewed one by one before blessing (FIP_PRELINT_BLESS=1);
#   7. the audit checklist: the pin site to change (APPLY=1 rewrites
#      rust-toolchain.toml, from which build.rs and the justfile read the toolchain)
#      and the trusted tables to re-audit by hand against the new sources.
#
# Logs and build directories go to $FIP_PRELINT_REPIN_DIR (default
# /tmp/fip-prelint-repin-<version>), never to the repository's target/.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: repin.sh <rustc version, e.g. 1.99.1>" >&2
  exit 2
fi
v=$1
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=${FIP_PRELINT_REPIN_DIR:-/tmp/fip-prelint-repin-$v}
mkdir -p "$out"
cur=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$here/rust-toolchain.toml")
step() { printf '\n== %s\n' "$*"; }
fail() { printf 'repin: FAILED: %s\n' "$*" >&2; exit 1; }

step "1. toolchain $v (pinned now: $cur)"
if ! rustup toolchain list | grep -q "^$v-"; then
  if [ "${INSTALL:-0}" = 1 ]; then
    rustup toolchain install "$v" --profile minimal --component rustc-dev,rust-src,llvm-tools
  else
    fail "toolchain $v is not installed (INSTALL=1 installs it with rustc-dev, rust-src, llvm-tools)"
  fi
fi
for c in rustc-dev rust-src; do
  rustup +"$v" component list --installed | grep -q "^$c" || fail "component $c missing for $v"
done
sysroot=$(rustc +"$v" --print sysroot)
release=$(rustc +"$v" -vV | sed -n 's/^release: //p')
host=$(rustc +"$v" -vV | sed -n 's/^host: //p')
echo "rustc $release, host $host, sysroot $sysroot"

step "2. build the driver"
(cd "$here" && RUSTC_BOOTSTRAP=1 cargo +"$v" build --ignore-rust-version --target-dir "$out/target") > "$out/build.log" 2>&1 \
  || { tail -30 "$out/build.log"; fail "the driver does not build with $v (see the log: a rustc_private API change); log: $out/build.log"; }
bin="$out/target/debug"
echo "built: $bin/fip-prelint"

step "3. probes"
p="$out/probes"; rm -rf "$p"; mkdir -p "$p"
export LD_LIBRARY_PATH="$sysroot/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
for probe in optimized_mir_probe rustc_public_probe; do
  RUSTC_BOOTSTRAP=1 rustc +"$v" --edition 2024 -O "$here/probes/$probe.rs" -o "$p/$probe" > "$p/$probe.build.log" 2>&1 \
    || { cat "$p/$probe.build.log"; fail "probe $probe does not build"; }
done
echo 'extern crate dep; fn main() {}' > "$p/consumer.rs"
for flag in on off; do
  mkdir -p "$p/$flag"
  extra=(); [ "$flag" = on ] && extra=(-Zalways-encode-mir)
  RUSTC_BOOTSTRAP=1 rustc +"$v" --edition 2024 --crate-type lib --crate-name dep --emit=metadata -Copt-level=0 \
    "${extra[@]}" "$here/probes/dep.rs" --out-dir "$p/$flag"
  PROBE_SYSROOT="$sysroot" PROBE_DEP=dep PROBE_FN=big RUSTC_BOOTSTRAP=1 "$p/optimized_mir_probe" \
    --edition 2024 "$p/consumer.rs" --extern "dep=$p/$flag/libdep.rmeta" -o "$p/consumer-$flag" > "$p/mir-$flag.log" 2>&1 || true
  cat "$p/mir-$flag.log"
done
grep -q "PROBE dep::big is_mir_available=true" "$p/mir-on.log" || fail "MIR of dep::big not readable with -Zalways-encode-mir"
grep -q "PROBE dep::big is_mir_available=false" "$p/mir-off.log" || fail "MIR of dep::big readable without -Zalways-encode-mir (the export rule assumes it is not)"
tool=(--cfg fip_prelint -Zcrate-attr='feature(register_tool)' -Zcrate-attr='feature(custom_inner_attributes)' -Zcrate-attr='register_tool(fip)' -Zalways-encode-mir)
RUSTC_BOOTSTRAP=1 rustc +"$v" --edition 2024 --crate-type lib --crate-name dep --emit=metadata "${tool[@]}" \
  "$here/probes/dep2.rs" --out-dir "$p/export"
PROBE_SYSROOT="$sysroot" RUSTC_BOOTSTRAP=1 "$p/rustc_public_probe" --edition 2024 --crate-type lib \
  --emit=metadata "${tool[@]}" "$here/probes/cons2.rs" --extern "dep=$p/export/libdep.rmeta" --out-dir "$p/export" \
  > "$p/attrs.log" 2>&1 || true
cat "$p/attrs.log"
grep -q 'DEP crate root tool attrs: .*"fip::export"' "$p/attrs.log" || fail "crate-root fip::export of a dependency not readable"
grep -q 'DEP fn dep::marked .*fip::mark' "$p/attrs.log" || fail "fip::mark of a dependency's function not readable"
if [ "$v" != "$cur" ] && rustup toolchain list | grep -q "^$cur-"; then
  if rustc +"$cur" --edition 2024 "$p/consumer.rs" --extern "dep=$p/on/libdep.rmeta" --emit=metadata \
       --out-dir "$p/cross" > "$p/e0514.log" 2>&1; then
    fail "rustc $cur read metadata of $v (expected E0514)"
  fi
  grep -q "E0514" "$p/e0514.log" || { cat "$p/e0514.log"; fail "rustc $cur failed on metadata of $v for another reason"; }
  echo "E0514 when rustc $cur reads metadata of $v: as expected"
fi

step "4. allocator entry points (FIP_PRELINT_DUMP=1)"
e="$out/entry"; rm -rf "$e"; mkdir -p "$e/src"
cat > "$e/Cargo.toml" <<'EOF'
[package]
name = "entry"
version = "0.0.0"
edition = "2024"
publish = false

[workspace]

[lints.rust]
unexpected_cfgs = { level = "allow" }
EOF
cat > "$e/src/lib.rs" <<'EOF'
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn box_new(x: u32) -> Box<u32> { Box::new(x) }
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn vec_macro(x: u8) -> Vec<u8> { vec![x, x, x] }
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn with_capacity(n: usize) -> Vec<u8> { Vec::with_capacity(n) }
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn string_from(s: &str) -> String { String::from(s) }
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn format(x: u32) -> String { format!("{x}") }
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn push(v: &mut Vec<u8>) { v.push(1) }
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn drop_box(b: Box<u32>) { drop(b) }
EOF
(cd "$e" && FIP_PRELINT_TOOLCHAIN="$v" FIP_PRELINT_DUMP=1 FIP_PRELINT_TARGET_DIR="$e/target" \
   FIP_PRELINT_DRIVER_PATH="$bin/fip-prelint" "$bin/cargo-fip-prelint" fip-prelint --message-format short) \
   > "$e/dump.log" 2>&1 || true
for root in box_new vec_macro with_capacity string_from format push; do
  grep -q "\`$root\` is #\[fip\] but may allocate" "$e/dump.log" || fail "$root does not reach an allocation; log: $e/dump.log"
done
grep -q "\`drop_box\` is #\[fip\] but may free" "$e/dump.log" || fail "drop_box does not reach a free; log: $e/dump.log"
echo "leaves reached (compare with TODOs/fip-prelint.md, \"Allocator entry points\"):"
grep 'is #\[fip\] but may' "$e/dump.log" \
  | sed -E 's/^.*`([a-z_]+)` is #\[fip\] but (may [a-z]+).*: ((allocation|free)[^;]*)$/  \1: \2, leaf: \3/' | sort -u

std_targets() {
  for d in "$sysroot"/lib/rustlib/*/lib; do
    if ls "$d"/libstd-*.rlib > /dev/null 2>&1; then
      basename "$(dirname "$d")"
    fi
  done
}
targets=${TARGETS:-$(std_targets | sort | tr '\n' ' ')}
step "5. std summaries for: $targets"
for t in $targets; do
  committed="$here/std-summaries/$release-$t.txt"
  if [ "$v" = "$cur" ] && [ -f "$committed" ]; then
    gen="$out/std-summaries-$release-$t.txt"
  else
    gen="$committed"
  fi
  FIP_PRELINT_TOOLCHAIN="$v" FIP_PRELINT_TARGET_DIR="$out/std-build" FIP_PRELINT_DRIVER_PATH="$bin/fip-prelint" \
    "$bin/cargo-fip-prelint" fip-prelint --std-summaries --target "$t" --out "$gen" > "$out/std-summaries-$t.log" 2>&1 \
    || { tail -30 "$out/std-summaries-$t.log"; fail "std summaries generation for $t"; }
  if [ "$gen" != "$committed" ]; then
    cmp "$gen" "$committed" || fail "regenerated std summaries differ from $committed"
    echo "regenerated std summaries are identical to $committed"
  else
    echo "written: $committed (review and commit it; remove files of rustc versions no longer pinned)"
  fi
done

step "6. driver tests with $v (fixtures, self-check, targets, compile_fail examples)"
if (cd "$here" && RUSTC_BOOTSTRAP=1 FIP_PRELINT_TOOLCHAIN="$v" cargo +"$v" test --ignore-rust-version --target-dir "$out/target") > "$out/test.log" 2>&1; then
  echo "all driver tests pass with $v"
  tests_ok=1
else
  grep -E "^test .* FAILED|^---- " "$out/test.log" || true
  echo "some tests fail with $v; review each diff (log: $out/test.log), then bless with FIP_PRELINT_BLESS=1"
  tests_ok=0
fi

step "7. audit checklist"
echo "Pin site (APPLY=1 rewrites it from $cur to $v): the driver's toolchain is read from"
echo "it by tools/fip-prelint/build.rs (DEFAULT_TOOLCHAIN, the tests) and by the justfile (prelint_tc):"
grep -n "\"$cur\"" "$repo/tools/fip-prelint/rust-toolchain.toml" | sed "s|^|  tools/fip-prelint/rust-toolchain.toml:|"
if [ "${APPLY:-0}" = 1 ] && [ "$v" != "$cur" ]; then
  sed -i "s/^channel = \"$cur\"$/channel = \"$v\"/" "$repo/tools/fip-prelint/rust-toolchain.toml"
  echo "  rewritten to $v"
fi
cat <<EOF
Re-audit by hand against $sysroot/lib/rustlib/src/rust/library (trusted, not derived):
  - fip_lint_rules::mir: ALLOC_ENTRY_POINTS, REALLOC_ENTRY_POINTS, DEALLOC_ENTRY_POINTS,
    ALLOC_FREE_SYMBOLS, FOREIGN_ALLOC_SYMBOLS, ALLOCATOR_TRAIT_METHODS, PANIC_PREFIXES,
    UB_CHECK_MARKERS, ALLOC_FREE_INTRINSICS, PANIC_INTRINSICS, INTRINSIC_RESULT_BOUNDS
    (crates/fip-lint-rules/src/lib.rs; compare with step 4's leaves);
  - fip_lint_rules: NON_ALLOCATING_CONSTRUCTORS and CORE_TABLE, then add $release to
    NON_ALLOCATING_CONSTRUCTORS_AUDITED_AT and CORE_TABLE_AUDITED_AT (tests fail on an
    unaudited compiler);
  - tools/fip-prelint/src/value.rs: the iterator contracts (Range, RangeInclusive,
    Rev, slice::Iter{,Mut}, Enumerate, Zip; their differential unit tests run the real
    adapters) and the drop_glue lang item used for drops;
  - tools/fip-prelint/src/analysis.rs: core never assigns Formatter::buf after
    building a Formatter (bindings of the std summaries);
  - the Verus toolchain: the driver's rustc must be the pinned Verus's
    (\`just verus-pin\` checks it, tools/fip-prelint/verus-trusted.txt), and the
    workspace MSRV (Cargo.toml rust-version, which the justfile's msrv reads).
Then: amend docs/decisions/2026-11-01-fip-prelint.md, update README and TODOs, and run
\`just ci\`.
EOF
[ "$tests_ok" = 1 ] || exit 1
echo "repin checks for $v: ok"
