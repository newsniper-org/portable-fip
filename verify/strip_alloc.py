# SPDX-License-Identifier: MIT OR Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
"""Strips the allocation layer of the Verus fork from Rust sources (`just verify-upstream`).

Upstream Verus has no `allocates` clause, no `call_allocations` and no
`vstd::alloc_check` (decision record 2026-11-06-redesign-verus-allocates, section 3:
`allocates` is a parse error on upstream 0.2026.11.02). The strip gate verifies the
stripped sources with upstream Verus, showing that the functional proofs do not depend
on the fork's allocation pass.

usage: strip_alloc.py <dst-dir> <src-dir-or-file>..

Each source (a directory tree or one file) is copied under <dst-dir> with its base
name; every `.rs` file of the copy that Verus reads is rewritten: a file source, and
the `src/` tree of a directory source (a crate's `tests/` are plain Rust, never given
to Verus). Removed:
  - `deallocates E` clauses on a line of their own, lines mentioning `deallocated()`
    or `call_deallocations`, and the whole text of `dealloc_spec.rs` (the fork's
    deallocation counting, 2026-11-22; the module stays, empty);
  - `allocates E` clauses: a line starting with `allocates `, or `, allocates E` at
    the end of a one-line `verus_spec(..)` (E up to the closing parenthesis), and a
    closure attribute line `#[cfg_attr(verus_keep_ghost, verus_spec(r: T => allocates E))]`
    whose only clause is the bound;
  - lines mentioning `allocated()` or `call_allocations` (invariants, requires, `pre`
    conjuncts), and `forall` lines whose next line is such a conjunct;
  - proof hints about adapter bounds: `proof! { assert(..allocs(..)..) }` lines, and
    multi-line `proof! { .. }` blocks holding only `assert(..allocs(..)..);` lines;
  - the `allocs` spec function of `FipFn` and its implementations;
  - `verus! { .. }` blocks whose first item comment starts with `/// \\`allocates\\`
    total` or `/// Callbacks that allocate nothing` (sum spec functions, zero lemmas);
  - `unsafe impl .. vstd::alloc_check::AllocFreeDrop for ..` (with its
    `#[cfg(verus_keep_ghost)]`) and the bounds on it; the Verus-only re-exports of
    `AllocFreeDrop` / `NoDeallocDrop` become marker traits with a blanket impl, as in
    plain builds;
  - the drop preconditions `vstd::alloc_check::bound_drop_alloc_free::<F>()` and
    `!vstd::alloc_check::drop_may_deallocate::<F>()` (a conjunct on a line of its own;
    with its `requires` where it is the only one);
  - hand-written `#[cfg_attr(verus_keep_ghost, verifier::fip)]` attribute lines (the
    fork's `fip`, phase 5; upstream has no such attribute).
What `#[fip_macros::fip(strict ..)]`/`(total)` generate is macro output, which this
script cannot see: `just verify-upstream` sets `FIP_MACROS_UPSTREAM=1` for that
(`fip-macros` then leaves out `allocates` and `#[verifier::fip]`, never `requires`
or `no_unwind`).
The script then fails if any code line (comments excluded) still names `allocates`,
`allocated()`, `call_allocations`, `deallocates`, `deallocated()`, `call_deallocations`,
`alloc_check` or `verifier::fip`: a new spelling must
be taught here, never passed silently to upstream Verus (where it would be an error
anyway).
"""

import pathlib
import re
import shutil
import sys

ONLY_ALLOCATES_ATTR = re.compile(
    r"^\s*#\[cfg_attr\(verus_keep_ghost, verus_spec\(\w+(?:: [^=]+)? => allocates [^()]*(?:\([^()]*\))?\)\)\]$"
)
LEFTOVER = re.compile(
    r"\ballocates\b|\ballocated\(\)|\bcall_allocations\b|\balloc_check\b|\bverifier::fip\b"
    r"|\bdeallocates\b|\bdeallocated\(\)|\bcall_deallocations\b|\bcall_unwinds\b"
)
FIP_ATTR = re.compile(r"^\s*#\[cfg_attr\(verus_keep_ghost, verifier::fip(?:\(strict\))?\)\]$")


def strip_inline_allocates(line: str) -> str:
    """`.., ensures r == x, allocates 0))]` -> `.., ensures r == x))]`."""
    m = re.search(r",\s*allocates\s", line)
    if not m:
        return line
    depth = 0
    for k in range(m.end(), len(line)):
        c = line[k]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                return line[: m.start()] + line[k:]
            depth -= 1
        elif c == "," and depth == 0:
            return line[: m.start()] + line[k:]
    raise SystemExit(f"strip_alloc: unterminated inline `allocates` in: {line.strip()}")


def strip(s: str) -> str:
    s = re.sub(r"\n\nverus! \{\n\n/// `allocates` total.*?\} // verus!\n", "\n", s, flags=re.S)
    s = re.sub(r"\n\nverus! \{\n\n/// Callbacks that allocate nothing.*?\} // verus!\n", "\n", s, flags=re.S)
    s = re.sub(r"\n[ ]*proof! \{\n(?:[ ]*assert\([^\n]*allocs\([^\n]*\);\n)+[ ]*\}(?=\n)", "", s)
    s = re.sub(
        r"\n[^\n]*forall\|i: int, j: int\|[^\n]*\n[^\n]*==> call_(?:allocations|deallocations)\([^\n]*",
        "",
        s,
    )
    # A `requires` with nothing but the fork's drop precondition (`Certified::assume`).
    s = re.sub(
        r"\n[ ]*requires\n[ ]*vstd::alloc_check::bound_drop_alloc_free::<\w+>\(\),(?=\n[ ]*ensures\b)",
        "",
        s,
    )
    lines: list[str] = []
    skip = 0
    for line in s.split("\n"):
        t = line.strip()
        if skip:
            skip -= 1
            continue
        if ONLY_ALLOCATES_ATTR.match(line) or FIP_ATTR.match(line):
            continue
        if t.startswith("allocates ") or t.startswith("deallocates "):
            if t.count("(") != t.count(")"):
                raise SystemExit(f"strip_alloc: multi-line `allocates` clause: {t}")
            continue
        if "allocated()" in t or "call_allocations" in t or "call_deallocations" in t:
            continue
        # The fork's unwinding of function values: `no_unwind when ..call_unwinds..` of
        # the `Fn`-based functions goes (upstream: they may unwind, as before), and
        # `Certified::may_unwind` is `true` (its `call` then claims nothing).
        if t.startswith("no_unwind when ") and "call_unwinds(" in t:
            continue
        if t == "call_unwinds(self.inner(), args)":
            lines.append(line.replace("call_unwinds(self.inner(), args)", "true"))
            continue
        # The drop preconditions of the `Fn`-based functions (conjuncts of a `requires`
        # that has others).
        if t.startswith("vstd::alloc_check::bound_drop_alloc_free::<") or t.startswith(
            "!vstd::alloc_check::drop_may_deallocate::<"
        ):
            continue
        if t.startswith("proof!") and "allocs(" in t:
            continue
        if ".allocs()" in t and "nonlinear_arith" in t:
            continue
        if t.startswith("/// Upper bound on the allocations of one call"):
            continue
        if t.startswith("spec fn allocs(&self)"):
            continue
        if t.startswith("open spec fn allocs(&self)"):
            skip = 2
            continue
        if "vstd::alloc_check::AllocFreeDrop for" in t or "vstd::alloc_check::NoDeallocDrop for" in t:
            if lines and lines[-1].strip().startswith('#[allow(unsafe_code, reason = "checked by Verus'):
                lines.pop()
            if lines and lines[-1].strip() == "#[cfg(verus_keep_ghost)]":
                lines.pop()
            continue
        lines.append(strip_inline_allocates(line))
    s = "\n".join(lines)
    s = s.replace("&&& self.inner().requires(args)", "self.inner().requires(args)")
    s = s.replace(
        "#[cfg(verus_keep_ghost)]\npub use vstd::alloc_check::AllocFreeDrop;",
        "#[cfg(verus_keep_ghost)]\npub trait AllocFreeDrop {}\n#[cfg(verus_keep_ghost)]\nimpl<T: ?Sized> AllocFreeDrop for T {}",
    )
    s = s.replace(
        "#[cfg(verus_keep_ghost)]\npub use vstd::alloc_check::NoDeallocDrop;",
        "#[cfg(verus_keep_ghost)]\npub trait NoDeallocDrop {}\n#[cfg(verus_keep_ghost)]\nimpl<T: ?Sized> NoDeallocDrop for T {}",
    )
    s = s.replace("broadcast use fip_core::spec::group_allocs_zero;\n", "")
    s = s.replace(": vstd::alloc_check::AllocFreeDrop", ": crate::AllocFreeDrop")
    s = s.replace("$($A: crate::AllocFreeDrop,)*", "$($A,)*")
    s = re.sub(r"(\w+): (?:crate::|fip_strict::)AllocFreeDrop([,>])", r"\1\2", s)
    s = s.replace(" + crate::NoDeallocDrop", "").replace(" + fip_strict::NoDeallocDrop", "")
    s = s.replace(" + crate::AllocFreeDrop", "")
    s = s.replace("pub use fip_strict::{AllocFreeDrop, NoDeallocDrop};\n", "")
    return s


def leftovers(path: pathlib.Path, s: str) -> list[str]:
    bad = []
    for n, line in enumerate(s.split("\n"), 1):
        code = line.split("//", 1)[0]
        if LEFTOVER.search(code):
            bad.append(f"{path}:{n}: {line.strip()}")
    return bad


def main() -> None:
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    dst = pathlib.Path(sys.argv[1])
    dst.mkdir(parents=True, exist_ok=True)
    files: list[pathlib.Path] = []
    for src in map(pathlib.Path, sys.argv[2:]):
        out = dst / src.name
        if out.exists():
            shutil.rmtree(out) if out.is_dir() else out.unlink()
        if src.is_dir():
            shutil.copytree(src, out, ignore=shutil.ignore_patterns("target"))
            files.extend(sorted((out / "src").rglob("*.rs")))
        else:
            shutil.copy2(src, out)
            files.append(out)
    bad: list[str] = []
    changed = 0
    for p in files:
        before = p.read_text()
        # The deallocation totals exist only for the fork's `deallocates` clauses.
        after = (
            "// (the fork's deallocation totals: stripped for upstream Verus)\n"
            if p.name == "dealloc_spec.rs"
            else strip(before)
        )
        if after != before:
            changed += 1
            p.write_text(after)
        bad.extend(leftovers(p, after))
    if bad:
        raise SystemExit("strip_alloc: allocation syntax left after stripping:\n" + "\n".join(bad))
    print(f"strip_alloc: {len(files)} files, {changed} rewritten -> {dst}")


if __name__ == "__main__":
    main()
