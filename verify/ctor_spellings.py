# SPDX-License-Identifier: MIT OR Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
"""Check `#[fip]` and `#[fip(strict = true)]` on every spelling of
`fip_lint_rules::callee::SPELLINGS` (crates/fip-lint-rules/src/callee.rs).

Each spelling is compiled with rustc against the built crates, as the body
`let _x: <type> = <expression>;` of a function with parameters
`v: Vec<u8>, mut a: u8, b: u8`, once under `#[fip_macros::fip]` and once under
`#[fip_macros::fip(strict = true)]`:

- `alloc Ty::f`: both fail with "allocation site `Ty::f`";
- `ok` (an audited non-allocating constructor): both compile;
- `inferred`: `#[fip]` compiles (the token rule cannot tell; `fip-prelint` decides),
  strict mode fails with "the type it builds is inferred";
- `other`: `#[fip]` compiles.

The same table drives `fip-lint-rules`' and `fip_testkit`'s unit tests.

Usage: python verify/ctor_spellings.py <cargo target dir>
"""

import glob
import os
import re
import subprocess
import sys
import tempfile

PRELUDE = """#![allow(unused, clippy::all)]
extern crate alloc;
use std::collections::*;
use std::rc::Rc;
pub struct Foo;
impl Foo { pub fn new() -> Foo { Foo } }
"""


def lib_dirs(target: str) -> list[str]:
    """Directories cargo puts a crate's artifacts in: `debug/deps` (cargo up to
    1.99) and `debug/build/<package>/<hash>/out` (cargo 1.100)."""
    dirs = [os.path.join(target, "debug", "deps")]
    dirs += sorted(glob.glob(os.path.join(target, "debug", "build", "*", "*", "out")))
    return [d for d in dirs if os.path.isdir(d)]


def newest(dirs: list[str], name: str) -> str:
    files = [f for d in dirs for f in glob.glob(os.path.join(d, name))]
    if not files:
        raise SystemExit(f"not found: {name} in {dirs}")
    return max(files, key=os.path.getmtime)


def search_args(dirs: list[str]) -> list[str]:
    return [a for d in dirs for a in ("-L", d)]


def spellings() -> list[tuple[str, str, str]]:
    src = open("crates/fip-lint-rules/src/callee.rs", encoding="utf-8").read()
    m = re.search(r"pub const SPELLINGS: &\[\(&str, &str, &str\)\] = &\[(.*?)\n\];", src, re.S)
    if not m:
        raise SystemExit("SPELLINGS not found")
    lit = r'"((?:[^"\\]|\\.)*)"'
    out = []
    for e, t, w in re.findall(r"\(\s*" + lit + r",\s*" + lit + r",\s*" + lit + r",?\s*\)", m.group(1)):
        out.append((e.replace('\\"', '"'), t, w))
    return out


def compile_errors(code: str, deps: list[str], externs: dict[str, str]) -> tuple[int, list[str]]:
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "t.rs")
        with open(path, "w", encoding="utf-8") as f:
            f.write(code)
        cmd = ["rustc", "--edition", "2024", "--crate-type", "lib",
               "--out-dir", d, *search_args(deps)]
        for name, lib in externs.items():
            cmd += ["--extern", f"{name}={lib}"]
        r = subprocess.run(cmd + [path], capture_output=True, text=True, check=False)
    errors = [l for l in r.stderr.splitlines() if l.startswith("error") and "aborting" not in l]
    return r.returncode, errors


def main() -> int:
    deps = lib_dirs(sys.argv[1])
    externs = {
        "fip_macros": newest(deps, "libfip_macros-*.so"),
        "fip_strict": newest(deps, "libfip_strict-*.rlib"),
    }
    table = spellings()
    if len(table) < 40:
        print(f"only {len(table)} spellings parsed")
        return 1
    bad = 0
    for expr, ty, want in table:
        ann = f": {ty}" if ty else ""
        for attr, strict in (("#[fip_macros::fip]", False), ("#[fip_macros::fip(strict = true)]", True)):
            if want == "other" and strict:
                continue
            code = f"{PRELUDE}{attr}\npub fn f(v: Vec<u8>, mut a: u8, b: u8) {{ let _x{ann} = {expr}; }}\n"
            status, errors = compile_errors(code, deps, externs)
            if want.startswith("alloc "):
                needle = f"allocation site `{want[6:]}`"
                ok = status != 0 and any(needle in e for e in errors)
            elif want == "inferred" and strict:
                ok = status != 0 and any("the type it builds is inferred" in e for e in errors)
            else:
                ok = status == 0
            mode = "strict" if strict else "plain "
            if ok:
                print(f"ok  {mode} {want:28} {expr}")
            else:
                bad += 1
                print(f"BAD {mode} {want:28} {expr}: {errors[:2]}")
    total = sum(1 if w == "other" else 2 for _, _, w in table)
    print(f"{total - bad}/{total} spelling checks as expected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
