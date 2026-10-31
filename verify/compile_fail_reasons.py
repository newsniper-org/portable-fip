# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
"""Check that every `compile_fail` doctest in fip-macros fails for the intended reason.

rustdoc's `compile_fail` passes on any compilation error, so a typo in an example
would make a rejected case look covered. This script compiles each example with
rustc against the built crates and checks the errors:

- an example with a hidden line `# // expect: <text>` must produce an error whose
  message contains <text>, and every other error must be a known follow-up of it;
- an example without one must fail only with fip-macros' own messages.

Usage: python verify/compile_fail_reasons.py <target dir with debug/deps>
"""

import glob
import os
import re
import subprocess
import sys
import tempfile

LINT_MARKERS = ("#[fip", "#[fbip", "FIP attributes", "`#[fbip]` takes")
# Errors rustc emits after the primary one for the same cause.
FOLLOW_UPS = ("erroneous constant", "aborting due to", "could not compile")


def newest(pattern: str) -> str:
    files = glob.glob(pattern)
    if not files:
        raise SystemExit(f"not found: {pattern}")
    return max(files, key=os.path.getmtime)


def main() -> int:
    deps = os.path.join(sys.argv[1], "debug", "deps")
    externs = {
        "fip_macros": newest(os.path.join(deps, "libfip_macros-*.so")),
        "fip_strict": newest(os.path.join(deps, "libfip_strict-*.rlib")),
    }
    src = open("crates/fip-macros/src/lib.rs", encoding="utf-8").read()
    blocks = re.findall(r"//! ```compile_fail\n((?://!.*\n)+?)//! ```", src)
    if not blocks:
        print("no compile_fail examples found")
        return 1
    bad = 0
    for i, block in enumerate(blocks):
        lines = [l[4:] if l.startswith("//! ") else "" for l in block.splitlines()]
        expect = None
        code_lines = []
        for l in lines:
            m = re.match(r"# // expect: (.*)", l)
            if m:
                expect = m.group(1).strip()
                continue
            code_lines.append(l[2:] if l.startswith("# ") else ("" if l == "#" else l))
        code = "\n".join(code_lines)
        if "fn main" not in code:
            code += "\nfn main() {}\n"
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "t.rs")
            with open(path, "w", encoding="utf-8") as f:
                f.write(code)
            cmd = ["rustc", "--edition", "2024", "--crate-type", "bin",
                   "-o", os.path.join(d, "o"), "-L", deps]
            for name, lib in externs.items():
                cmd += ["--extern", f"{name}={lib}"]
            r = subprocess.run(cmd + [path], capture_output=True, text=True, check=False)
        errors = [l for l in r.stderr.splitlines() if l.startswith("error")]
        errors = [e for e in errors if not any(f in e for f in FOLLOW_UPS)]
        if expect is not None:
            ours = [e for e in errors if expect in e]
            others = [e for e in errors if expect not in e]
        else:
            ours = [e for e in errors if any(m in e for m in LINT_MARKERS)]
            others = [e for e in errors if e not in ours]
        if r.returncode == 0 or not ours or others:
            bad += 1
            print(f"BAD example {i} (expect={expect!r}): matched={ours} other={others}")
        else:
            print(f"ok  example {i}: {ours[0]}")
    print(f"{len(blocks) - bad}/{len(blocks)} rejected for the intended reason")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
