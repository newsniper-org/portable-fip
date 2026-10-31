# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
"""Check that every `compile_fail` doctest in fip-macros fails *because of the lint*.

rustdoc's `compile_fail` passes on any compilation error, so a typo in an example
would make a rejected case look covered. This script compiles each example with
rustc against the built proc-macro and requires that every error comes from
fip-macros.

Usage: python verify/compile_fail_reasons.py <path to libfip_macros-*.so>
"""

import os
import re
import subprocess
import sys
import tempfile

LINT_MARKERS = ("#[fip", "#[fbip", "FIP attributes", "`#[fbip]` takes")


def main() -> int:
    so = sys.argv[1]
    src = open("crates/fip-macros/src/lib.rs", encoding="utf-8").read()
    blocks = re.findall(r"//! ```compile_fail\n((?://! .*\n)+?)//! ```", src)
    if not blocks:
        print("no compile_fail examples found")
        return 1
    bad = 0
    for i, block in enumerate(blocks):
        code = "\n".join(
            line[4:] if line.startswith("//! ") else "" for line in block.splitlines()
        ).replace("# fn main", "fn main")
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "t.rs")
            with open(path, "w", encoding="utf-8") as f:
                f.write(code)
            r = subprocess.run(
                ["rustc", "--edition", "2024", "--crate-type", "bin",
                 "-o", os.path.join(d, "o"), "--extern", f"fip_macros={so}", path],
                capture_output=True, text=True, check=False,
            )
        errors = [l for l in r.stderr.splitlines()
                  if l.startswith("error") and "aborting" not in l]
        ours = [e for e in errors if any(m in e for m in LINT_MARKERS)]
        others = [e for e in errors if e not in ours]
        if r.returncode == 0 or not ours or others:
            bad += 1
            print(f"BAD example {i}: lint={ours} other={others}")
        else:
            print(f"ok  example {i}: {ours[0]}")
    print(f"{len(blocks) - bad}/{len(blocks)} rejected by the lint itself")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
