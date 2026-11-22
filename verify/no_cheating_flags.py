# SPDX-License-Identifier: MIT OR Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
"""Every Verus run of the justfile verifies with `--no-cheating` (the fork audit,
2026-11-09).

Usage: `no_cheating_flags.py <justfile>`; exits 1 with one line per violation.

Checked, on the justfile's text:
- `verus_flags` (the flags of every gate's Verus run) holds `--no-cheating`;
- every line running `{{verus}}` or `{{verus_upstream}}` (the binary followed by an
  argument starting with `-`, other than `--version`) passes `{{verus_flags}}` or
  `--no-cheating` on that line, unless the line ends with the comment
  `# negative probe` (a run that must be refused, e.g. the generator's refusal of a
  run without `--no-cheating`);
- no line outside a `# negative probe` line passes `--is-vstd`, `--is-core` or
  `--is-stdlib-outside-of-core` (verifying the crate as a standard-library crate);
- `verus_flags` holds `--edition 2024`, and so does every such line that does not pass
  `{{verus_flags}}` (2026-11-22): Verus's default edition is not the workspace's, so a
  run without the flag verifies the sources as written for another edition than cargo
  compiles them for.

Fails closed: a justfile without `verus_flags` or without any Verus run fails.
"""

import re
import sys

PROBE = "# negative probe"
RUN = re.compile(r"\{\{(verus|verus_upstream)\}\}(\s+(\S+))?")
STD_CRATE = re.compile(r"(^|\s)--is-(vstd|core|stdlib-outside-of-core)(\s|$)")
NO_CHEATING = re.compile(r"(^|\s)--no-cheating(\s|$)")
EDITION = re.compile(r"(^|\s)--edition 2024(\s|$)")


def check(text: str) -> list[str]:
    errors = []
    flags = re.search(r'^verus_flags := "(.*)"$', text, re.M)
    if flags is None:
        errors.append("justfile: no `verus_flags := \"..\"` line")
    elif "--no-cheating" not in flags.group(1).split():
        errors.append(f"justfile: verus_flags `{flags.group(1)}` lacks --no-cheating")
    elif not EDITION.search(flags.group(1)):
        errors.append(f"justfile: verus_flags `{flags.group(1)}` lacks --edition 2024")
    runs = 0
    for n, line in enumerate(text.splitlines(), 1):
        if line.strip().startswith("#"):
            continue
        probe = line.rstrip().endswith(PROBE)
        if STD_CRATE.search(line) and not probe:
            errors.append(f"justfile:{n}: a standard-library crate flag: {line.strip()}")
        for m in RUN.finditer(line):
            arg = m.group(3)
            if arg is None or not arg.startswith("-") or arg.startswith("--version"):
                continue
            runs += 1
            if probe:
                continue
            if "{{verus_flags}}" in line:
                continue
            if not NO_CHEATING.search(line):
                errors.append(f"justfile:{n}: Verus run without --no-cheating: {line.strip()}")
            elif not EDITION.search(line):
                errors.append(f"justfile:{n}: Verus run without --edition 2024: {line.strip()}")
    if runs == 0:
        errors.append("justfile: no Verus run found")
    return errors


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: no_cheating_flags.py <justfile>", file=sys.stderr)
        return 2
    with open(sys.argv[1], encoding="utf-8") as f:
        errors = check(f.read())
    for e in errors:
        print(f"FAIL: {e}")
    if errors:
        return 1
    print("no-cheating flags: every Verus run of the justfile uses --no-cheating")
    return 0


if __name__ == "__main__":
    sys.exit(main())
