<!-- SPDX-License-Identifier: MIT OR Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Dual license: `MIT OR Apache-2.0`

**Status:** ACCEPTED, 2026-11-04.

## Decision

The project, previously `Apache-2.0` only, is licensed under `MIT OR Apache-2.0`
at the licensee's option (the Rust ecosystem convention).

- Every manifest that declares a license says `license = "MIT OR Apache-2.0"`
  (workspace `Cargo.toml`, inherited by the crates through `license.workspace`, and
  `tools/fip-prelint/Cargo.toml`; test fixtures and the std-summaries seed declare none).
- License texts: `LICENSE-APACHE` (the former `LICENSE`, unchanged) and `LICENSE-MIT`.
- Every SPDX header reads `SPDX-License-Identifier: MIT OR Apache-2.0`; headers stay
  one line, so line numbers in expected outputs do not move.
- `README.md` § License states the choice and the contribution clause: contributions
  intentionally submitted for inclusion are dual licensed as above, without any
  additional terms or conditions.

## Reason

Compatibility with MIT-licensed projects, notably Verus, so that code or proofs from
this repository can be contributed upstream without a license barrier.

The relicense needs no other consent: 윤병익 (BYUNG-IK YEUN) is the sole copyright
holder of all code in the repository.
