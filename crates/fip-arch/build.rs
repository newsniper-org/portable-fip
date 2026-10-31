// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Rejects unsupported `--cfg fip_cache_line="N"` values. A `cfg` predicate can only
//! test listed values, so an arbitrary value has to be caught here.

fn main() {
    println!("cargo::rerun-if-env-changed=CARGO_CFG_FIP_CACHE_LINE");
    if let Ok(v) = std::env::var("CARGO_CFG_FIP_CACHE_LINE") {
        // Cargo passes all values of a multi-valued cfg joined by ','.
        let vals: Vec<&str> = v.split(',').collect();
        assert!(
            vals.len() == 1 && ["32", "64", "128"].contains(&vals[0]),
            "fip_cache_line must be exactly one of \"32\", \"64\", \"128\"; got {v:?}"
        );
    }
}
