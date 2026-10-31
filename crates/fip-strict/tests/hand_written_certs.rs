// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `fip_strict::certs` is the one place where certificates are made without
//! `Cert::assume`. Pins its exact contents: adding a certificate means updating this
//! list and justifying the entry in `src/lib.rs`.

#[test]
fn certificates_made_here_are_exactly_the_documented_ones() {
    let src = include_str!("../src/lib.rs");
    let mut made: Vec<&str> = src
        .lines()
        .filter(|l| l.contains("Cert { allocs:"))
        .filter_map(|l| {
            l.split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .find(|w| w.starts_with("__fip_strict_"))
        })
        .collect();
    made.sort_unstable();
    assert_eq!(
        made,
        [
            "__fip_strict_refill",
            "__fip_strict_replace",
            "__fip_strict_swap"
        ]
    );
    // `Self { allocs }` in `Cert::assume` is the only other construction site.
    assert_eq!(src.matches("Cert { allocs:").count(), 3);
    assert_eq!(src.matches("Self { allocs }").count(), 1);
}
