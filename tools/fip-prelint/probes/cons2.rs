#![cfg_attr(fip_prelint, fip::export)]
#[cfg_attr(fip_prelint, fip::mark(fip, 1))]
pub fn g(x: u32) -> u32 { dep::marked(x) + dep::plain(x) }
