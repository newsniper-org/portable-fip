/// Non-generic, not `#[inline]`, with a loop.
pub fn looped(x: u32) -> u32 {
    let mut s = 0u32;
    let mut i = 0u32;
    while i < x { s = s.wrapping_add(i.wrapping_mul(3)); i += 1; }
    s
}
/// Non-generic, not `#[inline]`, a tiny leaf.
pub fn leaf(x: u32) -> u32 { x + 1 }
/// Non-generic, not `#[inline]`, large (beyond the cross-crate inlining heuristic).
pub fn big(x: u32) -> u32 {
    let mut s = x;
    s = s.wrapping_mul(3).wrapping_add(x ^ 1);
    if s % 2 == 0 { s = s.rotate_left(1); }
    s = s.wrapping_mul(4).wrapping_add(x ^ 8);
    if s % 3 == 0 { s = s.rotate_left(2); }
    s = s.wrapping_mul(5).wrapping_add(x ^ 15);
    if s % 4 == 0 { s = s.rotate_left(3); }
    s = s.wrapping_mul(6).wrapping_add(x ^ 22);
    if s % 5 == 0 { s = s.rotate_left(4); }
    s = s.wrapping_mul(7).wrapping_add(x ^ 29);
    if s % 6 == 0 { s = s.rotate_left(5); }
    s = s.wrapping_mul(8).wrapping_add(x ^ 36);
    if s % 7 == 0 { s = s.rotate_left(6); }
    s = s.wrapping_mul(9).wrapping_add(x ^ 43);
    if s % 8 == 0 { s = s.rotate_left(7); }
    s = s.wrapping_mul(10).wrapping_add(x ^ 50);
    if s % 9 == 0 { s = s.rotate_left(8); }
    s = s.wrapping_mul(11).wrapping_add(x ^ 57);
    if s % 10 == 0 { s = s.rotate_left(9); }
    s = s.wrapping_mul(12).wrapping_add(x ^ 64);
    if s % 11 == 0 { s = s.rotate_left(10); }
    s = s.wrapping_mul(13).wrapping_add(x ^ 71);
    if s % 12 == 0 { s = s.rotate_left(11); }
    s = s.wrapping_mul(14).wrapping_add(x ^ 78);
    if s % 13 == 0 { s = s.rotate_left(12); }
    s = s.wrapping_mul(15).wrapping_add(x ^ 85);
    if s % 14 == 0 { s = s.rotate_left(13); }
    s = s.wrapping_mul(16).wrapping_add(x ^ 92);
    if s % 15 == 0 { s = s.rotate_left(14); }
    s = s.wrapping_mul(17).wrapping_add(x ^ 99);
    if s % 16 == 0 { s = s.rotate_left(15); }
    s = s.wrapping_mul(18).wrapping_add(x ^ 106);
    if s % 17 == 0 { s = s.rotate_left(16); }
    s = s.wrapping_mul(19).wrapping_add(x ^ 113);
    if s % 18 == 0 { s = s.rotate_left(17); }
    s = s.wrapping_mul(20).wrapping_add(x ^ 120);
    if s % 19 == 0 { s = s.rotate_left(18); }
    s = s.wrapping_mul(21).wrapping_add(x ^ 127);
    if s % 20 == 0 { s = s.rotate_left(19); }
    s = s.wrapping_mul(22).wrapping_add(x ^ 134);
    if s % 21 == 0 { s = s.rotate_left(20); }
    s = s.wrapping_mul(23).wrapping_add(x ^ 141);
    if s % 22 == 0 { s = s.rotate_left(21); }
    s = s.wrapping_mul(24).wrapping_add(x ^ 148);
    if s % 23 == 0 { s = s.rotate_left(22); }
    s = s.wrapping_mul(25).wrapping_add(x ^ 155);
    if s % 24 == 0 { s = s.rotate_left(23); }
    s = s.wrapping_mul(26).wrapping_add(x ^ 162);
    if s % 25 == 0 { s = s.rotate_left(24); }
    s = s.wrapping_mul(27).wrapping_add(x ^ 169);
    if s % 26 == 0 { s = s.rotate_left(25); }
    s = s.wrapping_mul(28).wrapping_add(x ^ 176);
    if s % 27 == 0 { s = s.rotate_left(26); }
    s = s.wrapping_mul(29).wrapping_add(x ^ 183);
    if s % 28 == 0 { s = s.rotate_left(27); }
    s = s.wrapping_mul(30).wrapping_add(x ^ 190);
    if s % 29 == 0 { s = s.rotate_left(28); }
    s = s.wrapping_mul(31).wrapping_add(x ^ 197);
    if s % 30 == 0 { s = s.rotate_left(29); }
    s = s.wrapping_mul(32).wrapping_add(x ^ 204);
    if s % 31 == 0 { s = s.rotate_left(30); }
    s = s.wrapping_mul(33).wrapping_add(x ^ 211);
    if s % 32 == 0 { s = s.rotate_left(31); }
    s = s.wrapping_mul(34).wrapping_add(x ^ 218);
    if s % 33 == 0 { s = s.rotate_left(1); }
    s = s.wrapping_mul(35).wrapping_add(x ^ 225);
    if s % 34 == 0 { s = s.rotate_left(2); }
    s = s.wrapping_mul(36).wrapping_add(x ^ 232);
    if s % 35 == 0 { s = s.rotate_left(3); }
    s = s.wrapping_mul(37).wrapping_add(x ^ 239);
    if s % 36 == 0 { s = s.rotate_left(4); }
    s = s.wrapping_mul(38).wrapping_add(x ^ 246);
    if s % 37 == 0 { s = s.rotate_left(5); }
    s = s.wrapping_mul(39).wrapping_add(x ^ 253);
    if s % 38 == 0 { s = s.rotate_left(6); }
    s = s.wrapping_mul(40).wrapping_add(x ^ 260);
    if s % 39 == 0 { s = s.rotate_left(7); }
    s = s.wrapping_mul(41).wrapping_add(x ^ 267);
    if s % 40 == 0 { s = s.rotate_left(8); }
    s = s.wrapping_mul(42).wrapping_add(x ^ 274);
    if s % 41 == 0 { s = s.rotate_left(9); }
    s
}
