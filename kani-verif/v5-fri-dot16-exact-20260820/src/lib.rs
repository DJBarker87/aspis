use aspis_core::field::{CM31, M31, P, QM31};

fn read_word(bytes: &[u8; 256], slot: usize, index: usize) -> (u64, u32) {
    let offset = (slot * 16 + index) * 4;
    let value = u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ]);
    (u64::from(value & P), u32::from(value >= P))
}

fn raw4(weight_limbs: &[[u32; 4]; 16], start: usize, values: [u64; 4], limb: usize) -> u64 {
    u64::from(weight_limbs[start][limb]) * values[0]
        + u64::from(weight_limbs[start + 1][limb]) * values[1]
        + u64::from(weight_limbs[start + 2][limb]) * values[2]
        + u64::from(weight_limbs[start + 3][limb]) * values[3]
}

fn block4(
    weight_limbs: &[[u32; 4]; 16],
    bytes: &[u8; 256],
    slot: usize,
    start: usize,
) -> ([u64; 4], u32) {
    let (v0, e0) = read_word(bytes, slot, start);
    let (v1, e1) = read_word(bytes, slot, start + 1);
    let (v2, e2) = read_word(bytes, slot, start + 2);
    let (v3, e3) = read_word(bytes, slot, start + 3);
    let values = [v0, v1, v2, v3];
    let raw = [
        raw4(weight_limbs, start, values, 0),
        raw4(weight_limbs, start, values, 1),
        raw4(weight_limbs, start, values, 2),
        raw4(weight_limbs, start, values, 3),
    ];
    (raw, e0 | e1 | e2 | e3)
}

fn reduce4(b0: [u64; 4], b1: [u64; 4], b2: [u64; 4], b3: [u64; 4], limb: usize) -> M31 {
    M31::reduce_u64(
        u64::from(M31::reduce_u64(b0[limb]).0)
            + u64::from(M31::reduce_u64(b1[limb]).0)
            + u64::from(M31::reduce_u64(b2[limb]).0)
            + u64::from(M31::reduce_u64(b3[limb]).0),
    )
}

fn slot_dot(weight_limbs: &[[u32; 4]; 16], bytes: &[u8; 256], slot: usize) -> (QM31, u32) {
    let (b0, e0) = block4(weight_limbs, bytes, slot, 0);
    let (b1, e1) = block4(weight_limbs, bytes, slot, 4);
    let (b2, e2) = block4(weight_limbs, bytes, slot, 8);
    let (b3, e3) = block4(weight_limbs, bytes, slot, 12);
    let value = QM31 {
        c0: CM31::new(reduce4(b0, b1, b2, b3, 0), reduce4(b0, b1, b2, b3, 1)),
        c1: CM31::new(reduce4(b0, b1, b2, b3, 2), reduce4(b0, b1, b2, b3, 3)),
    };
    (value, e0 | e1 | e2 | e3)
}

/// A fully fixed-index spelling of the exact `N = 16` production helper.
///
/// This function deliberately has no iterator or loop state. Charon/Aeneas
/// can translate it, while Kani proves that it has exactly the same result as
/// the unchanged iterator-based production function for every input in scope.
pub fn indexed_dot16(weight_limbs: &[[u32; 4]; 16], bytes: &[u8; 256]) -> Option<[QM31; 4]> {
    let (v0, e0) = slot_dot(weight_limbs, bytes, 0);
    let (v1, e1) = slot_dot(weight_limbs, bytes, 1);
    let (v2, e2) = slot_dot(weight_limbs, bytes, 2);
    let (v3, e3) = slot_dot(weight_limbs, bytes, 3);
    if e0 | e1 | e2 | e3 == 0 {
        Some([v0, v1, v2, v3])
    } else {
        None
    }
}

#[cfg(kani)]
mod proofs;
