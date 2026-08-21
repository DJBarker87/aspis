use super::indexed_dot16;
use aspis_core::field::{qm31_m31_dot4_prepared_limbs_4b_bytes, P};

fn arbitrary_m31_limb() -> u32 {
    kani::any::<u32>() & P
}

fn arbitrary_weight_limbs() -> [[u32; 4]; 16] {
    [
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
        [
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
            arbitrary_m31_limb(),
        ],
    ]
}

fn word_is_canonical(bytes: &[u8; 256], word: usize) -> bool {
    let offset = word * 4;
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ]) < P
}

macro_rules! all_words_canonical {
    ($bytes:expr; $($word:expr),+ $(,)?) => {
        true $(&& word_is_canonical($bytes, $word))+
    };
}

fn every_word_is_canonical(bytes: &[u8; 256]) -> bool {
    all_words_canonical!(
        bytes;
        0, 1, 2, 3, 4, 5, 6, 7,
        8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23,
        24, 25, 26, 27, 28, 29, 30, 31,
        32, 33, 34, 35, 36, 37, 38, 39,
        40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55,
        56, 57, 58, 59, 60, 61, 62, 63,
    )
}

/// Full result equality for all 64 prepared M31 limbs and all 256 input bytes.
#[kani::proof]
#[kani::unwind(5)]
fn production_dot16_equals_indexed_dot16() {
    let weight_limbs = arbitrary_weight_limbs();
    let bytes: [u8; 256] = kani::any();
    let production = qm31_m31_dot4_prepared_limbs_4b_bytes::<16>(&weight_limbs, &bytes);
    let indexed = indexed_dot16(&weight_limbs, &bytes);
    let equal = match (production, indexed) {
        (Some(production), Some(indexed)) => {
            production[0] == indexed[0]
                && production[1] == indexed[1]
                && production[2] == indexed[2]
                && production[3] == indexed[3]
        }
        (None, None) => true,
        _ => false,
    };
    assert!(equal);
}

/// Independently checks all production safety properties, exact acceptance,
/// and completeness of every loop unwind used by the equality proof.
#[kani::proof]
#[kani::unwind(5)]
fn production_dot16_acceptance_safety_and_unwind() {
    let weight_limbs = arbitrary_weight_limbs();
    let bytes: [u8; 256] = kani::any();
    let production = qm31_m31_dot4_prepared_limbs_4b_bytes::<16>(&weight_limbs, &bytes);
    assert_eq!(production.is_some(), every_word_is_canonical(&bytes));
}

/// Independently checks all reference safety properties, exact acceptance,
/// and completeness of every loop unwind used by the equality proof.
#[kani::proof]
#[kani::unwind(5)]
fn indexed_dot16_acceptance_safety_and_unwind() {
    let weight_limbs = arbitrary_weight_limbs();
    let bytes: [u8; 256] = kani::any();
    let indexed = indexed_dot16(&weight_limbs, &bytes);
    assert_eq!(indexed.is_some(), every_word_is_canonical(&bytes));
}
