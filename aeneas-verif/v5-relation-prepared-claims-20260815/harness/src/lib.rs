#![allow(dead_code)]

// Compile the production files in a Solana-free harness so Charon can start
// from the prepared-claim function without translating the program entrypoint.
// The `#[path]` modules are the repository files themselves, not copied code.
#[path = "../../../../programs/aspis-verifier/src/v5_private_openings.rs"]
pub mod private_openings;

#[path = "../../../../programs/aspis-verifier/src/v5_fri_checks.rs"]
pub mod fri_checks;

/// Extraction root for the production QM31 addition used between the five
/// prepared-claim blocks.  The implementation is the production method
/// itself; this wrapper exists only because the pinned Charon version cannot
/// select an inherent method directly with `--start-from`.
pub fn extracted_qm31_add(
    left: aspis_core::field::QM31,
    right: aspis_core::field::QM31,
) -> aspis_core::field::QM31 {
    left.add(right)
}

/// Extraction roots for production field methods which the pinned Charon
/// cannot select directly because they are inherent methods.  These wrappers
/// add no arithmetic and are used only to retain the called production bodies
/// in the Rust-to-Lean field supplement.
pub fn extracted_prepared_qm31_new(
    value: aspis_core::field::QM31,
) -> aspis_core::field::PreparedQm31Multiplier {
    aspis_core::field::PreparedQm31Multiplier::new(value)
}

pub fn extracted_qm31_from_le_bytes(
    bytes: &[u8],
) -> Option<aspis_core::field::QM31> {
    aspis_core::field::QM31::from_le_bytes(bytes)
}

pub fn extracted_qm31_mul(
    left: aspis_core::field::QM31,
    right: aspis_core::field::QM31,
) -> aspis_core::field::QM31 {
    left.mul(right)
}

pub fn extracted_qm31_square(
    value: aspis_core::field::QM31,
) -> aspis_core::field::QM31 {
    value.square()
}

pub fn extracted_qm31_m31_dot4_prepared_limbs_4b_bytes<const N: usize>(
    weight_limbs: &[[u32; 4]; N],
    bytes: &[u8],
) -> Option<[aspis_core::field::QM31; 4]> {
    aspis_core::field::qm31_m31_dot4_prepared_limbs_4b_bytes(
        weight_limbs,
        bytes,
    )
}

pub fn extracted_qm31_m31_dot4_prepared_limbs_4b_bytes_16(
    weight_limbs: &[[u32; 4]; 16],
    bytes: &[u8],
) -> Option<[aspis_core::field::QM31; 4]> {
    aspis_core::field::qm31_m31_dot4_prepared_limbs_4b_bytes::<16>(
        weight_limbs,
        bytes,
    )
}
