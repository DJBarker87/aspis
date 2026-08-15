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
