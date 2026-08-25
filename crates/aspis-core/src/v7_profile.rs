//! Frozen constants for the V7 Phase-1 split-tensor algebra profile.
//!
//! This is deliberately not a production wire profile.  It binds the field,
//! lane order, padding, and gamma restriction that the reference algebra and
//! formal proofs share.  Enabling a V7 verifier requires a later wire-profile
//! freeze and its own discriminator.

pub const ALGEBRA_PROFILE_REVISION: &str = "r0-phase1-algebra";
pub const ALGEBRA_PROFILE_MANIFEST: &str = "manifests/v7-split-tensor-profile-r0.json";
pub const ALGEBRA_PROFILE_MANIFEST_BYTES: usize = 1_548;
pub const ALGEBRA_PROFILE_SHA256_HEX: &str =
    "871fd1518b1548d7daca2a48e88ef97ec05a6f5390c959d0df8af4067c89bbe0";
pub const ALGEBRA_PROFILE_SHA256: [u8; 32] = [
    0x87, 0x1f, 0xd1, 0x51, 0x8b, 0x15, 0x48, 0xd7, 0xda, 0xca, 0x2a, 0x48, 0xe8, 0x8e, 0xf9, 0x7e,
    0xc0, 0x5a, 0x6f, 0x53, 0x90, 0xc9, 0x59, 0xd0, 0xdf, 0x8a, 0xf4, 0x06, 0x7c, 0x89, 0xbb, 0xe0,
];

pub const ROW_VARIABLES: usize = 10;
pub const ROW_COEFFICIENTS: usize = 1 << ROW_VARIABLES;
pub const STAGE_A_SOURCE_LANES: usize = 26;
pub const STAGE_A_LANE_VARIABLES: usize = 5;
pub const STAGE_A_PADDED_LANES: usize = 1 << STAGE_A_LANE_VARIABLES;
pub const STAGE_B_QM31_LANES: usize = 3;
pub const QM31_LIMBS: usize = 4;
pub const STAGE_B_SOURCE_LIMBS: usize = STAGE_B_QM31_LANES * QM31_LIMBS;
pub const STAGE_B_LANE_VARIABLES: usize = 4;
pub const STAGE_B_PADDED_LANES: usize = 1 << STAGE_B_LANE_VARIABLES;
pub const STAGE_B_OUTER_GAMMA_POWER: u64 = STAGE_A_SOURCE_LANES as u64;
pub const COMBINED_LANES: usize = STAGE_A_SOURCE_LANES + STAGE_B_QM31_LANES;
pub const V6_FINAL_COEFFICIENTS: usize = 256;

const _: () = assert!(ROW_COEFFICIENTS == 1_024);
const _: () = assert!(STAGE_A_PADDED_LANES == 32);
const _: () = assert!(STAGE_B_SOURCE_LIMBS == 12);
const _: () = assert!(STAGE_B_PADDED_LANES == 16);
const _: () = assert!(COMBINED_LANES == 29);
