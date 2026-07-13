//! Guards for the host-only zero-factor QM31 tail rank bridge.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix,
};
use aspis_prover::state_only_hiding_rank::probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral;
use aspis_prover::HOST_HASH;

const ACTUAL_PROFILE22_PROOF: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin"
));
const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn schedule() -> aspis_core::state_only_prefix::StateOnlyTranscriptScheduleResult {
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(ACTUAL_PROFILE22_PROOF).unwrap();
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &STATEMENT_DIGEST,
    )
    .unwrap()
}

#[test]
fn zero_factor_tail_pairing_is_pointwise_root_neutral() {
    let gamma = QM31::ONE
        .add(state_only_mask_tower_basis(1).mul_m31(M31(7)))
        .add(state_only_mask_tower_basis(2).mul_m31(M31(11)));
    let d = QM31::ONE
        .mul_m31(M31(13))
        .add(state_only_mask_tower_basis(3).mul_m31(M31(17)));
    let delta_g = QM31::ZERO.sub(gamma.mul(d));
    let gamma_27 = gamma.pow(27);
    let gamma_28 = gamma_27.mul(gamma);
    assert_eq!(gamma_27.mul(delta_g).add(gamma_28.mul(d)), QM31::ZERO);

    // One four-slot QM31 leaf contribution, q16 values, and three terminal
    // values.  Production H/G stay at 26/27; D is appended at 28.
    assert_eq!(4 * 16, 64);
    assert_eq!(16 * 4 * 16 + 3 * 16, 1_072);
}

#[test]
#[ignore = "slow exact three-schedule conditional root-neutral replay"]
fn zero_factor_qm31_tail_closes_only_the_frozen_control() {
    let frozen_schedule = schedule();
    let frozen =
        probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(&frozen_schedule)
            .unwrap();
    assert_eq!(frozen.production_h_generator_index, 26);
    assert_eq!(frozen.production_g_generator_index, 27);
    assert_eq!(frozen.tail_generator_index, 28);
    assert_eq!(frozen.tail_raw_rank_m31, 268);
    assert_eq!(frozen.h1_inactive_padding_raw_rank_m31, 268);
    assert_eq!(frozen.qm31_raw_target_m31, 268);
    assert_eq!(frozen.remaining_gd_query_rank_m31, 256);
    assert_eq!(frozen.remaining_gd_terminal_schur_rank_m31, 12);
    assert_eq!(frozen.remaining_gd_terminal_schur_z_degree, 120);
    assert_eq!(
        frozen.remaining_gd_terminal_schur_minor.fingerprint,
        0x0a2d_bf8f_1a90_59c0
    );
    assert_eq!(frozen.h1_inactive_padding_query_rank_m31, 256);
    assert_eq!(frozen.h1_inactive_padding_terminal_schur_rank_m31, 12);
    assert_eq!(frozen.h1_inactive_padding_terminal_schur_z_degree, 120);
    assert_eq!(
        frozen.h1_inactive_padding_terminal_schur_minor.fingerprint,
        0x5c61_aee3_83df_f271
    );
    assert_eq!(frozen.baseline_existing_rank_m31, 1072);
    assert_eq!(frozen.conditional_rank_m31, 1076);
    assert_eq!(frozen.conditional_target_m31, 1076);
    assert!(frozen.every_post_raw_source_terminal_zero);
    assert_eq!(frozen.terminal_zero_sources_checked_m31, 17_324);
    assert_eq!(frozen.conditional_minor.fingerprint, 0xcc3e_3f3f_eeac_0dbb);
    assert!(frozen.complete);

    let i = state_only_mask_tower_basis(1);
    let u = state_only_mask_tower_basis(2);
    let mut terminal_schedule = frozen_schedule;
    terminal_schedule.prefix.z.fill(QM31::ONE);
    terminal_schedule.prefix.z[6] = QM31::ZERO;
    terminal_schedule.prefix.z[8] = i;
    terminal_schedule.prefix.z[9] = u;
    let terminal =
        probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(&terminal_schedule)
            .unwrap();
    assert_eq!(terminal.baseline_existing_rank_m31, 748);
    assert_eq!(terminal.conditional_rank_m31, 786);
    assert_eq!(
        terminal.conditional_minor.fingerprint,
        0x42e4_e7e8_60fa_7ad0
    );
    assert!(!terminal.complete);

    let mut affine_schedule = terminal_schedule;
    let thirty_two = QM31::from_cm31(CM31::from_m31(M31(32)));
    affine_schedule.prefix.z[0] = QM31::ZERO.sub(thirty_two.add(i).mul_m31(M31(9).inv()));
    let affine =
        probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(&affine_schedule)
            .unwrap();
    assert_eq!(affine.baseline_existing_rank_m31, 900);
    assert_eq!(affine.conditional_rank_m31, 912);
    assert_eq!(affine.conditional_minor.fingerprint, 0xfe33_8a9a_49ff_661d);
    assert!(!affine.complete);
}
