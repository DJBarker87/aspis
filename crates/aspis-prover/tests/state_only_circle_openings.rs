use aspis_core::circle_line_merkle::{
    RATE16_CIRCLE_OPENING_GEOMETRY, RATE32_CIRCLE_OPENING_GEOMETRY, RATE512_CIRCLE_OPENING_GEOMETRY,
};
use aspis_core::circle_openings::verify_and_check_state_only_circle_openings_for_geometry;
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::state_only_query::{
    StateOnlyQueryPowers, STATE_ONLY_C1_COLUMNS, STATE_ONLY_C2_COLUMNS,
};
use aspis_prover::circle_candidate::{build_fold_commitments_for_domain_log, CircleEncoder};
use aspis_prover::circle_candidate_openings::serialize_candidate_openings_for_fiber_count_with_leaf_bytes;
use aspis_prover::state_only_candidate::{
    encode_state_only_c1_columns, encode_state_only_c2_columns, gamma_combine_state_only_codewords,
    gamma_combine_state_only_messages, state_only_c1_layer0_leaves, state_only_c2_layer0_leaves,
    state_only_layer0_roots,
};
use aspis_prover::HOST_HASH;

#[derive(Clone, Copy)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
        self.0
    }

    fn m31(&mut self) -> M31 {
        M31((self.next() % u64::from(P)) as u32)
    }

    fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m31(), self.m31()),
            c1: CM31::new(self.m31(), self.m31()),
        }
    }
}

fn roundtrip(domain_log: u32, query_count: usize) {
    let mut rng = Rng(0x5354_4154_4531_3800 ^ u64::from(domain_log));
    let c1_messages: Vec<Vec<M31>> = (0..STATE_ONLY_C1_COLUMNS)
        .map(|_| (0..1024).map(|_| rng.m31()).collect())
        .collect();
    let c2_messages: Vec<Vec<QM31>> = (0..STATE_ONLY_C2_COLUMNS)
        .map(|_| (0..1024).map(|_| rng.qm31()).collect())
        .collect();
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let c1 = encode_state_only_c1_columns(&encoder, &c1_messages).unwrap();
    let c2 = encode_state_only_c2_columns(&encoder, &c2_messages).unwrap();
    let codeword_len = 1usize << domain_log;
    let fiber_count = codeword_len / 4;
    let c1_leaves = state_only_c1_layer0_leaves(&c1, codeword_len).unwrap();
    let c2_leaves = state_only_c2_layer0_leaves(&c2, codeword_len).unwrap();
    let (c1_root, c2_root) = state_only_layer0_roots(&c1_leaves, &c2_leaves, HOST_HASH).unwrap();
    let gamma = rng.qm31();
    let alphas = core::array::from_fn(|_| rng.qm31());
    let combined_codeword =
        gamma_combine_state_only_codewords(&c1, &c2, gamma, codeword_len).unwrap();
    let combined_message =
        gamma_combine_state_only_messages(&c1_messages, &c2_messages, gamma).unwrap();
    let folds = build_fold_commitments_for_domain_log(
        &combined_codeword,
        &combined_message,
        alphas,
        domain_log,
        HOST_HASH,
    )
    .unwrap();
    let queries: Vec<u32> = (0..query_count)
        .map(|i| ((i * 277 + i * i * 19 + 11) % fiber_count) as u32)
        .collect();
    let suffix = serialize_candidate_openings_for_fiber_count_with_leaf_bytes(
        &queries,
        &c1_leaves,
        &c2_leaves,
        &folds,
        fiber_count,
        HOST_HASH,
    )
    .unwrap();
    let geometry = match domain_log {
        14 => RATE16_CIRCLE_OPENING_GEOMETRY,
        15 => RATE32_CIRCLE_OPENING_GEOMETRY,
        19 => RATE512_CIRCLE_OPENING_GEOMETRY,
        _ => panic!("unsupported state-only opening test domain log {domain_log}"),
    };
    let powers = StateOnlyQueryPowers::new(gamma);
    let verified = verify_and_check_state_only_circle_openings_for_geometry(
        HOST_HASH,
        &c1_root,
        &c2_root,
        &folds.roots,
        &queries,
        &suffix,
        &powers,
        alphas,
        folds.final_coefficients,
        geometry,
    )
    .unwrap();
    assert_eq!(verified.later.indices.layer0.len(), query_count);

    let mut bad = suffix.clone();
    bad[verified.layer0.offsets.c1_leaves] ^= 1;
    assert!(verify_and_check_state_only_circle_openings_for_geometry(
        HOST_HASH,
        &c1_root,
        &c2_root,
        &folds.roots,
        &queries,
        &bad,
        &powers,
        alphas,
        folds.final_coefficients,
        geometry,
    )
    .is_err());
}

#[test]
fn rate16_q36_width18_roundtrip() {
    roundtrip(14, 36);
}

#[test]
fn rate32_q29_width18_roundtrip() {
    roundtrip(15, 29);
}

#[test]
fn rate512_q16_width28_roundtrip() {
    roundtrip(19, 16);
}
