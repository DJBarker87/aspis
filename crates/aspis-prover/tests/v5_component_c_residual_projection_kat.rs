//! Frozen-instance KAT for the v5 capstone's residual projections.
//!
//! This uses the current deterministic salted + affine-B-pivot CU fixture. It
//! pins one exact q18 schedule, roots, transcript state, prefix bytes, opened
//! records, and emitted E-matrix artifact. On that one instance it checks that
//! the atomic-v3 inactive functional and the 76-row Component-C `E` map of the
//! real pre-C word are deterministic projections of the released A/H/B bytes.
//! Component C's own `E(c)` remains separate and enters the full nineteen-lane
//! word only with `gamma^18`.
//!
//! This does not establish Rust-to-Lean correspondence, a universal schedule
//! theorem, same-statement coupling, sampler uniformity, or deployed ZK. The
//! full tag-67 proof body is assembled by private xtask functions in a crate
//! which `aspis-prover` does not depend on. Consequently this test pins the
//! externally reported full-proof hash but can recompute only the proof
//! surfaces exposed by `V5RealHostArtifact`.

#![cfg(feature = "v5-mask")]

use std::{fs, io::ErrorKind, path::PathBuf};

use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::sumcheck::WeightAccumulator;
use aspis_prover::circle_candidate::CircleEncoder;
use aspis_prover::v5_mask::component_c::{
    v5_c_dot, v5_c_inactive_functional, V5ComponentCLane, V5_C_ROWS,
};
use aspis_prover::v5_mask::component_c_emat::{
    evaluate_component_c_e_reference, validate_component_c_emat_artifact, V5ComponentCEmat,
    V5ComponentCFrozenESchedule, V5_C_EMAT_LAYER_ZERO_ROWS, V5_C_EMAT_QM31_BYTES, V5_C_EMAT_ROWS,
};
use aspis_prover::v5_mask::real_host_proof::{
    build_v5_real_host_artifact, V5HostPcsSalts, V5HostPowBits, V5PublicFsSalts,
    V5RealHostArtifact, V5RealHostInputs, V5_PUBLIC_FS_SALT_BYTES, V5_REAL_PREFIX_C1_ROOT_OFFSET,
    V5_REAL_PREFIX_C2_ROOT_OFFSET, V5_REAL_PREFIX_CLAIMS_OFFSET,
    V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET, V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET,
    V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET, V5_REAL_PREFIX_RESERVE_OFFSET,
    V5_REAL_PREFIX_SUMCHECK_OFFSET,
};
use aspis_prover::v5_mask::spend_messages::{
    gamma_combine_v5_messages, verify_v5_pcs_openings, VerifiedV5PcsOpenings, V5_C1_LANES,
    V5_COMPONENT_B_LANE, V5_COMPONENT_C_LANE, V5_FIBRE_SLOTS, V5_LATER_LAYERS,
    V5_LAYER_ZERO_LEAVES, V5_PRIVATE_DEPTHS, V5_TOTAL_LANES,
};
use aspis_prover::v5_mask::{
    sample_atomic_m31_lane_masks, Qm31WordSource, V5_DOMAIN_LOG, V5_TRACE_ROWS,
};
use aspis_prover::v5_sumcheck_mask::V5SumcheckMask;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
};
use sha2::{Digest as _, Sha256};

const PRE_C_LANES: usize = V5_C1_LANES + V5_COMPONENT_C_LANE;
const TRACE_LOG: u32 = V5_TRACE_ROWS.trailing_zeros();

const _: () = assert!(PRE_C_LANES + 1 == V5_TOTAL_LANES);
const _: () = assert!(V5_C_ROWS == V5_TRACE_ROWS);
const _: () = assert!(V5_C_EMAT_LAYER_ZERO_ROWS % V5_FIBRE_SLOTS == 0);

const EXPECTED_QUERIES: [u32; 18] = [
    115_997, 51_779, 92_617, 43_401, 78_758, 66_857, 81_115, 39_787, 112_113, 76_348, 73_402,
    59_549, 82_876, 101_923, 86_422, 120_558, 124_241, 68_942,
];
const EXPECTED_STATEMENT_DIGEST: &str =
    "f69ef3bc5428475f13889be77a5d0a9be24b9d78d18d93177b3721fc51f76471";
const EXPECTED_POST_QUERY_STATE: &str =
    "4fa9b07a975ee905c51562986b7ffdc4b0a72453d2bb2e957e81b30b768436fa";
const EXPECTED_ROOTS: [&str; 5] = [
    "a63bc60bb1008fccd407cdf6af34ad9299e787e8b1980fc82f65daa024e24243",
    "40bb5692f2445b63fda92165c9addda6ca6f2255e56807914831bda886251825",
    "840406f9ef6c451f51e41ca947c4f7ea43ef701914caa5d7188b68f24a91f889",
    "54a22d391084b009c91c7ee313cb8df3b8fd438c707bd14a7c68450b3c87d200",
    "320dd66a424c12c9c05a7ae7f62adc8f69e8201967c6623fd7e31a6a89b03017",
];
const EXPECTED_SCHEDULE_SHA256: &str =
    "24dd37c9ae99a5fb185a81ba2a88d50d63f211e81fcc0a1099728bf72e046e9f";
const EXPECTED_EMAT_SHA256: &str =
    "8fa7c5b0e009f59ec348cf09e5d5e788ca52d048ce9885fba674f13e3efc7e74";
const EXPECTED_EMAT_MATRIX_SHA256: &str =
    "76178865f6b34fd94507e70d336b2b409bf8f7758cb445958a1486e17f9a7d6d";
const EXTERNALLY_REPORTED_FULL_PROOF_SHA256: &str =
    "e6f63ab864fd85b3b781c226223a317072e3005a0561e8deb0717cc3f3650f34";

// Filled from artifact-exposed bytes and pinned below. They are intentionally
// distinct from the externally assembled full tag-67 proof body.
const EXPECTED_PREFIX_SHA256: &str =
    "a73b4f0518c4f0d5d8d85f3999a0ef2bf7eb9b19d00b27641eea4860a2a55783";
const EXPECTED_SUMCHECK_PROOF_SHA256: &str =
    "b17c2defa43451cdde78e0e42a1858de89466ff4c9abb73b3e68298b7db91060";
const EXPECTED_OPENINGS_SHA256: &str =
    "a8c7ab923d2c288f34c33fb8d6b7f822bed900a91f44f7028cc6372cd7408463";

fn hex(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        use core::fmt::Write as _;
        write!(&mut output, "{byte:02x}").unwrap();
    }
    output
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn results_path(file: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../results/spend")
        .join(file)
}

struct FixtureRng(u64);

impl Qm31WordSource for FixtureRng {
    fn next_word(&mut self) -> u32 {
        let mut value = self.0;
        value ^= value << 13;
        value ^= value >> 7;
        value ^= value << 17;
        self.0 = value;
        (value >> 21) as u32 % P
    }
}

fn q(seed: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
        c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
    }
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn statement_and_witness() -> (AtomicPaymentStatementV4, SpendWitness) {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
        index: 0x5_a5a5,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let statement = AtomicPaymentStatementV4 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
        deployment_domain: [0x5d; 32],
    };
    (statement, witness)
}

fn hcopy_padding() -> [QM31; V5_TRACE_ROWS] {
    let mut active = [false; V5_TRACE_ROWS];
    for &row in atomic_state_only_copy_active_rows_v3() {
        active[usize::from(row)] = true;
    }
    let pivot = (0..V5_TRACE_ROWS).find(|row| !active[*row]).unwrap();
    let mut padding = [QM31::ZERO; V5_TRACE_ROWS];
    let mut sum = QM31::ZERO;
    for row in 0..V5_TRACE_ROWS {
        if !active[row] && row != pivot {
            padding[row] = q(10_000 + row as u32);
            sum = sum.add(padding[row]);
        }
    }
    padding[pivot] = sum.neg();
    padding
}

fn private_salts(seed: u64, count: usize) -> Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]> {
    let mut state = seed;
    (0..count)
        .map(|_| {
            core::array::from_fn(|_| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                (state >> 27) as u8
            })
        })
        .collect()
}

fn public_fs_salts() -> V5PublicFsSalts {
    V5PublicFsSalts {
        c1: [0xa1; V5_PUBLIC_FS_SALT_BYTES],
        c2: [0xa2; V5_PUBLIC_FS_SALT_BYTES],
        later: [
            [0xb1; V5_PUBLIC_FS_SALT_BYTES],
            [0xb2; V5_PUBLIC_FS_SALT_BYTES],
            [0xb3; V5_PUBLIC_FS_SALT_BYTES],
        ],
    }
}

fn current_salted_p_fixture() -> (
    AtomicPaymentStatementV4,
    V5RealHostArtifact,
    V5ComponentCLane,
) {
    let (statement, witness) = statement_and_witness();
    let mut a_sources: [FixtureRng; V5_C1_LANES] =
        core::array::from_fn(|lane| FixtureRng(0xa531_0000_0000_0001 ^ lane as u64));
    let component_a = sample_atomic_m31_lane_masks(&mut a_sources).unwrap();
    let hcopy_padding = hcopy_padding();
    let sumcheck_mask = V5SumcheckMask::sample(&mut FixtureRng(0xb500_0000_0000_0001)).unwrap();
    let component_b_pads = core::array::from_fn(|index| q(20_000 + index as u32));
    let component_c = V5ComponentCLane::sample(&mut FixtureRng(0xc500_0000_0000_0001)).unwrap();
    let c1_salts = private_salts(0xc1, V5_LAYER_ZERO_LEAVES);
    let c2_salts = private_salts(0xc2, V5_LAYER_ZERO_LEAVES);
    let later_salts: [Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>; V5_LATER_LAYERS] =
        core::array::from_fn(|round| {
            private_salts(0xd1 + round as u64, 1usize << V5_PRIVATE_DEPTHS[round + 2])
        });

    let artifact = build_v5_real_host_artifact(V5RealHostInputs {
        statement: &statement,
        witness: &witness,
        component_a: &component_a,
        hcopy_padding: &hcopy_padding,
        sumcheck_mask: &sumcheck_mask,
        component_b_pads: &component_b_pads,
        component_b_pivot_pad: q(29_999),
        component_c: &component_c,
        salts: V5HostPcsSalts {
            c1: &c1_salts,
            c2: &c2_salts,
            later: [&later_salts[0], &later_salts[1], &later_salts[2]],
        },
        public_fs_salts: public_fs_salts(),
        hash: aspis_prover::HOST_HASH,
        pow_bits: V5HostPowBits::CU_ZERO,
    })
    .unwrap();
    (statement, artifact, component_c)
}

/// The already released A/H/B coordinates consumed by the v3 residual
/// projection. The B initial claim and ten round messages are retained so the
/// structure is the complete released B view, although these deterministic
/// projections need only its 76 independent residual coordinates.
#[derive(Clone)]
struct ReleasedAhbOuterView {
    b_initial_claim: QM31,
    b_round_messages: Vec<u8>,
    published_inactive: QM31,
    lane_e: [[QM31; V5_C_EMAT_ROWS]; PRE_C_LANES],
}

type PrefixClaims = [[QM31; V5_TOTAL_LANES]; 4];

fn decode_qm31(bytes: &[u8]) -> QM31 {
    QM31::from_le_bytes(bytes).expect("canonical frozen-fixture QM31 bytes")
}

fn prefix_claim_offset(claim: usize, lane: usize) -> usize {
    V5_REAL_PREFIX_CLAIMS_OFFSET + (claim * V5_TOTAL_LANES + lane) * 16
}

fn decode_prefix_claims(prefix: &[u8]) -> PrefixClaims {
    core::array::from_fn(|claim| {
        core::array::from_fn(|lane| {
            let start = prefix_claim_offset(claim, lane);
            decode_qm31(&prefix[start..start + 16])
        })
    })
}

fn write_prefix_qm31(prefix: &mut [u8], offset: usize, value: QM31) {
    value.write_le_bytes(&mut prefix[offset..offset + 16]);
}

fn released_lane_e(
    openings: &VerifiedV5PcsOpenings<'_>,
    schedule: &V5ComponentCFrozenESchedule,
    claims: &PrefixClaims,
    lane: usize,
) -> [QM31; V5_C_EMAT_ROWS] {
    assert_eq!(openings.indices.layer0, schedule.layer0_fibres);
    let mut output = [QM31::ZERO; V5_C_EMAT_ROWS];
    for fibre_ordinal in 0..schedule.layer0_fibres.len() {
        let c1_record = openings.c1.value(fibre_ordinal).unwrap();
        let c2_record = openings.c2.value(fibre_ordinal).unwrap();
        for slot in 0..V5_FIBRE_SLOTS {
            let row = V5_FIBRE_SLOTS * fibre_ordinal + slot;
            output[row] = if lane < V5_C1_LANES {
                let start = (slot * V5_C1_LANES + lane) * 4;
                let value = M31::from_le_bytes(c1_record[start..start + 4].try_into().unwrap())
                    .expect("canonical opened M31");
                QM31::from_cm31(CM31::from_m31(value))
            } else {
                let helper = lane - V5_C1_LANES;
                let start = (helper * V5_FIBRE_SLOTS + slot) * 16;
                decode_qm31(&c2_record[start..start + 16])
            };
        }
    }
    for claim in 0..4 {
        output[V5_C_EMAT_LAYER_ZERO_ROWS + claim] = claims[claim][lane];
    }
    output
}

fn released_outer_view(
    prefix: &[u8],
    openings: &VerifiedV5PcsOpenings<'_>,
    schedule: &V5ComponentCFrozenESchedule,
) -> ReleasedAhbOuterView {
    let claims = decode_prefix_claims(prefix);
    let published_inactive = QM31::from_le_bytes(
        &prefix[V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET..V5_REAL_PREFIX_RESERVE_OFFSET],
    )
    .unwrap();
    ReleasedAhbOuterView {
        b_initial_claim: decode_qm31(
            &prefix[V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET..V5_REAL_PREFIX_SUMCHECK_OFFSET],
        ),
        b_round_messages: prefix[V5_REAL_PREFIX_SUMCHECK_OFFSET..V5_REAL_PREFIX_CLAIMS_OFFSET]
            .to_vec(),
        published_inactive,
        lane_e: core::array::from_fn(|lane| released_lane_e(openings, schedule, &claims, lane)),
    }
}

fn project_pre_c_e(view: &ReleasedAhbOuterView, gamma: QM31) -> [QM31; V5_C_EMAT_ROWS] {
    let powers = qm31_power_table::<V5_TOTAL_LANES>(gamma);
    core::array::from_fn(|row| {
        (0..PRE_C_LANES).fold(QM31::ZERO, |sum, lane| {
            sum.add(powers[lane].mul(view.lane_e[lane][row]))
        })
    })
}

fn evaluate_word_e(
    word: &[QM31; V5_TRACE_ROWS],
    schedule: &V5ComponentCFrozenESchedule,
) -> [QM31; V5_C_EMAT_ROWS] {
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    let codeword = encoder.encode_c2_message(word).unwrap();
    let mut output = [QM31::ZERO; V5_C_EMAT_ROWS];
    for (fibre_ordinal, fibre) in schedule.layer0_fibres.iter().copied().enumerate() {
        for slot in 0..V5_FIBRE_SLOTS {
            output[V5_FIBRE_SLOTS * fibre_ordinal + slot] =
                codeword[V5_FIBRE_SLOTS * fibre as usize + slot];
        }
    }
    for (point_index, point) in schedule.points.iter().enumerate() {
        let mut evaluator = WeightAccumulator::empty(TRACE_LOG);
        evaluator
            .add_multilinear(QM31::ONE, point.to_vec())
            .unwrap();
        output[V5_C_EMAT_LAYER_ZERO_ROWS + point_index] = evaluator.dot(word);
    }
    output[V5_C_EMAT_ROWS - 1] = v5_c_dot(word, &schedule.terminal_covector);
    output
}

fn load_frozen_emat(schedule: &V5ComponentCFrozenESchedule) -> (V5ComponentCEmat, Vec<u8>) {
    let path = results_path("v5_component_c_frozen_q18_emat.bin");
    // Keep the 1.2 MiB derived matrix out of git. A clean checkout regenerates
    // the exact bytes in memory and immediately checks their frozen hash.
    let bytes = match fs::read(&path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == ErrorKind::NotFound => V5ComponentCEmat::generate(schedule)
            .unwrap()
            .encode_artifact(schedule),
        Err(error) => panic!(
            "read generated frozen Emat {}: {error}; regenerate with NO_DNA=1 cargo run --bin aspis-xtask -p aspis-xtask --release -- v5-component-c-emat",
            path.display()
        ),
    };
    assert_eq!(sha256_hex(&bytes), EXPECTED_EMAT_SHA256);
    let view = validate_component_c_emat_artifact(&bytes).unwrap();
    assert_eq!(hex(&view.schedule_sha256), EXPECTED_SCHEDULE_SHA256);
    assert_eq!(view.schedule_sha256, schedule.sha256());
    assert_eq!(hex(&view.matrix_sha256), EXPECTED_EMAT_MATRIX_SHA256);
    let entries = view
        .matrix_bytes
        .chunks_exact(V5_C_EMAT_QM31_BYTES)
        .map(decode_qm31)
        .collect::<Vec<_>>();
    (V5ComponentCEmat::from_entries(entries).unwrap(), bytes)
}

fn pin_external_full_proof_report() {
    // The complete account-body assembler is private to xtask and depends on
    // aspis-verifier, while this crate deliberately has no verifier
    // dependency. This checks the separately emitted report, not the proof
    // bytes themselves; the hash is therefore an explicit external boundary.
    let path = results_path("v5_full_transaction_cu_probe.json");
    let bytes = fs::read(&path).unwrap_or_else(|error| {
        panic!(
            "read generated full-CU report {}: {error}; regenerate with NO_DNA=1 cargo run --bin aspis-xtask -p aspis-xtask --release -- v5-cu-probe",
            path.display()
        )
    });
    let report: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(
        report["proof_body_sha256"].as_str(),
        Some(EXTERNALLY_REPORTED_FULL_PROOF_SHA256)
    );
    let reported_queries = report["query_indices"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value.as_u64().unwrap() as u32)
        .collect::<Vec<_>>();
    assert_eq!(reported_queries, EXPECTED_QUERIES);
    assert_eq!(report["accepted_three_of_three"].as_bool(), Some(true));
}

#[test]
#[ignore = "expensive current salted+p real-host fixture and full C2 encoder KAT"]
fn current_salted_p_pre_c_residuals_are_exact_released_view_projections() {
    let (_statement, artifact, component_c) = current_salted_p_fixture();
    let schedule = V5ComponentCFrozenESchedule::from_real_host_artifact(&artifact).unwrap();
    let prefix = artifact.encode_real_prefix();
    let openings = verify_v5_pcs_openings(
        aspis_prover::HOST_HASH,
        &artifact.roots,
        &artifact.queries,
        &artifact.openings.bytes,
    )
    .unwrap();

    // Exact frozen-instance pins. The raw q18 order is transcript order; the
    // opening parser independently derives its sorted fibre order.
    assert_eq!(artifact.queries, EXPECTED_QUERIES);
    assert_eq!(hex(&artifact.statement_digest), EXPECTED_STATEMENT_DIGEST);
    assert_eq!(
        hex(&artifact.transcript_state_after_queries),
        EXPECTED_POST_QUERY_STATE
    );
    let roots = [
        artifact.roots.c1,
        artifact.roots.c2,
        artifact.roots.later[0],
        artifact.roots.later[1],
        artifact.roots.later[2],
    ];
    for (root, expected) in roots.iter().zip(EXPECTED_ROOTS) {
        assert_eq!(hex(root), expected);
    }
    assert_eq!(hex(&schedule.sha256()), EXPECTED_SCHEDULE_SHA256);
    assert_eq!(
        &prefix[V5_REAL_PREFIX_C1_ROOT_OFFSET..V5_REAL_PREFIX_C2_ROOT_OFFSET],
        &artifact.roots.c1
    );
    assert_eq!(
        &prefix[V5_REAL_PREFIX_C2_ROOT_OFFSET..V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET],
        &artifact.roots.c2
    );
    let expected_public_salts = public_fs_salts();
    for section in 0..5 {
        let start = V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET + section * V5_PUBLIC_FS_SALT_BYTES;
        assert_eq!(
            &prefix[start..start + V5_PUBLIC_FS_SALT_BYTES],
            expected_public_salts.section(section)
        );
    }

    let prefix_sha = sha256_hex(&prefix);
    let sumcheck_sha = sha256_hex(&artifact.semantic_sumcheck.proof);
    let openings_sha = sha256_hex(&artifact.openings.bytes);
    eprintln!(
        "frozen artifact hashes: prefix={prefix_sha} sumcheck={sumcheck_sha} openings={openings_sha}"
    );
    assert_eq!(prefix_sha, EXPECTED_PREFIX_SHA256);
    assert_eq!(sumcheck_sha, EXPECTED_SUMCHECK_PROOF_SHA256);
    assert_eq!(openings_sha, EXPECTED_OPENINGS_SHA256);
    pin_external_full_proof_report();

    // From here on, the released claim table is decoded only from prefix
    // bytes, and the 72 raw E rows are decoded only from authenticated opening
    // records. The artifact-internal relation_claims table is not an input.
    let outer = released_outer_view(&prefix, &openings, &schedule);
    assert_eq!(outer.b_initial_claim, artifact.semantic_initial_claim);
    assert_eq!(outer.b_round_messages, artifact.semantic_sumcheck.proof);

    let gamma = artifact.challenges.gamma;
    let b_word: [QM31; V5_TRACE_ROWS] = artifact.layer_zero.c2.messages[V5_COMPONENT_B_LANE]
        .clone()
        .try_into()
        .unwrap();
    assert_eq!(
        v5_c_inactive_functional(&b_word),
        q(29_999),
        "the frozen affine-B pivot p changed"
    );

    let mut pre_c_messages = artifact.layer_zero.messages();
    pre_c_messages.c2[V5_COMPONENT_C_LANE].fill(QM31::ZERO);
    let pre_c_word: [QM31; V5_TRACE_ROWS] = gamma_combine_v5_messages(&pre_c_messages, gamma)
        .unwrap()
        .try_into()
        .unwrap();

    // First projection: the exact serialized inactive claim is ell(preC).
    // Component C contributes zero to this functional by construction.
    assert_eq!(v5_c_inactive_functional(component_c.values()), QM31::ZERO);
    assert_eq!(
        v5_c_inactive_functional(&pre_c_word),
        outer.published_inactive
    );

    // Second projection: gamma-combining the 18 released per-lane E views is
    // exactly the deployed encoder/relation evaluation of the pre-C word.
    let projected_pre_c_e = project_pre_c_e(&outer, gamma);
    let direct_pre_c_e = evaluate_word_e(&pre_c_word, &schedule);
    assert_eq!(projected_pre_c_e, direct_pre_c_e);

    // C's released E coordinate is separately bound to the real C2 encoder
    // and the Emat reference evaluator. It is not an input to either pre-C
    // projection. Only the full nineteen-lane word adds gamma^18 * E(c).
    let c_lane = V5_C1_LANES + V5_COMPONENT_C_LANE;
    let prefix_claims = decode_prefix_claims(&prefix);
    let released_c_e = released_lane_e(&openings, &schedule, &prefix_claims, c_lane);
    let (frozen_emat, emat_bytes) = load_frozen_emat(&schedule);
    let matrix_c_e = frozen_emat.mul_vec(&component_c.free_coordinates());
    assert_eq!(released_c_e, matrix_c_e);

    // Retain the original encoder self-consistency check, but do not confuse
    // it with the independent frozen-binary comparison above.
    let reference_c_e =
        evaluate_component_c_e_reference(&schedule, &component_c.free_coordinates()).unwrap();
    assert_eq!(released_c_e, reference_c_e);
    assert!(released_c_e.iter().any(|value| *value != QM31::ZERO));

    let full_word: [QM31; V5_TRACE_ROWS] =
        gamma_combine_v5_messages(&artifact.layer_zero.messages(), gamma)
            .unwrap()
            .try_into()
            .unwrap();
    let direct_full_e = evaluate_word_e(&full_word, &schedule);
    let gamma18 = qm31_power_table::<V5_TOTAL_LANES>(gamma)[c_lane];
    let recomposed_full_e =
        core::array::from_fn(|row| direct_pre_c_e[row].add(gamma18.mul(released_c_e[row])));
    assert_eq!(direct_full_e, recomposed_full_e);

    // Teeth: corrupting either deterministic projection is detected.
    let mut bad_inactive = outer.clone();
    bad_inactive.published_inactive = bad_inactive.published_inactive.add(QM31::ONE);
    assert_ne!(
        v5_c_inactive_functional(&pre_c_word),
        bad_inactive.published_inactive
    );

    let mut bad_e = outer.clone();
    bad_e.lane_e[0][0] = bad_e.lane_e[0][0].add(QM31::ONE);
    assert_ne!(project_pre_c_e(&bad_e, gamma), direct_pre_c_e);

    // Treating C's separately released coordinate as part of pre-C projects
    // the full word instead, and therefore fails the pre-C equality.
    assert_ne!(recomposed_full_e, direct_pre_c_e);

    // Byte-level lane/order tooth: swap two released prefix claim cells, then
    // decode the complete outer view again.
    let mut wrong_lane_prefix = prefix;
    let left_offset = prefix_claim_offset(0, 0);
    let right_offset = prefix_claim_offset(0, 1);
    let left: [u8; 16] = wrong_lane_prefix[left_offset..left_offset + 16]
        .try_into()
        .unwrap();
    let right: [u8; 16] = wrong_lane_prefix[right_offset..right_offset + 16]
        .try_into()
        .unwrap();
    wrong_lane_prefix[left_offset..left_offset + 16].copy_from_slice(&right);
    wrong_lane_prefix[right_offset..right_offset + 16].copy_from_slice(&left);
    let wrong_lane_outer = released_outer_view(&wrong_lane_prefix, &openings, &schedule);
    assert_ne!(project_pre_c_e(&wrong_lane_outer, gamma), direct_pre_c_e);

    // Byte-level terminal tooth: alter one terminal claim at its frozen
    // point-major prefix offset.
    let mut wrong_terminal_prefix = prefix;
    let terminal_offset = prefix_claim_offset(3, 0);
    let terminal = decode_qm31(&wrong_terminal_prefix[terminal_offset..terminal_offset + 16]);
    write_prefix_qm31(
        &mut wrong_terminal_prefix,
        terminal_offset,
        terminal.add(QM31::ONE),
    );
    let wrong_terminal_outer = released_outer_view(&wrong_terminal_prefix, &openings, &schedule);
    assert_ne!(
        project_pre_c_e(&wrong_terminal_outer, gamma),
        direct_pre_c_e
    );

    // Wrong gamma exponent: shifting every pre-C lane power by one does not
    // satisfy the frozen word equality.
    let wrong_gamma_projection = core::array::from_fn(|row| {
        (0..PRE_C_LANES).fold(QM31::ZERO, |sum, lane| {
            sum.add(gamma.pow((lane + 1) as u64).mul(outer.lane_e[lane][row]))
        })
    });
    assert_ne!(wrong_gamma_projection, direct_pre_c_e);

    // Wrong q18 order changes the canonical schedule fingerprint. Queries are
    // transcript-derived rather than serialized in the prefix, so this is the
    // strongest byte/spec tooth available at this crate boundary.
    let mut wrong_query_schedule = schedule.clone();
    wrong_query_schedule.queries.swap(0, 1);
    assert_ne!(wrong_query_schedule.queries, EXPECTED_QUERIES);
    assert_ne!(
        hex(&wrong_query_schedule.sha256()),
        EXPECTED_SCHEDULE_SHA256
    );

    // Wrong p: the prefix has no standalone p field. Its released binding at
    // this boundary is the combined inactive claim, so mutate that exact field
    // by gamma^17 while retaining the pinned C2 root.
    let mut wrong_p_prefix = prefix;
    let published_p = decode_qm31(
        &wrong_p_prefix[V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET..V5_REAL_PREFIX_RESERVE_OFFSET],
    );
    write_prefix_qm31(
        &mut wrong_p_prefix,
        V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET,
        published_p.add(gamma.pow(17)),
    );
    let wrong_p_outer = released_outer_view(&wrong_p_prefix, &openings, &schedule);
    assert_ne!(
        v5_c_inactive_functional(&pre_c_word),
        wrong_p_outer.published_inactive
    );
    assert_eq!(
        &wrong_p_prefix[V5_REAL_PREFIX_C2_ROOT_OFFSET..V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET],
        &artifact.roots.c2
    );

    // Wrong public salt/root/proof byte: every mutation breaks the frozen
    // prefix fingerprint. Replaying the transcript belongs to the verifier
    // crate and is not claimed here.
    for offset in [
        V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET,
        V5_REAL_PREFIX_C1_ROOT_OFFSET,
        V5_REAL_PREFIX_SUMCHECK_OFFSET,
    ] {
        let mut mutation = prefix;
        mutation[offset] ^= 1;
        assert_ne!(sha256_hex(&mutation), EXPECTED_PREFIX_SHA256);
    }

    // The emitted matrix artifact is hash-bound; row/order corruption is
    // rejected before any multiplication.
    let mut corrupt_emat = emat_bytes;
    *corrupt_emat.last_mut().unwrap() ^= 1;
    assert!(validate_component_c_emat_artifact(&corrupt_emat).is_err());
}
