//! Real-witness host proof material for the isolated v5 CU path.
//!
//! This is deliberately not a production proof grammar. It constructs every
//! algebraic and PCS value needed by the complete tag-67 CU transaction:
//! the atomic-v3 witness trace, split C1/C2 roots in Fiat--Shamir order, the
//! Component-B-masked semantic sumcheck, all `4 * 19` claims, the terminal
//! identity, one shared four-round relation, later roots, final polynomial,
//! transcript-derived q18 positions, and five real private opening sections.
//!
//! Component C remains provisional, so an artefact from this module is an
//! integration/measurement result only, not a security-approved proof.

use aspis_core::circle_fri::circle_fiber_point_for_domain_log;
use aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT;
use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineQueryIndices, CIRCLE_LINE_TAGS,
};
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::{qm31_power_table, CM31, M31, QM31};
use aspis_core::proof::M31_CIRCLE_BASIS_DISCRIMINATOR;
use aspis_core::state_only_hiding::begin_state_only_masked_sumcheck;
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_sumcheck::begin_state_only_zerocheck;
use aspis_core::sumcheck::{SumcheckPolynomial, SUMCHECK_COEFFICIENTS};
use aspis_core::transcript::{label, Transcript};
use aspis_core::HashFn;
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_row_masks_v3,
    atomic_state_only_selected_unmasked_terminal_value_compiled_v3,
};
use aspis_statement::{
    atomic_payment_statement_digest_v4, binary_successor_point, encode_atomic_payment_statement_v4,
    xor12_point, AtomicPaymentStatementV4, AtomicStatementError, SpendWitness,
    ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES,
};

use super::component_c::V5ComponentCLane;
use super::spend_messages::{
    gamma_combine_v5_messages, verify_v5_pcs_openings, V5BuiltPcsOpenings, V5PcsRoots,
    V5SpendMessageError, V5StructuredBLane, V5_B_PAD_COORDINATES, V5_C1_LANES, V5_C2_LANES,
    V5_LATER_LAYERS, V5_LAYER_ZERO_LEAVES, V5_PRIVATE_DEPTHS, V5_TOTAL_LANES,
};
use super::split_layer_zero::{
    build_and_commit_v5_c1, build_v5_relation_claims, finish_v5_split_layer_zero, V5RelationClaims,
    V5SplitLayerZero,
};
use super::{M31BlockMask, V5_CODEWORD_LEN, V5_DOMAIN_LOG, V5_TRACE_ROWS};
use crate::circle_candidate::{
    combined_layer_leaves, fold_candidate_codeword_round_for_domain_log, CircleCandidateError,
    COMBINED_LAYER_LEAF_BYTES,
};
use crate::state_only_private_openings::{
    build_state_only_private_merkle_tree, serialize_state_only_private_opening,
    StateOnlyPrivateMerkleTree, StateOnlyPrivateOpeningBuildError,
};
use crate::state_only_zerocheck::StateOnlyZerocheckTrace;
use crate::v5_mask::relation_prover::{
    V5IncrementalRelation, V5RelationProverError, V5RelationTrace,
};
use crate::v5_sumcheck_mask::{prove_v5_masked_state_only_zerocheck, V5SumcheckMask};

/// Historical transcript-domain bytes retained for host/verifier compatibility.
/// The `cu-v1` suffix is not the wire grammar version; `AV5PFX03` and the
/// explicit prefix version gate that grammar. Changing this literal forks the
/// Fiat--Shamir schedule and requires new proofs and artifacts.
pub const V5_REAL_HOST_TRANSCRIPT_DOMAIN: &[u8] = b"aspis-v5-real-witness-cu-v1";
pub const V5_REAL_HOST_QUERY_COUNT: usize = 18;
pub const V5_REAL_HOST_TERMINAL_CONTEXT_VALUES: usize = 3;
/// Maximum number of complete public GoodA/GoodB attempts before an honest
/// prover emits the explicit abort outcome.
pub const V5_REAL_HOST_GOOD_RETRY_CAP: u8 = 17;
/// The retry callback must derive each attempt from fresh public,
/// witness-independent transcript entropy. The host type cannot enforce that
/// cryptographic interface, so it remains an explicit deployment obligation.
pub const V5_REAL_HOST_GOOD_RETRY_FRESHNESS_OBLIGATION: &str =
    "each retry derives a fresh schedule triple from public witness-independent transcript entropy";

/// Exact real-transcript prefix consumed by the isolated tag-67 CU verifier
/// through the shared mode-9 kernel. This deliberately retains the existing
/// 6,423-byte account slot while replacing the old synthetic grammar with two
/// committed roots and the genuine masked semantic sumcheck.
pub const V5_REAL_PREFIX_MAGIC: [u8; 8] = *b"AV5PFX03";
pub const V5_REAL_PREFIX_VERSION: u8 = 3;
pub const V5_REAL_PREFIX_FLAGS: u8 = 0;
pub const V5_REAL_PREFIX_HEADER_BYTES: usize = 23;
pub const V5_REAL_PREFIX_C1_ROOT_OFFSET: usize = V5_REAL_PREFIX_HEADER_BYTES;
pub const V5_REAL_PREFIX_C2_ROOT_OFFSET: usize = V5_REAL_PREFIX_C1_ROOT_OFFSET + 32;
pub const V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET: usize = V5_REAL_PREFIX_C2_ROOT_OFFSET + 32;
pub const V5_REAL_PREFIX_SUMCHECK_OFFSET: usize = V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET + 16;
pub const V5_REAL_PREFIX_SUMCHECK_BYTES: usize = 4_480;
pub const V5_REAL_PREFIX_CLAIMS_OFFSET: usize =
    V5_REAL_PREFIX_SUMCHECK_OFFSET + V5_REAL_PREFIX_SUMCHECK_BYTES;
pub const V5_REAL_PREFIX_CLAIMS_BYTES: usize = 4 * V5_TOTAL_LANES * 16;
pub const V5_REAL_PREFIX_TERMINALS_OFFSET: usize =
    V5_REAL_PREFIX_CLAIMS_OFFSET + V5_REAL_PREFIX_CLAIMS_BYTES;
pub const V5_REAL_PREFIX_BYTES: usize = 6_423;
pub const V5_REAL_PREFIX_TERMINAL_BYTES: usize = 3 * 16;
pub const V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET: usize =
    V5_REAL_PREFIX_TERMINALS_OFFSET + V5_REAL_PREFIX_TERMINAL_BYTES;
pub const V5_REAL_PREFIX_RESERVE_OFFSET: usize = V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET + 16;
pub const V5_PUBLIC_FS_SALT_BYTES: usize = 32;
pub const V5_PUBLIC_FS_SALT_COUNT: usize = 2 + V5_LATER_LAYERS;
pub const V5_PUBLIC_FS_SALT_PRODUCTION_OBLIGATION: &str =
    "sample each public FS salt freshly and independently after its corresponding PCS root is fixed and before the first dependent challenge";
pub const V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET: usize = V5_REAL_PREFIX_RESERVE_OFFSET;
pub const V5_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES: usize =
    V5_PUBLIC_FS_SALT_COUNT * V5_PUBLIC_FS_SALT_BYTES;
pub const V5_REAL_PREFIX_ZERO_RESERVE_OFFSET: usize =
    V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET + V5_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES;
pub const V5_REAL_PREFIX_ZERO_RESERVE_BYTES: usize =
    V5_REAL_PREFIX_BYTES - V5_REAL_PREFIX_ZERO_RESERVE_OFFSET;

pub const V5_REAL_RELATION_POINT_BYTES: usize = 3 * 10 * 16;
pub const V5_REAL_RELATION_TAIL_BYTES: usize = 928;
pub const V5_REAL_ATOMIC_CONTEXT_BYTES: usize =
    ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES + (3 + 10 + 1) * 16;

const V5_LEGACY_ATOMIC_COLUMNS: usize = 28;
const V5_LEGACY_ATOMIC_CLAIMS: usize = 3 * V5_LEGACY_ATOMIC_COLUMNS;
const V5_LEGACY_HCOPY_COLUMN: usize = 26;

const _: () = assert!(V5_TOTAL_LANES == 19);
const _: () = assert!(V5_C1_LANES == 16);
const _: () = assert!(V5_C2_LANES == 3);
const _: () = assert!(V5_LEGACY_ATOMIC_CLAIMS == 84);
const _: () = assert!(V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET == 87);
const _: () = assert!(V5_REAL_PREFIX_SUMCHECK_OFFSET == 103);
const _: () = assert!(V5_REAL_PREFIX_CLAIMS_OFFSET == 4_583);
const _: () = assert!(V5_REAL_PREFIX_TERMINALS_OFFSET == 5_799);
const _: () = assert!(V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET == 5_847);
const _: () = assert!(V5_REAL_PREFIX_RESERVE_OFFSET == 5_863);
const _: () = assert!(V5_PUBLIC_FS_SALT_COUNT == 5);
const _: () = assert!(V5_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES == 160);
const _: () = assert!(V5_REAL_PREFIX_ZERO_RESERVE_OFFSET == 6_023);
const _: () = assert!(V5_REAL_PREFIX_ZERO_RESERVE_BYTES == 400);
const _: () = assert!(V5_REAL_PREFIX_ZERO_RESERVE_BYTES % 8 == 0);
const _: () = assert!(V5_REAL_RELATION_POINT_BYTES == 480);
const _: () = assert!(V5_REAL_RELATION_TAIL_BYTES == (4 + 6 + 8 + 8 + 4 * 7 + 4) * 16);
const _: () = assert!(V5_REAL_ATOMIC_CONTEXT_BYTES == 440);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5HostPowBits {
    pub folds: [u8; CANDIDATE_ROUND_COUNT],
    pub final_bits: u8,
}

impl V5HostPowBits {
    /// Fast isolated-CU construction. The transcript still binds and absorbs
    /// every nonce; the consuming verifier must use the same advertised bits.
    pub const CU_ZERO: Self = Self {
        folds: [0; CANDIDATE_ROUND_COUNT],
        final_bits: 0,
    };
}

#[derive(Clone, Copy)]
pub struct V5HostPcsSalts<'a> {
    pub c1: &'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    pub c2: &'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    pub later: [&'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]]; V5_LATER_LAYERS],
}

/// Fixed public Fiat--Shamir salts, one per committed PCS root.
///
/// The diagnostic builder deliberately accepts every 32-byte string, including
/// all-zero, so CU fixtures and byte KATs remain reproducible. Production must
/// instead use [`build_v5_real_host_artifact_with_fresh_public_fs_salts`], which
/// samples each salt only after its corresponding root is fixed. Neither path
/// discharges the separate radix-4/oracle, BCS, or HVZK proof obligations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5PublicFsSalts {
    pub c1: [u8; V5_PUBLIC_FS_SALT_BYTES],
    pub c2: [u8; V5_PUBLIC_FS_SALT_BYTES],
    pub later: [[u8; V5_PUBLIC_FS_SALT_BYTES]; V5_LATER_LAYERS],
}

impl V5PublicFsSalts {
    pub fn section(&self, section: usize) -> &[u8; V5_PUBLIC_FS_SALT_BYTES] {
        match section {
            0 => &self.c1,
            1 => &self.c2,
            2..=4 => &self.later[section - 2],
            _ => panic!("v5 public FS salt section out of range"),
        }
    }
}

pub struct V5RealHostInputs<'a> {
    pub statement: &'a AtomicPaymentStatementV4,
    pub witness: &'a SpendWitness,
    pub component_a: &'a [M31BlockMask; V5_C1_LANES],
    pub hcopy_padding: &'a [QM31; V5_TRACE_ROWS],
    pub sumcheck_mask: &'a V5SumcheckMask,
    pub component_b_pads: &'a [QM31; V5_B_PAD_COORDINATES],
    /// Fresh caller-owned scalar committed at B row 993 before `gamma`.
    /// The builder accepts deterministic values for test fixtures; production
    /// freshness is the caller obligation named by
    /// `V5_B_PIVOT_PAD_PRODUCTION_OBLIGATION`.
    pub component_b_pivot_pad: QM31,
    pub component_c: &'a V5ComponentCLane,
    pub salts: V5HostPcsSalts<'a>,
    pub public_fs_salts: V5PublicFsSalts,
    pub hash: HashFn,
    pub pow_bits: V5HostPowBits,
}

/// Production input surface for the public-FS-salt timing seam.
///
/// Unlike [`V5RealHostInputs`], this type has no public-salt field. The builder
/// owns five fresh OS draws and performs each draw only after the corresponding
/// PCS root exists and before that root is absorbed into the transcript.
pub struct V5FreshPublicFsRealHostInputs<'a> {
    pub statement: &'a AtomicPaymentStatementV4,
    pub witness: &'a SpendWitness,
    pub component_a: &'a [M31BlockMask; V5_C1_LANES],
    pub hcopy_padding: &'a [QM31; V5_TRACE_ROWS],
    pub sumcheck_mask: &'a V5SumcheckMask,
    pub component_b_pads: &'a [QM31; V5_B_PAD_COORDINATES],
    pub component_b_pivot_pad: QM31,
    pub component_c: &'a V5ComponentCLane,
    pub salts: V5HostPcsSalts<'a>,
    pub hash: HashFn,
    pub pow_bits: V5HostPowBits,
}

/// One immutable Component-B mask reference shared by every real-host role.
///
/// Keeping the four role accessors on one single-field handle makes it
/// impossible for the host builder to substitute a different mask between
/// commitment, initial-claim absorption, the masked sumcheck, and the
/// terminal evaluation.  It does not establish how the caller sampled the
/// referenced mask.
#[derive(Clone, Copy)]
struct V5RealHostBoundSumcheckMask<'a> {
    mask: &'a V5SumcheckMask,
}

impl<'a> V5RealHostBoundSumcheckMask<'a> {
    fn new(mask: &'a V5SumcheckMask) -> Self {
        Self { mask }
    }

    fn for_commitment(&self) -> &'a V5SumcheckMask {
        self.mask
    }

    fn for_initial_claim(&self) -> &'a V5SumcheckMask {
        self.mask
    }

    fn for_sumcheck(&self) -> &'a V5SumcheckMask {
        self.mask
    }

    fn for_terminal(&self) -> &'a V5SumcheckMask {
        self.mask
    }
}

struct V5RealHostCoreInputs<'a> {
    statement: &'a AtomicPaymentStatementV4,
    witness: &'a SpendWitness,
    component_a: &'a [M31BlockMask; V5_C1_LANES],
    hcopy_padding: &'a [QM31; V5_TRACE_ROWS],
    sumcheck_mask: V5RealHostBoundSumcheckMask<'a>,
    component_b_pads: &'a [QM31; V5_B_PAD_COORDINATES],
    component_b_pivot_pad: QM31,
    component_c: &'a V5ComponentCLane,
    salts: V5HostPcsSalts<'a>,
    hash: HashFn,
    pow_bits: V5HostPowBits,
}

impl<'a> V5RealHostCoreInputs<'a> {
    fn from_fixed(inputs: V5RealHostInputs<'a>) -> (Self, V5PublicFsSalts) {
        let V5RealHostInputs {
            statement,
            witness,
            component_a,
            hcopy_padding,
            sumcheck_mask,
            component_b_pads,
            component_b_pivot_pad,
            component_c,
            salts,
            public_fs_salts,
            hash,
            pow_bits,
        } = inputs;
        (
            Self {
                statement,
                witness,
                component_a,
                hcopy_padding,
                sumcheck_mask: V5RealHostBoundSumcheckMask::new(sumcheck_mask),
                component_b_pads,
                component_b_pivot_pad,
                component_c,
                salts,
                hash,
                pow_bits,
            },
            public_fs_salts,
        )
    }

    fn from_fresh(inputs: V5FreshPublicFsRealHostInputs<'a>) -> Self {
        let V5FreshPublicFsRealHostInputs {
            statement,
            witness,
            component_a,
            hcopy_padding,
            sumcheck_mask,
            component_b_pads,
            component_b_pivot_pad,
            component_c,
            salts,
            hash,
            pow_bits,
        } = inputs;
        Self {
            statement,
            witness,
            component_a,
            hcopy_padding,
            sumcheck_mask: V5RealHostBoundSumcheckMask::new(sumcheck_mask),
            component_b_pads,
            component_b_pivot_pad,
            component_c,
            salts,
            hash,
            pow_bits,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5SemanticChallenges {
    pub lambda: QM31,
    pub chi: QM31,
    pub theta: QM31,
    pub zerocheck_point: [QM31; 10],
    pub mu: QM31,
    pub eta: QM31,
    pub gamma: QM31,
    pub kappa: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5TerminalIdentity {
    pub real: QM31,
    pub mask: QM31,
    pub masked: QM31,
}

pub struct V5RealHostArtifact {
    pub statement_digest: [u8; 32],
    pub layer_zero: V5SplitLayerZero,
    pub challenges: V5SemanticChallenges,
    pub semantic_initial_claim: QM31,
    pub semantic_sumcheck: StateOnlyZerocheckTrace,
    pub relation_claims: V5RelationClaims,
    pub terminal: V5TerminalIdentity,
    pub inactive_claim: QM31,
    pub relation: V5RelationTrace,
    pub ood_points_circle: [[aspis_core::circle::SecureCirclePoint; CANDIDATE_OOD_SAMPLES]; 1],
    pub ood_points_line: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    pub ood_mixes: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub fold_nonces: [u64; CANDIDATE_ROUND_COUNT],
    pub alphas: [QM31; CANDIDATE_ROUND_COUNT],
    pub roots: V5PcsRoots,
    pub public_fs_salts: V5PublicFsSalts,
    pub final_nonce: u64,
    /// Public GoodA/GoodB certificate results for all three branches derived
    /// from the same pre-selector transcript. These are diagnostic host data;
    /// only `query_selector` and the selected branch are serialized.
    pub good_gate_evaluations: [V5HostGoodGateEvaluation; 3],
    pub query_selector: u8,
    pub queries: [u32; V5_REAL_HOST_QUERY_COUNT],
    pub opening_indices: CircleLineQueryIndices,
    pub openings: V5BuiltPcsOpenings,
    pub transcript_state_after_queries: [u8; 32],
}

impl V5RealHostArtifact {
    /// Serialize the exact real-witness semantic prefix. The reserve remaining
    /// after the five public FS salts stays canonical zero so the verifier can
    /// reject hidden extensions.
    pub fn encode_real_prefix(&self) -> [u8; V5_REAL_PREFIX_BYTES] {
        let mut bytes = [0u8; V5_REAL_PREFIX_BYTES];
        bytes[..8].copy_from_slice(&V5_REAL_PREFIX_MAGIC);
        bytes[8] = V5_REAL_PREFIX_VERSION;
        bytes[9] = V5_REAL_PREFIX_FLAGS;
        bytes[10..12].copy_from_slice(&256u16.to_le_bytes());
        bytes[12..14].copy_from_slice(&192u16.to_le_bytes());
        bytes[14] = V5_C1_LANES as u8;
        bytes[15] = V5_C2_LANES as u8;
        bytes[16..19].copy_from_slice(&[1, 2, 3]);
        bytes[19] = 10;
        bytes[20] = 27;
        bytes[21] = 4;
        bytes[22] = 0; // point-major claim layout

        bytes[V5_REAL_PREFIX_C1_ROOT_OFFSET..V5_REAL_PREFIX_C2_ROOT_OFFSET]
            .copy_from_slice(&self.roots.c1);
        bytes[V5_REAL_PREFIX_C2_ROOT_OFFSET..V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET]
            .copy_from_slice(&self.roots.c2);
        self.semantic_initial_claim.write_le_bytes(
            &mut bytes[V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET..V5_REAL_PREFIX_SUMCHECK_OFFSET],
        );
        bytes[V5_REAL_PREFIX_SUMCHECK_OFFSET..V5_REAL_PREFIX_CLAIMS_OFFSET]
            .copy_from_slice(&self.semantic_sumcheck.proof);
        bytes[V5_REAL_PREFIX_CLAIMS_OFFSET..V5_REAL_PREFIX_TERMINALS_OFFSET]
            .copy_from_slice(&self.relation_claims.encode_point_major());
        for (index, terminal) in [self.terminal.real, self.terminal.mask, self.terminal.masked]
            .iter()
            .copied()
            .enumerate()
        {
            let start = V5_REAL_PREFIX_TERMINALS_OFFSET + index * 16;
            terminal.write_le_bytes(&mut bytes[start..start + 16]);
        }
        self.inactive_claim.write_le_bytes(
            &mut bytes[V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET..V5_REAL_PREFIX_RESERVE_OFFSET],
        );
        for section in 0..V5_PUBLIC_FS_SALT_COUNT {
            let start = V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET + section * V5_PUBLIC_FS_SALT_BYTES;
            bytes[start..start + V5_PUBLIC_FS_SALT_BYTES]
                .copy_from_slice(self.public_fs_salts.section(section));
        }
        debug_assert!(bytes[V5_REAL_PREFIX_ZERO_RESERVE_OFFSET..]
            .iter()
            .all(|byte| *byte == 0));
        bytes
    }

    /// Serialize `(z, successor(z), xor12(z))`, point-major, for the existing
    /// account-backed relation/semantic tooth.
    pub fn encode_relation_points(&self) -> [u8; V5_REAL_RELATION_POINT_BYTES] {
        let mut bytes = [0u8; V5_REAL_RELATION_POINT_BYTES];
        for (point, coordinates) in self.relation_claims.points.iter().enumerate() {
            for (coordinate, value) in coordinates.iter().copied().enumerate() {
                let start = (point * 10 + coordinate) * 16;
                value.write_le_bytes(&mut bytes[start..start + 16]);
            }
        }
        bytes
    }

    /// Serialize the complete honest four-round relation payload in the
    /// verifier's fixed order: circle coordinates, later line points, OOD
    /// values, OOD mixes, four degree-six sumchecks, and final four values.
    pub fn encode_relation_tail(&self) -> [u8; V5_REAL_RELATION_TAIL_BYTES] {
        let mut bytes = [0u8; V5_REAL_RELATION_TAIL_BYTES];
        let mut field = 0usize;
        let write = |bytes: &mut [u8], field: &mut usize, value: QM31| {
            let start = *field * 16;
            value.write_le_bytes(&mut bytes[start..start + 16]);
            *field += 1;
        };

        for point in self.ood_points_circle[0] {
            write(&mut bytes, &mut field, point.x);
            write(&mut bytes, &mut field, point.y);
        }
        for round in self.ood_points_line {
            for point in round {
                write(&mut bytes, &mut field, point);
            }
        }
        for round in self.relation.ood_values {
            for value in round {
                write(&mut bytes, &mut field, value);
            }
        }
        for round in self.ood_mixes {
            for mix in round {
                write(&mut bytes, &mut field, mix);
            }
        }
        for polynomial in self.relation.sumchecks {
            for coefficient in polynomial {
                write(&mut bytes, &mut field, coefficient);
            }
        }
        for coefficient in self.relation.final_coefficients {
            write(&mut bytes, &mut field, coefficient);
        }
        debug_assert_eq!(field * 16, V5_REAL_RELATION_TAIL_BYTES);
        bytes
    }

    /// Serialize the fixed 440-byte statement/challenge context used only by
    /// the local CU wrapper. `eta` is intentionally omitted: the verifier
    /// derives it from the pre-challenge transcript and refuses a duplicate.
    pub fn encode_atomic_terminal_context(
        &self,
        statement: &AtomicPaymentStatementV4,
    ) -> Result<[u8; V5_REAL_ATOMIC_CONTEXT_BYTES], AtomicStatementError> {
        let mut bytes = [0u8; V5_REAL_ATOMIC_CONTEXT_BYTES];
        bytes[..ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES]
            .copy_from_slice(&encode_atomic_payment_statement_v4(statement)?);
        let mut offset = ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES;
        for value in [
            self.challenges.lambda,
            self.challenges.chi,
            self.challenges.theta,
        ] {
            value.write_le_bytes(&mut bytes[offset..offset + 16]);
            offset += 16;
        }
        for value in self.challenges.zerocheck_point {
            value.write_le_bytes(&mut bytes[offset..offset + 16]);
            offset += 16;
        }
        self.challenges
            .mu
            .write_le_bytes(&mut bytes[offset..offset + 16]);
        debug_assert_eq!(offset + 16, V5_REAL_ATOMIC_CONTEXT_BYTES);
        Ok(bytes)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5RealHostError {
    Message(V5SpendMessageError),
    Relation(V5RelationProverError),
    Circle(CircleCandidateError),
    Opening(StateOnlyPrivateOpeningBuildError),
    /// Fresh public-FS entropy was unavailable. The OS error is deliberately
    /// not exposed through the proof-building interface.
    PublicFsEntropy,
    AllGoodCandidatesBad,
    GoodRetryCapExhausted,
    Stage(&'static str),
    Consistency(&'static str),
}

/// Successful output of the bounded public GoodA/GoodB retry manager. The
/// failed-attempt count and the selected artifact are returned together so the
/// caller cannot silently discard retry metadata that may be externally
/// observable.
pub struct V5GoodRetryOutput<T> {
    pub failed_attempts: u8,
    pub value: T,
}

/// Run at most 17 complete attempts. Only the public all-three-bad outcome is
/// retried; every algebraic, serialization, or commitment failure is returned
/// immediately. The callback is the explicit executable seam at which a
/// production caller must instantiate
/// [`V5_REAL_HOST_GOOD_RETRY_FRESHNESS_OBLIGATION`].
pub fn retry_v5_public_good_attempts<T>(
    mut attempt: impl FnMut(u8) -> Result<T, V5RealHostError>,
) -> Result<V5GoodRetryOutput<T>, V5RealHostError> {
    for failed_attempts in 0..V5_REAL_HOST_GOOD_RETRY_CAP {
        match attempt(failed_attempts) {
            Ok(value) => {
                return Ok(V5GoodRetryOutput {
                    failed_attempts,
                    value,
                });
            }
            Err(V5RealHostError::AllGoodCandidatesBad) => {}
            Err(error) => return Err(error),
        }
    }
    Err(V5RealHostError::GoodRetryCapExhausted)
}

impl From<V5SpendMessageError> for V5RealHostError {
    fn from(error: V5SpendMessageError) -> Self {
        Self::Message(error)
    }
}

impl From<V5RelationProverError> for V5RealHostError {
    fn from(error: V5RelationProverError) -> Self {
        Self::Relation(error)
    }
}

impl From<CircleCandidateError> for V5RealHostError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Circle(error)
    }
}

impl From<StateOnlyPrivateOpeningBuildError> for V5RealHostError {
    fn from(error: StateOnlyPrivateOpeningBuildError) -> Self {
        Self::Opening(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V5PublicFsSaltStage {
    C1,
    C2,
    Later0,
    Later1,
    Later2,
}

impl V5PublicFsSaltStage {
    const fn section(self) -> usize {
        match self {
            Self::C1 => 0,
            Self::C2 => 1,
            Self::Later0 => 2,
            Self::Later1 => 3,
            Self::Later2 => 4,
        }
    }

    const fn later(round: usize) -> Self {
        match round {
            0 => Self::Later0,
            1 => Self::Later1,
            2 => Self::Later2,
            _ => panic!("v5 public FS later stage out of range"),
        }
    }
}

trait V5PublicFsSaltProvider {
    /// Produce one salt after `root` is fixed. Implementations must not cache a
    /// future production salt before this method is called.
    fn sample_after_root(
        &mut self,
        stage: V5PublicFsSaltStage,
        root: &[u8; 32],
    ) -> Result<[u8; V5_PUBLIC_FS_SALT_BYTES], V5RealHostError>;
}

struct FixedV5PublicFsSaltProvider {
    salts: V5PublicFsSalts,
}

impl V5PublicFsSaltProvider for FixedV5PublicFsSaltProvider {
    fn sample_after_root(
        &mut self,
        stage: V5PublicFsSaltStage,
        _root: &[u8; 32],
    ) -> Result<[u8; V5_PUBLIC_FS_SALT_BYTES], V5RealHostError> {
        Ok(*self.salts.section(stage.section()))
    }
}

struct FreshV5PublicFsSaltProvider;

impl V5PublicFsSaltProvider for FreshV5PublicFsSaltProvider {
    fn sample_after_root(
        &mut self,
        _stage: V5PublicFsSaltStage,
        _root: &[u8; 32],
    ) -> Result<[u8; V5_PUBLIC_FS_SALT_BYTES], V5RealHostError> {
        let mut salt = [0u8; V5_PUBLIC_FS_SALT_BYTES];
        getrandom::fill(&mut salt).map_err(|_| V5RealHostError::PublicFsEntropy)?;
        Ok(salt)
    }
}

fn absorb_round_root(
    transcript: &mut Transcript,
    layer: usize,
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_PUBLIC_FS_SALT_BYTES],
) {
    let mut record = [0u8; 65];
    record[0] = layer as u8;
    record[1..33].copy_from_slice(root);
    record[33..].copy_from_slice(public_fs_salt);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn sample_and_absorb_round_root(
    transcript: &mut Transcript,
    provider: &mut impl V5PublicFsSaltProvider,
    stage: V5PublicFsSaltStage,
    layer: usize,
    root: &[u8; 32],
) -> Result<[u8; V5_PUBLIC_FS_SALT_BYTES], V5RealHostError> {
    let salt = provider.sample_after_root(stage, root)?;
    absorb_round_root(transcript, layer, root, &salt);
    Ok(salt)
}

fn absorb_c2_root(
    transcript: &mut Transcript,
    root: &[u8; 32],
    public_fs_salt: &[u8; V5_PUBLIC_FS_SALT_BYTES],
) {
    let mut record = [0u8; 64];
    record[..32].copy_from_slice(root);
    record[32..].copy_from_slice(public_fs_salt);
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &record);
}

fn sample_and_absorb_c2_root(
    transcript: &mut Transcript,
    provider: &mut impl V5PublicFsSaltProvider,
    root: &[u8; 32],
) -> Result<[u8; V5_PUBLIC_FS_SALT_BYTES], V5RealHostError> {
    let salt = provider.sample_after_root(V5PublicFsSaltStage::C2, root)?;
    absorb_c2_root(transcript, root, &salt);
    Ok(salt)
}

fn absorb_ood(
    transcript: &mut Transcript,
    ood_label: u8,
    layer: usize,
    sample: usize,
    value: QM31,
) {
    let mut record = [0u8; 18];
    record[0] = layer as u8;
    record[1] = sample as u8;
    value.write_le_bytes(&mut record[2..]);
    transcript.absorb(ood_label, &record);
}

fn absorb_relation_sumcheck(
    transcript: &mut Transcript,
    layer: usize,
    polynomial: &SumcheckPolynomial,
) {
    let mut record = [0u8; 1 + SUMCHECK_COEFFICIENTS * 16];
    record[0] = layer as u8;
    for (index, value) in polynomial.iter().enumerate() {
        value.write_le_bytes(&mut record[1 + index * 16..][..16]);
    }
    transcript.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &record);
}

fn absorb_fold_pow(transcript: &mut Transcript, layer: usize, nonce: u64) {
    let mut record = [0u8; 1 + CANDIDATE_NONCE_LEN];
    record[0] = layer as u8;
    record[1..].copy_from_slice(&nonce.to_le_bytes());
    transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
}

fn absorb_final(transcript: &mut Transcript, coefficients: &[QM31; CANDIDATE_FINAL_POLY_LEN]) {
    let mut bytes = [0u8; CANDIDATE_FINAL_POLY_LEN * 16];
    for (index, value) in coefficients.iter().enumerate() {
        value.write_le_bytes(&mut bytes[index * 16..index * 16 + 16]);
    }
    transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, &bytes);
}

fn absorb_points(transcript: &mut Transcript, points: &[[QM31; 10]; 3]) {
    let mut bytes = [0u8; 3 * 10 * 16];
    for (point, coordinates) in points.iter().enumerate() {
        for (coordinate, value) in coordinates.iter().enumerate() {
            value.write_le_bytes(&mut bytes[(point * 10 + coordinate) * 16..][..16]);
        }
    }
    transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &bytes);
}

fn absorb_terminal(transcript: &mut Transcript, terminal: V5TerminalIdentity) {
    let mut bytes = [0u8; V5_REAL_HOST_TERMINAL_CONTEXT_VALUES * 16];
    terminal.real.write_le_bytes(&mut bytes[..16]);
    terminal.mask.write_le_bytes(&mut bytes[16..32]);
    terminal.masked.write_le_bytes(&mut bytes[32..48]);
    transcript.absorb(label::CLAIM, &bytes);
}

fn v5_legacy_atomic_claims(
    c1: &[Vec<M31>; V5_C1_LANES],
    hcopy: &[QM31],
    point: &[QM31; 10],
) -> [QM31; V5_LEGACY_ATOMIC_CLAIMS] {
    let points = [*point, binary_successor_point(point), xor12_point(point)];
    let mut claims = [QM31::ZERO; V5_LEGACY_ATOMIC_CLAIMS];
    for (point_index, evaluation_point) in points.iter().enumerate() {
        let start = point_index * V5_LEGACY_ATOMIC_COLUMNS;
        for lane in 0..V5_C1_LANES {
            claims[start + lane] = crate::multilinear_eval(&c1[lane], evaluation_point);
        }
        claims[start + V5_LEGACY_HCOPY_COLUMN] =
            crate::multilinear_eval_extension(hcopy, evaluation_point);
    }
    claims
}

/// Exact v5 adapter to the existing atomic-v3 unmasked terminal. The deleted
/// mask-only and G slots are zero; that function's unmasked return path uses
/// only the sixteen semantic lanes and Hcopy.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_v5_atomic_original_oracle(
    statement: &AtomicPaymentStatementV4,
    layer_zero: &V5SplitLayerZero,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
) -> Result<QM31, V5RealHostError> {
    let claims =
        v5_legacy_atomic_claims(layer_zero.c1.messages(), &layer_zero.c2.messages[0], point);
    atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
        statement,
        &claims,
        point,
        lambda,
        chi,
        theta,
        zerocheck_point,
        mu,
    )
    .map_err(|_| V5RealHostError::Stage("atomic terminal"))
}

fn gamma_combine_split_codewords(
    layer_zero: &V5SplitLayerZero,
    gamma: QM31,
) -> Result<Vec<QM31>, V5RealHostError> {
    if layer_zero.c1.encoded.len() != V5_C1_LANES
        || layer_zero.c2.encoded.len() != V5_C2_LANES
        || layer_zero
            .c1
            .encoded
            .iter()
            .any(|word| word.len() != V5_CODEWORD_LEN)
        || layer_zero
            .c2
            .encoded
            .iter()
            .any(|word| word.len() != V5_CODEWORD_LEN)
    {
        return Err(V5RealHostError::Consistency("encoded layer-zero shape"));
    }
    let powers = qm31_power_table::<V5_TOTAL_LANES>(gamma);
    let mut output = vec![QM31::ZERO; V5_CODEWORD_LEN];
    for (lane, word) in layer_zero.c1.encoded.iter().enumerate() {
        for (out, value) in output.iter_mut().zip(word.iter().copied()) {
            *out = out.add(powers[lane].mul_m31(value));
        }
    }
    for (helper, word) in layer_zero.c2.encoded.iter().enumerate() {
        let power = powers[V5_C1_LANES + helper];
        for (out, value) in output.iter_mut().zip(word.iter().copied()) {
            *out = out.add(power.mul(value));
        }
    }
    Ok(output)
}

fn flatten_combined_leaves(leaves: &[[u8; COMBINED_LAYER_LEAF_BYTES]]) -> Vec<u8> {
    let mut values = Vec::with_capacity(leaves.len() * COMBINED_LAYER_LEAF_BYTES);
    for leaf in leaves {
        values.extend_from_slice(leaf);
    }
    values
}

fn aggregate_claims(claims: &V5RelationClaims, gamma: QM31) -> [QM31; 4] {
    let powers = qm31_power_table::<V5_TOTAL_LANES>(gamma);
    core::array::from_fn(|point| {
        claims.point_major[point]
            .iter()
            .copied()
            .zip(powers)
            .fold(QM31::ZERO, |sum, (value, power)| sum.add(power.mul(value)))
    })
}

fn mine(transcript: &Transcript, bits: u8) -> u64 {
    crate::pow::find_grinding_nonce(transcript, bits)
}

const V5_GOOD_A_SIZE: usize = 12;
const V5_GOOD_B_SIZE: usize = 4;
const V5_GOOD_KERNEL_DEGREE: usize = 36;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5HostGoodGateEvaluation {
    pub queries: [u32; V5_REAL_HOST_QUERY_COUNT],
    pub good_a_matrix: [[M31; V5_GOOD_A_SIZE]; V5_GOOD_A_SIZE],
    pub good_a_determinant: M31,
    pub good_b_matrix: [[QM31; V5_GOOD_B_SIZE]; V5_GOOD_B_SIZE],
    pub good_b_determinant: QM31,
}

impl V5HostGoodGateEvaluation {
    pub fn is_good(self) -> bool {
        !self.good_a_determinant.is_zero() && !self.good_b_determinant.is_zero()
    }
}

fn good_kernel_polynomial(
    queries: &[u32; V5_REAL_HOST_QUERY_COUNT],
) -> Result<[M31; V5_GOOD_KERNEL_DEGREE + 1], V5RealHostError> {
    let mut polynomial = [M31::ZERO; V5_GOOD_KERNEL_DEGREE + 1];
    polynomial[0] = M31::ONE;
    let mut degree = 0usize;
    for &query in queries {
        let x = circle_fiber_point_for_domain_log(V5_DOMAIN_LOG as u32, query as usize)
            .map_err(|_| V5RealHostError::Stage("GoodA/GoodB q18 representative"))?
            .x;
        let constant = x.mul(x).neg();
        let mut next = [M31::ZERO; V5_GOOD_KERNEL_DEGREE + 1];
        for coefficient in 0..=degree {
            next[coefficient] = next[coefficient].add(polynomial[coefficient].mul(constant));
            next[coefficient + 2] = next[coefficient + 2].add(polynomial[coefficient]);
        }
        polynomial = next;
        degree += 2;
    }
    if degree != V5_GOOD_KERNEL_DEGREE || polynomial[V5_GOOD_KERNEL_DEGREE] != M31::ONE {
        return Err(V5RealHostError::Consistency("GoodA/GoodB kernel degree"));
    }
    Ok(polynomial)
}

fn good_mle_weights(point: &[QM31; 10]) -> [QM31; V5_TRACE_ROWS] {
    let mut weights = [QM31::ZERO; V5_TRACE_ROWS];
    weights[0] = QM31::ONE;
    let mut width = 1usize;
    for coordinate in point {
        for index in (0..width).rev() {
            let parent = weights[index];
            let right = coordinate.mul(parent);
            weights[2 * index] = parent.sub(right);
            weights[2 * index + 1] = right;
        }
        width *= 2;
    }
    debug_assert_eq!(width, V5_TRACE_ROWS);
    weights
}

fn good_relation_points(point: &[QM31; 10]) -> [[QM31; 10]; 3] {
    [*point, binary_successor_point(point), xor12_point(point)]
}

fn good_a_functionals(point: &[QM31; 10], conversion: &[Vec<M31>]) -> [[[QM31; 48]; 2]; 3] {
    debug_assert_eq!(conversion.len(), 48);
    let points = good_relation_points(point);
    let mut output = [[[QM31::ZERO; 48]; 2]; 3];
    for (terminal, terminal_point) in points.iter().enumerate() {
        let weights = good_mle_weights(terminal_point);
        for block in 0..2 {
            for degree in 0..48 {
                output[terminal][block][degree] = conversion[degree]
                    .iter()
                    .copied()
                    .enumerate()
                    .fold(QM31::ZERO, |sum, (natural, coefficient)| {
                        sum.add(weights[896 + 2 * natural + block].mul_m31(coefficient))
                    });
            }
        }
    }
    output
}

fn good_b_functionals(point: &[QM31; 10], conversion: &[Vec<M31>]) -> [[[QM31; 64]; 2]; 4] {
    debug_assert_eq!(conversion.len(), 64);
    let points = good_relation_points(point);
    let inactive = atomic_state_only_copy_inactive_row_masks_v3();
    let mut output = [[[QM31::ZERO; 64]; 2]; 4];
    for block in 0..2 {
        for degree in 0..64 {
            output[0][block][degree] = conversion[degree]
                .iter()
                .copied()
                .enumerate()
                .filter(|(natural, _)| {
                    let row = 256 + 2 * natural + block;
                    inactive[row >> 4] & (1 << (row & 15)) != 0
                })
                .fold(QM31::ZERO, |sum, (_, coefficient)| {
                    sum.add(QM31::from_cm31(CM31::from_m31(coefficient)))
                });
        }
    }
    for (terminal, terminal_point) in points.iter().enumerate() {
        let weights = good_mle_weights(terminal_point);
        for block in 0..2 {
            for degree in 0..64 {
                output[terminal + 1][block][degree] = conversion[degree]
                    .iter()
                    .copied()
                    .enumerate()
                    .fold(QM31::ZERO, |sum, (natural, coefficient)| {
                        sum.add(weights[256 + 2 * natural + block].mul_m31(coefficient))
                    });
            }
        }
    }
    output
}

fn good_qm31_limbs(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

fn good_a_matrix(
    kernel: &[M31; V5_GOOD_KERNEL_DEGREE + 1],
    functionals: &[[[QM31; 48]; 2]; 3],
) -> [[M31; V5_GOOD_A_SIZE]; V5_GOOD_A_SIZE] {
    let mut matrix = [[M31::ZERO; V5_GOOD_A_SIZE]; V5_GOOD_A_SIZE];
    for direction in 0..V5_GOOD_A_SIZE {
        let block = usize::from(direction == 11);
        let shift = if direction == 11 { 1 } else { direction + 1 };
        for terminal in 0..3 {
            let value = (0..=V5_GOOD_KERNEL_DEGREE).fold(QM31::ZERO, |sum, degree| {
                sum.add(
                    functionals[terminal][block][degree + shift]
                        .sub(functionals[terminal][block][degree])
                        .mul_m31(kernel[degree]),
                )
            });
            for (limb, coordinate) in good_qm31_limbs(value).into_iter().enumerate() {
                matrix[4 * terminal + limb][direction] = coordinate;
            }
        }
    }
    matrix
}

fn good_b_matrix(
    kernel: &[M31; V5_GOOD_KERNEL_DEGREE + 1],
    functionals: &[[[QM31; 64]; 2]; 4],
) -> [[QM31; V5_GOOD_B_SIZE]; V5_GOOD_B_SIZE] {
    let mut matrix = [[QM31::ZERO; V5_GOOD_B_SIZE]; V5_GOOD_B_SIZE];
    for direction in 0..V5_GOOD_B_SIZE {
        for output in 0..V5_GOOD_B_SIZE {
            matrix[output][direction] =
                (0..=V5_GOOD_KERNEL_DEGREE).fold(QM31::ZERO, |sum, degree| {
                    sum.add(functionals[output][0][degree + direction].mul_m31(kernel[degree]))
                });
        }
    }
    matrix
}

fn good_m31_determinant(mut matrix: [[M31; V5_GOOD_A_SIZE]; V5_GOOD_A_SIZE]) -> M31 {
    let mut determinant = M31::ONE;
    for column in 0..V5_GOOD_A_SIZE {
        let Some(pivot) = (column..V5_GOOD_A_SIZE).find(|&row| !matrix[row][column].is_zero())
        else {
            return M31::ZERO;
        };
        if pivot != column {
            matrix.swap(pivot, column);
            determinant = determinant.neg();
        }
        let pivot_value = matrix[column][column];
        determinant = determinant.mul(pivot_value);
        let pivot_inverse = pivot_value.inv();
        let pivot_row = matrix[column];
        for row in column + 1..V5_GOOD_A_SIZE {
            let scale = matrix[row][column].mul(pivot_inverse);
            for entry in column..V5_GOOD_A_SIZE {
                matrix[row][entry] = matrix[row][entry].sub(scale.mul(pivot_row[entry]));
            }
        }
    }
    determinant
}

fn good_qm31_determinant(mut matrix: [[QM31; V5_GOOD_B_SIZE]; V5_GOOD_B_SIZE]) -> QM31 {
    let mut determinant = QM31::ONE;
    for column in 0..V5_GOOD_B_SIZE {
        let Some(pivot) = (column..V5_GOOD_B_SIZE).find(|&row| !matrix[row][column].is_zero())
        else {
            return QM31::ZERO;
        };
        if pivot != column {
            matrix.swap(pivot, column);
            determinant = determinant.neg();
        }
        let pivot_value = matrix[column][column];
        determinant = determinant.mul(pivot_value);
        let pivot_inverse = pivot_value.inv();
        let pivot_row = matrix[column];
        for row in column + 1..V5_GOOD_B_SIZE {
            let scale = matrix[row][column].mul(pivot_inverse);
            for entry in column..V5_GOOD_B_SIZE {
                matrix[row][entry] = matrix[row][entry].sub(scale.mul(pivot_row[entry]));
            }
        }
    }
    determinant
}

fn evaluate_host_good_gate(
    point: &[QM31; 10],
    queries: [u32; V5_REAL_HOST_QUERY_COUNT],
    conversion48: &[Vec<M31>],
    conversion64: &[Vec<M31>],
) -> Result<V5HostGoodGateEvaluation, V5RealHostError> {
    let kernel = good_kernel_polynomial(&queries)?;
    let good_a_matrix = good_a_matrix(&kernel, &good_a_functionals(point, conversion48));
    let good_a_determinant = good_m31_determinant(good_a_matrix);
    let good_b_matrix = good_b_matrix(&kernel, &good_b_functionals(point, conversion64));
    let good_b_determinant = good_qm31_determinant(good_b_matrix);
    Ok(V5HostGoodGateEvaluation {
        queries,
        good_a_matrix,
        good_a_determinant,
        good_b_matrix,
        good_b_determinant,
    })
}

/// Build every real host value consumed by the isolated v5 CU verifier using
/// caller-fixed public FS salts. This is the deterministic diagnostic/KAT path;
/// production must use
/// [`build_v5_real_host_artifact_with_fresh_public_fs_salts`].
pub fn build_v5_real_host_artifact(
    inputs: V5RealHostInputs<'_>,
) -> Result<V5RealHostArtifact, V5RealHostError> {
    let (inputs, public_fs_salts) = V5RealHostCoreInputs::from_fixed(inputs);
    let mut provider = FixedV5PublicFsSaltProvider {
        salts: public_fs_salts,
    };
    build_v5_real_host_artifact_with_provider(inputs, &mut provider)
}

/// Build the same candidate artifact while owning the public FS entropy seam.
///
/// Each 32-byte salt is drawn from the OS only after its PCS root is fixed and
/// immediately before that root is transcript-absorbed. Entropy failure is a
/// fatal [`V5RealHostError::PublicFsEntropy`] with no OS-specific detail. This
/// function does not own mask/private-salt entropy and therefore is not, by
/// itself, a complete production attempt manager.
pub fn build_v5_real_host_artifact_with_fresh_public_fs_salts(
    inputs: V5FreshPublicFsRealHostInputs<'_>,
) -> Result<V5RealHostArtifact, V5RealHostError> {
    let inputs = V5RealHostCoreInputs::from_fresh(inputs);
    build_v5_real_host_artifact_with_provider(inputs, &mut FreshV5PublicFsSaltProvider)
}

#[allow(clippy::too_many_lines)]
fn build_v5_real_host_artifact_with_provider(
    inputs: V5RealHostCoreInputs<'_>,
    public_fs_salt_provider: &mut impl V5PublicFsSaltProvider,
) -> Result<V5RealHostArtifact, V5RealHostError> {
    let statement_digest = atomic_payment_statement_digest_v4(inputs.statement, inputs.hash)
        .map_err(|_| V5RealHostError::Stage("statement digest"))?;

    let c1 = build_and_commit_v5_c1(
        inputs.statement,
        inputs.witness,
        inputs.component_a,
        inputs.salts.c1,
        inputs.hash,
    )?;
    let mut transcript = Transcript::new(inputs.hash);
    transcript.absorb(label::PROFILE, V5_REAL_HOST_TRANSCRIPT_DOMAIN);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, &statement_digest);
    let c1_root = c1.root();
    let c1_public_fs_salt = sample_and_absorb_round_root(
        &mut transcript,
        public_fs_salt_provider,
        V5PublicFsSaltStage::C1,
        0,
        &c1_root,
    )?;
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| V5RealHostError::Stage("lambda"))?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| V5RealHostError::Stage("chi"))?;

    let component_b = V5StructuredBLane::encode(
        inputs.sumcheck_mask.for_commitment(),
        inputs.component_b_pads,
        inputs.component_b_pivot_pad,
    )?;
    let layer_zero = finish_v5_split_layer_zero(
        c1,
        inputs.hcopy_padding,
        &component_b,
        inputs.component_c,
        lambda,
        chi,
        inputs.salts.c2,
        inputs.hash,
    )?;
    let c2_root = layer_zero.c2.root();
    let c2_public_fs_salt =
        sample_and_absorb_c2_root(&mut transcript, public_fs_salt_provider, &c2_root)?;

    let batching = begin_state_only_zerocheck(&mut transcript)
        .map_err(|_| V5RealHostError::Stage("semantic batching"))?;
    let semantic_initial_claim = inputs.sumcheck_mask.for_initial_claim().initial_claim();
    let eta = begin_state_only_masked_sumcheck(&mut transcript, semantic_initial_claim)
        .map_err(|_| V5RealHostError::Stage("eta"))?;
    let semantic_sumcheck = prove_v5_masked_state_only_zerocheck(
        &mut transcript,
        inputs.sumcheck_mask.for_sumcheck(),
        eta,
        |point| {
            evaluate_v5_atomic_original_oracle(
                inputs.statement,
                &layer_zero,
                point,
                lambda,
                chi,
                batching.theta,
                &batching.zerocheck_point,
                batching.mu,
            )
        },
    )
    .map_err(|_| V5RealHostError::Stage("masked semantic sumcheck"))?;

    let relation_claims = build_v5_relation_claims(&layer_zero, &semantic_sumcheck.challenges);
    absorb_points(&mut transcript, &relation_claims.points);
    let claim_bytes = relation_claims.encode_point_major();
    transcript.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, &claim_bytes);
    let terminal_real = evaluate_v5_atomic_original_oracle(
        inputs.statement,
        &layer_zero,
        &semantic_sumcheck.challenges,
        lambda,
        chi,
        batching.theta,
        &batching.zerocheck_point,
        batching.mu,
    )?;
    let terminal_mask = inputs
        .sumcheck_mask
        .for_terminal()
        .evaluate(&semantic_sumcheck.challenges);
    let terminal = V5TerminalIdentity {
        real: terminal_real,
        mask: terminal_mask,
        masked: semantic_sumcheck.terminal_claim,
    };
    if terminal.mask.add(eta.mul(terminal.real)) != terminal.masked
        || relation_claims.point_major[3][V5_C1_LANES + 1] != terminal.mask
    {
        return Err(V5RealHostError::Consistency("semantic terminal identity"));
    }
    absorb_terminal(&mut transcript, terminal);

    let gamma = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V5RealHostError::Stage("gamma"))?;
    let messages = layer_zero.messages();
    let combined_message = gamma_combine_v5_messages(&messages, gamma)?;
    let inactive_masks = atomic_state_only_copy_inactive_row_masks_v3();
    let inactive_claim = combined_message
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| inactive_masks[row >> 4] & (1 << (row & 15)) != 0)
        .fold(QM31::ZERO, |sum, (_, value)| sum.add(value));
    let mut inactive_claim_bytes = [0u8; 16];
    inactive_claim.write_le_bytes(&mut inactive_claim_bytes);
    transcript.absorb(label::SECOND_PHASE_CLAIM, &inactive_claim_bytes);
    let kappa = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V5RealHostError::Stage("kappa"))?;
    let mut combined_codeword = gamma_combine_split_codewords(&layer_zero, gamma)?;
    let kappa2 = kappa.square();
    let kappa3 = kappa2.mul(kappa);
    let mut relation = V5IncrementalRelation::new(
        combined_message,
        &relation_claims.points,
        [QM31::ONE, kappa, kappa2],
        inactive_masks,
        inactive_claim,
        &relation_claims.terminal_covector,
        kappa3,
    )?;

    let mut circle_points = [[aspis_core::circle::SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES]; 1];
    let mut line_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut ood_mixes = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut fold_nonces = [0u64; CANDIDATE_ROUND_COUNT];
    let mut alphas = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    let mut later_values: [Vec<u8>; V5_LATER_LAYERS] = core::array::from_fn(|_| Vec::new());
    let mut later_trees: [Option<StateOnlyPrivateMerkleTree>; V5_LATER_LAYERS] =
        core::array::from_fn(|_| None);
    let mut later_public_fs_salts = [[0u8; V5_PUBLIC_FS_SALT_BYTES]; V5_LATER_LAYERS];

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = transcript
                    .challenge_secure_circle_point()
                    .map_err(|_| V5RealHostError::Stage("circle OOD point"))?;
                let value = relation.evaluate_circle_ood(point)?;
                absorb_ood(
                    &mut transcript,
                    label::M31_CIRCLE_OOD_VALUE,
                    round,
                    sample,
                    value,
                );
                let mix = transcript
                    .challenge_qm31()
                    .map_err(|_| V5RealHostError::Stage("circle OOD mix"))?;
                relation.add_circle_ood(point, value, mix)?;
                circle_points[0][sample] = point;
                ood_mixes[round][sample] = mix;
            } else {
                let point = transcript
                    .challenge_ood_qm31()
                    .map_err(|_| V5RealHostError::Stage("line OOD point"))?;
                let value = relation.evaluate_line_ood(point)?;
                absorb_ood(
                    &mut transcript,
                    label::M31_LINE_OOD_VALUE,
                    round,
                    sample,
                    value,
                );
                let mix = transcript
                    .challenge_qm31()
                    .map_err(|_| V5RealHostError::Stage("line OOD mix"))?;
                relation.add_line_ood(point, value, mix)?;
                line_points[round - 1][sample] = point;
                ood_mixes[round][sample] = mix;
            }
        }
        let polynomial = relation.polynomial()?;
        absorb_relation_sumcheck(&mut transcript, round, &polynomial);
        fold_nonces[round] = mine(&transcript, inputs.pow_bits.folds[round]);
        absorb_fold_pow(&mut transcript, round, fold_nonces[round]);
        alphas[round] = transcript
            .challenge_qm31()
            .map_err(|_| V5RealHostError::Stage("fold alpha"))?;
        relation.fold(alphas[round])?;
        combined_codeword = fold_candidate_codeword_round_for_domain_log(
            &combined_codeword,
            alphas[round],
            round,
            V5_DOMAIN_LOG,
        )?;
        if round < V5_LATER_LAYERS {
            let leaves = combined_layer_leaves(&combined_codeword);
            later_values[round] = flatten_combined_leaves(&leaves);
            let tree = build_state_only_private_merkle_tree(
                inputs.hash,
                V5_PRIVATE_DEPTHS[2 + round],
                CIRCLE_LINE_TAGS[round],
                COMBINED_LAYER_LEAF_BYTES,
                &later_values[round],
                inputs.salts.later[round],
            )?;
            let root = tree.root();
            later_public_fs_salts[round] = sample_and_absorb_round_root(
                &mut transcript,
                public_fs_salt_provider,
                V5PublicFsSaltStage::later(round),
                round + 1,
                &root,
            )?;
            later_trees[round] = Some(tree);
        }
    }
    let relation = relation.finish()?;
    let aggregated = aggregate_claims(&relation_claims, gamma);
    if relation.point_claims != aggregated[..3] || relation.terminal_claim != aggregated[3] {
        return Err(V5RealHostError::Consistency(
            "gamma-aggregated relation claims",
        ));
    }
    absorb_final(&mut transcript, &relation.final_coefficients);
    let final_nonce = mine(&transcript, inputs.pow_bits.final_bits);
    transcript.absorb(label::GRIND_NONCE, &final_nonce.to_le_bytes());
    let pre_selector_transcript = transcript.clone();
    let conversion48 = super::ordinary_monomials_in_natural_line_basis(48);
    let conversion64 = super::ordinary_monomials_in_natural_line_basis(64);
    let mut selected = None;
    let mut good_gate_evaluations = [None; 3];
    for candidate in 0..3u8 {
        let mut branch = pre_selector_transcript.clone();
        branch.absorb(label::M31_STATE_ONLY_QUERY_CANDIDATE, &[candidate]);
        let queries: [u32; V5_REAL_HOST_QUERY_COUNT] = branch
            .challenge_queries_without_replacement(
                V5_REAL_HOST_QUERY_COUNT,
                V5_LAYER_ZERO_LEAVES as u32,
                PAYMENT_HIDING_QUERY_DRAW_LIMIT,
            )
            .map_err(|_| V5RealHostError::Stage("q18 candidate"))?
            .try_into()
            .map_err(|_| V5RealHostError::Consistency("q18 candidate count"))?;
        let evaluation = evaluate_host_good_gate(
            &semantic_sumcheck.challenges,
            queries,
            &conversion48,
            &conversion64,
        )?;
        good_gate_evaluations[usize::from(candidate)] = Some(evaluation);
        if selected.is_none() && evaluation.is_good() {
            selected = Some((candidate, queries, branch));
        }
    }
    let (query_selector, queries, selected_transcript) =
        selected.ok_or(V5RealHostError::AllGoodCandidatesBad)?;
    let good_gate_evaluations = good_gate_evaluations.map(|evaluation| {
        evaluation.expect("all three public GoodA/GoodB branches were evaluated")
    });
    transcript = selected_transcript;

    let later_roots: [[u8; 32]; V5_LATER_LAYERS] =
        core::array::from_fn(|layer| later_trees[layer].as_ref().unwrap().root());
    let roots = V5PcsRoots {
        c1: layer_zero.c1.root(),
        c2: layer_zero.c2.root(),
        later: later_roots,
    };
    let opening_indices =
        derive_circle_line_query_indices_for_count(&queries, V5_LAYER_ZERO_LEAVES)
            .map_err(|_| V5RealHostError::Stage("opening indices"))?;
    let section_indices: [&[u32]; 5] = [
        &opening_indices.layer0,
        &opening_indices.layer0,
        &opening_indices.later[0],
        &opening_indices.later[1],
        &opening_indices.later[2],
    ];
    let section_values: [&[u8]; 5] = [
        &layer_zero.c1.packed_values,
        &layer_zero.c2.packed_values,
        &later_values[0],
        &later_values[1],
        &later_values[2],
    ];
    let section_salts: [&[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]]; 5] = [
        inputs.salts.c1,
        inputs.salts.c2,
        inputs.salts.later[0],
        inputs.salts.later[1],
        inputs.salts.later[2],
    ];
    let section_trees: [&StateOnlyPrivateMerkleTree; 5] = [
        &layer_zero.c1.tree,
        &layer_zero.c2.tree,
        later_trees[0].as_ref().unwrap(),
        later_trees[1].as_ref().unwrap(),
        later_trees[2].as_ref().unwrap(),
    ];
    let mut opening_bytes = Vec::new();
    let mut section_bytes = [0usize; 5];
    let mut frontier_nodes = [0usize; 5];
    for section in 0..5 {
        let opening = serialize_state_only_private_opening(
            section_trees[section],
            section_values[section],
            section_salts[section],
            section_indices[section],
        )?;
        section_bytes[section] = opening.bytes.len();
        frontier_nodes[section] = opening.frontier_nodes;
        opening_bytes.extend_from_slice(&opening.bytes);
    }
    let openings = V5BuiltPcsOpenings {
        bytes: opening_bytes,
        indices: opening_indices.clone(),
        section_bytes,
        frontier_nodes,
    };
    let verified = verify_v5_pcs_openings(inputs.hash, &roots, &queries, &openings.bytes)?;
    if verified.end != openings.bytes.len() {
        return Err(V5RealHostError::Consistency("opening self-verification"));
    }

    Ok(V5RealHostArtifact {
        statement_digest,
        layer_zero,
        challenges: V5SemanticChallenges {
            lambda,
            chi,
            theta: batching.theta,
            zerocheck_point: batching.zerocheck_point,
            mu: batching.mu,
            eta,
            gamma,
            kappa,
        },
        semantic_initial_claim,
        semantic_sumcheck,
        relation_claims,
        terminal,
        inactive_claim,
        relation,
        ood_points_circle: circle_points,
        ood_points_line: line_points,
        ood_mixes,
        fold_nonces,
        alphas,
        roots,
        public_fs_salts: V5PublicFsSalts {
            c1: c1_public_fs_salt,
            c2: c2_public_fs_salt,
            later: later_public_fs_salts,
        },
        final_nonce,
        good_gate_evaluations,
        query_selector,
        queries,
        opening_indices,
        openings,
        transcript_state_after_queries: transcript.diagnostic_state(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, P};
    use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment, Digest, MerklePath,
        SpendPublic,
    };

    use crate::v5_mask::{sample_atomic_m31_lane_masks, Qm31WordSource};
    use crate::HOST_HASH;

    struct XorShift(u64);

    const TEST_PUBLIC_FS_STAGES: [V5PublicFsSaltStage; V5_PUBLIC_FS_SALT_COUNT] = [
        V5PublicFsSaltStage::C1,
        V5PublicFsSaltStage::C2,
        V5PublicFsSaltStage::Later0,
        V5PublicFsSaltStage::Later1,
        V5PublicFsSaltStage::Later2,
    ];

    struct RecordingPublicFsSaltProvider {
        calls: Vec<(V5PublicFsSaltStage, [u8; 32])>,
        fail_at: Option<V5PublicFsSaltStage>,
    }

    impl RecordingPublicFsSaltProvider {
        fn new(fail_at: Option<V5PublicFsSaltStage>) -> Self {
            Self {
                calls: Vec::new(),
                fail_at,
            }
        }
    }

    impl V5PublicFsSaltProvider for RecordingPublicFsSaltProvider {
        fn sample_after_root(
            &mut self,
            stage: V5PublicFsSaltStage,
            root: &[u8; 32],
        ) -> Result<[u8; V5_PUBLIC_FS_SALT_BYTES], V5RealHostError> {
            self.calls.push((stage, *root));
            if self.fail_at == Some(stage) {
                return Err(V5RealHostError::PublicFsEntropy);
            }
            Ok([0xa0 + stage.section() as u8; V5_PUBLIC_FS_SALT_BYTES])
        }
    }

    fn test_public_fs_roots() -> [[u8; 32]; V5_PUBLIC_FS_SALT_COUNT] {
        core::array::from_fn(|section| [0x40 + section as u8; 32])
    }

    fn exercise_public_fs_stages(
        transcript: &mut Transcript,
        provider: &mut impl V5PublicFsSaltProvider,
        roots: &[[u8; 32]; V5_PUBLIC_FS_SALT_COUNT],
    ) -> Result<V5PublicFsSalts, V5RealHostError> {
        let c1 = sample_and_absorb_round_root(
            transcript,
            provider,
            V5PublicFsSaltStage::C1,
            0,
            &roots[0],
        )?;
        let c2 = sample_and_absorb_c2_root(transcript, provider, &roots[1])?;
        let mut later = [[0u8; V5_PUBLIC_FS_SALT_BYTES]; V5_LATER_LAYERS];
        for round in 0..V5_LATER_LAYERS {
            later[round] = sample_and_absorb_round_root(
                transcript,
                provider,
                V5PublicFsSaltStage::later(round),
                round + 1,
                &roots[2 + round],
            )?;
        }
        Ok(V5PublicFsSalts { c1, c2, later })
    }

    fn absorb_public_fs_stage_reference(
        transcript: &mut Transcript,
        stage: V5PublicFsSaltStage,
        root: &[u8; 32],
        salt: &[u8; V5_PUBLIC_FS_SALT_BYTES],
    ) {
        match stage {
            V5PublicFsSaltStage::C1 => absorb_round_root(transcript, 0, root, salt),
            V5PublicFsSaltStage::C2 => absorb_c2_root(transcript, root, salt),
            V5PublicFsSaltStage::Later0
            | V5PublicFsSaltStage::Later1
            | V5PublicFsSaltStage::Later2 => {
                absorb_round_root(transcript, stage.section() - 1, root, salt);
            }
        }
    }

    fn public_fs_test_transcript() -> Transcript {
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::PROFILE, b"v5-public-fs-staged-provider-test-v1");
        transcript
    }

    #[test]
    fn staged_public_fs_provider_observes_exact_order_and_roots() {
        let roots = test_public_fs_roots();
        let mut provider = RecordingPublicFsSaltProvider::new(None);
        let mut transcript = public_fs_test_transcript();
        let salts = exercise_public_fs_stages(&mut transcript, &mut provider, &roots).unwrap();

        assert_eq!(
            provider.calls,
            TEST_PUBLIC_FS_STAGES
                .into_iter()
                .enumerate()
                .map(|(section, stage)| (stage, roots[section]))
                .collect::<Vec<_>>()
        );
        for stage in TEST_PUBLIC_FS_STAGES {
            assert_eq!(
                salts.section(stage.section()),
                &[0xa0 + stage.section() as u8; V5_PUBLIC_FS_SALT_BYTES]
            );
        }
    }

    #[test]
    fn fixed_public_fs_provider_preserves_exact_root_record_bytes() {
        let roots = test_public_fs_roots();
        let fixed = V5PublicFsSalts {
            c1: [0x11; V5_PUBLIC_FS_SALT_BYTES],
            c2: [0x22; V5_PUBLIC_FS_SALT_BYTES],
            later: [
                [0x31; V5_PUBLIC_FS_SALT_BYTES],
                [0x32; V5_PUBLIC_FS_SALT_BYTES],
                [0x33; V5_PUBLIC_FS_SALT_BYTES],
            ],
        };
        let mut provider = FixedV5PublicFsSaltProvider { salts: fixed };
        let mut staged = public_fs_test_transcript();
        let returned = exercise_public_fs_stages(&mut staged, &mut provider, &roots).unwrap();

        let mut reference = public_fs_test_transcript();
        for (section, stage) in TEST_PUBLIC_FS_STAGES.into_iter().enumerate() {
            absorb_public_fs_stage_reference(
                &mut reference,
                stage,
                &roots[section],
                fixed.section(section),
            );
        }

        assert_eq!(returned, fixed);
        assert_eq!(staged.diagnostic_state(), reference.diagnostic_state());
    }

    #[test]
    fn public_fs_entropy_failure_is_fatal_at_every_stage_before_absorption() {
        let roots = test_public_fs_roots();
        for (failed_section, failed_stage) in TEST_PUBLIC_FS_STAGES.into_iter().enumerate() {
            let mut provider = RecordingPublicFsSaltProvider::new(Some(failed_stage));
            let mut staged = public_fs_test_transcript();
            assert_eq!(
                exercise_public_fs_stages(&mut staged, &mut provider, &roots),
                Err(V5RealHostError::PublicFsEntropy)
            );
            assert_eq!(
                provider.calls,
                TEST_PUBLIC_FS_STAGES[..=failed_section]
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(section, stage)| (stage, roots[section]))
                    .collect::<Vec<_>>()
            );

            let mut reference = public_fs_test_transcript();
            for (section, stage) in TEST_PUBLIC_FS_STAGES[..failed_section]
                .iter()
                .copied()
                .enumerate()
            {
                let salt = [0xa0 + section as u8; V5_PUBLIC_FS_SALT_BYTES];
                absorb_public_fs_stage_reference(&mut reference, stage, &roots[section], &salt);
            }
            assert_eq!(staged.diagnostic_state(), reference.diagnostic_state());
        }
    }

    #[test]
    fn public_good_retry_selects_first_success_and_releases_count() {
        let mut calls = 0u8;
        let output = retry_v5_public_good_attempts(|attempt| {
            assert_eq!(attempt, calls);
            calls += 1;
            if attempt < 2 {
                Err(V5RealHostError::AllGoodCandidatesBad)
            } else {
                Ok(41u8)
            }
        })
        .unwrap();
        assert_eq!(output.failed_attempts, 2);
        assert_eq!(output.value, 41);
        assert_eq!(calls, 3);
    }

    #[test]
    fn public_good_retry_aborts_exactly_at_cap_17() {
        let mut calls = 0u8;
        let result = retry_v5_public_good_attempts::<()>(|attempt| {
            assert_eq!(attempt, calls);
            calls += 1;
            Err(V5RealHostError::AllGoodCandidatesBad)
        });
        assert!(matches!(
            result,
            Err(V5RealHostError::GoodRetryCapExhausted)
        ));
        assert_eq!(calls, V5_REAL_HOST_GOOD_RETRY_CAP);
        assert_eq!(V5_REAL_HOST_GOOD_RETRY_CAP, 17);
    }

    #[test]
    fn public_good_retry_does_not_retry_non_gate_failures() {
        let mut calls = 0u8;
        let result = retry_v5_public_good_attempts::<()>(|_| {
            calls += 1;
            Err(V5RealHostError::Consistency("hostile non-gate failure"))
        });
        assert!(matches!(
            result,
            Err(V5RealHostError::Consistency("hostile non-gate failure"))
        ));
        assert_eq!(calls, 1);
    }

    #[test]
    fn public_good_retry_does_not_retry_public_fs_entropy_failure() {
        let mut calls = 0u8;
        let result = retry_v5_public_good_attempts::<()>(|_| {
            calls += 1;
            Err(V5RealHostError::PublicFsEntropy)
        });
        assert!(matches!(result, Err(V5RealHostError::PublicFsEntropy)));
        assert_eq!(calls, 1);
    }

    impl Qm31WordSource for XorShift {
        fn next_word(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            (x >> 21) as u32 % P
        }
    }

    #[test]
    fn bound_sumcheck_mask_roles_are_pointer_identical() {
        let committed = V5SumcheckMask::sample(&mut XorShift(0xb500_0000_0000_0001)).unwrap();
        let substituted = V5SumcheckMask::sample(&mut XorShift(0xb500_0000_0000_0002)).unwrap();
        let bound = V5RealHostBoundSumcheckMask::new(&committed);

        assert!(core::ptr::eq(bound.for_commitment(), &committed));
        assert!(core::ptr::eq(bound.for_initial_claim(), &committed));
        assert!(core::ptr::eq(bound.for_sumcheck(), &committed));
        assert!(core::ptr::eq(bound.for_terminal(), &committed));
        assert!(!core::ptr::eq(bound.for_terminal(), &substituted));
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

    fn fixture() -> (AtomicPaymentStatementV4, SpendWitness) {
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

    fn salts(domain: u8, count: usize) -> Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]> {
        (0..count)
            .map(|leaf| {
                core::array::from_fn(|byte| {
                    domain
                        .wrapping_add((leaf as u8).wrapping_mul(37))
                        .wrapping_add((byte as u8).wrapping_mul(19))
                })
            })
            .collect()
    }

    #[test]
    #[ignore = "expensive real-witness integration fixture; run explicitly before CU measurement"]
    fn real_witness_artifact_is_algebraically_and_merkle_self_consistent() {
        let (statement, witness) = fixture();
        let mut a_sources: [XorShift; V5_C1_LANES] =
            core::array::from_fn(|lane| XorShift(0xa531_0000_0000_0001 ^ lane as u64));
        let component_a = sample_atomic_m31_lane_masks(&mut a_sources).unwrap();
        let hcopy_padding = hcopy_padding();
        let sumcheck_mask = V5SumcheckMask::sample(&mut XorShift(0xb500_0000_0000_0001)).unwrap();
        let b_pads = core::array::from_fn(|index| q(20_000 + index as u32));
        let component_c = V5ComponentCLane::sample(&mut XorShift(0xc500_0000_0000_0001)).unwrap();
        let c1_salts = salts(0xc1, V5_LAYER_ZERO_LEAVES);
        let c2_salts = salts(0xc2, V5_LAYER_ZERO_LEAVES);
        let later_salts = [
            salts(0xd1, 1 << 15),
            salts(0xd2, 1 << 13),
            salts(0xd3, 1 << 11),
        ];
        let artifact = build_v5_real_host_artifact(V5RealHostInputs {
            statement: &statement,
            witness: &witness,
            component_a: &component_a,
            hcopy_padding: &hcopy_padding,
            sumcheck_mask: &sumcheck_mask,
            component_b_pads: &b_pads,
            component_b_pivot_pad: q(29_999),
            component_c: &component_c,
            salts: V5HostPcsSalts {
                c1: &c1_salts,
                c2: &c2_salts,
                later: [&later_salts[0], &later_salts[1], &later_salts[2]],
            },
            public_fs_salts: V5PublicFsSalts {
                c1: [0x11; V5_PUBLIC_FS_SALT_BYTES],
                c2: [0x22; V5_PUBLIC_FS_SALT_BYTES],
                later: [
                    [0x31; V5_PUBLIC_FS_SALT_BYTES],
                    [0x32; V5_PUBLIC_FS_SALT_BYTES],
                    [0x33; V5_PUBLIC_FS_SALT_BYTES],
                ],
            },
            hash: HOST_HASH,
            pow_bits: V5HostPowBits::CU_ZERO,
        })
        .unwrap();

        assert_eq!(
            artifact.semantic_sumcheck.challenges,
            artifact.relation_claims.points[0]
        );
        assert_eq!(
            artifact
                .terminal
                .mask
                .add(artifact.challenges.eta.mul(artifact.terminal.real)),
            artifact.terminal.masked
        );
        assert_eq!(artifact.relation.final_coefficients.len(), 4);
        assert_eq!(artifact.queries.len(), 18);
        assert_eq!(artifact.openings.indices, artifact.opening_indices);
        assert!(artifact
            .openings
            .section_bytes
            .iter()
            .all(|bytes| *bytes > 0));
        assert_ne!(artifact.roots.c1, [0u8; 32]);
        assert_ne!(artifact.roots.c2, [0u8; 32]);
        assert!(artifact.roots.later.iter().all(|root| *root != [0u8; 32]));

        // Re-run the exact affine-B joint-rank check on this artifact's own
        // salted+p transcript point and transcript-derived q18 positions.
        // This deliberately does not reuse the older frozen release schedule.
        let current_positions = artifact
            .opening_indices
            .layer0
            .iter()
            .flat_map(|query| {
                (0..crate::v5_mask::spend_messages::V5_FIBRE_SLOTS).map(move |slot| {
                    *query as usize * crate::v5_mask::spend_messages::V5_FIBRE_SLOTS + slot
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(
            current_positions.len(),
            V5_REAL_HOST_QUERY_COUNT * crate::v5_mask::spend_messages::V5_FIBRE_SLOTS
        );
        assert_eq!(
            crate::v5_mask::v5_b_structured_rank::component_b_affine_joint_ranks(
                &artifact.semantic_sumcheck.challenges,
                &current_positions,
            ),
            [76, 76, 76, 77, 271, 76, 347]
        );

        let prefix = artifact.encode_real_prefix();
        assert_eq!(&prefix[..8], &V5_REAL_PREFIX_MAGIC);
        assert_eq!(
            &prefix[V5_REAL_PREFIX_C1_ROOT_OFFSET..V5_REAL_PREFIX_C2_ROOT_OFFSET],
            &artifact.roots.c1
        );
        assert_eq!(
            &prefix[V5_REAL_PREFIX_C2_ROOT_OFFSET..V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET],
            &artifact.roots.c2
        );
        assert_eq!(
            &prefix[V5_REAL_PREFIX_SUMCHECK_OFFSET..V5_REAL_PREFIX_CLAIMS_OFFSET],
            &artifact.semantic_sumcheck.proof
        );
        assert_eq!(
            QM31::from_le_bytes(
                &prefix[V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET..V5_REAL_PREFIX_RESERVE_OFFSET]
            ),
            Some(artifact.inactive_claim)
        );
        for section in 0..V5_PUBLIC_FS_SALT_COUNT {
            let start = V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET + section * V5_PUBLIC_FS_SALT_BYTES;
            assert_eq!(
                &prefix[start..start + V5_PUBLIC_FS_SALT_BYTES],
                artifact.public_fs_salts.section(section)
            );
        }
        assert!(prefix[V5_REAL_PREFIX_ZERO_RESERVE_OFFSET..]
            .iter()
            .all(|byte| *byte == 0));
        assert_eq!(
            artifact.encode_relation_points().len(),
            V5_REAL_RELATION_POINT_BYTES
        );
        assert_eq!(
            artifact.encode_relation_tail().len(),
            V5_REAL_RELATION_TAIL_BYTES
        );
        assert_eq!(
            artifact
                .encode_atomic_terminal_context(&statement)
                .unwrap()
                .len(),
            V5_REAL_ATOMIC_CONTEXT_BYTES
        );
    }

    fn probe_qm31(state: &mut u64) -> QM31 {
        let mut limb = || {
            let mut x = *state;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *state = x;
            M31((x as u32) % P)
        };
        QM31 {
            c0: CM31::new(limb(), limb()),
            c1: CM31::new(limb(), limb()),
        }
    }

    fn probe_point_and_transcript(seed: u64) -> ([QM31; 10], Transcript) {
        use aspis_core::state_only_sumcheck::{
            absorb_state_only_sumcheck_round, encode_state_only_polynomial,
            STATE_ONLY_SUMCHECK_COEFFICIENTS,
        };

        let mut transcript = Transcript::new(crate::HOST_HASH);
        transcript.absorb(label::PROFILE, V5_REAL_HOST_TRANSCRIPT_DOMAIN);
        transcript.absorb(label::STATEMENT, &seed.to_le_bytes());
        let mut state = seed ^ 0xa517_3d29_60c4_e8f1;
        let mut point = [QM31::ZERO; 10];
        for (round, output) in point.iter_mut().enumerate() {
            let polynomial = core::array::from_fn::<_, STATE_ONLY_SUMCHECK_COEFFICIENTS, _>(|_| {
                probe_qm31(&mut state)
            });
            let encoded = encode_state_only_polynomial(&polynomial);
            *output = absorb_state_only_sumcheck_round(&mut transcript, round, &encoded).unwrap();
        }
        (point, transcript)
    }

    fn probe_q18_candidates(
        mut transcript: Transcript,
        seed: u64,
    ) -> [[u32; V5_REAL_HOST_QUERY_COUNT]; 3] {
        let mut state = seed ^ 0xb84c_91e7_235a_d60f;
        let mut final_bytes = [0u8; CANDIDATE_FINAL_POLY_LEN * 16];
        for (index, chunk) in final_bytes.chunks_exact_mut(16).enumerate() {
            let value = probe_qm31(&mut state);
            value.write_le_bytes(chunk);
            debug_assert!(index < CANDIDATE_FINAL_POLY_LEN);
        }
        transcript.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, &seed.to_le_bytes());
        transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, &final_bytes);
        transcript.absorb(label::GRIND_NONCE, &seed.rotate_left(17).to_le_bytes());
        core::array::from_fn(|selector| {
            let mut branch = transcript.clone();
            branch.absorb(label::M31_STATE_ONLY_QUERY_CANDIDATE, &[selector as u8]);
            branch
                .challenge_queries_without_replacement(
                    V5_REAL_HOST_QUERY_COUNT,
                    V5_LAYER_ZERO_LEAVES as u32,
                    PAYMENT_HIDING_QUERY_DRAW_LIMIT,
                )
                .unwrap()
                .try_into()
                .unwrap()
        })
    }

    fn probe_kernel_polynomial(queries: &[u32; V5_REAL_HOST_QUERY_COUNT]) -> [M31; 37] {
        use aspis_core::circle_fri::circle_fiber_point_for_domain_log;

        let mut polynomial = [M31::ZERO; 37];
        polynomial[0] = M31::ONE;
        let mut degree = 0usize;
        for &query in queries {
            let x = circle_fiber_point_for_domain_log(V5_DOMAIN_LOG as u32, query as usize)
                .unwrap()
                .x;
            let constant = x.mul(x).neg();
            let mut next = [M31::ZERO; 37];
            for coefficient in 0..=degree {
                next[coefficient] = next[coefficient].add(polynomial[coefficient].mul(constant));
                next[coefficient + 2] = next[coefficient + 2].add(polynomial[coefficient]);
            }
            polynomial = next;
            degree += 2;
        }
        assert_eq!(degree, 36);
        assert_eq!(polynomial[36], M31::ONE);
        polynomial
    }

    fn probe_mle_weights(point: &[QM31; 10]) -> [QM31; V5_TRACE_ROWS] {
        let mut weights = [QM31::ZERO; V5_TRACE_ROWS];
        weights[0] = QM31::ONE;
        let mut width = 1usize;
        for coordinate in point {
            for index in (0..width).rev() {
                let parent = weights[index];
                let right = coordinate.mul(parent);
                weights[2 * index] = parent.sub(right);
                weights[2 * index + 1] = right;
            }
            width *= 2;
        }
        assert_eq!(width, V5_TRACE_ROWS);
        weights
    }

    fn probe_relation_points(point: &[QM31; 10]) -> [[QM31; 10]; 3] {
        [*point, binary_successor_point(point), xor12_point(point)]
    }

    fn probe_a_functionals(point: &[QM31; 10], conversion: &[Vec<M31>]) -> [[[QM31; 48]; 2]; 3] {
        assert_eq!(conversion.len(), 48);
        let points = probe_relation_points(point);
        let mut output = [[[QM31::ZERO; 48]; 2]; 3];
        for (terminal, terminal_point) in points.iter().enumerate() {
            let weights = probe_mle_weights(terminal_point);
            for block in 0..2 {
                for degree in 0..48 {
                    output[terminal][block][degree] = conversion[degree]
                        .iter()
                        .copied()
                        .enumerate()
                        .fold(QM31::ZERO, |sum, (natural, coefficient)| {
                            sum.add(weights[896 + 2 * natural + block].mul_m31(coefficient))
                        });
                }
            }
        }
        output
    }

    fn probe_b_functionals(point: &[QM31; 10], conversion: &[Vec<M31>]) -> [[[QM31; 64]; 2]; 4] {
        assert_eq!(conversion.len(), 64);
        let points = probe_relation_points(point);
        let inactive = atomic_state_only_copy_inactive_row_masks_v3();
        let mut output = [[[QM31::ZERO; 64]; 2]; 4];
        for block in 0..2 {
            for degree in 0..64 {
                output[0][block][degree] = conversion[degree]
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(natural, _)| {
                        let row = 256 + 2 * natural + block;
                        inactive[row >> 4] & (1 << (row & 15)) != 0
                    })
                    .fold(QM31::ZERO, |sum, (_, coefficient)| {
                        sum.add(QM31::from_cm31(CM31::from_m31(coefficient)))
                    });
            }
        }
        for (terminal, terminal_point) in points.iter().enumerate() {
            let weights = probe_mle_weights(terminal_point);
            for block in 0..2 {
                for degree in 0..64 {
                    output[terminal + 1][block][degree] = conversion[degree]
                        .iter()
                        .copied()
                        .enumerate()
                        .fold(QM31::ZERO, |sum, (natural, coefficient)| {
                            sum.add(weights[256 + 2 * natural + block].mul_m31(coefficient))
                        });
                }
            }
        }
        output
    }

    fn probe_qm31_limbs(value: QM31) -> [M31; 4] {
        [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
    }

    fn probe_a_matrix(
        kernel: &[M31; 37],
        functionals: &[[[QM31; 48]; 2]; 3],
        columns: &[usize],
    ) -> Vec<Vec<M31>> {
        let mut matrix = vec![vec![M31::ZERO; columns.len()]; 12];
        for (output_column, &direction) in columns.iter().enumerate() {
            assert!(direction < 22);
            let block = direction / 11;
            let shift = direction % 11 + 1;
            for terminal in 0..3 {
                let value = (0..=36).fold(QM31::ZERO, |sum, degree| {
                    sum.add(
                        functionals[terminal][block][degree + shift]
                            .sub(functionals[terminal][block][degree])
                            .mul_m31(kernel[degree]),
                    )
                });
                for (limb, coordinate) in probe_qm31_limbs(value).into_iter().enumerate() {
                    matrix[4 * terminal + limb][output_column] = coordinate;
                }
            }
        }
        matrix
    }

    fn probe_b_matrix(
        kernel: &[M31; 37],
        functionals: &[[[QM31; 64]; 2]; 4],
        columns: &[usize],
    ) -> Vec<Vec<QM31>> {
        let mut matrix = vec![vec![QM31::ZERO; columns.len()]; 4];
        for (output_column, &direction) in columns.iter().enumerate() {
            assert!(direction < 56);
            let block = direction / 28;
            let shift = direction % 28;
            for output in 0..4 {
                matrix[output][output_column] = (0..=36).fold(QM31::ZERO, |sum, degree| {
                    sum.add(functionals[output][block][degree + shift].mul_m31(kernel[degree]))
                });
            }
        }
        matrix
    }

    fn probe_m31_pivots(matrix: &[Vec<M31>]) -> Vec<usize> {
        let mut work = matrix.to_vec();
        let mut rank = 0usize;
        let mut pivots = Vec::new();
        for column in 0..work[0].len() {
            let Some(pivot) = (rank..work.len()).find(|&row| !work[row][column].is_zero()) else {
                continue;
            };
            work.swap(rank, pivot);
            let pivot_row = work[rank].clone();
            let inverse = pivot_row[column].inv();
            for row in rank + 1..work.len() {
                let scale = work[row][column].mul(inverse);
                for entry in column..work[row].len() {
                    work[row][entry] = work[row][entry].sub(scale.mul(pivot_row[entry]));
                }
            }
            pivots.push(column);
            rank += 1;
            if rank == work.len() {
                break;
            }
        }
        pivots
    }

    fn probe_qm31_pivots(matrix: &[Vec<QM31>]) -> Vec<usize> {
        let mut work = matrix.to_vec();
        let mut rank = 0usize;
        let mut pivots = Vec::new();
        for column in 0..work[0].len() {
            let Some(pivot) = (rank..work.len()).find(|&row| !work[row][column].is_zero()) else {
                continue;
            };
            work.swap(rank, pivot);
            let pivot_row = work[rank].clone();
            let inverse = pivot_row[column].inv();
            for row in rank + 1..work.len() {
                let scale = work[row][column].mul(inverse);
                for entry in column..work[row].len() {
                    work[row][entry] = work[row][entry].sub(scale.mul(pivot_row[entry]));
                }
            }
            pivots.push(column);
            rank += 1;
            if rank == work.len() {
                break;
            }
        }
        pivots
    }

    fn probe_m31_inverse(matrix: &[Vec<M31>]) -> Option<Vec<Vec<M31>>> {
        let size = matrix.len();
        if size == 0 || matrix.iter().any(|row| row.len() != size) {
            return None;
        }
        let mut work = vec![vec![M31::ZERO; 2 * size]; size];
        for row in 0..size {
            work[row][..size].copy_from_slice(&matrix[row]);
            work[row][size + row] = M31::ONE;
        }
        for column in 0..size {
            let pivot = (column..size).find(|&row| !work[row][column].is_zero())?;
            work.swap(column, pivot);
            let inverse = work[column][column].inv();
            for entry in column..2 * size {
                work[column][entry] = work[column][entry].mul(inverse);
            }
            let pivot_row = work[column].clone();
            for row in 0..size {
                if row == column {
                    continue;
                }
                let scale = work[row][column];
                for entry in column..2 * size {
                    work[row][entry] = work[row][entry].sub(scale.mul(pivot_row[entry]));
                }
            }
        }
        Some(work.into_iter().map(|row| row[size..].to_vec()).collect())
    }

    fn probe_qm31_inverse(matrix: &[Vec<QM31>]) -> Option<Vec<Vec<QM31>>> {
        let size = matrix.len();
        if size == 0 || matrix.iter().any(|row| row.len() != size) {
            return None;
        }
        let mut work = vec![vec![QM31::ZERO; 2 * size]; size];
        for row in 0..size {
            work[row][..size].copy_from_slice(&matrix[row]);
            work[row][size + row] = QM31::ONE;
        }
        for column in 0..size {
            let pivot = (column..size).find(|&row| !work[row][column].is_zero())?;
            work.swap(column, pivot);
            let inverse = work[column][column].inv();
            for entry in column..2 * size {
                work[column][entry] = work[column][entry].mul(inverse);
            }
            let pivot_row = work[column].clone();
            for row in 0..size {
                if row == column {
                    continue;
                }
                let scale = work[row][column];
                for entry in column..2 * size {
                    work[row][entry] = work[row][entry].sub(scale.mul(pivot_row[entry]));
                }
            }
        }
        Some(work.into_iter().map(|row| row[size..].to_vec()).collect())
    }

    fn probe_print_first_witness(
        point: &[QM31; 10],
        stored_queries: &[u32; V5_REAL_HOST_QUERY_COUNT],
        a_matrix: &[Vec<M31>],
        b_matrix: &[Vec<QM31>],
    ) {
        let natural_queries = stored_queries.map(|query| query.reverse_bits() >> 15);
        let point_limbs = point.map(|value| probe_qm31_limbs(value).map(|limb| limb.0));
        let a_values = a_matrix
            .iter()
            .map(|row| row.iter().map(|value| value.0).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let b_values = b_matrix
            .iter()
            .map(|row| {
                row.iter()
                    .map(|value| probe_qm31_limbs(*value).map(|limb| limb.0))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let a_inverse = probe_m31_inverse(a_matrix)
            .unwrap()
            .into_iter()
            .map(|row| row.into_iter().map(|value| value.0).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let b_inverse = probe_qm31_inverse(b_matrix)
            .unwrap()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|value| probe_qm31_limbs(value).map(|limb| limb.0))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        println!("v5-good-witness stored_q18={stored_queries:?}");
        println!("v5-good-witness natural_q18={natural_queries:?}");
        println!("v5-good-witness point_limbs={point_limbs:?}");
        println!("v5-good-witness a_matrix={a_values:?}");
        println!("v5-good-witness a_inverse={a_inverse:?}");
        println!("v5-good-witness b_matrix={b_values:?}");
        println!("v5-good-witness b_inverse={b_inverse:?}");
    }

    /// Offline acceptance probe for the public sufficient certificates.  It
    /// runs the exact transcript challenge and without-replacement q18
    /// samplers, cloning each common post-final prefix into selector branches
    /// zero, one, and two. Its seeded post-sumcheck transcript bytes are
    /// synthetic; the output is acceptance evidence, never a universal theorem.
    #[test]
    #[ignore = "offline A/B public-certificate acceptance probe"]
    fn v5_public_good_a_good_b_schedule_probe() {
        let z_samples = std::env::var("V5_GOOD_PROBE_Z")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(4);
        let q18_per_z = std::env::var("V5_GOOD_PROBE_Q18_PER_Z")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(32);
        let requested_threads = std::env::var("V5_GOOD_PROBE_THREADS")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, usize::from));
        let thread_count = requested_threads.max(1).min(z_samples.max(1));
        let print_first = std::env::var_os("V5_GOOD_PROBE_PRINT_FIRST").is_some();
        let conversion48 = super::super::ordinary_monomials_in_natural_line_basis(48);
        let conversion64 = super::super::ordinary_monomials_in_natural_line_basis(64);
        const A_COLUMNS: [usize; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        const B_COLUMNS: [usize; 4] = [0, 1, 2, 3];
        let all_a_columns = (0..22).collect::<Vec<_>>();
        let all_b_columns = (0..56).collect::<Vec<_>>();
        let chunk_size = z_samples.div_ceil(thread_count);
        let [a_full, a_fixed, b_full, b_fixed, combined, total] = std::thread::scope(|scope| {
            let mut workers = Vec::with_capacity(thread_count);
            for worker in 0..thread_count {
                let start = worker * chunk_size;
                let end = (start + chunk_size).min(z_samples);
                let conversion48 = &conversion48;
                let conversion64 = &conversion64;
                let all_a_columns = &all_a_columns;
                let all_b_columns = &all_b_columns;
                workers.push(scope.spawn(move || {
                    let mut counts = [0usize; 6];
                    for z_ordinal in start..end {
                        let seed = 0x9d13_2a74_5bc8_e601u64 ^ z_ordinal as u64;
                        let (point, transcript) = probe_point_and_transcript(seed);
                        let a_functionals = probe_a_functionals(&point, conversion48);
                        let b_functionals = probe_b_functionals(&point, conversion64);
                        for attempt_ordinal in 0..q18_per_z {
                            let schedule_seed = seed.rotate_left(23) ^ attempt_ordinal as u64;
                            let candidates =
                                probe_q18_candidates(transcript.clone(), schedule_seed);
                            for (selector, queries) in candidates.into_iter().enumerate() {
                                let kernel = probe_kernel_polynomial(&queries);
                                let a_matrix = probe_a_matrix(&kernel, &a_functionals, &A_COLUMNS);
                                let b_matrix = probe_b_matrix(&kernel, &b_functionals, &B_COLUMNS);
                                let fixed_a_good = probe_m31_pivots(&a_matrix).len() == 12;
                                let fixed_b_good = probe_qm31_pivots(&b_matrix).len() == 4;
                                if print_first
                                    && z_ordinal == 0
                                    && attempt_ordinal == 0
                                    && selector == 0
                                {
                                    assert!(fixed_a_good && fixed_b_good);
                                    probe_print_first_witness(
                                        &point, &queries, &a_matrix, &b_matrix,
                                    );
                                }
                                let full_a_good = fixed_a_good
                                    || probe_m31_pivots(&probe_a_matrix(
                                        &kernel,
                                        &a_functionals,
                                        all_a_columns,
                                    ))
                                    .len()
                                        == 12;
                                let full_b_good = fixed_b_good
                                    || probe_qm31_pivots(&probe_b_matrix(
                                        &kernel,
                                        &b_functionals,
                                        all_b_columns,
                                    ))
                                    .len()
                                        == 4;
                                counts[0] += usize::from(full_a_good);
                                counts[1] += usize::from(fixed_a_good);
                                counts[2] += usize::from(full_b_good);
                                counts[3] += usize::from(fixed_b_good);
                                counts[4] += usize::from(fixed_a_good && fixed_b_good);
                                counts[5] += 1;
                            }
                        }
                    }
                    counts
                }));
            }
            workers.into_iter().fold([0usize; 6], |mut total, worker| {
                for (sum, value) in total.iter_mut().zip(worker.join().unwrap()) {
                    *sum += value;
                }
                total
            })
        });

        println!(
            "v5-good-probe total={total} threads={thread_count} a_full={a_full} a_fixed={a_fixed} b_full={b_full} b_fixed={b_fixed} combined={combined} a_columns={A_COLUMNS:?} b_columns={B_COLUMNS:?}"
        );
        assert!(combined > 0);
    }

    fn cu_fixture_salts(seed: u64, count: usize) -> Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]> {
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

    fn current_cu_fixture() -> V5RealHostArtifact {
        let (statement, witness) = fixture();
        let mut a_sources: [XorShift; V5_C1_LANES] =
            core::array::from_fn(|lane| XorShift(0xa531_0000_0000_0001 ^ lane as u64));
        let component_a = sample_atomic_m31_lane_masks(&mut a_sources).unwrap();
        let hcopy_padding = hcopy_padding();
        let sumcheck_mask = V5SumcheckMask::sample(&mut XorShift(0xb500_0000_0000_0001)).unwrap();
        let b_pads = core::array::from_fn(|index| q(20_000 + index as u32));
        let component_c = V5ComponentCLane::sample(&mut XorShift(0xc500_0000_0000_0001)).unwrap();
        let c1_salts = cu_fixture_salts(0xc1, V5_LAYER_ZERO_LEAVES);
        let c2_salts = cu_fixture_salts(0xc2, V5_LAYER_ZERO_LEAVES);
        let later_salts = [
            cu_fixture_salts(0xd1, 1 << 15),
            cu_fixture_salts(0xd2, 1 << 13),
            cu_fixture_salts(0xd3, 1 << 11),
        ];
        build_v5_real_host_artifact(V5RealHostInputs {
            statement: &statement,
            witness: &witness,
            component_a: &component_a,
            hcopy_padding: &hcopy_padding,
            sumcheck_mask: &sumcheck_mask,
            component_b_pads: &b_pads,
            component_b_pivot_pad: q(29_999),
            component_c: &component_c,
            salts: V5HostPcsSalts {
                c1: &c1_salts,
                c2: &c2_salts,
                later: [&later_salts[0], &later_salts[1], &later_salts[2]],
            },
            public_fs_salts: V5PublicFsSalts {
                c1: [0xa1; V5_PUBLIC_FS_SALT_BYTES],
                c2: [0xa2; V5_PUBLIC_FS_SALT_BYTES],
                later: [
                    [0xb1; V5_PUBLIC_FS_SALT_BYTES],
                    [0xb2; V5_PUBLIC_FS_SALT_BYTES],
                    [0xb3; V5_PUBLIC_FS_SALT_BYTES],
                ],
            },
            hash: HOST_HASH,
            pow_bits: V5HostPowBits::CU_ZERO,
        })
        .unwrap()
    }

    fn current_row256_raw_basis_commutes(
        stored_queries: &[u32; V5_REAL_HOST_QUERY_COUNT],
        conversion: &[Vec<M31>],
    ) -> bool {
        use aspis_core::circle_fri::circle_fiber_point_for_domain_log;

        let encoder = super::super::v5_encoder();
        for ordinary in 0..128 {
            let block = ordinary / 64;
            let degree = ordinary % 64;
            for &stored in stored_queries {
                let representative =
                    circle_fiber_point_for_domain_log(V5_DOMAIN_LOG as u32, stored as usize)
                        .unwrap();
                for slot in 0..4 {
                    let position = stored as usize * 4 + slot;
                    let mut actual = M31::ZERO;
                    for (natural, &coefficient) in conversion[degree].iter().enumerate() {
                        let row = 256 + 2 * natural + block;
                        actual = actual.add(
                            coefficient.mul(encoder.encode_c1_basis_value(row, position).unwrap()),
                        );
                    }
                    let x = if slot < 2 {
                        representative.x
                    } else {
                        representative.x.neg()
                    };
                    let y = if slot == 0 || slot == 3 {
                        representative.y
                    } else {
                        representative.y.neg()
                    };
                    let factor = encoder.encode_c1_basis_value(256, position).unwrap();
                    let expected = if block == 0 {
                        factor.mul(x.pow(degree as u64))
                    } else {
                        factor.mul(y).mul(x.pow(degree as u64))
                    };
                    if actual != expected {
                        eprintln!(
                            "row256-commute-failure stored={stored} slot={slot} ordinary={ordinary} actual={} expected={}",
                            actual.0, expected.0
                        );
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Exact current deterministic CU fixture, replayed under all three
    /// selectable post-final query branches. This is fixture applicability
    /// evidence, not a universal schedule theorem or a Rust--Lean proof.
    #[test]
    #[ignore = "offline exact-current-fixture GoodB applicability probe"]
    fn current_cu_fixture_fixed_good_b_all_selectors() {
        let conversion = super::super::ordinary_monomials_in_natural_line_basis(64);
        const B_COLUMNS: [usize; 4] = [0, 1, 2, 3];
        let artifact = current_cu_fixture();
        for (selector, evaluation) in artifact.good_gate_evaluations.iter().enumerate() {
            let mut sorted = evaluation.queries;
            sorted.sort_unstable();
            assert!(sorted.windows(2).all(|pair| pair[0] != pair[1]));
            let natural_queries = evaluation.queries.map(|query| query.reverse_bits() >> 15);
            let kernel = probe_kernel_polynomial(&evaluation.queries);
            let functionals = probe_b_functionals(&artifact.relation_claims.points[0], &conversion);
            let matrix = probe_b_matrix(&kernel, &functionals, &B_COLUMNS);
            let determinant = super::super::qm31_determinant(&matrix);
            let determinant_limbs = probe_qm31_limbs(determinant).map(|limb| limb.0);
            let point_limbs = artifact.relation_claims.points[0]
                .map(|value| probe_qm31_limbs(value).map(|limb| limb.0));
            let matrix_limbs = matrix
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|&value| probe_qm31_limbs(value).map(|limb| limb.0))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let inverse_limbs = probe_qm31_inverse(&matrix)
                .unwrap()
                .into_iter()
                .map(|row| {
                    row.into_iter()
                        .map(|value| probe_qm31_limbs(value).map(|limb| limb.0))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let commutes = current_row256_raw_basis_commutes(&evaluation.queries, &conversion);
            println!(
                "v5-current-goodb selector={selector} stored_q18={:?} natural_q18={natural_queries:?} point={point_limbs:?} matrix={matrix_limbs:?} inverse={inverse_limbs:?} determinant={determinant_limbs:?} row256_basis_commutes={commutes}",
                evaluation.queries,
            );
            assert!(!determinant.is_zero());
            assert!(commutes);
        }
    }

    fn probe_m31_determinant(matrix: &[Vec<M31>]) -> M31 {
        let size = matrix.len();
        assert!(size > 0 && matrix.iter().all(|row| row.len() == size));
        let mut work = matrix.to_vec();
        let mut determinant = M31::ONE;
        for column in 0..size {
            let Some(pivot) = (column..size).find(|&row| !work[row][column].is_zero()) else {
                return M31::ZERO;
            };
            if pivot != column {
                work.swap(column, pivot);
                determinant = determinant.neg();
            }
            let pivot_value = work[column][column];
            determinant = determinant.mul(pivot_value);
            let pivot_inverse = pivot_value.inv();
            let pivot_row = work[column].clone();
            for row in column + 1..size {
                let scale = work[row][column].mul(pivot_inverse);
                for entry in column..size {
                    work[row][entry] = work[row][entry].sub(scale.mul(pivot_row[entry]));
                }
            }
        }
        determinant
    }

    /// Exact fixed `12 x 12` Component-A minor from the current deterministic
    /// CU fixture, replayed under all three selectable post-final q18 branches.
    /// This is fixture applicability evidence, not a universal theorem or a
    /// Rust--Lean correspondence proof.
    #[test]
    #[ignore = "offline exact-current-fixture GoodA applicability probe"]
    fn current_cu_fixture_fixed_good_a_all_selectors() {
        let conversion = super::super::ordinary_monomials_in_natural_line_basis(48);
        const A_COLUMNS: [usize; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let artifact = current_cu_fixture();
        for (selector, evaluation) in artifact.good_gate_evaluations.iter().enumerate() {
            let natural_queries = evaluation.queries.map(|query| query.reverse_bits() >> 15);
            let kernel = probe_kernel_polynomial(&evaluation.queries);
            let functionals = probe_a_functionals(&artifact.relation_claims.points[0], &conversion);
            let matrix = probe_a_matrix(&kernel, &functionals, &A_COLUMNS);
            let determinant = probe_m31_determinant(&matrix);
            let pivots = probe_m31_pivots(&matrix);
            let matrix_limbs = matrix
                .iter()
                .map(|row| row.iter().map(|value| value.0).collect::<Vec<_>>())
                .collect::<Vec<_>>();
            println!(
                "v5-current-gooda selector={selector} stored_q18={:?} natural_q18={natural_queries:?} matrix={matrix_limbs:?} determinant={} pivots={pivots:?}",
                evaluation.queries, determinant.0,
            );
            assert!(!determinant.is_zero());
            assert_eq!(pivots, A_COLUMNS);
        }
    }
}
