//! Aspis on-chain verifier (Stage 0 slice).
//!
//! The program is the crate seam the design cares about: it parses and
//! verifies proof envelopes against a statement digest and knows nothing
//! about spends. Staged upload follows the Yano pattern: a proof account is
//! populated chunk by chunk, then `Verify` runs `aspis_core::verify` over it
//! with the SHA-256 syscall as the hash backend.
//!
//! Proof account layout:
//! [0..4] magic "ASPU", [4..8] proof_len u32 LE, [8..40] upload authority,
//! [40..40+proof_len] proof bytes.

// Solana's entrypoint macro emits `target_os = "solana"`; the host toolchain's
// check-cfg list does not know that SBF target even though cargo-build-sbf does.
#![allow(unexpected_cfgs)]

// Production must never be feature-unified with a PoW bypass or an older
// statement candidate. The stable marker is checked by the release harness so
// an unrelated compiler failure cannot masquerade as this isolation tooth.
#[cfg(all(
    feature = "profile23-production",
    any(
        feature = "diagnostic-unmined-mutation",
        feature = "diagnostic-unmined-profile21-mutation",
        feature = "diagnostic-unmined-profile22-acceptance",
        feature = "diagnostic-unmined-profile22-mutation",
        feature = "diagnostic-unmined-profile23-acceptance",
        feature = "diagnostic-unmined-profile23-mutation",
        feature = "profile20-mutation-candidate",
        feature = "profile21-integrated-candidate",
        feature = "profile21-mutation-candidate",
        feature = "profile22-integrated-candidate",
        feature = "profile22-mutation-candidate",
    )
))]
compile_error!(
    "PROFILE23_PRODUCTION_FEATURE_ISOLATION: profile23-production cannot be combined with diagnostic or legacy Profile20/21/22 candidate features"
);

#[cfg(all(
    feature = "profile23-minimal-dispatch",
    not(feature = "profile23-production")
))]
compile_error!(
    "PROFILE23_MINIMAL_DISPATCH_REQUIRES_PRODUCTION: the minimal wire surface is valid only for profile23-production"
);

#[cfg(all(
    feature = "profile23-dynamic-rate512",
    not(feature = "profile23-production")
))]
compile_error!(
    "PROFILE23_DYNAMIC_RATE512_REQUIRES_PRODUCTION: query-local public coordinates are enabled only for profile23-production"
);

pub mod atomic_payment;

use borsh::{BorshDeserialize, BorshSerialize};
#[cfg(not(feature = "no-entrypoint"))]
use solana_program::entrypoint;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    declare_id,
    entrypoint::ProgramResult,
    hash::hashv,
    log::sol_log_compute_units,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

// Bound to the checked-in deployment keypair. Release artifacts pin the
// resulting SBF hash; changing this identifier requires a full rebuild and
// release-certificate regeneration.
declare_id!("7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue");

const PROOF_ACCOUNT_MAGIC: [u8; 4] = *b"ASPU";
pub const PROOF_ACCOUNT_HEADER_LEN: usize = 40;
const AUTHORITY_OFFSET: usize = 8;

#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum ZkKernelKind {
    M31InverseSoftware,
    M31InverseSyscall,
    Qm31SquareGeneric,
    Qm31SquareSpecialized,
    M31Pow2Generic,
    M31Pow2Shift,
    Sha256AppendChain,
}

#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum ExactWideV4DiagnosticMode {
    BaselineFourDots,
    FusedDot4,
    EmptyLeafHashControl,
    C1LeafHash,
    C2LeafHash,
    GammaPowersControl,
    GammaPowers0To50,
    FusedBatch36Unprepared,
    FusedBatch36Prepared,
    FusedBatch36PreparedBytes,
}

/// Decision-packet-only probes for a possible genuine-circle M31 C1 basis.
/// None of these modes is a production proof parser or verifier.
#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum M31CircleBasisDiagnosticMode {
    RlcStructuredFourDots,
    RlcFusedCanonicalBytes,
    EmptyLeafHashControl,
    C1LeafHash784,
    FoldPrevalidatedCoordinates,
    FoldDerivedCoordinatesBatchInverse,
    FoldCachedCoordinatesPrevalidatedInverses,
    // Append-only: preserve the diagnostic submode ordinals above.
    RlcDecodedFusedDot4,
    RlcStreamingFourDots,
    RlcPreparedLimbs49,
    RlcPreparedLimbs49TwoRows,
}

/// Neutral, measurement-only two-point relation shapes. The ordinals are
/// pinned inside append-only instruction tag 25 and select no production
/// batching or soundness rule.
#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum TwoPointBatchingDiagnosticMode {
    OnePointBaseline,
    FreshKappaSingleLane,
    TwoIndependentRelationLanes,
    DisjointGamma51SingleLane,
}

/// Overlap-reconciled partitions of the literal q74/g32 Johnson query-cost
/// diagnostic. The instruction always carries `start` and `end` so every
/// row has the same wire framing; only `Layer0Range` consumes them.
#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum JohnsonM31CircleDiagnosticPhase {
    PreparedBase,
    Layer0Range,
    LaterAll,
    Full,
}

/// Read-only partitions of the complete width-28 state-only verifier. Each
/// partition replays the same parser and unmined transcript base; marker
/// deltas, not naive inclusive sums, are used for reconciliation.
#[derive(Clone, Copy, Debug, BorshSerialize, BorshDeserialize)]
pub enum StateOnlyWidth28DiagnosticPhase {
    PreparedBase,
    Terminal,
    Relation,
    Openings,
    Queries,
    QueryLayer0,
    QueryLaterAll,
    TerminalBreakdown,
    TerminalNoMask,
}

impl TwoPointBatchingDiagnosticMode {
    const fn index(self) -> usize {
        match self {
            Self::OnePointBaseline => 0,
            Self::FreshKappaSingleLane => 1,
            Self::TwoIndependentRelationLanes => 2,
            Self::DisjointGamma51SingleLane => 3,
        }
    }

    const fn core_mode(self) -> aspis_core::two_point::TwoPointBatchingMode {
        match self {
            Self::OnePointBaseline => aspis_core::two_point::TwoPointBatchingMode::OnePointBaseline,
            Self::FreshKappaSingleLane => {
                aspis_core::two_point::TwoPointBatchingMode::FreshKappaSingleLane
            }
            Self::TwoIndependentRelationLanes => {
                aspis_core::two_point::TwoPointBatchingMode::TwoIndependentRelationLanes
            }
            Self::DisjointGamma51SingleLane => {
                aspis_core::two_point::TwoPointBatchingMode::DisjointGamma51SingleLane
            }
        }
    }
}

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub enum AspisInstruction {
    /// Set the proof length header. Account must be pre-created with owner =
    /// this program and space >= 4 + total_len.
    InitProof { total_len: u32 },
    /// Copy `chunk` into the proof body at `offset`.
    UploadChunk { offset: u32, chunk: Vec<u8> },
    /// Verify the uploaded proof against `statement_digest` with the selected
    /// cached-domain and unit-circle-conjugate kernels.
    Verify { statement_digest: [u8; 32] },
    /// Diagnostic verifier run with CU markers in the simulation logs.
    VerifyProfile { statement_digest: [u8; 32] },
    /// Synthetic wide-row layout probe for the Stage 2 layout decision.
    LayoutProbe {
        log_rows: u8,
        columns: u16,
        query_count: u16,
        leaf_bytes: u16,
    },
    /// Known-answer transcript vector: recompute `aspis_core::transcript_kat`
    /// with the SHA-256 syscall backend and compare against the host-pinned
    /// digest supplied by the client. A mismatch is a host/SBF transcript
    /// divergence and errors loudly.
    TranscriptKat { expected: [u8; 32] },
    /// Verify a claim-carrying proof. The (z, v) evaluation claim is a public
    /// input (16-byte LE QM31 coordinates + value), transcript-absorbed and
    /// enforced by the interleaved relation sumcheck.
    VerifyWithClaim {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        claim_v: [u8; 16],
    },
    /// Pure-compute Stage 2 measurement. This runs the extension-field
    /// constraint composition in isolation and requires no accounts.
    ConstraintCompositionProbe {
        opened_values: u16,
        poseidon_sbox_terms: u16,
        poseidon_linear_terms: u16,
        logup_degree3_terms: u16,
        range_bit_terms: u16,
        eq_variables: u8,
        optimized: bool,
    },
    /// Pure-compute software Poseidon2-M31 permutation measurement.
    Poseidon2Probe { permutations: u16 },
    // Keep every variant above this line at its first-introduction wire tag
    // (0..=8). New diagnostics are append-only below.
    /// Compatibility alias for the optimized verifier.
    VerifyFast { statement_digest: [u8; 32] },
    /// Legacy batch-denominator verifier with `sol_big_mod_exp` supplying its
    /// one M31 inverse per round. Measurement-only comparison path.
    VerifySyscallInverse { statement_digest: [u8; 32] },
    /// The same permutation using lazy M31 linear layers and power-of-two
    /// shifts. Kept as a separate instruction so the SBF delta is literal.
    Poseidon2OptimizedProbe { permutations: u16 },
    /// Microbench reusable field kernels proposed for a `solmath-zk` crate.
    ZkKernelProbe { kind: ZkKernelKind, iterations: u16 },
    /// Correct wide-column gamma RLC probe. Kernel 0 is precomputed powers,
    /// 1 is a four-product lazy dot, 2 is per-query Horner, 3/4 pack four
    /// M31 columns into QM31, 5 packs pairs into CM31, 6 uses whole-dot u128
    /// accumulation, 7 lazily accumulates four-term block reductions, and 8
    /// specializes that winner to fixed stack-backed k=80 tables.
    WideRlcProbe {
        columns: u16,
        query_count: u16,
        kernel: u8,
    },
    /// Synthetic minimal-subtree traversal with current binary nodes or
    /// candidate radix-4 nodes. Leaf hashing is deliberately excluded.
    MerkleArityProbe {
        depth: u8,
        query_count: u16,
        arity: u8,
    },
    /// Pre-optimization software-batch denominator path; measurement only.
    VerifyLegacySoftware { statement_digest: [u8; 32] },
    /// Pure-compute probe for the fused statement-sumcheck verifier work
    /// that the synthetic 30,000-CU allowance stands in for: mu-batched
    /// zero claims, `rounds` transcript-absorbed degree-(coefficients-1)
    /// messages with boundary checks and Horner terminal evaluation, and
    /// block-periodic selector evaluation with enumerated exception rows.
    /// eq(r,z) and the composition C(v_1..v_k) are deliberately excluded:
    /// the constraint-composition probe already prices them.
    StatementSumcheckProbe {
        rounds: u8,
        coefficients: u8,
        claims: u8,
        selector_terms: u16,
        selector_exceptions: u8,
    },
    /// Host/SBF conformance check for the pinned LogUp tagged-tuple encoding.
    /// Appended to preserve every existing Borsh instruction discriminant.
    LogUpCompressionKat { expected_phi: [u8; 16] },
    /// Isolated A/B measurement for one versus two sequential per-round
    /// `(beta, y, mu)` OOD relation samples. The expected sink makes every
    /// relation-weight fold and terminal evaluation observable and doubles
    /// as a host/SBF conformance check. Measurement only; no proof format or
    /// production transcript schedule is selected by this instruction.
    OodSampleRelationProbe {
        samples_per_round: u8,
        expected_sink: [u8; 16],
    },
    /// V4/s=2 two-helper PCS-scaffold transcript known-answer vector. This is
    /// deliberately separate from tag 5 so the frozen v3 schedule remains
    /// independently testable. The final payment-v4 KAT is a later tag.
    TranscriptKatV4S2PcsScaffold { expected: [u8; 32] },
    /// Full payment-v4 transcript KAT, including the pre-gamma batching work
    /// record and the exact distinct-query tail.
    FinalPaymentTranscriptKatV4 { expected: [u8; 32] },
    /// Account-backed exact-wide arithmetic/hash diagnostic. The fixture is
    /// uploaded outside the measured transaction, avoiding generation-cost
    /// contamination. This is a measurement seam, not a proof verifier.
    ExactWideV4Diagnostic {
        mode: ExactWideV4DiagnosticMode,
        expected_sink: [u8; 32],
    },
    /// Diagnostic-only proof verifier for the reconciled exact-wide v4 PCS
    /// scaffold. It runs the real parser/Merkle/fold/final-check path but is
    /// isolated from production tag 6 until the final 102-value statement
    /// semantics exist.
    VerifyExactWideV4Scaffold {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        claim_v: [u8; 16],
    },
    /// Arithmetic/leaf-shape probe for an alternative circle-polynomial PCS
    /// with M31-valued C1 symbols. It deliberately does not reinterpret the
    /// current Aspis proof format and cannot authorize a payment.
    M31CircleBasisDiagnostic {
        mode: M31CircleBasisDiagnosticMode,
        expected_sink: [u8; 32],
    },
    /// Append-only wire allocation for the v4/s=2 M31-circle candidate.
    /// This slice validates only the diagnostic header and public-input
    /// framing, then rejects: no circle PCS verifier or payment path is
    /// enabled by allocating tag 24.
    VerifyM31CircleV4Diagnostic {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        statement_evaluations_digest: [u8; 32],
    },
    /// Pure-compute verifier-side comparison of four unselected two-point
    /// MLE batching shapes. It consumes embedded deterministic relation
    /// messages and cannot verify a proof or authorize a payment.
    TwoPointBatchingDiagnostic {
        mode: TwoPointBatchingDiagnosticMode,
        expected_sink: [u8; 16],
    },
    /// Selected fresh-kappa M31 circle-PCS verifier. This append-only
    /// diagnostic accepts the complete PCS fixture but performs no payment
    /// state transition.
    VerifyM31CircleFreshKappa {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
    },
    /// Literal q74/g32 measurement path. This is append-only and diagnostic:
    /// separate phase runs are reconciled by subtracting their repeated
    /// prefix/transcript/relation/Merkle/query-setup base.
    MeasureM31CircleJohnson {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        phase: JohnsonM31CircleDiagnosticPhase,
        start: u16,
        end: u16,
    },
    /// Rate-1/16 q36/g32 Johnson-query diagnostic. Same phase framing as tag
    /// 27, with larger evaluation/Merkle domains and no payment transition.
    MeasureM31CircleRate16 {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        phase: JohnsonM31CircleDiagnosticPhase,
        start: u16,
        end: u16,
    },
    /// Same-instruction pricing of the complete rate-1/16 PCS followed by
    /// the r2 payment-constraint composition kernel. `stress` selects 70
    /// rather than 38 linear terms. Opened-value RLC work is zero here because
    /// the preceding PCS query path already performed it.
    MeasureM31CircleRate16Composition {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        stress: bool,
    },
    /// Rate-1/16 q36/g36 Johnson candidate with transcript-bound work before
    /// all four fold challenges. Append-only measurement path; payment and
    /// state transition remain separate until the integrated spend tag.
    MeasureM31CircleRate16Hardened {
        statement_digest: [u8; 32],
        claim_z: Vec<[u8; 16]>,
        phase: JohnsonM31CircleDiagnosticPhase,
        start: u16,
        end: u16,
    },
    /// Exact verifier-side payment zerocheck and terminal composition over a
    /// pre-uploaded fixture. This prices the real 252-constraint registry and
    /// ten transcript rounds; it does not authenticate the 102 evaluations
    /// and therefore remains measurement-only.
    MeasurePaymentStatementV4,
    /// Pure-compute q36 placement comparison for the six-oracle payment
    /// hiding candidate. Placement 0 is one in-batch C2 tree; placement 1 is
    /// separate h1 and mask trees. The common aggregate fold relation is a
    /// separate measurement object.
    MeasurePaymentHidingPlacementV4 {
        placement: u8,
        expected_sink: [u8; 16],
    },
    /// Common mask-aggregate point/OOD/fold/query relation excluded from the
    /// placement A/B above. Measurement only.
    MeasurePaymentHidingAggregateRelationV4 { phase: u8, expected_sink: [u8; 16] },
    /// Complete profile-15 algebra/CU diagnostic over an uploaded proof.
    /// Nonce bytes are absorbed at their production positions but their PoW
    /// predicates are deliberately skipped; this tag cannot authorize state.
    MeasurePaymentHidingProfile15 {
        statement_digest: [u8; 32],
        public_input: [u8; 104],
        phase: JohnsonM31CircleDiagnosticPhase,
        start: u16,
        end: u16,
    },
    /// Append-only, production-neutral q36/depth12 same-index Merkle A/B.
    /// Arity 4 is the current parent primitive; arity 8 is the isolated
    /// candidate. `corrupt_frontier` selects a built-in one-bit mutation and
    /// succeeds only when the verifier rejects it.
    Radix8MerkleDepth12Probe { arity: u8, corrupt_frontier: bool },
    /// Append-only, production-neutral comparison of the current five
    /// independent radix-4 walks with the acceptance-equivalent staggered
    /// forest walk. `corrupt_lane=255` is the clean A/B; 0..=4 flips one
    /// built-in frontier byte and succeeds only when it is rejected.
    MerkleForestProbe { fused: bool, corrupt_lane: u8 },
    /// Append-only, production-neutral q36 layer-zero arithmetic probe.
    /// `columns` selects the current 49-column C1 control or hypothetical
    /// state-only widths 33/17/16. Every row performs four prepared-limb M31
    /// byte dots plus the same two QM31 C2 helper products. `corrupt=1/2`
    /// makes one C1/C2 coordinate noncanonical and succeeds only on reject.
    Layer0DotWidthProbe {
        columns: u8,
        corrupt: u8,
        expected_sink: [u8; 32],
    },
    /// Append-only tag 38 reserves the exact account/public-input framing for
    /// the one-instruction atomic payment transition. The transition kernel
    /// is implemented and tested, but this dispatch remains fail-closed until
    /// the state-only proof verifier can supply its complete verification
    /// closure. No existing measurement/proof tag can authorize state.
    AtomicPaymentStateTransitionV1 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 39. Complete width-28 state-only verifier over an
    /// uploaded proof. `diagnostic_unmined=true` bypasses only PoW acceptance
    /// and can never mutate accounts; false calls the production verifier.
    VerifyStateOnlyWidth28 {
        statement_digest: [u8; 32],
        public_input: [u8; 104],
        diagnostic_unmined: bool,
    },
    /// Append-only tag 40. Read-only segmented measurement of tag 39's exact
    /// parser/transcript/terminal/relation/opening/query implementations.
    MeasureStateOnlyWidth28 {
        statement_digest: [u8; 32],
        public_input: [u8; 104],
        phase: StateOnlyWidth28DiagnosticPhase,
    },
    /// Append-only tag 41. Isolated verifier-cost probe for the upstream
    /// HVZK-WHIR mask base case mapped to the state-only four-fold geometry.
    /// It has no accounts, parses no proof, and cannot authorize state.
    /// `scope=0/1/2` selects PCS-internal masks, the external degree-27
    /// zerocheck masks, or both. `mode=0` keeps the upstream one-fresh-tree
    /// per carried group; `mode=1` applies only timing-safe commitment and
    /// random-linear-identity batching within equal code shapes.
    /// `phase=0..=10` selects control, Merkle, scalar spot checks, the
    /// batched spot-check kernel, dedicated PoW, the target identity, or
    /// transcript absorption. Query ranges partition phases that can exceed
    /// the transaction CU ceiling.
    HvzkWhirMaskProbe {
        mask_log_inv_rate: u8,
        mask_queries: u8,
        scope: u8,
        mode: u8,
        phase: u8,
        start: u8,
        end: u8,
    },
    /// Append-only tag 42. Isolated A/B of the sound atomic-v3 copy lane's
    /// legacy rank-103 row partition and exact rank-74 repartition. It has no
    /// accounts, changes no statement or proof bytes, and cannot mutate state.
    AtomicRoutingPartitionProbe {
        optimized: bool,
        seed: u32,
        expected_sink: [u8; 16],
    },
    /// Append-only tag 43. Read-only profile-20 cost candidate which replaces
    /// the old terminal with the complete atomic-v3 terminal and runs the
    /// unchanged relation/openings/query tail once. The expected terminal is
    /// diagnostic input until an atomic prover and hiding-rank repin exist;
    /// this tag has no mutation path and cannot authorize state.
    AtomicStateOnlyProfile20CostCandidate {
        statement_digest: [u8; 32],
        public_input: [u8; 104],
        output_anchor: [u8; 32],
        expected_atomic_terminal: [u8; 16],
    },
    /// Append-only tag 44. Read-only exact A/B of profile 20's relation
    /// accumulator. The optimized arm defers the fixed binary inactive-copy
    /// covector's first fold and evaluates both low folds with nine shared
    /// cross-products. `corrupt_claim` requires rejection after perturbing a
    /// prepared claim. No accounts are writable and no state can mutate.
    StateOnlyRelationStructuralProbe {
        statement_digest: [u8; 32],
        deferred_binary_copy: bool,
        corrupt_claim: bool,
    },
    /// Append-only tag 45. Read-only profile-21 masked-switch PCS diagnostic.
    /// It verifies the dedicated pre-delta X/F root, positioned source and
    /// final work witnesses, disclosed U coefficients, two post-root OOD
    /// evaluations, both radix-four q16 multiproofs, and the affine query
    /// equations. It is not a state-transition acceptance path.
    StateOnlyMaskedSwitchProfile21Probe {
        statement_digest: [u8; 32],
        diagnostic_unmined: bool,
        direct_u_query_evaluation: bool,
    },
    /// Append-only tag 46. Acceptance-complete, read-only atomic-v3
    /// profile-20 verifier over the proof's own masked terminal, relation,
    /// openings, and all q16 queries. `diagnostic_unmined` bypasses only the
    /// PoW acceptance predicate; the nonce remains transcript-bound. This
    /// instruction has no writable accounts and cannot mutate pool state.
    VerifyAtomicStateOnlyProfile20V3 {
        pool: [u8; 32],
        sequence: u64,
        public_input: [u8; 104],
        output_anchor: [u8; 32],
        diagnostic_unmined: bool,
    },
    /// Append-only tag 47. Exact production-PoW atomic profile-20 mutation
    /// candidate. There is deliberately no diagnostic/unmined flag. Default
    /// builds keep it fail-closed while profile-21 complete-view hiding is
    /// open; the nondefault candidate arm calls the no-bypass verifier before
    /// the first CPI or account write.
    ApplyAtomicStateOnlyProfile20V3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 48. Local-validator CU diagnostic for tag 47's exact
    /// account-transition kernel using the transcript-bound unmined fixture.
    /// The dispatch arm is absent from default/production SBF builds and
    /// returns fail-closed unless `diagnostic-unmined-mutation` is compiled.
    MeasureAtomicStateOnlyProfile20MutationV3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 49. Read-only SHA-256 leaf-rehash A/B for profile 21.
    /// Modes 0/1 compare the existing 128-byte C2 leaf with the shared-root
    /// 256-byte C2 leaf. Modes 2/3 compare all five q16 opened-leaf sets
    /// without/with one contiguous 32-byte private-Merkle salt per logical
    /// leaf. It has no accounts and cannot authorize or mutate state.
    StateOnlyPrivateMerkleSaltProbe { mode: u8, expected_sink: [u8; 32] },
    /// Append-only tag 50. Final integrated profile-21 atomic wrapper over the
    /// shared X/F C2 root, private-Merkle salted openings, translated splice,
    /// and literal logical-U q16 evaluation. Default builds remain fail-closed.
    /// The diagnostic arm is read-only; no tag-50 variant can mutate state.
    VerifyAtomicStateOnlyProfile21V3 {
        pool: [u8; 32],
        sequence: u64,
        public_input: [u8; 104],
        output_anchor: [u8; 32],
        diagnostic_unmined: bool,
    },
    /// Append-only tag 51. Exact production-PoW profile-21 mutation wrapper.
    /// There is deliberately no diagnostic flag in this wire shape. Default
    /// builds remain fail-closed until the independent soundness and
    /// complete-view HVZK gates are green and a production nonce is mined.
    ApplyAtomicStateOnlyProfile21V3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 52. Local-validator CU diagnostic for tag 51's exact
    /// account-transition kernel. Its nondefault build reuses the tag-50
    /// parser/verifier and bypasses only the transcript-bound PoW predicate.
    MeasureAtomicStateOnlyProfile21MutationV3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 53. Read-only q16-equivalent arithmetic A/B for the
    /// current width-28 layer-zero word. Both arms execute the same 26-column
    /// C1 byte dot and two QM31 helper products for sixteen varied fibers;
    /// `fused_helpers` selects the exact lazy two-product accumulator.
    /// `corrupt` requires canonical-decoding rejection. No accounts or proof
    /// semantics are present and this instruction cannot authorize state.
    StateOnlyHelperDot2Probe {
        fused_helpers: bool,
        corrupt: u8,
        expected_sink: [u8; 32],
    },
    /// Append-only tag 54. Read-only q16-equivalent arithmetic A/B for the
    /// pending three-QM31-lane main RLC shape. Both arms canonically decode
    /// the same 16 four-slot, three-lane fibers; `fused_helpers` selects one
    /// exact prepared dot3 instead of three independently reduced products.
    /// No accounts or proof semantics are present and this instruction cannot
    /// authorize state.
    StateOnlyHelperDot3Probe {
        fused_helpers: bool,
        corrupt: u8,
        expected_sink: [u8; 32],
    },
    /// Append-only tag 55. Read-only q16 four-round fold A/B. Both arms
    /// canonically decode the same fibers and evaluate the same normalized
    /// cubic fold polynomial; `polynomial_basis` selects one lazy prepared
    /// dot3 over its alpha/alpha^2/alpha^3 coefficients. No accounts or state.
    StateOnlyFoldPolynomialProbe {
        polynomial_basis: bool,
        corrupt: u8,
        expected_sink: [u8; 32],
    },
    /// Append-only tag 56. Complete read-only profile-22 verifier: the
    /// profile-20 atomic relation and q16 PCS equations with all five Merkle
    /// trees privately salted. The diagnostic selector bypasses only PoW and
    /// cannot mutate state. Default builds remain fail-closed.
    VerifyAtomicStateOnlyProfile22V3 {
        pool: [u8; 32],
        sequence: u64,
        public_input: [u8; 104],
        output_anchor: [u8; 32],
        diagnostic_unmined: bool,
    },
    /// Append-only tag 57. Production-PoW profile-22 atomic mutation wrapper.
    /// Its wire has no diagnostic selector; the verifier completes before the
    /// first CPI or state write. Default builds remain fail-closed.
    ApplyAtomicStateOnlyProfile22V3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 58. Local-validator mutation-cost path. Its nondefault
    /// build reuses tag 56's exact parser and bypasses only transcript-bound
    /// PoW; no production build contains the bypassing dispatch arm.
    MeasureAtomicStateOnlyProfile22MutationV3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 59. Complete read-only Profile23 H26/G27/D28
    /// verifier. The diagnostic selector bypasses only PoW in an explicitly
    /// nondefault build; default binaries reject before proof interpretation.
    VerifyAtomicStateOnlyProfile23V3 {
        pool: [u8; 32],
        sequence: u64,
        public_input: [u8; 104],
        output_anchor: [u8; 32],
        diagnostic_unmined: bool,
    },
    /// Append-only tag 60. Production-PoW Profile23 mutation wrapper. This
    /// remains feature-gated and has no unmined selector on its wire.
    ApplyAtomicStateOnlyProfile23V3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 61. Local-validator-only mutation measurement that
    /// reuses tag 59's parser and bypasses transcript PoW only.
    MeasureAtomicStateOnlyProfile23MutationV3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 62. Irreversibly seals an uploaded proof account by
    /// replacing its upload-authority field with the all-zero sentinel.
    /// Production Profile23 tags 59/60 accept only sealed accounts.
    FinalizeProof,
    /// Append-only tag 63. Initializes a newly created, program-owned pool
    /// account. The pool key must sign, the exact 48-byte account must still
    /// be all zero, and the initial anchor must be canonically encoded.
    InitializeAtomicPool { sequence: u64, anchor: [u8; 32] },
}

fn trace_payment_hiding_profile15_cu(
    event: aspis_core::circle_hiding_verify::PaymentHidingTraceEvent,
) {
    use aspis_core::circle_hiding_verify::PaymentHidingTraceEvent;
    match event {
        PaymentHidingTraceEvent::Parsed => msg!("aspis-cu:h15_parsed"),
        PaymentHidingTraceEvent::TranscriptDone => msg!("aspis-cu:h15_transcript_done"),
        PaymentHidingTraceEvent::RelationDone => msg!("aspis-cu:h15_relation_done"),
        PaymentHidingTraceEvent::MerkleDone => msg!("aspis-cu:h15_merkle_done"),
        PaymentHidingTraceEvent::QueriesDone => msg!("aspis-cu:h15_queries_done"),
    }
    sol_log_compute_units();
}

fn trace_payment_hiding_statement_cu(event: u8) {
    msg!("aspis-cu:h15_statement_phase={}", event);
    sol_log_compute_units();
}

fn run_payment_hiding_placement_v4(placement: u8, expected_sink: [u8; 16]) -> ProgramResult {
    let placement = match placement {
        0 => aspis_core::statement_hiding::PaymentHidingPlacement::InBatch,
        1 => aspis_core::statement_hiding::PaymentHidingPlacement::SeparateCommitment,
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    let result = aspis_core::statement_hiding::payment_hiding_placement_probe(sbf_hashv, placement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let mut actual = [0u8; 16];
    result.write_le_bytes(&mut actual);
    if actual == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

fn run_payment_hiding_aggregate_relation_v4(phase: u8, expected_sink: [u8; 16]) -> ProgramResult {
    let phase = match phase {
        0 => aspis_core::statement_hiding::PaymentHidingAggregatePhase::EmptyControl,
        1 => aspis_core::statement_hiding::PaymentHidingAggregatePhase::Relation,
        2 => aspis_core::statement_hiding::PaymentHidingAggregatePhase::Layer0,
        3 => aspis_core::statement_hiding::PaymentHidingAggregatePhase::LaterFolds,
        4 => aspis_core::statement_hiding::PaymentHidingAggregatePhase::LaterMerkle,
        5 => aspis_core::statement_hiding::PaymentHidingAggregatePhase::Full,
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    let result = aspis_core::statement_hiding::payment_hiding_aggregate_relation_probe_phase(
        sbf_hashv, phase,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    let mut actual = [0u8; 16];
    result.write_le_bytes(&mut actual);
    if actual == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

fn run_ood_sample_relation_probe(samples_per_round: u8, expected_sink: [u8; 16]) -> ProgramResult {
    if samples_per_round != 1 && samples_per_round != 2 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let value = aspis_core::verify::ood_sample_relation_probe(sbf_hashv, samples_per_round)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let mut actual_sink = [0u8; 16];
    value.write_le_bytes(&mut actual_sink);
    if actual_sink == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

fn run_two_point_batching_diagnostic(
    mode: TwoPointBatchingDiagnosticMode,
    expected_sink: [u8; 16],
) -> ProgramResult {
    if expected_sink != aspis_core::two_point::TWO_POINT_BATCHING_EXPECTED_SINKS[mode.index()] {
        return Err(ProgramError::InvalidInstructionData);
    }
    let result = aspis_core::two_point::two_point_batching_probe(sbf_hashv, mode.core_mode())
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let mut actual_sink = [0u8; 16];
    result.sink.write_le_bytes(&mut actual_sink);
    if actual_sink == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

fn run_poseidon2_probe(permutations: u16, optimized: bool) -> ProgramResult {
    if permutations > 128 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut state = core::array::from_fn(|index| aspis_core::field::M31(index as u32 + 1));
    for iteration in 0..permutations {
        state[0] = state[0].add(aspis_core::field::M31(iteration as u32 + 1));
        if optimized {
            aspis_statement::poseidon2::permute_optimized(&mut state);
        } else {
            aspis_statement::poseidon2::permute(&mut state);
        }
    }
    // The branch makes the computed state observable to the optimizer. The
    // old `permutations == u16::MAX` conjunction was unreachable after the
    // 128-round input bound and therefore did not keep the probe work live.
    if state[0] == aspis_core::field::M31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

fn run_constraint_composition_probe(
    probe: aspis_statement::CompositionProbe,
    optimized: bool,
) -> ProgramResult {
    if probe.opened_values > 256
        || probe.poseidon_sbox_terms > 256
        || probe.poseidon_linear_terms > 512
        || probe.logup_degree3_terms > 8
        || probe.range_bit_terms > 256
        || probe.eq_variables > 24
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let result = if optimized {
        aspis_statement::evaluate_composition_probe_optimized(probe)
    } else {
        aspis_statement::evaluate_composition_probe(probe)
    };
    // Keep the dynamic computation observably live without adding a hash or
    // log call to the isolated field-arithmetic measurement. Branch directly
    // on the accumulator; the old u32::MAX counter conjunction was
    // unreachable under the validated term bounds.
    if result.accumulator == aspis_core::field::QM31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

#[allow(unexpected_cfgs)]
#[inline(always)]
fn m31_inverse_syscall(value: aspis_core::field::M31) -> aspis_core::field::M31 {
    #[cfg(target_os = "solana")]
    {
        #[repr(C)]
        struct BigModExpParams {
            base: *const u8,
            base_len: u64,
            exponent: *const u8,
            exponent_len: u64,
            modulus: *const u8,
            modulus_len: u64,
        }

        let base = value.0.to_be_bytes();
        let exponent = (aspis_core::field::P - 2).to_be_bytes();
        let modulus = aspis_core::field::P.to_be_bytes();
        let mut output = [0u8; 4];
        let params = BigModExpParams {
            base: base.as_ptr(),
            base_len: base.len() as u64,
            exponent: exponent.as_ptr(),
            exponent_len: exponent.len() as u64,
            modulus: modulus.as_ptr(),
            modulus_len: modulus.len() as u64,
        };
        #[allow(deprecated)]
        unsafe {
            solana_program::syscalls::sol_big_mod_exp(
                &params as *const _ as *const u8,
                output.as_mut_ptr(),
            );
        }
        aspis_core::field::M31(u32::from_be_bytes(output))
    }
    #[cfg(not(target_os = "solana"))]
    {
        value.inv()
    }
}

fn run_zk_kernel_probe(kind: ZkKernelKind, iterations: u16) -> ProgramResult {
    use aspis_core::field::{CM31, M31, QM31};

    if iterations > 8_192 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut scalar = M31(17);
    let mut extension = QM31 {
        c0: CM31::new(M31(3), M31(5)),
        c1: CM31::new(M31(7), M31(11)),
    };
    let mut chain_anchor = [0x42u8; 32];
    let chain_leaf = core::array::from_fn(|index| M31(101 + index as u32 * 17));
    for iteration in 0..iterations {
        let step = M31(1 + iteration as u32 % 1_000);
        match kind {
            ZkKernelKind::M31InverseSoftware => {
                scalar = scalar.add(step).inv();
            }
            ZkKernelKind::M31InverseSyscall => {
                scalar = m31_inverse_syscall(scalar.add(step));
            }
            ZkKernelKind::Qm31SquareGeneric => {
                extension.c0.a = extension.c0.a.add(step);
                extension = extension.mul(extension);
                scalar = scalar.add(extension.c0.a);
            }
            ZkKernelKind::Qm31SquareSpecialized => {
                extension.c0.a = extension.c0.a.add(step);
                extension = extension.square();
                scalar = scalar.add(extension.c0.a);
            }
            ZkKernelKind::M31Pow2Generic => {
                let shift = (iteration % 17) as u8;
                scalar = scalar.add(step).mul(M31(1u32 << shift));
            }
            ZkKernelKind::M31Pow2Shift => {
                let shift = (iteration % 17) as u8;
                scalar = scalar.add(step).mul_pow2(shift);
            }
            ZkKernelKind::Sha256AppendChain => {
                chain_anchor = aspis_statement::atomic_append_chain_anchor(
                    &chain_anchor,
                    &chain_leaf,
                    u64::from(iteration),
                    sbf_hashv,
                );
                scalar = scalar.add(M31::reduce_u64(u64::from(u32::from_le_bytes(
                    chain_anchor[..4].try_into().unwrap(),
                ))));
            }
        }
    }
    if scalar == M31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

fn run_wide_rlc_probe(columns: u16, query_count: u16, kernel: u8) -> ProgramResult {
    use aspis_core::field::{
        qm31_cm31_dot, qm31_dot, qm31_m31_dot, qm31_m31_dot_eager_outer, qm31_m31_dot_u128, CM31,
        M31, QM31,
    };

    if columns == 0
        || columns > 256
        || query_count > 64
        || kernel > 13
        || (kernel == 8 && columns != 80)
        || (kernel == 9 && columns != 84)
        || (kernel == 10 && columns != 67)
        || (kernel == 11 && columns != 65)
        || (kernel == 12 && columns != 51)
        || (kernel == 13 && columns != 49)
        || ((kernel == 3 || kernel == 4) && columns & 3 != 0)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let gamma = QM31 {
        c0: CM31::new(M31(7), M31(11)),
        c1: CM31::new(M31(13), M31(17)),
    };
    // Fixed-width variants of the winning outer-lazy kernel: 80 is the
    // historical k80 candidate, 84 the k'<=84 pin, 67/51 the r=3 and r=2
    // rounds-per-row layout candidates, and 65/49 those layouts under
    // LogUp-GKR (no committed helper columns).
    match kernel {
        8 => return run_wide_rlc_fixed::<80>(query_count, gamma),
        9 => return run_wide_rlc_fixed::<84>(query_count, gamma),
        10 => return run_wide_rlc_fixed::<67>(query_count, gamma),
        11 => return run_wide_rlc_fixed::<65>(query_count, gamma),
        12 => return run_wide_rlc_fixed::<51>(query_count, gamma),
        13 => return run_wide_rlc_fixed::<49>(query_count, gamma),
        _ => {}
    }
    let coefficient_count = if kernel == 5 {
        columns / 2
    } else if kernel == 3 || kernel == 4 {
        columns / 4
    } else {
        columns
    };
    let mut powers = Vec::with_capacity(coefficient_count as usize);
    if kernel != 2 {
        let mut power = QM31::ONE;
        for _ in 0..coefficient_count {
            powers.push(power);
            power = power.mul(gamma);
        }
    }
    let mut values = Vec::with_capacity(columns as usize);
    let mut packed_values = Vec::with_capacity((columns / 4) as usize);
    let mut paired_values = Vec::with_capacity((columns / 2) as usize);
    let mut sink = QM31::ONE;
    for query in 0..query_count {
        values.clear();
        for column in 0..columns {
            let seed = 1 + (query as u32 * 131 + column as u32 * 17) % 1_000_000;
            values.push(M31(seed));
        }
        if kernel == 5 {
            paired_values.clear();
            for chunk in values.chunks_exact(2) {
                paired_values.push(CM31::new(chunk[0], chunk[1]));
            }
        } else if kernel == 3 || kernel == 4 {
            packed_values.clear();
            for chunk in values.chunks_exact(4) {
                packed_values.push(QM31 {
                    c0: CM31::new(chunk[0], chunk[1]),
                    c1: CM31::new(chunk[2], chunk[3]),
                });
            }
        }
        let rlc = match kernel {
            0 => powers
                .iter()
                .zip(&values)
                .fold(QM31::ZERO, |sum, (power, value)| {
                    sum.add(power.mul_m31(*value))
                }),
            1 => qm31_m31_dot_eager_outer(&powers, &values),
            2 => values.iter().rev().fold(QM31::ZERO, |accumulator, value| {
                accumulator
                    .mul(gamma)
                    .add(QM31::from_cm31(CM31::from_m31(*value)))
            }),
            3 => qm31_dot(&powers, &packed_values),
            4 => powers
                .iter()
                .zip(&packed_values)
                .fold(QM31::ZERO, |sum, (power, value)| sum.add(power.mul(*value))),
            5 => qm31_cm31_dot(&powers, &paired_values),
            6 => qm31_m31_dot_u128(&powers, &values),
            7 => qm31_m31_dot(&powers, &values),
            _ => unreachable!(),
        };
        sink = sink.add(rlc);
    }
    if sink == QM31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

#[inline(never)]
fn run_wide_rlc_fixed<const N: usize>(
    query_count: u16,
    gamma: aspis_core::field::QM31,
) -> ProgramResult {
    use aspis_core::field::{qm31_m31_dot, qm31_power_table, M31, QM31};

    let powers = qm31_power_table::<N>(gamma);
    let mut values = [M31::ZERO; N];
    let mut sink = QM31::ONE;
    for query in 0..query_count {
        for (column, value) in values.iter_mut().enumerate() {
            let seed = 1 + (query as u32 * 131 + column as u32 * 17) % 1_000_000;
            *value = M31(seed);
        }
        sink = sink.add(qm31_m31_dot(&powers, &values));
    }
    if sink == QM31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

fn run_statement_sumcheck_probe(
    rounds: u8,
    coefficients: u8,
    claims: u8,
    selector_terms: u16,
    selector_exceptions: u8,
) -> ProgramResult {
    use aspis_core::field::{CM31, M31, QM31};
    use aspis_core::transcript::{label, Transcript};

    if rounds > 32
        || coefficients == 0
        || coefficients > 32
        || claims > 8
        || selector_terms > 256
        || selector_exceptions > 32
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let sample = |index: u32, lane: u32| -> QM31 {
        let value = |offset: u32| M31(1 + index.wrapping_mul(131).wrapping_add(offset) % 1_000_003);
        QM31 {
            c0: CM31 {
                a: value(lane * 17),
                b: value(lane * 17 + 3),
            },
            c1: CM31 {
                a: value(lane * 17 + 7),
                b: value(lane * 17 + 11),
            },
        }
    };

    let mut transcript = Transcript::new(sbf_hashv);
    transcript.absorb(label::STATEMENT, &[0x5a; 32]);

    // mu-batch the zero claims (zerocheck plus the sum(h)=0 claims).
    let mut claim_bytes = [0u8; 16];
    for claim in 0..claims {
        sample(claim as u32, 1).write_le_bytes(&mut claim_bytes);
        transcript.absorb(label::CLAIM, &claim_bytes);
    }
    let mu = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let mut mu_power = QM31::ONE;
    let mut running_claim = QM31::ZERO;
    for claim in 0..claims {
        running_claim = running_claim.add(mu_power.mul(sample(claim as u32, 1)));
        mu_power = mu_power.mul(mu);
    }

    let mut sink = QM31::ONE;
    let mut round_bytes = [0u8; 16 * 32];
    let mut challenges = [QM31::ZERO; 32];
    for round in 0..rounds {
        let coefficient = |j: u8| sample(u32::from(round) * 32 + u32::from(j), 2);
        for j in 0..coefficients {
            coefficient(j).write_le_bytes(&mut round_bytes[usize::from(j) * 16..][..16]);
        }
        transcript.absorb(
            label::SUMCHECK_POLY,
            &round_bytes[..usize::from(coefficients) * 16],
        );
        // Boundary p(0) + p(1) against the running claim; the probe folds
        // the residual into the sink instead of enforcing it.
        let mut p1 = QM31::ZERO;
        for j in 0..coefficients {
            p1 = p1.add(coefficient(j));
        }
        sink = sink.add(coefficient(0).add(p1).sub(running_claim));
        let challenge = transcript
            .challenge_qm31()
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        challenges[usize::from(round)] = challenge;
        let mut value = QM31::ZERO;
        for j in (0..coefficients).rev() {
            value = value.mul(challenge).add(coefficient(j));
        }
        running_claim = value;
    }

    // Block-periodic selector at the terminal point plus enumerated
    // exception rows corrected with eq(row_i, r) factors.
    let mut selector = QM31::ZERO;
    for term in 0..selector_terms {
        selector = selector.add(sample(u32::from(term), 3).mul(sample(u32::from(term) + 7, 4)));
    }
    for exception in 0..selector_exceptions {
        let mut eq = QM31::ONE;
        for round in 0..rounds {
            let challenge = challenges[usize::from(round)];
            let bit = (u32::from(exception) >> (u32::from(round) % 30)) & 1 == 1;
            let factor = if bit {
                challenge
            } else {
                QM31::ONE.sub(challenge)
            };
            eq = eq.mul(factor);
        }
        selector = selector.add(eq);
    }
    sink = sink.add(selector.mul(running_claim));

    if sink == QM31::ZERO {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

fn payment_terminal_trace(event: u8) {
    msg!("aspis-payment-phase:{}", event);
    sol_log_compute_units();
}

fn payment_pre_trace(event: u8) {
    msg!("aspis-payment-pre:{}", event);
    sol_log_compute_units();
}

#[inline(never)]
fn measure_uploaded_payment_statement_v4(proof_account: &AccountInfo) -> ProgramResult {
    use aspis_core::circle_prefix::{
        encode_payment_statement_points, RATE16_PAYMENT_CANDIDATE_SHAPE,
    };
    use aspis_core::field::{M31, QM31};
    use aspis_core::proof::{Header, HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR};
    use aspis_core::statement_sumcheck::{
        begin_payment_zerocheck, decode_wire, verify_payment_sumcheck_messages,
        PAYMENT_SUMCHECK_BYTES, PAYMENT_SUMCHECK_ROUNDS, PAYMENT_SUMCHECK_ROUND_BYTES,
        PAYMENT_SUMCHECK_WIRE_COEFFICIENTS,
    };
    use aspis_core::transcript::{label, Transcript};
    use aspis_statement::{payment_terminal_value_with_trace, PointOpeningsV4, SpendPublic};

    payment_pre_trace(0);
    const MAGIC: &[u8; 4] = b"APST";
    const VERSION: u8 = 1;
    const PUBLIC_M31_VALUES: usize = 8 * 3 + 1;
    const PUBLIC_BYTES: usize = PUBLIC_M31_VALUES * 4 + 4;
    const EVALUATION_BYTES: usize = 102 * 16;
    const FIXTURE_BYTES: usize = 4
        + 1
        + HEADER_LEN
        + 32
        + 32
        + 32
        + PUBLIC_BYTES
        + PAYMENT_SUMCHECK_BYTES
        + EVALUATION_BYTES;

    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    if total_len != FIXTURE_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let end = PROOF_ACCOUNT_HEADER_LEN + total_len;
    let fixture = data
        .get(PROOF_ACCOUNT_HEADER_LEN..end)
        .ok_or(ProgramError::InvalidAccountData)?;
    let mut cursor = 0usize;
    let take = |cursor: &mut usize, len: usize| -> Result<&[u8], ProgramError> {
        let start = *cursor;
        *cursor = cursor
            .checked_add(len)
            .ok_or(ProgramError::InvalidAccountData)?;
        fixture
            .get(start..*cursor)
            .ok_or(ProgramError::InvalidAccountData)
    };
    if take(&mut cursor, 4)? != MAGIC || take(&mut cursor, 1)?[0] != VERSION {
        return Err(ProgramError::InvalidAccountData);
    }
    let header_bytes: &[u8; HEADER_LEN] = take(&mut cursor, HEADER_LEN)?.try_into().unwrap();
    let header = Header::parse(header_bytes).ok_or(ProgramError::InvalidAccountData)?;
    if header.profile_id != RATE16_PAYMENT_CANDIDATE_SHAPE.profile_id
        || header.log_rows != 10
        || header.log_blowup != RATE16_PAYMENT_CANDIDATE_SHAPE.log_blowup
        || header.query_count != RATE16_PAYMENT_CANDIDATE_SHAPE.query_count
        || header.grinding_bits != RATE16_PAYMENT_CANDIDATE_SHAPE.grinding_bits
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let statement_digest: &[u8; 32] = take(&mut cursor, 32)?.try_into().unwrap();
    let c1_root: &[u8; 32] = take(&mut cursor, 32)?.try_into().unwrap();
    let c2_root: &[u8; 32] = take(&mut cursor, 32)?.try_into().unwrap();
    let public_bytes = take(&mut cursor, PUBLIC_BYTES)?;
    let mut public_values = [M31::ZERO; PUBLIC_M31_VALUES];
    for (index, output) in public_values.iter_mut().enumerate() {
        *output = M31::from_le_bytes(public_bytes[index * 4..index * 4 + 4].try_into().unwrap())
            .ok_or(ProgramError::InvalidInstructionData)?;
    }
    let fee = u32::from_le_bytes(public_bytes[PUBLIC_M31_VALUES * 4..].try_into().unwrap());
    let public = SpendPublic {
        anchor: public_values[0..8].try_into().unwrap(),
        nullifier: public_values[8..16].try_into().unwrap(),
        output_commitment: public_values[16..24].try_into().unwrap(),
        asset_id: public_values[24],
        fee,
    };
    let sumcheck_bytes = take(&mut cursor, PAYMENT_SUMCHECK_BYTES)?;
    let mut messages =
        Box::new([[QM31::ZERO; PAYMENT_SUMCHECK_WIRE_COEFFICIENTS]; PAYMENT_SUMCHECK_ROUNDS]);
    for (round, message) in messages.iter_mut().enumerate() {
        let start = round * PAYMENT_SUMCHECK_ROUND_BYTES;
        *message = decode_wire(&sumcheck_bytes[start..start + PAYMENT_SUMCHECK_ROUND_BYTES])
            .ok_or(ProgramError::InvalidInstructionData)?;
    }
    let evaluation_bytes = take(&mut cursor, EVALUATION_BYTES)?;
    if cursor != FIXTURE_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let mut values = Box::new([QM31::ZERO; 102]);
    for (index, output) in values.iter_mut().enumerate() {
        *output = QM31::from_le_bytes(&evaluation_bytes[index * 16..index * 16 + 16])
            .ok_or(ProgramError::InvalidInstructionData)?;
    }
    payment_pre_trace(1);

    let mut transcript = Transcript::new(sbf_hashv);
    transcript.absorb(label::PROFILE, header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);
    let mut root_record = [0u8; 33];
    root_record[1..].copy_from_slice(c1_root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &root_record);
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, c2_root);
    let batching = begin_payment_zerocheck(&mut transcript)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    payment_pre_trace(2);
    let verified = verify_payment_sumcheck_messages(&mut transcript, &messages)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    payment_pre_trace(3);
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_POINTS,
        &encode_payment_statement_points(&verified.point),
    );
    transcript.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, evaluation_bytes);
    let _gamma = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    payment_pre_trace(4);

    let openings = Box::new(PointOpeningsV4 {
        c1: core::array::from_fn(|column| values[column]),
        c1_xor11: core::array::from_fn(|column| values[51 + column]),
        c2: [values[49], values[50]],
    });
    payment_pre_trace(5);
    let terminal = payment_terminal_value_with_trace(
        &public,
        &openings,
        &verified.point,
        &batching,
        lambda,
        chi,
        Some(payment_terminal_trace),
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    sol_log_compute_units();
    if terminal != verified.terminal_claim {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}

fn run_merkle_arity_probe(depth: u8, query_count: u16, arity: u8) -> ProgramResult {
    if depth == 0
        || depth > 16
        || query_count == 0
        || query_count > 64
        || (arity != 2 && arity != 4)
        || (arity == 4 && depth & 1 != 0)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mask = (1u32 << depth) - 1;
    let mut level = Vec::with_capacity(query_count as usize);
    for query in 0..query_count {
        let index = (query as u32)
            .wrapping_mul(0x9e37_79b9)
            .wrapping_add(0x7f4a_7c15)
            & mask;
        let mut value = [0u8; 32];
        value[0..4].copy_from_slice(&index.to_le_bytes());
        level.push((index, value));
    }
    level.sort_unstable_by_key(|entry| entry.0);
    level.dedup_by_key(|entry| entry.0);
    let mut next = Vec::with_capacity(level.len());
    if arity == 2 {
        for _ in 0..depth {
            next.clear();
            let mut position = 0usize;
            while position < level.len() {
                let (index, hash) = level[position];
                let parent = if index & 1 == 0
                    && position + 1 < level.len()
                    && level[position + 1].0 == index + 1
                {
                    let parent =
                        aspis_core::merkle::node_hash(sbf_hashv, &hash, &level[position + 1].1);
                    position += 2;
                    parent
                } else {
                    let sibling = [0u8; 32];
                    position += 1;
                    if index & 1 == 0 {
                        aspis_core::merkle::node_hash(sbf_hashv, &hash, &sibling)
                    } else {
                        aspis_core::merkle::node_hash(sbf_hashv, &sibling, &hash)
                    }
                };
                next.push((index >> 1, parent));
            }
            core::mem::swap(&mut level, &mut next);
        }
    } else {
        for _ in 0..depth / 2 {
            next.clear();
            let mut position = 0usize;
            while position < level.len() {
                let parent_index = level[position].0 >> 2;
                let mut children = [[0u8; 32]; 4];
                while position < level.len() && level[position].0 >> 2 == parent_index {
                    let slot = (level[position].0 & 3) as usize;
                    children[slot] = level[position].1;
                    position += 1;
                }
                let mut input = [0u8; 129];
                input[0] = 0x12;
                for (slot, child) in children.iter().enumerate() {
                    input[1 + slot * 32..1 + (slot + 1) * 32].copy_from_slice(child);
                }
                next.push((parent_index, sbf_hashv(&[&input])));
            }
            core::mem::swap(&mut level, &mut next);
        }
    }
    if level.len() == 1 && level[0].1 != [0u8; 32] {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

#[inline(always)]
fn hvzk_probe_qm31(tag: u32) -> aspis_core::field::QM31 {
    use aspis_core::field::{CM31, M31, P, QM31};
    let limb = |offset: u32| M31(tag.wrapping_mul(65_537).wrapping_add(offset) % P);
    QM31 {
        c0: CM31::new(limb(1), limb(17)),
        c1: CM31::new(limb(257), limb(4_099)),
    }
}

fn hvzk_probe_depth(message_len: usize, queries: usize, log_inv_rate: usize) -> u32 {
    (message_len + queries).next_power_of_two().ilog2() + log_inv_rate as u32
}

fn hvzk_probe_tree_sink(depth: u32, queries: usize, width: usize, tree_tag: u8) -> [u8; 32] {
    let mask = (1u32 << depth) - 1;
    let mut level = Vec::with_capacity(queries);
    let mut leaf = vec![0u8; width * 16];
    for query in 0..queries {
        let index = (query as u32)
            .wrapping_mul(0x9e37_79b9)
            .wrapping_add(0x7f4a_7c15)
            & mask;
        for (byte, dst) in leaf.iter_mut().enumerate() {
            *dst = (index as u8)
                .wrapping_add(tree_tag)
                .wrapping_add(byte as u8);
        }
        let digest = aspis_core::merkle::leaf_hash(sbf_hashv, tree_tag, &leaf);
        level.push((index, digest));
    }
    level.sort_unstable_by_key(|entry| entry.0);
    level.dedup_by_key(|entry| entry.0);
    let mut next = Vec::with_capacity(level.len());
    for _ in 0..depth / 2 {
        next.clear();
        let mut position = 0usize;
        while position < level.len() {
            let parent_index = level[position].0 >> 2;
            let mut children = [[0u8; 32]; 4];
            while position < level.len() && level[position].0 >> 2 == parent_index {
                children[(level[position].0 & 3) as usize] = level[position].1;
                position += 1;
            }
            next.push((
                parent_index,
                aspis_core::merkle::node_hash4(sbf_hashv, &children),
            ));
        }
        core::mem::swap(&mut level, &mut next);
    }
    if depth & 1 != 0 {
        next.clear();
        let mut position = 0usize;
        while position < level.len() {
            let (index, digest) = level[position];
            let parent = if index & 1 == 0
                && position + 1 < level.len()
                && level[position + 1].0 == index + 1
            {
                let parent =
                    aspis_core::merkle::node_hash(sbf_hashv, &digest, &level[position + 1].1);
                position += 2;
                parent
            } else {
                position += 1;
                let zero = [0u8; 32];
                if index & 1 == 0 {
                    aspis_core::merkle::node_hash(sbf_hashv, &digest, &zero)
                } else {
                    aspis_core::merkle::node_hash(sbf_hashv, &zero, &digest)
                }
            };
            next.push((index >> 1, parent));
        }
        core::mem::swap(&mut level, &mut next);
    }
    level.first().map_or([0u8; 32], |entry| entry.1)
}

fn hvzk_probe_classes(scope: u8, queries: usize) -> Result<Vec<(usize, usize)>, ProgramError> {
    let mut classes = Vec::new();
    if scope == 0 || scope == 2 {
        // Four internal arity-4 sumcheck batches, then three switch masks.
        classes.push((8, 7 + queries));
        classes.push((3, 31 + queries));
    }
    if scope == 1 || scope == 2 {
        // External ten-variable, degree-27 state-only zerocheck.
        classes.push((10, 28 + queries));
    }
    if scope == 3 {
        // Minimal one-switch repair: exactly one (r || two OOD pads) mask.
        classes.push((1, 31 + queries));
    }
    if classes.is_empty() {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(classes)
    }
}

fn hvzk_probe_scalar_spots(
    classes: &[(usize, usize)],
    start: usize,
    end: usize,
) -> aspis_core::field::QM31 {
    use aspis_core::field::QM31;
    let gamma = hvzk_probe_qm31(0x4741_4d4d);
    let mut sink = QM31::ZERO;
    let mut mask_index = 0usize;
    for &(width, coefficients) in classes {
        for member in 0..width {
            for query in start..end {
                let point = hvzk_probe_qm31(0x1000_0000u32.wrapping_add(query as u32));
                let mut evaluation = QM31::ZERO;
                for coefficient in (0..coefficients).rev() {
                    evaluation = evaluation.mul(point).add(hvzk_probe_qm31(
                        (mask_index as u32).wrapping_mul(1_009) + coefficient as u32,
                    ));
                }
                let carried =
                    hvzk_probe_qm31(0x2000_0000u32.wrapping_add((query * 31 + mask_index) as u32));
                let fresh =
                    hvzk_probe_qm31(0x3000_0000u32.wrapping_add((query * 37 + mask_index) as u32));
                sink = sink.add(evaluation.sub(fresh.add(gamma.mul(carried))));
            }
            mask_index += 1;
            let _ = member;
        }
    }
    sink
}

fn hvzk_probe_batched_spots(
    classes: &[(usize, usize)],
    start: usize,
    end: usize,
) -> aspis_core::field::QM31 {
    use aspis_core::field::QM31;
    let gamma = hvzk_probe_qm31(0x4741_4d4d);
    let eta = hvzk_probe_qm31(0x4554_4121);
    let total_masks: usize = classes.iter().map(|class| class.0).sum();
    let max_coefficients = classes.iter().map(|class| class.1).max().unwrap_or(0);
    let mut eta_powers = Vec::with_capacity(total_masks);
    let mut power = QM31::ONE;
    for _ in 0..total_masks {
        eta_powers.push(power);
        power = power.mul(eta);
    }
    if total_masks == 1 {
        let coefficients = classes[0].1;
        let combined: Vec<QM31> = (0..coefficients)
            .map(|coefficient| hvzk_probe_qm31(coefficient as u32))
            .collect();
        let mut sink = combined.first().copied().unwrap_or(QM31::ONE);
        for query in start..end {
            let point = hvzk_probe_qm31(0x1000_0000u32.wrapping_add(query as u32));
            let mut evaluation = QM31::ZERO;
            for &coefficient in combined.iter().rev() {
                evaluation = evaluation.mul(point).add(coefficient);
            }
            let carried = hvzk_probe_qm31(0x2000_0000u32.wrapping_add((query * 31) as u32));
            let fresh = hvzk_probe_qm31(0x3000_0000u32.wrapping_add((query * 37) as u32));
            sink = sink.add(evaluation.sub(fresh.add(gamma.mul(carried))));
        }
        return sink;
    }
    // One-time random linear combination of every revealed coefficient
    // vector. Shorter vectors are embedded by zero padding at high degree.
    let mut combined = vec![QM31::ZERO; max_coefficients];
    let mut mask_index = 0usize;
    for &(width, coefficients) in classes {
        for _ in 0..width {
            for (coefficient, dst) in combined.iter_mut().take(coefficients).enumerate() {
                let value =
                    hvzk_probe_qm31((mask_index as u32).wrapping_mul(1_009) + coefficient as u32);
                *dst = dst.add(eta_powers[mask_index].mul(value));
            }
            mask_index += 1;
        }
    }
    let gamma_eta: Vec<QM31> = eta_powers.iter().map(|&weight| gamma.mul(weight)).collect();
    // Keep the one-time coefficient batch observable even for the dedicated
    // setup-only segment (`start == end`).
    let mut sink = combined.first().copied().unwrap_or(QM31::ONE);
    for query in start..end {
        let point = hvzk_probe_qm31(0x1000_0000u32.wrapping_add(query as u32));
        let mut evaluation = QM31::ZERO;
        for &coefficient in combined.iter().rev() {
            evaluation = evaluation.mul(point).add(coefficient);
        }
        let mut rhs = QM31::ZERO;
        for mask in 0..total_masks {
            let carried = hvzk_probe_qm31(0x2000_0000u32.wrapping_add((query * 31 + mask) as u32));
            let fresh = hvzk_probe_qm31(0x3000_0000u32.wrapping_add((query * 37 + mask) as u32));
            rhs = rhs
                .add(eta_powers[mask].mul(fresh))
                .add(gamma_eta[mask].mul(carried));
        }
        sink = sink.add(evaluation.sub(rhs));
    }
    sink
}

fn hvzk_probe_target_identity(scope: u8) -> aspis_core::field::QM31 {
    use aspis_core::field::QM31;
    let mut sink = QM31::ZERO;
    let mut mask = 0usize;
    let mut dot = |width: usize, message_len: usize| {
        for _ in 0..width {
            for coefficient in 0..message_len {
                sink = sink.add(hvzk_probe_qm31((mask * 1_009 + coefficient) as u32).mul(
                    hvzk_probe_qm31(0x6000_0000u32.wrapping_add((mask * 257 + coefficient) as u32)),
                ));
            }
            mask += 1;
        }
    };
    if scope == 0 || scope == 2 {
        dot(8, 7);
        dot(3, 31);
    }
    if scope == 1 || scope == 2 {
        dot(10, 28);
    }
    if scope == 3 {
        dot(1, 31);
    }
    if scope != 3 {
        // Four final-source message coordinates in the full base case.
        for coefficient in 0..4 {
            sink = sink.add(
                hvzk_probe_qm31(0x7000_0000 + coefficient)
                    .mul(hvzk_probe_qm31(0x7100_0000 + coefficient)),
            );
        }
    }
    sink
}

fn hvzk_probe_transcript(
    scope: u8,
    mode: u8,
    queries: usize,
) -> Result<aspis_core::field::QM31, ProgramError> {
    use aspis_core::transcript::Transcript;
    let classes = hvzk_probe_classes(scope, queries)?;
    let mask_roots = match (scope, mode) {
        (0, 0) => 14,
        (0, 1) => 5,
        (1, _) => 2,
        (2, 0) => 16,
        (2, 1) => 5,
        (3, _) => 2,
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    let mut transcript = Transcript::new(sbf_hashv);
    let root = [0x42u8; 32];
    for tree in 0..mask_roots {
        let mut tagged = root;
        tagged[0] = tree as u8;
        transcript.absorb(200, &tagged);
    }
    // Fresh-side target claim. The full base case additionally commits a
    // fresh main source blind; the isolated one-switch identity does not.
    if scope != 3 {
        transcript.absorb(201, &root);
    }
    transcript.absorb(202, &[0x51u8; 16]);
    let _gamma = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    // Source message/randomness reveals belong to Construction 7.2's full
    // source identity, not the isolated one-switch repair.
    if scope != 3 {
        transcript.absorb(203, &vec![0x11u8; 4 * 16]);
        transcript.absorb(204, &vec![0x12u8; 29 * 16]);
    }
    // Upstream observes each mask's message and randomness separately.
    for &(width, coefficients) in &classes {
        let message_len = if coefficients == 7 + queries {
            7
        } else if coefficients == 31 + queries {
            31
        } else {
            28
        };
        for member in 0..width {
            transcript.absorb(205, &vec![member as u8; message_len * 16]);
            transcript.absorb(206, &vec![member as u8; queries * 16]);
        }
    }
    // Identity batching challenge, sampled after all reveals and before the
    // shared mask query positions.
    transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)
}

fn hvzk_probe_one_switch_overlap_transcript() -> Result<aspis_core::field::QM31, ProgramError> {
    use aspis_core::transcript::Transcript;
    let mut transcript = Transcript::new(sbf_hashv);
    // Both commitments are assumed to have been absorbed by causally
    // existing roots. Only the fresh-side claim and the single reveal are
    // incremental here.
    transcript.absorb(202, &[0x51u8; 16]);
    let _gamma = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    transcript.absorb(205, &vec![0x31u8; 31 * 16]);
    transcript.absorb(206, &vec![0x29u8; 29 * 16]);
    transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidInstructionData)
}

fn run_hvzk_whir_mask_probe(
    mask_log_inv_rate: u8,
    mask_queries: u8,
    scope: u8,
    mode: u8,
    phase: u8,
    start: u8,
    end: u8,
) -> ProgramResult {
    if !matches!(mask_log_inv_rate, 4 | 5 | 6 | 8)
        || mask_queries == 0
        || mask_queries > 64
        || scope > 3
        || mode > 1
        || phase > 12
        || start > end
        || (phase != 1 && end > mask_queries)
        || (phase == 1 && end > 16)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let queries = mask_queries as usize;
    let classes = hvzk_probe_classes(scope, queries)?;
    let mut digest_sink = [0u8; 32];
    let field_sink = match phase {
        0 => hvzk_probe_qm31(
            ((mask_log_inv_rate as u32) << 24)
                | ((mask_queries as u32) << 16)
                | ((scope as u32) << 8)
                | mode as u32,
        ),
        1 => {
            // Baseline mirrors one fresh tree per chronological carried
            // group. The timing-safe mode precommits independent sumcheck
            // masks, leaves three challenge-dependent switch roots
            // sequential, and groups all fresh masks at the base case.
            let mut trees: Vec<(usize, usize)> = Vec::new();
            if mode == 0 {
                if scope == 0 || scope == 2 {
                    for _ in 0..2 {
                        trees.extend([(7, 2), (7, 2), (7, 2), (7, 2)]);
                        trees.extend([(31, 1), (31, 1), (31, 1)]);
                    }
                }
                if scope == 1 || scope == 2 {
                    trees.extend([(28, 10), (28, 10)]);
                }
                if scope == 3 {
                    trees.extend([(31, 1), (31, 1)]);
                }
            } else {
                match scope {
                    0 => trees.extend([(31, 8), (31, 1), (31, 1), (31, 1), (31, 11)]),
                    1 => trees.extend([(28, 10), (28, 10)]),
                    2 => trees.extend([(31, 18), (31, 1), (31, 1), (31, 1), (31, 21)]),
                    3 => trees.extend([(31, 1), (31, 1)]),
                    _ => unreachable!(),
                }
            }
            let tree_start = start as usize;
            let tree_end = end as usize;
            if tree_start >= tree_end || tree_end > trees.len() {
                return Err(ProgramError::InvalidInstructionData);
            }
            for (tree, &(message_len, width)) in trees[tree_start..tree_end].iter().enumerate() {
                let depth = hvzk_probe_depth(message_len, queries, mask_log_inv_rate as usize);
                let root = hvzk_probe_tree_sink(depth, queries, width, (tree_start + tree) as u8);
                for (dst, src) in digest_sink.iter_mut().zip(root) {
                    *dst ^= src;
                }
            }
            hvzk_probe_qm31(u32::from_le_bytes(digest_sink[..4].try_into().unwrap()))
        }
        2 => hvzk_probe_scalar_spots(&classes, start as usize, end as usize),
        3 => hvzk_probe_batched_spots(&classes, start as usize, end as usize),
        4 => {
            // One verification hash for an optional dedicated mask-query
            // PoW. Difficulty affects honest-prover work, not verifier CU.
            digest_sink = sbf_hashv(&[
                b"aspis-hvzk-mask-pow-v0",
                &[mask_log_inv_rate, mask_queries, scope, mode, start, end],
            ]);
            hvzk_probe_qm31(u32::from_le_bytes(digest_sink[..4].try_into().unwrap()))
        }
        5 => hvzk_probe_target_identity(scope),
        6 => hvzk_probe_transcript(scope, mode, queries)?,
        7 => {
            // Fresh-main/source equality at the 29 final-source positions:
            // evaluate the 4-message + 29-randomness reveal, then compare it
            // with fresh + gamma*source.
            let gamma = hvzk_probe_qm31(0x534f_5552);
            let mut sink = aspis_core::field::QM31::ZERO;
            for query in 0..29usize {
                let point = hvzk_probe_qm31(0x7200_0000 + query as u32);
                let mut evaluation = aspis_core::field::QM31::ZERO;
                for coefficient in (0..33usize).rev() {
                    evaluation = evaluation
                        .mul(point)
                        .add(hvzk_probe_qm31(0x7300_0000 + coefficient as u32));
                }
                let fresh = hvzk_probe_qm31(0x7400_0000 + query as u32);
                let source = hvzk_probe_qm31(0x7500_0000 + query as u32);
                sink = sink.add(evaluation.sub(fresh.add(gamma.mul(source))));
            }
            sink
        }
        8 | 9 => {
            let depths: [u32; 4] = if phase == 8 {
                [13, 11, 9, 7]
            } else {
                [14, 12, 11, 11]
            };
            for (tree, depth) in depths.into_iter().enumerate() {
                let root = hvzk_probe_tree_sink(depth, 29, 4, (0x80 + tree) as u8);
                for (dst, src) in digest_sink.iter_mut().zip(root) {
                    *dst ^= src;
                }
            }
            hvzk_probe_qm31(u32::from_le_bytes(digest_sink[..4].try_into().unwrap()))
        }
        10 => {
            digest_sink = hvzk_probe_tree_sink(7, 29, 1, 0x90);
            hvzk_probe_qm31(u32::from_le_bytes(digest_sink[..4].try_into().unwrap()))
        }
        11 => hvzk_probe_one_switch_overlap_transcript()?,
        12 => {
            let leaf_len = if mode == 0 { 64 } else { 80 };
            let mut leaf = vec![0x5au8; leaf_len];
            for query in 0..29u8 {
                leaf[0] = query;
                let digest = aspis_core::merkle::leaf_hash(sbf_hashv, 0xa0, &leaf);
                for (dst, src) in digest_sink.iter_mut().zip(digest) {
                    *dst ^= src;
                }
            }
            hvzk_probe_qm31(u32::from_le_bytes(digest_sink[..4].try_into().unwrap()))
        }
        _ => unreachable!(),
    };
    if field_sink.is_zero() && digest_sink == [0u8; 32] {
        Err(ProgramError::InvalidInstructionData)
    } else {
        Ok(())
    }
}

const RADIX8_DEPTH12_Q36_INDICES: [u32; 36] = [
    185, 248, 420, 431, 693, 915, 961, 1_366, 1_371, 1_418, 1_525, 1_533, 1_690, 1_788, 1_894,
    1_898, 1_922, 1_981, 1_983, 2_141, 2_266, 2_369, 2_513, 2_637, 2_710, 2_851, 2_877, 2_884,
    3_017, 3_348, 3_420, 3_449, 3_566, 3_896, 3_964, 4_053,
];
const RADIX4_DEPTH12_FRONTIER_BYTES: usize = 301 * 32;
const RADIX8_DEPTH12_FRONTIER_BYTES: usize = 469 * 32;
static RADIX4_DEPTH12_FRONTIER: [u8; RADIX4_DEPTH12_FRONTIER_BYTES] =
    [0u8; RADIX4_DEPTH12_FRONTIER_BYTES];
static RADIX8_DEPTH12_FRONTIER: [u8; RADIX8_DEPTH12_FRONTIER_BYTES] =
    [0u8; RADIX8_DEPTH12_FRONTIER_BYTES];

const fn one_bit_frontier<const N: usize>() -> [u8; N] {
    let mut bytes = [0u8; N];
    bytes[N / 2] = 1;
    bytes
}

static RADIX4_DEPTH12_CORRUPTED_FRONTIER: [u8; RADIX4_DEPTH12_FRONTIER_BYTES] = one_bit_frontier();
static RADIX8_DEPTH12_CORRUPTED_FRONTIER: [u8; RADIX8_DEPTH12_FRONTIER_BYTES] = one_bit_frontier();

const RADIX4_DEPTH12_ROOT: [u8; 32] = [
    0xc9, 0x62, 0xc0, 0x84, 0xee, 0xa9, 0xac, 0xc4, 0xe5, 0x82, 0xe6, 0x7d, 0x9e, 0x21, 0xdd, 0x2e,
    0x4f, 0xfe, 0x7b, 0xa2, 0x27, 0x81, 0x1f, 0xde, 0xbd, 0xae, 0x48, 0x7f, 0x77, 0x63, 0x51, 0x26,
];
const RADIX8_DEPTH12_ROOT: [u8; 32] = [
    0xeb, 0x5b, 0x3d, 0x0b, 0xc7, 0x0d, 0xeb, 0xe0, 0xea, 0xf7, 0xbd, 0x92, 0x01, 0x0b, 0xa6, 0x49,
    0x87, 0xea, 0xd9, 0x78, 0x52, 0x08, 0xa4, 0xd3, 0x99, 0x83, 0xbc, 0x12, 0x70, 0xac, 0xbf, 0x9a,
];

fn run_radix8_merkle_depth12_probe(arity: u8, corrupt_frontier: bool) -> ProgramResult {
    let mut entries = Vec::with_capacity(RADIX8_DEPTH12_Q36_INDICES.len());
    for index in RADIX8_DEPTH12_Q36_INDICES {
        let mut digest = [0u8; 32];
        digest[..4].copy_from_slice(&index.to_le_bytes());
        entries.push((index, digest));
    }
    let mut level = Vec::with_capacity(entries.len());
    let mut next = Vec::with_capacity(entries.len());
    let verified = match arity {
        4 => aspis_core::merkle::verify_radix4_minimal_subtree_bytes(
            sbf_hashv,
            &RADIX4_DEPTH12_ROOT,
            12,
            &entries,
            if corrupt_frontier {
                &RADIX4_DEPTH12_CORRUPTED_FRONTIER
            } else {
                &RADIX4_DEPTH12_FRONTIER
            },
            &mut level,
            &mut next,
        ),
        8 => aspis_core::merkle_radix8::verify_radix8_minimal_subtree_bytes(
            sbf_hashv,
            &RADIX8_DEPTH12_ROOT,
            12,
            &entries,
            if corrupt_frontier {
                &RADIX8_DEPTH12_CORRUPTED_FRONTIER
            } else {
                &RADIX8_DEPTH12_FRONTIER
            },
            &mut level,
            &mut next,
        ),
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    if verified == !corrupt_frontier {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

const FOREST_PROBE_INDICES: [u32; 36] = [
    76, 268, 492, 545, 699, 981, 982, 1_010, 1_026, 1_072, 1_114, 1_129, 1_133, 1_822, 1_823,
    1_889, 1_934, 1_967, 2_000, 2_098, 2_136, 2_171, 2_237, 2_245, 2_263, 2_549, 2_730, 2_758,
    2_843, 3_000, 3_059, 3_242, 3_322, 3_369, 3_537, 3_753,
];
const FOREST_PROBE_START_LEVELS: [u32; 5] = [0, 0, 1, 2, 3];
const FOREST_PROBE_FRONTIER_BYTES: [usize; 5] = [9_632, 9_632, 6_432, 3_296, 896];
static FOREST_PROBE_ZERO_FRONTIER: [u8; 9_632] = [0u8; 9_632];
const FOREST_PROBE_ROOTS: [[u8; 32]; 5] = [
    [
        0xc8, 0x05, 0xac, 0xc5, 0xbb, 0xe3, 0x19, 0x3f, 0xd5, 0x93, 0x63, 0xd5, 0x41, 0xe7, 0xf4,
        0x69, 0xdd, 0xd2, 0x33, 0xd4, 0x7c, 0x14, 0x8f, 0x30, 0x6a, 0x53, 0x35, 0x0a, 0xf8, 0x0b,
        0x00, 0xe8,
    ],
    [
        0x38, 0xd5, 0x5c, 0xf2, 0x74, 0x64, 0xeb, 0xe8, 0x13, 0x23, 0x7a, 0x87, 0xfa, 0x03, 0xbb,
        0x0d, 0x19, 0x5c, 0xc5, 0xa9, 0x73, 0xfc, 0xc0, 0xb4, 0xbf, 0xa9, 0x90, 0x09, 0x1b, 0x79,
        0x28, 0x16,
    ],
    [
        0x40, 0x4c, 0x6f, 0xf3, 0x67, 0xf7, 0xbe, 0x81, 0xa9, 0xaf, 0xfa, 0x1c, 0x87, 0x89, 0xf8,
        0x14, 0xdd, 0x8c, 0x12, 0xd2, 0x6b, 0xd5, 0x45, 0xcb, 0xe9, 0x8b, 0x07, 0x83, 0x88, 0x4f,
        0xff, 0x23,
    ],
    [
        0x98, 0xed, 0xb7, 0x9f, 0x6a, 0xd6, 0xa5, 0x49, 0x9d, 0x42, 0x3d, 0xda, 0x44, 0x51, 0xc4,
        0xee, 0xad, 0x73, 0xaa, 0xaf, 0x6d, 0xef, 0xe8, 0xf2, 0x25, 0x06, 0x1b, 0x7a, 0x06, 0x38,
        0x68, 0x4f,
    ],
    [
        0x41, 0x45, 0xaf, 0x0c, 0x46, 0xae, 0x0e, 0xd3, 0xbe, 0xa7, 0x97, 0xd9, 0xe2, 0x9d, 0x0a,
        0xd5, 0x72, 0xe7, 0xc7, 0x0e, 0x6c, 0xc8, 0x4d, 0x6e, 0x78, 0xb0, 0x6d, 0x4f, 0xbc, 0xac,
        0x46, 0xd3,
    ],
];

fn forest_probe_shifted_indices(start_level: u32) -> Vec<u32> {
    let mut indices = FOREST_PROBE_INDICES
        .iter()
        .map(|index| index >> (2 * start_level))
        .collect::<Vec<_>>();
    indices.dedup();
    indices
}

fn forest_probe_leaf_digest(lane: usize, index: u32) -> [u8; 32] {
    let mut digest = [0u8; 32];
    digest[0] = lane as u8 + 1;
    digest[1..5].copy_from_slice(&index.to_le_bytes());
    digest
}

fn run_merkle_forest_probe(fused: bool, corrupt_lane: u8) -> ProgramResult {
    if corrupt_lane != u8::MAX && corrupt_lane >= 5 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let shifted: [Vec<u32>; 5] =
        core::array::from_fn(|lane| forest_probe_shifted_indices(FOREST_PROBE_START_LEVELS[lane]));
    let leaf_digests: [Vec<[u8; 32]>; 5] = core::array::from_fn(|lane| {
        shifted[lane]
            .iter()
            .map(|index| forest_probe_leaf_digest(lane, *index))
            .collect()
    });
    let mut corrupted_storage = if corrupt_lane == u8::MAX {
        None
    } else {
        let lane = corrupt_lane as usize;
        let mut bytes = FOREST_PROBE_ZERO_FRONTIER[..FOREST_PROBE_FRONTIER_BYTES[lane]].to_vec();
        let middle = bytes.len() / 2;
        bytes[middle] ^= 1;
        Some(bytes)
    };
    let frontiers: [&[u8]; 5] = core::array::from_fn(|lane| {
        if corrupt_lane as usize == lane {
            corrupted_storage.as_deref().unwrap()
        } else {
            &FOREST_PROBE_ZERO_FRONTIER[..FOREST_PROBE_FRONTIER_BYTES[lane]]
        }
    });

    let verified = if fused {
        let lanes: [aspis_core::merkle_forest::StaggeredRadix4Lane<'_>; 5] =
            core::array::from_fn(|lane| aspis_core::merkle_forest::StaggeredRadix4Lane {
                start_level: FOREST_PROBE_START_LEVELS[lane],
                root: &FOREST_PROBE_ROOTS[lane],
                leaf_digests: &leaf_digests[lane],
                frontier: frontiers[lane],
            });
        aspis_core::merkle_forest::verify_staggered_radix4_forest_bytes(
            sbf_hashv,
            12,
            &FOREST_PROBE_INDICES,
            &lanes,
            &mut aspis_core::merkle_forest::StaggeredRadix4ForestScratch::with_capacity(
                FOREST_PROBE_INDICES.len(),
            ),
        )
    } else {
        let mut all_verified = true;
        let mut level = Vec::with_capacity(FOREST_PROBE_INDICES.len());
        let mut next = Vec::with_capacity(FOREST_PROBE_INDICES.len());
        for lane in 0..5 {
            let entries = shifted[lane]
                .iter()
                .copied()
                .zip(leaf_digests[lane].iter().copied())
                .collect::<Vec<_>>();
            all_verified &= aspis_core::merkle::verify_radix4_minimal_subtree_bytes(
                sbf_hashv,
                &FOREST_PROBE_ROOTS[lane],
                12 - 2 * FOREST_PROBE_START_LEVELS[lane],
                &entries,
                frontiers[lane],
                &mut level,
                &mut next,
            );
        }
        all_verified
    };
    corrupted_storage.take();
    if verified == (corrupt_lane == u8::MAX) {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

const LAYER0_DOT_WIDTH_QUERIES: u32 = 36;
const LAYER0_DOT_WIDTH_MAX_C1_BYTES: usize = 4 * 49 * 4;
const LAYER0_DOT_WIDTH_C2_BYTES: usize = 2 * 4 * 16;

#[inline(never)]
fn layer0_dot_width_sink<const N: usize>(corrupt: u8) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{
        qm31_m31_dot4_prepared_limbs_4b1_bytes, qm31_m31_dot4_prepared_limbs_4b_bytes,
        PreparedQm31Multiplier, CM31, M31, P, QM31,
    };

    let gamma = QM31 {
        c0: CM31::new(M31(7), M31(11)),
        c1: CM31::new(M31(13), M31(17)),
    };
    let mut power = QM31::ONE;
    let weight_limbs: [[u32; 4]; N] = core::array::from_fn(|_| {
        let limbs = [power.c0.a.0, power.c0.b.0, power.c1.a.0, power.c1.b.0];
        power = power.mul(gamma);
        limbs
    });
    let helper0 = PreparedQm31Multiplier::new(power);
    power = power.mul(gamma);
    let helpers = [helper0, PreparedQm31Multiplier::new(power)];

    // Build one deterministic slot-major authenticated-leaf payload outside
    // the measured q36 loop. One coordinate changes per query so LLVM cannot
    // hoist the canonical decode/dot out of the loop.
    let mut c1 = [0u8; LAYER0_DOT_WIDTH_MAX_C1_BYTES];
    for slot in 0..4 {
        for column in 0..N {
            let value = 1 + ((slot as u32 * 1_009 + column as u32 * 131) % 1_000_003);
            let offset = (slot * N + column) * 4;
            c1[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        }
    }
    let mut c2 = [0u8; LAYER0_DOT_WIDTH_C2_BYTES];
    for helper in 0..2 {
        for slot in 0..4 {
            let offset = (helper * 4 + slot) * 16;
            let value = QM31 {
                c0: CM31::new(
                    M31(10_001 + helper as u32 * 101 + slot as u32 * 11),
                    M31(20_003 + helper as u32 * 103 + slot as u32 * 13),
                ),
                c1: CM31::new(
                    M31(30_007 + helper as u32 * 107 + slot as u32 * 17),
                    M31(40_009 + helper as u32 * 109 + slot as u32 * 19),
                ),
            };
            value.write_le_bytes(&mut c2[offset..offset + 16]);
        }
    }
    if corrupt == 1 {
        let offset = (4 * N - 1) * 4;
        c1[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
    } else if corrupt == 2 {
        let offset = LAYER0_DOT_WIDTH_C2_BYTES - 4;
        c2[offset..].copy_from_slice(&P.to_le_bytes());
    }

    let mut accumulator = [QM31::ZERO; 4];
    for query in 0..LAYER0_DOT_WIDTH_QUERIES {
        c1[..4].copy_from_slice(&(100_003 + query * 997).to_le_bytes());
        c2[..4].copy_from_slice(&(200_003 + query * 991).to_le_bytes());
        let decoded = if N % 4 == 0 {
            qm31_m31_dot4_prepared_limbs_4b_bytes::<N>(&weight_limbs, &c1[..4 * N * 4])
        } else {
            qm31_m31_dot4_prepared_limbs_4b1_bytes::<N>(&weight_limbs, &c1[..4 * N * 4])
        };
        let mut combined = decoded.ok_or(ProgramError::InvalidAccountData)?;
        for helper in 0..2 {
            for (slot, combined_slot) in combined.iter_mut().enumerate() {
                let offset = (helper * 4 + slot) * 16;
                let value = QM31::from_le_bytes(&c2[offset..offset + 16])
                    .ok_or(ProgramError::InvalidAccountData)?;
                *combined_slot = combined_slot.add(helpers[helper].mul(value));
            }
        }
        for slot in 0..4 {
            accumulator[slot] = accumulator[slot].add(combined[slot]);
        }
    }

    let mut encoded = [0u8; 64];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    let width = [N as u8];
    Ok(sbf_hashv(&[
        b"aspis-layer0-dot-width-probe-v1",
        &width,
        &encoded,
    ]))
}

fn run_layer0_dot_width_probe(columns: u8, corrupt: u8, expected_sink: [u8; 32]) -> ProgramResult {
    if corrupt > 2 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let result = match columns {
        49 => layer0_dot_width_sink::<49>(corrupt),
        33 => layer0_dot_width_sink::<33>(corrupt),
        17 => layer0_dot_width_sink::<17>(corrupt),
        16 => layer0_dot_width_sink::<16>(corrupt),
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    match (corrupt, result) {
        (0, Ok(actual)) if actual == expected_sink => Ok(()),
        (1 | 2, Err(_)) => Ok(()),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

const STATE_ONLY_HELPER_DOT2_PROBE_QUERIES: u32 = 16;

/// Deterministic q16-equivalent arithmetic sink for append-only tag 53.
/// The two arms differ only in whether the two prepared helper products are
/// reduced independently or accumulated in one exact lazy dot.
#[inline(never)]
pub fn state_only_helper_dot2_probe_sink(
    fused_helpers: bool,
    corrupt: u8,
) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{CM31, M31, P, QM31};
    use aspis_core::state_only_query::{
        gamma_combine_state_only_layer0_helpers_dot2_candidate,
        gamma_combine_state_only_layer0_prepared, StateOnlyQueryPowers, STATE_ONLY_C1_COLUMNS,
        STATE_ONLY_C1_LEAF_BYTES, STATE_ONLY_C2_COLUMNS, STATE_ONLY_C2_LEAF_BYTES,
    };

    if corrupt > 2 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let gamma = QM31 {
        c0: CM31::new(M31(41), M31(43)),
        c1: CM31::new(M31(47), M31(53)),
    };
    let powers = StateOnlyQueryPowers::new(gamma);
    let mut c1 = [0u8; STATE_ONLY_C1_LEAF_BYTES];
    for slot in 0..4 {
        for column in 0..STATE_ONLY_C1_COLUMNS {
            let value = 1 + ((slot as u32 * 1_009 + column as u32 * 131) % 1_000_003);
            let offset = (slot * STATE_ONLY_C1_COLUMNS + column) * 4;
            c1[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        }
    }
    let mut c2 = [0u8; STATE_ONLY_C2_LEAF_BYTES];
    for helper in 0..STATE_ONLY_C2_COLUMNS {
        for slot in 0..4 {
            let offset = (helper * 4 + slot) * 16;
            let value = QM31 {
                c0: CM31::new(
                    M31(10_001 + helper as u32 * 101 + slot as u32 * 11),
                    M31(20_003 + helper as u32 * 103 + slot as u32 * 13),
                ),
                c1: CM31::new(
                    M31(30_007 + helper as u32 * 107 + slot as u32 * 17),
                    M31(40_009 + helper as u32 * 109 + slot as u32 * 19),
                ),
            };
            value.write_le_bytes(&mut c2[offset..offset + 16]);
        }
    }
    if corrupt == 1 {
        let offset = c1.len() - 4;
        c1[offset..].copy_from_slice(&P.to_le_bytes());
    } else if corrupt == 2 {
        let offset = c2.len() - 4;
        c2[offset..].copy_from_slice(&P.to_le_bytes());
    }

    let mut accumulator = [QM31::ZERO; 4];
    for query in 0..STATE_ONLY_HELPER_DOT2_PROBE_QUERIES {
        c1[..4].copy_from_slice(&(100_003 + query * 997).to_le_bytes());
        c2[..4].copy_from_slice(&(200_003 + query * 991).to_le_bytes());
        let combined = if fused_helpers {
            gamma_combine_state_only_layer0_helpers_dot2_candidate(&c1, &c2, &powers)
        } else {
            gamma_combine_state_only_layer0_prepared(&c1, &c2, &powers)
        }
        .map_err(|_| ProgramError::InvalidAccountData)?;
        for slot in 0..4 {
            accumulator[slot] = accumulator[slot].add(combined[slot]);
        }
    }
    let mut encoded = [0u8; 64];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[
        b"aspis-state-only-helper-dot2-probe-v1",
        &encoded,
    ]))
}

fn run_state_only_helper_dot2_probe(
    fused_helpers: bool,
    corrupt: u8,
    expected_sink: [u8; 32],
) -> ProgramResult {
    msg!("aspis-cu:helper53_instruction_start");
    sol_log_compute_units();
    let result = state_only_helper_dot2_probe_sink(fused_helpers, corrupt);
    let accepted = match (corrupt, result) {
        (0, Ok(actual)) => actual == expected_sink,
        (1 | 2, Err(_)) => true,
        _ => false,
    };
    if !accepted {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!("aspis-cu:helper53_done");
    sol_log_compute_units();
    Ok(())
}

const STATE_ONLY_HELPER_DOT3_PROBE_QUERIES: u32 = 16;

/// Deterministic q16 four-slot arithmetic sink for append-only tag 54.
/// The arms have identical powers, symbols and canonical decodes.  They differ
/// only in whether the three prepared products reduce independently or share
/// one exact nine-channel reduction.
#[inline(never)]
pub fn state_only_helper_dot3_probe_sink(
    fused_helpers: bool,
    corrupt: u8,
) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{
        qm31_power_table, qm31_sum_products3_prepared, PreparedQm31Multiplier, CM31, M31, P, QM31,
    };

    if corrupt > 1 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let gamma = QM31 {
        c0: CM31::new(M31(41), M31(43)),
        c1: CM31::new(M31(47), M31(53)),
    };
    let powers = qm31_power_table::<29>(gamma);
    let prepared: [PreparedQm31Multiplier; 3] =
        [powers[26], powers[27], powers[28]].map(PreparedQm31Multiplier::new);
    let mut accumulator = [QM31::ZERO; 4];
    for query in 0..STATE_ONLY_HELPER_DOT3_PROBE_QUERIES {
        for (slot, output) in accumulator.iter_mut().enumerate() {
            let mut encoded = [0u8; 48];
            for lane in 0..3usize {
                let seed = 1 + query * 65_537 + slot as u32 * 1_009 + lane as u32 * 131;
                let value = QM31 {
                    c0: CM31::new(M31(seed + 10_001), M31(seed + 20_003)),
                    c1: CM31::new(M31(seed + 30_007), M31(seed + 40_009)),
                };
                value.write_le_bytes(&mut encoded[lane * 16..(lane + 1) * 16]);
            }
            if corrupt == 1 && query == STATE_ONLY_HELPER_DOT3_PROBE_QUERIES - 1 && slot == 3 {
                encoded[44..48].copy_from_slice(&P.to_le_bytes());
            }
            let mut symbols = [QM31::ZERO; 3];
            for lane in 0..3 {
                symbols[lane] = QM31::from_le_bytes(&encoded[lane * 16..(lane + 1) * 16])
                    .ok_or(ProgramError::InvalidAccountData)?;
            }
            let contribution = if fused_helpers {
                qm31_sum_products3_prepared(&prepared, &symbols)
            } else {
                prepared[0]
                    .mul(symbols[0])
                    .add(prepared[1].mul(symbols[1]))
                    .add(prepared[2].mul(symbols[2]))
            };
            *output = output.add(contribution);
        }
    }
    let mut encoded = [0u8; 64];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[
        b"aspis-state-only-helper-dot3-probe-v1",
        &encoded,
    ]))
}

fn run_state_only_helper_dot3_probe(
    fused_helpers: bool,
    corrupt: u8,
    expected_sink: [u8; 32],
) -> ProgramResult {
    msg!("aspis-cu:helper54_instruction_start");
    sol_log_compute_units();
    let result = state_only_helper_dot3_probe_sink(fused_helpers, corrupt);
    let accepted = match (corrupt, result) {
        (0, Ok(actual)) => actual == expected_sink,
        (1, Err(_)) => true,
        _ => false,
    };
    if !accepted {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!("aspis-cu:helper54_done");
    sol_log_compute_units();
    Ok(())
}

const STATE_ONLY_FOLD_POLYNOMIAL_PROBE_QUERIES: u32 = 16;

/// Deterministic q16-by-four-fold sink for append-only tag 55.
#[inline(never)]
pub fn state_only_fold_polynomial_probe_sink(
    polynomial_basis: bool,
    corrupt: u8,
) -> Result<[u8; 32], ProgramError> {
    use aspis_core::circle_fri::{
        normalized_circle_to_line_arity4_prepared_multipliers,
        normalized_circle_to_line_arity4_prepared_polynomial_candidate,
        normalized_line_arity4_prepared_multipliers,
        normalized_line_arity4_prepared_polynomial_candidate,
    };
    use aspis_core::field::{PreparedQm31Multiplier, CM31, M31, P, QM31};

    if corrupt > 1 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let alphas = [
        QM31 {
            c0: CM31::new(M31(41), M31(43)),
            c1: CM31::new(M31(47), M31(53)),
        },
        QM31 {
            c0: CM31::new(M31(59), M31(61)),
            c1: CM31::new(M31(67), M31(71)),
        },
        QM31 {
            c0: CM31::new(M31(73), M31(79)),
            c1: CM31::new(M31(83), M31(89)),
        },
        QM31 {
            c0: CM31::new(M31(97), M31(101)),
            c1: CM31::new(M31(103), M31(107)),
        },
    ];
    let alpha_squared_values = alphas.map(QM31::square);
    let alpha_prepared = alphas.map(PreparedQm31Multiplier::new);
    let alpha_squared_prepared = alpha_squared_values.map(PreparedQm31Multiplier::new);
    let alpha_cubed_prepared = if polynomial_basis {
        core::array::from_fn(|round| {
            PreparedQm31Multiplier::new(alpha_squared_values[round].mul(alphas[round]))
        })
    } else {
        [PreparedQm31Multiplier::new(QM31::ZERO); 4]
    };

    let mut accumulator = QM31::ZERO;
    for query in 0..STATE_ONLY_FOLD_POLYNOMIAL_PROBE_QUERIES {
        for round in 0..4usize {
            let mut encoded = [0u8; 64];
            for slot in 0..4usize {
                let seed = 1 + query * 65_537 + round as u32 * 4_099 + slot as u32 * 131;
                let value = QM31 {
                    c0: CM31::new(M31(seed + 10_001), M31(seed + 20_003)),
                    c1: CM31::new(M31(seed + 30_007), M31(seed + 40_009)),
                };
                value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
            }
            if corrupt == 1 && query == STATE_ONLY_FOLD_POLYNOMIAL_PROBE_QUERIES - 1 && round == 3 {
                encoded[60..64].copy_from_slice(&P.to_le_bytes());
            }
            let mut values = [QM31::ZERO; 4];
            for slot in 0..4 {
                values[slot] = QM31::from_le_bytes(&encoded[slot * 16..(slot + 1) * 16])
                    .ok_or(ProgramError::InvalidAccountData)?;
            }
            let base = 1 + query * 17 + round as u32 * 7;
            let inverses = [M31(base + 3), M31(base + 5), M31(base + 9)];
            let folded = if round == 0 {
                if polynomial_basis {
                    normalized_circle_to_line_arity4_prepared_polynomial_candidate(
                        values,
                        alpha_prepared[round],
                        alpha_squared_prepared[round],
                        alpha_cubed_prepared[round],
                        inverses[2],
                        inverses[0],
                    )
                } else {
                    normalized_circle_to_line_arity4_prepared_multipliers(
                        values,
                        alpha_prepared[round],
                        alpha_squared_prepared[round],
                        inverses[2],
                        inverses[0],
                    )
                }
            } else if polynomial_basis {
                normalized_line_arity4_prepared_polynomial_candidate(
                    values,
                    alpha_prepared[round],
                    alpha_squared_prepared[round],
                    alpha_cubed_prepared[round],
                    inverses,
                )
            } else {
                normalized_line_arity4_prepared_multipliers(
                    values,
                    alpha_prepared[round],
                    alpha_squared_prepared[round],
                    inverses,
                )
            };
            accumulator = accumulator.add(folded);
        }
    }
    let mut encoded = [0u8; 16];
    accumulator.write_le_bytes(&mut encoded);
    Ok(sbf_hashv(&[
        b"aspis-state-only-fold-polynomial-probe-v1",
        &encoded,
    ]))
}

fn run_state_only_fold_polynomial_probe(
    polynomial_basis: bool,
    corrupt: u8,
    expected_sink: [u8; 32],
) -> ProgramResult {
    msg!("aspis-cu:fold55_instruction_start");
    sol_log_compute_units();
    let result = state_only_fold_polynomial_probe_sink(polynomial_basis, corrupt);
    let accepted = match (corrupt, result) {
        (0, Ok(actual)) => actual == expected_sink,
        (1, Err(_)) => true,
        _ => false,
    };
    if !accepted {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!("aspis-cu:fold55_done");
    sol_log_compute_units();
    Ok(())
}

#[inline(never)]
pub fn atomic_routing_partition_probe_sink(optimized: bool, seed: u32) -> [u8; 16] {
    use aspis_core::field::{CM31, M31, QM31};

    let m31 = |offset: u32| M31(1 + seed.wrapping_mul(65_537).wrapping_add(offset) % 1_000_003);
    let qm31 = |offset: u32| QM31 {
        c0: CM31::new(m31(offset), m31(offset + 1)),
        c1: CM31::new(m31(offset + 2), m31(offset + 3)),
    };
    let openings = core::array::from_fn(|index| qm31(100 + 7 * index as u32));
    let h1 = qm31(1_000);
    let point = core::array::from_fn(|index| qm31(2_000 + 11 * index as u32));
    let lambda = qm31(3_000);
    let chi = qm31(4_000);
    let value = if optimized {
        aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_terminal_lane_compiled_v3(
            &openings, h1, &point, lambda, chi,
        )
    } else {
        aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_terminal_lane_legacy_partition_v3(
            &openings, h1, &point, lambda, chi,
        )
    };
    let mut output = [0u8; 16];
    value.write_le_bytes(&mut output);
    output
}

fn run_atomic_routing_partition_probe(
    optimized: bool,
    seed: u32,
    expected_sink: [u8; 16],
) -> ProgramResult {
    let actual = atomic_routing_partition_probe_sink(optimized, seed);
    if actual == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

/// hashv-shaped backend over the Solana SHA-256 syscall.
fn sbf_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    hashv(inputs).to_bytes()
}

const PRIVATE_MERKLE_SALT_BYTES: usize = 32;
const PRIVATE_MERKLE_OPENED_LEAVES: usize = 16;
const PRIVATE_MERKLE_MAX_LEAF_BYTES: usize = 416;
const PRIVATE_MERKLE_LEAF_LENGTHS: [usize; 5] = [416, 256, 64, 64, 64];

/// Literal leaf-hash microbenchmark for the profile-21 shared-root/salt
/// layout. The salt is contiguous with the opened leaf on the wire, so both
/// salted and unsalted hashes use the production-optimal two `hashv` slices:
/// `[DOM_LEAF, tree] || [salt || leaf]` versus
/// `[DOM_LEAF, tree] || [leaf]`.
fn run_state_only_private_merkle_salt_probe(mode: u8, expected_sink: [u8; 32]) -> ProgramResult {
    const DOM_LEAF: u8 = 0x10;
    let (leaf_lengths, salted): (&[usize], bool) = match mode {
        0 => (&[128], false),
        1 => (&[256], false),
        2 => (&PRIVATE_MERKLE_LEAF_LENGTHS, false),
        3 => (&PRIVATE_MERKLE_LEAF_LENGTHS, true),
        _ => return Err(ProgramError::InvalidInstructionData),
    };

    let mut storage = [0u8; PRIVATE_MERKLE_SALT_BYTES + PRIVATE_MERKLE_MAX_LEAF_BYTES];
    for (offset, byte) in storage.iter_mut().enumerate() {
        *byte = (offset as u8).wrapping_mul(73).wrapping_add(19);
    }
    let mut sink = [0u8; 32];
    for (tree, &leaf_len) in leaf_lengths.iter().enumerate() {
        let domain = [DOM_LEAF, tree as u8];
        for leaf in 0..PRIVATE_MERKLE_OPENED_LEAVES {
            storage[0] = (tree as u8).wrapping_mul(29).wrapping_add(leaf as u8);
            storage[PRIVATE_MERKLE_SALT_BYTES] =
                (tree as u8).wrapping_mul(61).wrapping_add(leaf as u8);
            let opened = if salted {
                &storage[..PRIVATE_MERKLE_SALT_BYTES + leaf_len]
            } else {
                &storage[PRIVATE_MERKLE_SALT_BYTES..PRIVATE_MERKLE_SALT_BYTES + leaf_len]
            };
            let digest = sbf_hashv(&[&domain, opened]);
            for (coordinate, byte) in digest.iter().enumerate() {
                sink[coordinate] ^= byte.rotate_left(((tree + leaf + coordinate) & 7) as u32);
            }
        }
    }
    if sink == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

const EXACT_WIDE_V4_GAMMA_BYTES: usize = 16;
const EXACT_WIDE_V4_FIBER_BYTES: usize =
    aspis_statement::wide_v4::C1_FIBER_BYTES + aspis_statement::wide_v4::C2_FIBER_BYTES;
const EXACT_WIDE_V4_FIXTURE_BYTES: usize = EXACT_WIDE_V4_GAMMA_BYTES + EXACT_WIDE_V4_FIBER_BYTES;
pub const EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS: usize = 36;
const EXACT_WIDE_V4_BATCH_FIXTURE_BYTES: usize =
    EXACT_WIDE_V4_GAMMA_BYTES + EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS * EXACT_WIDE_V4_FIBER_BYTES;

#[inline(never)]
fn decode_exact_wide_v4_fiber_into(
    bytes: &[u8],
    fiber: &mut aspis_statement::wide_v4::ExactWideFiber,
) -> ProgramResult {
    use aspis_core::field::{CM31, QM31};
    use aspis_statement::wide_v4::{C1_COLUMNS, C2_COLUMNS, FIBER_SLOTS};

    if bytes.len() != EXACT_WIDE_V4_FIBER_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let c2_start = aspis_statement::wide_v4::C1_FIBER_BYTES;
    for slot in 0..FIBER_SLOTS {
        for column in 0..C1_COLUMNS {
            let offset = (slot * C1_COLUMNS + column) * 8;
            fiber.c1[slot][column] = CM31::from_le_bytes(&bytes[offset..offset + 8])
                .ok_or(ProgramError::InvalidAccountData)?;
        }
    }
    for helper in 0..C2_COLUMNS {
        for slot in 0..FIBER_SLOTS {
            let offset = c2_start + (helper * FIBER_SLOTS + slot) * 16;
            fiber.c2[slot][helper] = QM31::from_le_bytes(&bytes[offset..offset + 16])
                .ok_or(ProgramError::InvalidAccountData)?;
        }
    }
    Ok(())
}

#[inline(never)]
fn decode_exact_wide_v4_fiber(
    bytes: &[u8],
) -> Result<aspis_statement::wide_v4::ExactWideFiber, ProgramError> {
    use aspis_core::field::{CM31, QM31};
    use aspis_statement::wide_v4::{C1_COLUMNS, C2_COLUMNS, FIBER_SLOTS};

    let mut fiber = aspis_statement::wide_v4::ExactWideFiber {
        c1: [[CM31::ZERO; C1_COLUMNS]; FIBER_SLOTS],
        c2: [[QM31::ZERO; C2_COLUMNS]; FIBER_SLOTS],
    };
    decode_exact_wide_v4_fiber_into(bytes, &mut fiber)?;
    Ok(fiber)
}

#[inline(never)]
fn boxed_zero_exact_wide_v4_fiber() -> Box<aspis_statement::wide_v4::ExactWideFiber> {
    use aspis_core::field::{CM31, QM31};
    use aspis_statement::wide_v4::{C1_COLUMNS, C2_COLUMNS, FIBER_SLOTS};

    Box::new(aspis_statement::wide_v4::ExactWideFiber {
        c1: [[CM31::ZERO; C1_COLUMNS]; FIBER_SLOTS],
        c2: [[QM31::ZERO; C2_COLUMNS]; FIBER_SLOTS],
    })
}

#[inline(never)]
fn decode_exact_wide_v4_fixture(
    bytes: &[u8],
) -> Result<
    (
        aspis_core::field::QM31,
        aspis_statement::wide_v4::ExactWideFiber,
    ),
    ProgramError,
> {
    use aspis_core::field::QM31;

    if bytes.len() != EXACT_WIDE_V4_FIXTURE_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let gamma = QM31::from_le_bytes(&bytes[..EXACT_WIDE_V4_GAMMA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    // C2 wire layout is helper-major; the decoder transposes to the
    // arithmetic seam's slot-major representation.
    let fiber = decode_exact_wide_v4_fiber(&bytes[EXACT_WIDE_V4_GAMMA_BYTES..])?;
    Ok((gamma, fiber))
}

#[inline(never)]
fn exact_wide_v4_baseline_combine(
    fiber: &aspis_statement::wide_v4::ExactWideFiber,
    gamma: aspis_core::field::QM31,
) -> [aspis_core::field::QM31; 4] {
    aspis_statement::wide_v4::combine_exact_wide_fiber_baseline(fiber, gamma)
}

#[inline(never)]
fn exact_wide_v4_fused_combine(
    fiber: &aspis_statement::wide_v4::ExactWideFiber,
    gamma: aspis_core::field::QM31,
) -> [aspis_core::field::QM31; 4] {
    aspis_statement::wide_v4::combine_exact_wide_fiber(fiber, gamma)
}

#[inline(never)]
fn exact_wide_v4_prepared_combine(
    fiber: &aspis_statement::wide_v4::ExactWideFiber,
    weights: &aspis_statement::wide_v4::ExactWideWeights,
) -> [aspis_core::field::QM31; 4] {
    aspis_statement::wide_v4::combine_exact_wide_fiber_prepared(fiber, weights)
}

#[inline(never)]
fn exact_wide_v4_prepared_bytes_combine(
    c1_bytes: &[u8],
    c2_bytes: &[u8],
    weights: &aspis_statement::wide_v4::ExactWideWeights,
) -> Result<[aspis_core::field::QM31; 4], ProgramError> {
    aspis_statement::wide_v4::combine_exact_wide_bytes_prepared(c1_bytes, c2_bytes, weights)
        .ok_or(ProgramError::InvalidAccountData)
}

#[inline(never)]
fn exact_wide_v4_prepare_weights(
    gamma: aspis_core::field::QM31,
) -> aspis_statement::wide_v4::ExactWideWeights {
    aspis_statement::wide_v4::prepare_exact_wide_weights(gamma)
}

#[inline(never)]
fn exact_wide_v4_combined_sink(fixture: &[u8], fused: bool) -> Result<[u8; 32], ProgramError> {
    let (gamma, fiber) = decode_exact_wide_v4_fixture(fixture)?;
    let combined = if fused {
        exact_wide_v4_fused_combine(&fiber, gamma)
    } else {
        exact_wide_v4_baseline_combine(&fiber, gamma)
    };
    let mut encoded = [0u8; aspis_statement::wide_v4::FIBER_SLOTS * 16];
    for (slot, value) in combined.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[b"aspis-exact-wide-v4-combined", &encoded]))
}

#[inline(never)]
fn exact_wide_v4_power_sink(fixture: &[u8], actual: bool) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{qm31_power_table, QM31};
    use aspis_statement::wide_v4::TOTAL_COLUMNS;

    let gamma = QM31::from_le_bytes(&fixture[..EXACT_WIDE_V4_GAMMA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    let mut encoded = [0u8; TOTAL_COLUMNS * 16];
    if actual {
        let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
        for (power, chunk) in powers.iter().zip(encoded.chunks_exact_mut(16)) {
            power.write_le_bytes(chunk);
        }
    } else {
        for chunk in encoded.chunks_exact_mut(16) {
            QM31::ONE.write_le_bytes(chunk);
        }
    }
    Ok(sbf_hashv(&[b"aspis-exact-wide-v4-powers", &encoded]))
}

#[inline(never)]
fn exact_wide_v4_batch_sink(fixture: &[u8], prepared: bool) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::QM31;

    let gamma = QM31::from_le_bytes(&fixture[..EXACT_WIDE_V4_GAMMA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    let mut accumulator = [QM31::ZERO; aspis_statement::wide_v4::FIBER_SLOTS];
    let mut fiber = boxed_zero_exact_wide_v4_fiber();
    if prepared {
        let weights = exact_wide_v4_prepare_weights(gamma);
        for index in 0..EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS {
            let start = EXACT_WIDE_V4_GAMMA_BYTES + index * EXACT_WIDE_V4_FIBER_BYTES;
            decode_exact_wide_v4_fiber_into(
                &fixture[start..start + EXACT_WIDE_V4_FIBER_BYTES],
                &mut fiber,
            )?;
            let combined = exact_wide_v4_prepared_combine(&fiber, &weights);
            for slot in 0..aspis_statement::wide_v4::FIBER_SLOTS {
                accumulator[slot] = accumulator[slot].add(combined[slot]);
            }
        }
    } else {
        for index in 0..EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS {
            let start = EXACT_WIDE_V4_GAMMA_BYTES + index * EXACT_WIDE_V4_FIBER_BYTES;
            decode_exact_wide_v4_fiber_into(
                &fixture[start..start + EXACT_WIDE_V4_FIBER_BYTES],
                &mut fiber,
            )?;
            let combined = exact_wide_v4_fused_combine(&fiber, gamma);
            for slot in 0..aspis_statement::wide_v4::FIBER_SLOTS {
                accumulator[slot] = accumulator[slot].add(combined[slot]);
            }
        }
    }
    let mut encoded = [0u8; aspis_statement::wide_v4::FIBER_SLOTS * 16];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[b"aspis-exact-wide-v4-batch36", &encoded]))
}

#[inline(never)]
fn exact_wide_v4_batch_bytes_sink(fixture: &[u8]) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::QM31;

    let gamma = QM31::from_le_bytes(&fixture[..EXACT_WIDE_V4_GAMMA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    let weights = exact_wide_v4_prepare_weights(gamma);
    let mut accumulator = [QM31::ZERO; aspis_statement::wide_v4::FIBER_SLOTS];
    for index in 0..EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS {
        let start = EXACT_WIDE_V4_GAMMA_BYTES + index * EXACT_WIDE_V4_FIBER_BYTES;
        let c2_start = start + aspis_statement::wide_v4::C1_FIBER_BYTES;
        let combined = exact_wide_v4_prepared_bytes_combine(
            &fixture[start..c2_start],
            &fixture[c2_start..c2_start + aspis_statement::wide_v4::C2_FIBER_BYTES],
            &weights,
        )?;
        for slot in 0..aspis_statement::wide_v4::FIBER_SLOTS {
            accumulator[slot] = accumulator[slot].add(combined[slot]);
        }
    }
    let mut encoded = [0u8; aspis_statement::wide_v4::FIBER_SLOTS * 16];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[b"aspis-exact-wide-v4-batch36", &encoded]))
}

fn run_exact_wide_v4_diagnostic(
    fixture_account: &AccountInfo,
    mode: ExactWideV4DiagnosticMode,
    expected_sink: [u8; 32],
) -> ProgramResult {
    let data = fixture_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let batch_mode = matches!(
        mode,
        ExactWideV4DiagnosticMode::FusedBatch36Unprepared
            | ExactWideV4DiagnosticMode::FusedBatch36Prepared
            | ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes
    );
    let expected_len = if batch_mode {
        EXACT_WIDE_V4_BATCH_FIXTURE_BYTES
    } else {
        EXACT_WIDE_V4_FIXTURE_BYTES
    };
    if total_len != expected_len {
        return Err(ProgramError::InvalidAccountData);
    }
    let end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    if end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let fixture = &data[PROOF_ACCOUNT_HEADER_LEN..end];
    let c1_start = EXACT_WIDE_V4_GAMMA_BYTES;
    let c2_start = c1_start + aspis_statement::wide_v4::C1_FIBER_BYTES;

    let sink = match mode {
        ExactWideV4DiagnosticMode::BaselineFourDots => exact_wide_v4_combined_sink(fixture, false)?,
        ExactWideV4DiagnosticMode::FusedDot4 => exact_wide_v4_combined_sink(fixture, true)?,
        ExactWideV4DiagnosticMode::EmptyLeafHashControl => {
            aspis_core::merkle::leaf_hash(sbf_hashv, 0, &[])
        }
        ExactWideV4DiagnosticMode::C1LeafHash => {
            aspis_core::merkle::leaf_hash(sbf_hashv, 0, &fixture[c1_start..c2_start])
        }
        ExactWideV4DiagnosticMode::C2LeafHash => aspis_core::merkle::leaf_hash(
            sbf_hashv,
            aspis_core::proof::SECOND_PHASE_LAYER_TAG,
            &fixture[c2_start..],
        ),
        ExactWideV4DiagnosticMode::GammaPowersControl => exact_wide_v4_power_sink(fixture, false)?,
        ExactWideV4DiagnosticMode::GammaPowers0To50 => exact_wide_v4_power_sink(fixture, true)?,
        ExactWideV4DiagnosticMode::FusedBatch36Unprepared => {
            exact_wide_v4_batch_sink(fixture, false)?
        }
        ExactWideV4DiagnosticMode::FusedBatch36Prepared => exact_wide_v4_batch_sink(fixture, true)?,
        ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes => {
            exact_wide_v4_batch_bytes_sink(fixture)?
        }
    };
    if sink == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

pub const M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS: usize = 36;
pub const M31_CIRCLE_BASIS_C1_COLUMNS: usize = 49;
pub const M31_CIRCLE_BASIS_C1_LEAF_BYTES: usize = 4 * M31_CIRCLE_BASIS_C1_COLUMNS * 4;
pub const M31_CIRCLE_BASIS_C2_LEAF_BYTES: usize = 2 * 4 * 16;
const M31_CIRCLE_BASIS_GAMMA_BYTES: usize = 16;
const M31_CIRCLE_BASIS_RLC_FIBER_BYTES: usize =
    M31_CIRCLE_BASIS_C1_LEAF_BYTES + M31_CIRCLE_BASIS_C2_LEAF_BYTES;
pub const M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES: usize = M31_CIRCLE_BASIS_GAMMA_BYTES
    + M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS * M31_CIRCLE_BASIS_RLC_FIBER_BYTES;

const M31_CIRCLE_FOLD_ALPHA_BYTES: usize = 16;
const M31_CIRCLE_FOLD_RECORD_BYTES: usize = 2 + 4 * 4 + 4 * 16;
pub const M31_CIRCLE_FOLD_FIXTURE_BYTES: usize =
    M31_CIRCLE_FOLD_ALPHA_BYTES + M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS * M31_CIRCLE_FOLD_RECORD_BYTES;

#[inline(never)]
fn m31_circle_basis_rlc_sink_with<F>(
    fixture: &[u8],
    mut combine_c1: F,
) -> Result<[u8; 32], ProgramError>
where
    F: FnMut(
        &[aspis_core::field::QM31; M31_CIRCLE_BASIS_C1_COLUMNS],
        &[u8],
    ) -> Result<[aspis_core::field::QM31; 4], ProgramError>,
{
    use aspis_core::field::{qm31_power_table, QM31};

    if fixture.len() != M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let gamma = QM31::from_le_bytes(&fixture[..M31_CIRCLE_BASIS_GAMMA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    let powers = qm31_power_table::<51>(gamma);
    let c1_weights: &[QM31; M31_CIRCLE_BASIS_C1_COLUMNS] = powers[..M31_CIRCLE_BASIS_C1_COLUMNS]
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let mut accumulator = [QM31::ZERO; 4];

    for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
        let start = M31_CIRCLE_BASIS_GAMMA_BYTES + fiber * M31_CIRCLE_BASIS_RLC_FIBER_BYTES;
        let c2_start = start + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
        let c1_bytes = &fixture[start..c2_start];
        let mut combined = combine_c1(c1_weights, c1_bytes)?;
        let c2 = &fixture[c2_start..c2_start + M31_CIRCLE_BASIS_C2_LEAF_BYTES];
        for helper in 0..2 {
            for (slot, combined_slot) in combined.iter_mut().enumerate() {
                let offset = (helper * 4 + slot) * 16;
                let value = QM31::from_le_bytes(&c2[offset..offset + 16])
                    .ok_or(ProgramError::InvalidAccountData)?;
                *combined_slot = combined_slot.add(powers[49 + helper].mul(value));
            }
        }
        for slot in 0..4 {
            accumulator[slot] = accumulator[slot].add(combined[slot]);
        }
    }

    let mut encoded = [0u8; 64];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[
        b"aspis-m31-circle-basis-rlc-shape-v1",
        &encoded,
    ]))
}

#[inline(never)]
fn m31_circle_basis_rlc_prepared49_sink(fixture: &[u8]) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{
        qm31_m31_dot4_prepared_limbs49_bytes, qm31_power_table, PreparedQm31Multiplier, QM31,
    };

    if fixture.len() != M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let gamma = QM31::from_le_bytes(&fixture[..M31_CIRCLE_BASIS_GAMMA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    let powers = qm31_power_table::<51>(gamma);
    let weight_limbs: [[u32; 4]; M31_CIRCLE_BASIS_C1_COLUMNS] = core::array::from_fn(|index| {
        let weight = powers[index];
        [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]
    });
    let helper_multipliers = [
        PreparedQm31Multiplier::new(powers[49]),
        PreparedQm31Multiplier::new(powers[50]),
    ];
    let mut accumulator = [QM31::ZERO; 4];
    for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
        let start = M31_CIRCLE_BASIS_GAMMA_BYTES + fiber * M31_CIRCLE_BASIS_RLC_FIBER_BYTES;
        let c2_start = start + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
        let mut combined =
            qm31_m31_dot4_prepared_limbs49_bytes(&weight_limbs, &fixture[start..c2_start])
                .ok_or(ProgramError::InvalidAccountData)?;
        let c2 = &fixture[c2_start..c2_start + M31_CIRCLE_BASIS_C2_LEAF_BYTES];
        for helper in 0..2 {
            for (slot, combined_slot) in combined.iter_mut().enumerate() {
                let offset = (helper * 4 + slot) * 16;
                let value = QM31::from_le_bytes(&c2[offset..offset + 16])
                    .ok_or(ProgramError::InvalidAccountData)?;
                *combined_slot = combined_slot.add(helper_multipliers[helper].mul(value));
            }
        }
        for slot in 0..4 {
            accumulator[slot] = accumulator[slot].add(combined[slot]);
        }
    }
    let mut encoded = [0u8; 64];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[
        b"aspis-m31-circle-basis-rlc-shape-v1",
        &encoded,
    ]))
}

#[inline(never)]
fn m31_circle_basis_rlc_prepared49_two_rows_sink(fixture: &[u8]) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{
        qm31_m31_dot4_prepared_limbs49_bytes_two_rows, qm31_power_table, PreparedQm31Multiplier,
        QM31,
    };

    if fixture.len() != M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let gamma = QM31::from_le_bytes(&fixture[..M31_CIRCLE_BASIS_GAMMA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    let powers = qm31_power_table::<51>(gamma);
    let weight_limbs: [[u32; 4]; M31_CIRCLE_BASIS_C1_COLUMNS] = core::array::from_fn(|index| {
        let weight = powers[index];
        [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]
    });
    let helper_multipliers = [
        PreparedQm31Multiplier::new(powers[49]),
        PreparedQm31Multiplier::new(powers[50]),
    ];
    let mut accumulator = [QM31::ZERO; 4];
    for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
        let start = M31_CIRCLE_BASIS_GAMMA_BYTES + fiber * M31_CIRCLE_BASIS_RLC_FIBER_BYTES;
        let c2_start = start + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
        let mut combined =
            qm31_m31_dot4_prepared_limbs49_bytes_two_rows(&weight_limbs, &fixture[start..c2_start])
                .ok_or(ProgramError::InvalidAccountData)?;
        let c2 = &fixture[c2_start..c2_start + M31_CIRCLE_BASIS_C2_LEAF_BYTES];
        for helper in 0..2 {
            for (slot, combined_slot) in combined.iter_mut().enumerate() {
                let offset = (helper * 4 + slot) * 16;
                let value = QM31::from_le_bytes(&c2[offset..offset + 16])
                    .ok_or(ProgramError::InvalidAccountData)?;
                *combined_slot = combined_slot.add(helper_multipliers[helper].mul(value));
            }
        }
        for slot in 0..4 {
            accumulator[slot] = accumulator[slot].add(combined[slot]);
        }
    }
    let mut encoded = [0u8; 64];
    for (slot, value) in accumulator.iter().enumerate() {
        value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
    }
    Ok(sbf_hashv(&[
        b"aspis-m31-circle-basis-rlc-shape-v1",
        &encoded,
    ]))
}

#[inline(never)]
fn m31_circle_basis_rlc_sink(
    fixture: &[u8],
    mode: M31CircleBasisDiagnosticMode,
) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{qm31_m31_dot, qm31_m31_dot4, qm31_m31_dot4_prepared_bytes, M31};

    match mode {
        M31CircleBasisDiagnosticMode::RlcStructuredFourDots => {
            let mut decoded = vec![M31::ZERO; 4 * M31_CIRCLE_BASIS_C1_COLUMNS];
            m31_circle_basis_rlc_sink_with(fixture, |weights, c1_bytes| {
                for (index, chunk) in c1_bytes.chunks_exact(4).enumerate() {
                    decoded[index] = M31::from_le_bytes(
                        chunk
                            .try_into()
                            .map_err(|_| ProgramError::InvalidAccountData)?,
                    )
                    .ok_or(ProgramError::InvalidAccountData)?;
                }
                Ok(core::array::from_fn(|slot| {
                    let offset = slot * M31_CIRCLE_BASIS_C1_COLUMNS;
                    qm31_m31_dot(
                        weights,
                        &decoded[offset..offset + M31_CIRCLE_BASIS_C1_COLUMNS],
                    )
                }))
            })
        }
        M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes => {
            m31_circle_basis_rlc_sink_with(fixture, |weights, c1_bytes| {
                qm31_m31_dot4_prepared_bytes(weights, c1_bytes)
                    .ok_or(ProgramError::InvalidAccountData)
            })
        }
        M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4 => {
            let mut decoded = vec![M31::ZERO; 4 * M31_CIRCLE_BASIS_C1_COLUMNS];
            m31_circle_basis_rlc_sink_with(fixture, |weights, c1_bytes| {
                for (index, chunk) in c1_bytes.chunks_exact(4).enumerate() {
                    decoded[index] = M31::from_le_bytes(
                        chunk
                            .try_into()
                            .map_err(|_| ProgramError::InvalidAccountData)?,
                    )
                    .ok_or(ProgramError::InvalidAccountData)?;
                }
                Ok(qm31_m31_dot4(
                    weights,
                    [
                        &decoded[0..M31_CIRCLE_BASIS_C1_COLUMNS],
                        &decoded[M31_CIRCLE_BASIS_C1_COLUMNS..2 * M31_CIRCLE_BASIS_C1_COLUMNS],
                        &decoded[2 * M31_CIRCLE_BASIS_C1_COLUMNS..3 * M31_CIRCLE_BASIS_C1_COLUMNS],
                        &decoded[3 * M31_CIRCLE_BASIS_C1_COLUMNS..4 * M31_CIRCLE_BASIS_C1_COLUMNS],
                    ],
                ))
            })
        }
        M31CircleBasisDiagnosticMode::RlcStreamingFourDots => {
            let mut decoded = [M31::ZERO; M31_CIRCLE_BASIS_C1_COLUMNS];
            m31_circle_basis_rlc_sink_with(fixture, |weights, c1_bytes| {
                let mut combined = [aspis_core::field::QM31::ZERO; 4];
                let slot_bytes = M31_CIRCLE_BASIS_C1_COLUMNS * 4;
                for (slot, combined_slot) in combined.iter_mut().enumerate() {
                    for (index, chunk) in c1_bytes[slot * slot_bytes..(slot + 1) * slot_bytes]
                        .chunks_exact(4)
                        .enumerate()
                    {
                        decoded[index] = M31::from_le_bytes(
                            chunk
                                .try_into()
                                .map_err(|_| ProgramError::InvalidAccountData)?,
                        )
                        .ok_or(ProgramError::InvalidAccountData)?;
                    }
                    *combined_slot = qm31_m31_dot(weights, &decoded);
                }
                Ok(combined)
            })
        }
        M31CircleBasisDiagnosticMode::RlcPreparedLimbs49 => {
            m31_circle_basis_rlc_prepared49_sink(fixture)
        }
        M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows => {
            m31_circle_basis_rlc_prepared49_two_rows_sink(fixture)
        }
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

#[inline(never)]
fn m31_circle_basis_fold_sink(
    fixture: &[u8],
    mode: M31CircleBasisDiagnosticMode,
) -> Result<[u8; 32], ProgramError> {
    use aspis_core::field::{m31_batch_inverse_with, qm31_circle_to_line_fold4, CM31, M31, QM31};
    use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16;
    use aspis_core::verify::layer_geometry;

    if fixture.len() != M31_CIRCLE_FOLD_FIXTURE_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    let derive_coordinates = matches!(
        mode,
        M31CircleBasisDiagnosticMode::FoldCachedCoordinatesPrevalidatedInverses
            | M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse
    );
    let batch_invert = matches!(
        mode,
        M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse
    );
    let alpha = QM31::from_le_bytes(&fixture[..M31_CIRCLE_FOLD_ALPHA_BYTES])
        .ok_or(ProgramError::InvalidAccountData)?;
    let geometry = layer_geometry(&PROFILE_CAPACITY_LR10_Q36_G16, 0);
    let mut omega_powers = [CM31::ONE; aspis_core::params::CIRCLE_LOG_ORDER as usize];
    omega_powers[0] = geometry.omega;
    for bit in 1..omega_powers.len() {
        omega_powers[bit] = omega_powers[bit - 1].square();
    }
    let cached_point = |mut index: u32| {
        let mut point = geometry.offset;
        let mut bit = 0usize;
        while index != 0 {
            if index & 1 != 0 {
                point = point.mul(omega_powers[bit]);
            }
            index >>= 1;
            bit += 1;
        }
        point
    };
    let mut coordinates = vec![M31::ZERO; 2 * M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
    let mut inverses = vec![M31::ZERO; 2 * M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
    let mut values = vec![[QM31::ZERO; 4]; M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
    let mut previous_index = None;

    for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
        let start = M31_CIRCLE_FOLD_ALPHA_BYTES + fiber * M31_CIRCLE_FOLD_RECORD_BYTES;
        let index = u16::from_le_bytes(
            fixture[start..start + 2]
                .try_into()
                .map_err(|_| ProgramError::InvalidAccountData)?,
        );
        if usize::from(index) >= geometry.fiber_count as usize
            || previous_index.is_some_and(|previous| index <= previous)
        {
            return Err(ProgramError::InvalidAccountData);
        }
        previous_index = Some(index);
        let x = M31::from_le_bytes(
            fixture[start + 2..start + 6]
                .try_into()
                .map_err(|_| ProgramError::InvalidAccountData)?,
        )
        .ok_or(ProgramError::InvalidAccountData)?;
        let y = M31::from_le_bytes(
            fixture[start + 6..start + 10]
                .try_into()
                .map_err(|_| ProgramError::InvalidAccountData)?,
        )
        .ok_or(ProgramError::InvalidAccountData)?;
        if derive_coordinates {
            let point = cached_point(u32::from(index));
            if point.a != x || point.b != y || x == M31::ZERO || y == M31::ZERO {
                return Err(ProgramError::InvalidAccountData);
            }
            coordinates[2 * fiber] = x;
            coordinates[2 * fiber + 1] = y;
        }
        if !batch_invert {
            let supplied_inv_x = M31::from_le_bytes(
                fixture[start + 10..start + 14]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?,
            )
            .ok_or(ProgramError::InvalidAccountData)?;
            let supplied_inv_y = M31::from_le_bytes(
                fixture[start + 14..start + 18]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?,
            )
            .ok_or(ProgramError::InvalidAccountData)?;
            inverses[2 * fiber] = supplied_inv_x;
            inverses[2 * fiber + 1] = supplied_inv_y;
        }
        let values_start = start + 18;
        for slot in 0..4 {
            values[fiber][slot] = QM31::from_le_bytes(
                &fixture[values_start + slot * 16..values_start + (slot + 1) * 16],
            )
            .ok_or(ProgramError::InvalidAccountData)?;
        }
    }
    if batch_invert {
        m31_batch_inverse_with(&coordinates, &mut inverses, m31_inverse_syscall);
    }

    let mut accumulator = QM31::ZERO;
    for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
        let inv_2x = inverses[2 * fiber].half();
        let inv_2y = inverses[2 * fiber + 1].half();
        accumulator = accumulator.add(qm31_circle_to_line_fold4(
            values[fiber],
            alpha,
            inv_2x,
            inv_2y,
        ));
    }
    let mut encoded = [0u8; 16];
    accumulator.write_le_bytes(&mut encoded);
    Ok(sbf_hashv(&[
        b"aspis-m31-circle-basis-fold-control-v1",
        &encoded,
    ]))
}

fn run_m31_circle_basis_diagnostic(
    fixture_account: &AccountInfo,
    mode: M31CircleBasisDiagnosticMode,
    expected_sink: [u8; 32],
) -> ProgramResult {
    let data = fixture_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let expected_len = match mode {
        M31CircleBasisDiagnosticMode::RlcStructuredFourDots
        | M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes
        | M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4
        | M31CircleBasisDiagnosticMode::RlcStreamingFourDots
        | M31CircleBasisDiagnosticMode::RlcPreparedLimbs49
        | M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows
        | M31CircleBasisDiagnosticMode::EmptyLeafHashControl
        | M31CircleBasisDiagnosticMode::C1LeafHash784 => M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES,
        M31CircleBasisDiagnosticMode::FoldPrevalidatedCoordinates
        | M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse
        | M31CircleBasisDiagnosticMode::FoldCachedCoordinatesPrevalidatedInverses => {
            M31_CIRCLE_FOLD_FIXTURE_BYTES
        }
    };
    let end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    if total_len != expected_len || end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let fixture = &data[PROOF_ACCOUNT_HEADER_LEN..end];
    let sink = match mode {
        M31CircleBasisDiagnosticMode::RlcStructuredFourDots
        | M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes
        | M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4
        | M31CircleBasisDiagnosticMode::RlcStreamingFourDots
        | M31CircleBasisDiagnosticMode::RlcPreparedLimbs49
        | M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows => {
            m31_circle_basis_rlc_sink(fixture, mode)?
        }
        M31CircleBasisDiagnosticMode::EmptyLeafHashControl => {
            aspis_core::merkle::leaf_hash(sbf_hashv, 0, &[])
        }
        M31CircleBasisDiagnosticMode::C1LeafHash784 => aspis_core::merkle::leaf_hash(
            sbf_hashv,
            0,
            &fixture[M31_CIRCLE_BASIS_GAMMA_BYTES
                ..M31_CIRCLE_BASIS_GAMMA_BYTES + M31_CIRCLE_BASIS_C1_LEAF_BYTES],
        ),
        M31CircleBasisDiagnosticMode::FoldPrevalidatedCoordinates => {
            m31_circle_basis_fold_sink(fixture, mode)?
        }
        M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse => {
            m31_circle_basis_fold_sink(fixture, mode)?
        }
        M31CircleBasisDiagnosticMode::FoldCachedCoordinatesPrevalidatedInverses => {
            m31_circle_basis_fold_sink(fixture, mode)?
        }
    };
    if sink == expected_sink {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

fn trace_cu(event: aspis_core::TraceEvent) {
    match event {
        aspis_core::TraceEvent::Start => msg!("aspis-cu:start"),
        aspis_core::TraceEvent::HeaderParsed => msg!("aspis-cu:header_parsed"),
        aspis_core::TraceEvent::TranscriptReady => msg!("aspis-cu:transcript_ready"),
        aspis_core::TraceEvent::LayerOodDone(layer) => msg!("aspis-cu:layer_ood_done:{}", layer),
        aspis_core::TraceEvent::LayerSumcheckDone(layer) => {
            msg!("aspis-cu:layer_sumcheck_done:{}", layer)
        }
        aspis_core::TraceEvent::QueriesReady => msg!("aspis-cu:queries_ready"),
        aspis_core::TraceEvent::LayerStart(layer) => msg!("aspis-cu:layer_start:{}", layer),
        aspis_core::TraceEvent::LayerMerkleDone(layer) => {
            msg!("aspis-cu:layer_merkle_done:{}", layer)
        }
        aspis_core::TraceEvent::LayerFoldDone(layer) => msg!("aspis-cu:layer_fold_done:{}", layer),
        aspis_core::TraceEvent::FinalCheckStart => msg!("aspis-cu:final_check_start"),
        aspis_core::TraceEvent::Done => msg!("aspis-cu:done"),
    }
    sol_log_compute_units();
}

fn trace_m31_fresh_kappa_cu(event: aspis_core::circle_candidate_verify::FreshKappaTraceEvent) {
    use aspis_core::circle_candidate_verify::FreshKappaTraceEvent;
    match event {
        FreshKappaTraceEvent::Parsed => msg!("aspis-cu:m31_fk_parsed"),
        FreshKappaTraceEvent::TranscriptDone => msg!("aspis-cu:m31_fk_transcript_done"),
        FreshKappaTraceEvent::RelationDone => msg!("aspis-cu:m31_fk_relation_done"),
        FreshKappaTraceEvent::MerkleDone => msg!("aspis-cu:m31_fk_merkle_done"),
        FreshKappaTraceEvent::QueriesDone => msg!("aspis-cu:m31_fk_queries_done"),
    }
    sol_log_compute_units();
}

fn trace_m31_fresh_kappa_query_cu(completed: usize) {
    msg!("aspis-cu:m31_fk_queries_completed={}", completed);
    sol_log_compute_units();
}

fn run_layout_probe(
    log_rows: u8,
    columns: u16,
    query_count: u16,
    leaf_bytes: u16,
) -> ProgramResult {
    if log_rows > 16 || columns == 0 || query_count == 0 || leaf_bytes == 0 || leaf_bytes > 4096 {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!(
        "aspis-layout:start log_rows={} columns={} queries={} leaf_bytes={}",
        log_rows,
        columns,
        query_count,
        leaf_bytes
    );
    sol_log_compute_units();

    let leaf = vec![0u8; leaf_bytes as usize];
    let mut acc = [0u8; 32];
    for q in 0..query_count {
        let q_bytes = q.to_le_bytes();
        acc = hashv(&[b"aspis-layout-leaf", &leaf, &q_bytes]).to_bytes();
    }
    msg!("aspis-layout:leaf_hash_done");
    sol_log_compute_units();

    for q in 0..query_count {
        for level in 0..log_rows {
            let q_bytes = q.to_le_bytes();
            let level_bytes = level.to_le_bytes();
            acc = hashv(&[b"aspis-layout-node", &acc, &q_bytes, &level_bytes]).to_bytes();
        }
    }
    msg!("aspis-layout:merkle_done");
    sol_log_compute_units();

    let gamma = aspis_core::field::QM31 {
        c0: aspis_core::field::CM31 {
            a: aspis_core::field::M31(7),
            b: aspis_core::field::M31(11),
        },
        c1: aspis_core::field::CM31 {
            a: aspis_core::field::M31(13),
            b: aspis_core::field::M31(17),
        },
    };
    let mut rlc = aspis_core::field::QM31::ZERO;
    for q in 0..query_count {
        for c in 0..columns {
            let limb = aspis_core::field::CM31::from_m31(aspis_core::field::M31(
                1 + ((q as u32).wrapping_mul(131) + c as u32) % 1_000_000,
            ));
            rlc = rlc.add(gamma.mul_cm31(limb));
        }
    }
    let mut rlc_bytes = [0u8; 16];
    rlc.write_le_bytes(&mut rlc_bytes);
    let digest = hashv(&[b"aspis-layout-rlc", &acc, &rlc_bytes]).to_bytes();
    msg!("aspis-layout:rlc_done");
    sol_log_compute_units();

    if digest[0] == 255 {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!("aspis-layout:done");
    Ok(())
}

fn verify_uploaded_proof(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    claim: Option<&aspis_core::EvaluationClaim>,
    profile_cu: bool,
    denominator_mode: u8,
    allow_exact_wide_scaffold: bool,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    if end > data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let proof = &data[PROOF_ACCOUNT_HEADER_LEN..end];
    let trace_fn = if profile_cu {
        Some(trace_cu as _)
    } else {
        None
    };
    let result = if allow_exact_wide_scaffold {
        aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            proof,
            &statement_digest,
            claim,
            sbf_hashv,
        )
    } else if denominator_mode == 2 {
        aspis_core::verify_with_claim_trace_and_inverse(
            proof,
            &statement_digest,
            claim,
            sbf_hashv,
            trace_fn,
            m31_inverse_syscall,
        )
    } else if denominator_mode == 1 {
        aspis_core::verify_with_claim_and_trace(
            proof,
            &statement_digest,
            claim,
            sbf_hashv,
            trace_fn,
        )
    } else {
        aspis_core::verify_with_claim_trace_and_inverse(
            proof,
            &statement_digest,
            claim,
            sbf_hashv,
            trace_fn,
            aspis_core::field::M31::inv,
        )
    };
    match result {
        Ok(()) => {
            msg!("aspis: proof accepted");
            Ok(())
        }
        Err(err) => {
            msg!("aspis: proof rejected");
            Err(ProgramError::Custom(err.code()))
        }
    }
}

fn proof_account_initialized(data: &[u8]) -> bool {
    data.len() >= PROOF_ACCOUNT_HEADER_LEN && data[0..4] == PROOF_ACCOUNT_MAGIC
}

fn proof_account_finalized(data: &[u8]) -> bool {
    proof_account_initialized(data)
        && data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .iter()
            .all(|byte| *byte == 0)
}

fn proof_len(data: &[u8]) -> Result<usize, ProgramError> {
    if data.len() < PROOF_ACCOUNT_HEADER_LEN || data[0..4] != PROOF_ACCOUNT_MAGIC {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(u32::from_le_bytes(data[4..8].try_into().unwrap()) as usize)
}

/// Validate only the append-only M31-circle diagnostic envelope. This is a
/// cheap framing gate: it intentionally performs no transcript, field,
/// Merkle, or statement work and therefore cannot accept a proof.
fn validate_m31_circle_v4_diagnostic_header(
    proof: &[u8],
) -> Result<aspis_core::proof::Header, ProgramError> {
    use aspis_core::params::{MerkleMode, PROFILE_CAPACITY_LR10_Q36_G16 as DIAGNOSTIC_PROFILE};
    use aspis_core::proof::{
        Header, FLAG_EVALUATION_CLAIM, FLAG_M31_CIRCLE_C1_DIAGNOSTIC, FLAG_SECOND_PHASE,
        VERSION_V4_S2,
    };

    let header = Header::parse(proof).ok_or(ProgramError::Custom(
        aspis_core::VerifyError::BadHeader.code(),
    ))?;
    let required_flags = FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;
    if header.version != VERSION_V4_S2
        || header.flags != required_flags
        || header.profile_id != DIAGNOSTIC_PROFILE.id
        || header.log_rows != DIAGNOSTIC_PROFILE.log_rows
        || header.log_blowup != DIAGNOSTIC_PROFILE.log_blowup
        || header.query_count != DIAGNOSTIC_PROFILE.query_count
        || header.grinding_bits != DIAGNOSTIC_PROFILE.grinding_bits
        || header.fold_payload != aspis_core::FoldPayload::RawFibers as u8
        || header.merkle_mode != MerkleMode::Radix4MinimalSubtree as u8
        || header.num_rounds != DIAGNOSTIC_PROFILE.num_rounds()
        || header.final_poly_log_len != aspis_core::params::FINAL_POLY_LOG_LEN
    {
        return Err(ProgramError::Custom(
            aspis_core::VerifyError::BadHeader.code(),
        ));
    }
    Ok(header)
}

fn validate_m31_circle_v4_diagnostic_public_inputs(claim_z: &[[u8; 16]]) -> ProgramResult {
    if claim_z.len() != 10
        || claim_z
            .iter()
            .any(|coordinate| aspis_core::field::QM31::from_le_bytes(coordinate).is_none())
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}

fn validate_uploaded_m31_circle_v4_diagnostic_header(
    proof_account: &AccountInfo,
) -> Result<aspis_core::proof::Header, ProgramError> {
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..end)
        .ok_or(ProgramError::InvalidAccountData)?;
    validate_m31_circle_v4_diagnostic_header(proof)
}

fn verify_uploaded_m31_circle_fresh_kappa(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    claim_z: &[[u8; 16]],
) -> ProgramResult {
    if claim_z.len() != 10 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let z: [aspis_core::field::QM31; 10] = claim_z
        .iter()
        .map(|bytes| aspis_core::field::QM31::from_le_bytes(bytes))
        .collect::<Option<Vec<_>>>()
        .ok_or(ProgramError::InvalidInstructionData)?
        .try_into()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..end)
        .ok_or(ProgramError::InvalidAccountData)?;

    msg!("aspis-cu:m31_circle_fresh_kappa_start");
    sol_log_compute_units();
    aspis_core::circle_candidate_verify::verify_fresh_kappa_candidate_with_trace(
        proof,
        &statement_digest,
        &z,
        sbf_hashv,
        Some(trace_m31_fresh_kappa_cu),
        Some(trace_m31_fresh_kappa_query_cu),
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    msg!("aspis-cu:m31_circle_fresh_kappa_done");
    sol_log_compute_units();
    Ok(())
}

fn measure_uploaded_m31_circle_johnson(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    claim_z: &[[u8; 16]],
    phase: JohnsonM31CircleDiagnosticPhase,
    start: u16,
    end: u16,
) -> ProgramResult {
    if claim_z.len() != 10 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let z: [aspis_core::field::QM31; 10] = claim_z
        .iter()
        .map(|bytes| aspis_core::field::QM31::from_le_bytes(bytes))
        .collect::<Option<Vec<_>>>()
        .ok_or(ProgramError::InvalidInstructionData)?
        .try_into()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let segment = match phase {
        JohnsonM31CircleDiagnosticPhase::PreparedBase => {
            aspis_core::circle_openings::CircleQuerySegment::PreparedBase
        }
        JohnsonM31CircleDiagnosticPhase::Layer0Range => {
            aspis_core::circle_openings::CircleQuerySegment::Layer0Range {
                start: usize::from(start),
                end: usize::from(end),
            }
        }
        JohnsonM31CircleDiagnosticPhase::LaterAll => {
            aspis_core::circle_openings::CircleQuerySegment::LaterAll
        }
        JohnsonM31CircleDiagnosticPhase::Full => {
            aspis_core::circle_openings::CircleQuerySegment::Full
        }
    };
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..PROOF_ACCOUNT_HEADER_LEN + total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    aspis_core::circle_candidate_verify::verify_johnson_candidate_segment(
        proof,
        &statement_digest,
        &z,
        sbf_hashv,
        segment,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)
}

fn measure_uploaded_m31_circle_rate16(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    claim_z: &[[u8; 16]],
    phase: JohnsonM31CircleDiagnosticPhase,
    start: u16,
    end: u16,
) -> ProgramResult {
    if claim_z.len() != 10 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let z: [aspis_core::field::QM31; 10] = claim_z
        .iter()
        .map(|bytes| aspis_core::field::QM31::from_le_bytes(bytes))
        .collect::<Option<Vec<_>>>()
        .ok_or(ProgramError::InvalidInstructionData)?
        .try_into()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let segment = match phase {
        JohnsonM31CircleDiagnosticPhase::PreparedBase => {
            aspis_core::circle_openings::CircleQuerySegment::PreparedBase
        }
        JohnsonM31CircleDiagnosticPhase::Layer0Range => {
            aspis_core::circle_openings::CircleQuerySegment::Layer0Range {
                start: usize::from(start),
                end: usize::from(end),
            }
        }
        JohnsonM31CircleDiagnosticPhase::LaterAll => {
            aspis_core::circle_openings::CircleQuerySegment::LaterAll
        }
        JohnsonM31CircleDiagnosticPhase::Full => {
            aspis_core::circle_openings::CircleQuerySegment::Full
        }
    };
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..end)
        .ok_or(ProgramError::InvalidAccountData)?;
    aspis_core::circle_candidate_verify::verify_rate16_candidate_segment(
        proof,
        &statement_digest,
        &z,
        sbf_hashv,
        segment,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)
}

fn measure_uploaded_m31_circle_rate16_hardened(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    claim_z: &[[u8; 16]],
    phase: JohnsonM31CircleDiagnosticPhase,
    start: u16,
    end: u16,
) -> ProgramResult {
    if claim_z.len() != 10 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let z: [aspis_core::field::QM31; 10] = claim_z
        .iter()
        .map(|bytes| aspis_core::field::QM31::from_le_bytes(bytes))
        .collect::<Option<Vec<_>>>()
        .ok_or(ProgramError::InvalidInstructionData)?
        .try_into()
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let segment = match phase {
        JohnsonM31CircleDiagnosticPhase::PreparedBase => {
            aspis_core::circle_openings::CircleQuerySegment::PreparedBase
        }
        JohnsonM31CircleDiagnosticPhase::Layer0Range => {
            aspis_core::circle_openings::CircleQuerySegment::Layer0Range {
                start: usize::from(start),
                end: usize::from(end),
            }
        }
        JohnsonM31CircleDiagnosticPhase::LaterAll => {
            aspis_core::circle_openings::CircleQuerySegment::LaterAll
        }
        JohnsonM31CircleDiagnosticPhase::Full => {
            aspis_core::circle_openings::CircleQuerySegment::Full
        }
    };
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..proof_end)
        .ok_or(ProgramError::InvalidAccountData)?;
    aspis_core::circle_candidate_verify::verify_rate16_hardened_candidate_segment(
        proof,
        &statement_digest,
        &z,
        sbf_hashv,
        segment,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)
}

#[inline(never)]
fn verify_payment_hiding_profile15_statement(
    verified: &aspis_core::circle_hiding_verify::VerifiedPaymentHidingCandidate<'_>,
    public_input: &[u8; 104],
) -> ProgramResult {
    let mut public_values = [aspis_core::field::M31::ZERO; 25];
    for (index, output) in public_values.iter_mut().enumerate() {
        *output = aspis_core::field::M31::from_le_bytes(
            public_input[index * 4..index * 4 + 4].try_into().unwrap(),
        )
        .ok_or(ProgramError::InvalidInstructionData)?;
    }
    let public = aspis_statement::SpendPublic {
        anchor: public_values[0..8].try_into().unwrap(),
        nullifier: public_values[8..16].try_into().unwrap(),
        output_commitment: public_values[16..24].try_into().unwrap(),
        asset_id: public_values[24],
        fee: u32::from_le_bytes(public_input[100..104].try_into().unwrap()),
    };
    let openings = Box::new(aspis_statement::DirectRangeHidingPointOpeningsV4 {
        c1: core::array::from_fn(|column| verified.prefix.statement_evaluation(column).unwrap()),
        c1_xor11: core::array::from_fn(|column| {
            verified.prefix.statement_evaluation(51 + column).unwrap()
        }),
        h1: verified.prefix.statement_evaluation(49).unwrap(),
        payment_mask: verified.prefix.statement_evaluation(50).unwrap(),
    });
    let original = aspis_statement::direct_range_hiding_payment_terminal_value_with_trace(
        &public,
        &openings,
        &verified.schedule.prefix.z,
        &verified.schedule.prefix.batching,
        verified.schedule.prefix.lambda,
        verified.schedule.prefix.chi,
        Some(trace_payment_hiding_statement_cu),
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    let mask = aspis_core::statement_hiding::payment_sparse_mask_value(
        &openings.c1,
        openings.payment_mask,
        &verified.schedule.prefix.z,
    );
    let expected_masked = mask.add(verified.schedule.prefix.eta.mul(original));
    if expected_masked != verified.schedule.prefix.masked_terminal_claim {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}

fn decode_spend_public(
    public_input: &[u8; 104],
) -> Result<aspis_statement::SpendPublic, ProgramError> {
    let mut public_values = [aspis_core::field::M31::ZERO; 25];
    for (index, output) in public_values.iter_mut().enumerate() {
        *output = aspis_core::field::M31::from_le_bytes(
            public_input[index * 4..index * 4 + 4].try_into().unwrap(),
        )
        .ok_or(ProgramError::InvalidInstructionData)?;
    }
    Ok(aspis_statement::SpendPublic {
        anchor: public_values[0..8].try_into().unwrap(),
        nullifier: public_values[8..16].try_into().unwrap(),
        output_commitment: public_values[16..24].try_into().unwrap(),
        asset_id: public_values[24],
        fee: u32::from_le_bytes(public_input[100..104].try_into().unwrap()),
    })
}

fn trace_state_only_width28_phase(phase: aspis_statement::StateOnlyVerifyPhase) {
    match phase {
        aspis_statement::StateOnlyVerifyPhase::Parsed => msg!("aspis-cu:state28_parse_done"),
        aspis_statement::StateOnlyVerifyPhase::Transcript => {
            msg!("aspis-cu:state28_transcript_done")
        }
        aspis_statement::StateOnlyVerifyPhase::Terminal => {
            msg!("aspis-cu:state28_terminal_done")
        }
        aspis_statement::StateOnlyVerifyPhase::Relation => {
            msg!("aspis-cu:state28_relation_done")
        }
        aspis_statement::StateOnlyVerifyPhase::OpeningsParsed => {
            msg!("aspis-cu:state28_openings_parse_done")
        }
        aspis_statement::StateOnlyVerifyPhase::QueriesDone => {
            msg!("aspis-cu:state28_queries_done")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalPrepared => {
            msg!("aspis-cu:state28_terminal_prepared")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalPoseidon => {
            msg!("aspis-cu:state28_terminal_poseidon")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticInitial => {
            msg!("aspis-cu:state28_terminal_semantic_initial")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticAbsorption => {
            msg!("aspis-cu:state28_terminal_semantic_absorption")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticMerkle => {
            msg!("aspis-cu:state28_terminal_semantic_merkle")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticRange => {
            msg!("aspis-cu:state28_terminal_semantic_range")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticPublic => {
            msg!("aspis-cu:state28_terminal_semantic_public")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCopyPatterns => {
            msg!("aspis-cu:state28_terminal_copy_patterns")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCopyRouting => {
            msg!("aspis-cu:state28_terminal_copy_routing")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCopy => {
            msg!("aspis-cu:state28_terminal_copy_algebra")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCompositionEquality => {
            msg!("aspis-cu:state28_terminal_composition_equality")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalMask => {
            msg!("aspis-cu:state28_terminal_mask")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalFinal => {
            msg!("aspis-cu:state28_terminal_final")
        }
    }
    sol_log_compute_units();
}

fn trace_atomic_profile20_phase(phase: aspis_statement::StateOnlyVerifyPhase) {
    match phase {
        aspis_statement::StateOnlyVerifyPhase::Parsed => msg!("aspis-cu:atomic20_parse_done"),
        aspis_statement::StateOnlyVerifyPhase::Transcript => {
            msg!("aspis-cu:atomic20_transcript_done")
        }
        aspis_statement::StateOnlyVerifyPhase::Terminal => {
            msg!("aspis-cu:atomic20_terminal_done")
        }
        aspis_statement::StateOnlyVerifyPhase::Relation => {
            msg!("aspis-cu:atomic20_relation_done")
        }
        aspis_statement::StateOnlyVerifyPhase::OpeningsParsed => {
            msg!("aspis-cu:atomic20_openings_parse_done")
        }
        aspis_statement::StateOnlyVerifyPhase::QueriesDone => {
            msg!("aspis-cu:atomic20_queries_done")
        }
        _ => return,
    }
    sol_log_compute_units();
}

fn trace_state_only_relation_structural_phase(
    phase: aspis_statement::state_only_verify::StateOnlyRelationStructuralPhase,
) {
    use aspis_statement::state_only_verify::StateOnlyRelationStructuralPhase;
    match phase {
        StateOnlyRelationStructuralPhase::Parsed => msg!("aspis-cu:rel44_parse_done"),
        StateOnlyRelationStructuralPhase::Transcript => {
            msg!("aspis-cu:rel44_transcript_done")
        }
        StateOnlyRelationStructuralPhase::Prepared => msg!("aspis-cu:rel44_prepare_done"),
        StateOnlyRelationStructuralPhase::PointWeights => {
            msg!("aspis-cu:rel44_point_weights_done")
        }
        StateOnlyRelationStructuralPhase::Round0 => msg!("aspis-cu:rel44_round0_done"),
        StateOnlyRelationStructuralPhase::Round1 => msg!("aspis-cu:rel44_round1_done"),
        StateOnlyRelationStructuralPhase::Round2 => msg!("aspis-cu:rel44_round2_done"),
        StateOnlyRelationStructuralPhase::Round3 => msg!("aspis-cu:rel44_round3_done"),
        StateOnlyRelationStructuralPhase::Final => msg!("aspis-cu:rel44_final_done"),
    }
    sol_log_compute_units();
}

#[inline(never)]
fn run_state_only_relation_structural_probe(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    deferred_binary_copy: bool,
    corrupt_claim: bool,
) -> ProgramResult {
    msg!("aspis-cu:rel44_instruction_start");
    sol_log_compute_units();
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..proof_end)
        .ok_or(ProgramError::InvalidAccountData)?;
    msg!("aspis-cu:rel44_proof_loaded");
    sol_log_compute_units();
    aspis_statement::state_only_verify::verify_state_only_relation_structural_probe_unmined_traced(
        proof,
        &statement_digest,
        sbf_hashv,
        deferred_binary_copy,
        corrupt_claim,
        trace_state_only_relation_structural_phase,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    msg!("aspis-cu:rel44_done");
    sol_log_compute_units();
    Ok(())
}

#[inline(never)]
fn run_state_only_masked_switch_profile21_probe(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    diagnostic_unmined: bool,
    direct_u_query_evaluation: bool,
) -> ProgramResult {
    msg!("aspis-cu:switch45_instruction_start");
    sol_log_compute_units();
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..proof_end)
        .ok_or(ProgramError::InvalidAccountData)?;
    msg!("aspis-cu:switch45_proof_loaded");
    sol_log_compute_units();
    match (diagnostic_unmined, direct_u_query_evaluation) {
        // Diagnostic mode table, keeping the tag-45 wire shape stable:
        // 10 = fused four-query M31 candidate, 11 = scalar M31 reference,
        // 01 = generic-QM31 reference, 00 = no-bypass production API.
        (true, false) => {
            aspis_core::state_only_masked_switch::verify_state_only_masked_switch_production_equivalent_unmined_traced(
                proof,
                &statement_digest,
                sbf_hashv,
                trace_state_only_masked_switch_profile21,
            )
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        }
        (true, true) => {
            aspis_core::state_only_masked_switch::verify_state_only_masked_switch_m31_sparse_unmined_traced(
                proof,
                &statement_digest,
                sbf_hashv,
                trace_state_only_masked_switch_profile21,
            )
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        }
        (false, true) => {
            aspis_core::state_only_masked_switch::verify_state_only_masked_switch_diagnostic_unmined_traced(
                proof,
                &statement_digest,
                sbf_hashv,
                trace_state_only_masked_switch_profile21,
            )
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        }
        (false, false) => {
            aspis_core::state_only_masked_switch::verify_state_only_masked_switch(
                proof,
                &statement_digest,
                sbf_hashv,
            )
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        }
    }
    msg!("aspis-cu:switch45_done");
    sol_log_compute_units();
    Ok(())
}

fn trace_state_only_masked_switch_profile21(
    event: aspis_core::state_only_masked_switch::MaskedSwitchTraceEvent,
) {
    use aspis_core::state_only_masked_switch::MaskedSwitchTraceEvent;
    match event {
        MaskedSwitchTraceEvent::HeaderParsed => msg!("aspis-cu:switch45_header_parsed"),
        MaskedSwitchTraceEvent::TranscriptAndPrefixDone => {
            msg!("aspis-cu:switch45_transcript_fields_done")
        }
        MaskedSwitchTraceEvent::QueryEquationsDone => {
            msg!("aspis-cu:switch45_query_equations_done")
        }
        MaskedSwitchTraceEvent::XfMerkleDone => msg!("aspis-cu:switch45_xf_merkle_done"),
        MaskedSwitchTraceEvent::UMerkleDone => msg!("aspis-cu:switch45_u_merkle_done"),
    }
    sol_log_compute_units();
}

#[inline(never)]
fn verify_uploaded_atomic_profile20_cost_candidate(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    public_input: &[u8; 104],
    output_anchor: [u8; 32],
    expected_atomic_terminal: [u8; 16],
) -> ProgramResult {
    msg!("aspis-cu:atomic20_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let output_anchor = aspis_statement::decode_digest_canonical(&output_anchor)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let expected_atomic_terminal =
        aspis_core::field::QM31::from_le_bytes(&expected_atomic_terminal)
            .ok_or(ProgramError::InvalidInstructionData)?;
    let statement = aspis_statement::AtomicPaymentStatementV3 {
        pool: [0u8; 32],
        sequence: 0,
        spend: public,
        output_anchor,
    };
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..proof_end)
        .ok_or(ProgramError::InvalidAccountData)?;
    msg!("aspis-cu:atomic20_proof_loaded");
    sol_log_compute_units();
    aspis_statement::verify_state_only_atomic_terminal_cost_candidate_unmined_traced(
        proof,
        &statement,
        &statement_digest,
        expected_atomic_terminal,
        sbf_hashv,
        trace_atomic_profile20_phase,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    msg!("aspis-cu:atomic20_done");
    sol_log_compute_units();
    Ok(())
}

fn trace_atomic_profile20_acceptance_phase(phase: aspis_statement::StateOnlyVerifyPhase) {
    match phase {
        aspis_statement::StateOnlyVerifyPhase::Parsed => msg!("aspis-cu:atomic46_parse_done"),
        aspis_statement::StateOnlyVerifyPhase::Transcript => {
            msg!("aspis-cu:atomic46_transcript_done")
        }
        aspis_statement::StateOnlyVerifyPhase::Terminal => {
            msg!("aspis-cu:atomic46_terminal_done")
        }
        aspis_statement::StateOnlyVerifyPhase::Relation => {
            msg!("aspis-cu:atomic46_relation_done")
        }
        aspis_statement::StateOnlyVerifyPhase::OpeningsParsed => {
            msg!("aspis-cu:atomic46_openings_parse_done")
        }
        aspis_statement::StateOnlyVerifyPhase::QueriesDone => {
            msg!("aspis-cu:atomic46_queries_done")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalPrepared => {
            msg!("aspis-cu:atomic46_terminal_prepared")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalPoseidon => {
            msg!("aspis-cu:atomic46_terminal_poseidon")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticInitial => {
            msg!("aspis-cu:atomic46_terminal_semantic_initial")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticAbsorption => {
            msg!("aspis-cu:atomic46_terminal_semantic_absorption")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticMerkle => {
            msg!("aspis-cu:atomic46_terminal_semantic_merkle")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticRange => {
            msg!("aspis-cu:atomic46_terminal_semantic_range")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalSemanticPublic => {
            msg!("aspis-cu:atomic46_terminal_semantic_public")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCopyPatterns => {
            msg!("aspis-cu:atomic46_terminal_copy_patterns")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCopyRouting => {
            msg!("aspis-cu:atomic46_terminal_copy_routing")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCopy => {
            msg!("aspis-cu:atomic46_terminal_copy_algebra")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalCompositionEquality => {
            msg!("aspis-cu:atomic46_terminal_composition_equality")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalMask => {
            msg!("aspis-cu:atomic46_terminal_mask")
        }
        aspis_statement::StateOnlyVerifyPhase::TerminalFinal => {
            msg!("aspis-cu:atomic46_terminal_final")
        }
    }
    sol_log_compute_units();
}

// Profile 21's hiding-rank proof and its integrated verifier must consume the
// same frozen logical-to-natural q16 basis.  Keep this pin in the wrapper
// crate as well as in `aspis-core`: changing the generated basis without a
// profile/version bump must make the candidate fail at build time.
const ATOMIC_PROFILE21_MASKED_SWITCH_BASIS_FINGERPRINT: u64 = 0xceb3_5dd3_ee50_e051;
const _: () = assert!(
    aspis_core::state_only_masked_switch_basis::MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT
        == ATOMIC_PROFILE21_MASKED_SWITCH_BASIS_FINGERPRINT
);

#[cfg(feature = "profile21-integrated-candidate")]
fn trace_atomic_profile21_acceptance_phase(
    event: aspis_statement::state_only_profile21::Profile21TraceEvent,
) {
    use aspis_statement::state_only_profile21::Profile21TraceEvent;
    match event {
        Profile21TraceEvent::ParseBase => msg!("aspis-cu:atomic50_parse_base"),
        Profile21TraceEvent::TranscriptBase => msg!("aspis-cu:atomic50_transcript_base"),
        Profile21TraceEvent::Terminal => msg!("aspis-cu:atomic50_terminal"),
        Profile21TraceEvent::Relation => msg!("aspis-cu:atomic50_relation"),
        Profile21TraceEvent::ExistingOpenings => msg!("aspis-cu:atomic50_existing_openings"),
        Profile21TraceEvent::ExistingQueries => msg!("aspis-cu:atomic50_existing_queries"),
        Profile21TraceEvent::SourceXfSharedC2 => {
            msg!("aspis-cu:atomic50_source_xf_shared_c2")
        }
        Profile21TraceEvent::SourceWork => msg!("aspis-cu:atomic50_source_work"),
        Profile21TraceEvent::TranslatedSplice => msg!("aspis-cu:atomic50_translated_splice"),
        Profile21TraceEvent::DirectUQuery => msg!("aspis-cu:atomic50_direct_u_query"),
        Profile21TraceEvent::FinalQueryWork => msg!("aspis-cu:atomic50_final_query_work"),
        Profile21TraceEvent::Complete => msg!("aspis-cu:atomic50_core_complete"),
    }
    sol_log_compute_units();
}

#[cfg(feature = "diagnostic-unmined-profile21-mutation")]
fn trace_atomic_profile21_mutation_phase(
    event: aspis_statement::state_only_profile21::Profile21TraceEvent,
) {
    use aspis_statement::state_only_profile21::Profile21TraceEvent;
    match event {
        Profile21TraceEvent::ParseBase => msg!("aspis-cu:atomic52_parse_base"),
        Profile21TraceEvent::TranscriptBase => msg!("aspis-cu:atomic52_transcript_base"),
        Profile21TraceEvent::Terminal => msg!("aspis-cu:atomic52_terminal"),
        Profile21TraceEvent::Relation => msg!("aspis-cu:atomic52_relation"),
        Profile21TraceEvent::ExistingOpenings => msg!("aspis-cu:atomic52_existing_openings"),
        Profile21TraceEvent::ExistingQueries => msg!("aspis-cu:atomic52_existing_queries"),
        Profile21TraceEvent::SourceXfSharedC2 => {
            msg!("aspis-cu:atomic52_source_xf_shared_c2")
        }
        Profile21TraceEvent::SourceWork => msg!("aspis-cu:atomic52_source_work"),
        Profile21TraceEvent::TranslatedSplice => msg!("aspis-cu:atomic52_translated_splice"),
        Profile21TraceEvent::DirectUQuery => msg!("aspis-cu:atomic52_direct_u_query"),
        Profile21TraceEvent::FinalQueryWork => msg!("aspis-cu:atomic52_final_query_work"),
        Profile21TraceEvent::Complete => msg!("aspis-cu:atomic52_core_complete"),
    }
    sol_log_compute_units();
}

#[cfg(feature = "diagnostic-unmined-profile21-mutation")]
fn trace_atomic_profile21_mutation_event(event: atomic_payment::AtomicPaymentTransitionTraceEvent) {
    use atomic_payment::AtomicPaymentTransitionTraceEvent;
    match event {
        AtomicPaymentTransitionTraceEvent::AccountsValidatedProgramOwned => {
            msg!("aspis-cu:atomic52_accounts_validated_program_owned")
        }
        AtomicPaymentTransitionTraceEvent::AccountsValidatedSystemOwned => {
            msg!("aspis-cu:atomic52_accounts_validated_system_owned")
        }
        AtomicPaymentTransitionTraceEvent::StatementDigestDone => {
            msg!("aspis-cu:atomic52_statement_digest_done")
        }
        AtomicPaymentTransitionTraceEvent::ProofVerified => {
            msg!("aspis-cu:atomic52_proof_verified")
        }
        AtomicPaymentTransitionTraceEvent::ProgramOwnedMarkerReady => {
            msg!("aspis-cu:atomic52_program_marker_ready")
        }
        AtomicPaymentTransitionTraceEvent::SystemOwnedMarkerCreated => {
            msg!("aspis-cu:atomic52_system_marker_created")
        }
        AtomicPaymentTransitionTraceEvent::MutableStateRechecked => {
            msg!("aspis-cu:atomic52_state_rechecked")
        }
        AtomicPaymentTransitionTraceEvent::StateApplied => {
            msg!("aspis-cu:atomic52_state_applied")
        }
    }
    sol_log_compute_units();
}

#[cfg(feature = "profile22-integrated-candidate")]
fn trace_atomic_profile22_acceptance_phase(
    event: aspis_statement::state_only_profile22::Profile22TraceEvent,
) {
    use aspis_statement::state_only_profile22::Profile22TraceEvent;
    match event {
        Profile22TraceEvent::Parsed => msg!("aspis-cu:atomic56_parsed"),
        Profile22TraceEvent::Transcript => msg!("aspis-cu:atomic56_transcript"),
        Profile22TraceEvent::Terminal => msg!("aspis-cu:atomic56_terminal"),
        Profile22TraceEvent::Relation => msg!("aspis-cu:atomic56_relation"),
        Profile22TraceEvent::Openings => msg!("aspis-cu:atomic56_openings"),
        Profile22TraceEvent::Layer0Queries => msg!("aspis-cu:atomic56_layer0_queries"),
        Profile22TraceEvent::LaterQueries => msg!("aspis-cu:atomic56_later_queries"),
        Profile22TraceEvent::Complete => msg!("aspis-cu:atomic56_core_complete"),
    }
    sol_log_compute_units();
}

#[cfg(feature = "diagnostic-unmined-profile22-mutation")]
fn trace_atomic_profile22_mutation_phase(
    event: aspis_statement::state_only_profile22::Profile22TraceEvent,
) {
    use aspis_statement::state_only_profile22::Profile22TraceEvent;
    match event {
        Profile22TraceEvent::Parsed => msg!("aspis-cu:atomic58_parsed"),
        Profile22TraceEvent::Transcript => msg!("aspis-cu:atomic58_transcript"),
        Profile22TraceEvent::Terminal => msg!("aspis-cu:atomic58_terminal"),
        Profile22TraceEvent::Relation => msg!("aspis-cu:atomic58_relation"),
        Profile22TraceEvent::Openings => msg!("aspis-cu:atomic58_openings"),
        Profile22TraceEvent::Layer0Queries => msg!("aspis-cu:atomic58_layer0_queries"),
        Profile22TraceEvent::LaterQueries => msg!("aspis-cu:atomic58_later_queries"),
        Profile22TraceEvent::Complete => msg!("aspis-cu:atomic58_core_complete"),
    }
    sol_log_compute_units();
}

#[cfg(feature = "profile23-integrated-candidate")]
fn trace_atomic_profile23_acceptance_phase(
    event: aspis_statement::state_only_profile23::Profile23TraceEvent,
) {
    use aspis_statement::state_only_profile23::Profile23TraceEvent;
    match event {
        Profile23TraceEvent::Parsed => msg!("aspis-cu:atomic59_parsed"),
        Profile23TraceEvent::Transcript => msg!("aspis-cu:atomic59_transcript"),
        Profile23TraceEvent::Terminal => msg!("aspis-cu:atomic59_terminal"),
        Profile23TraceEvent::Relation => msg!("aspis-cu:atomic59_relation"),
        Profile23TraceEvent::Openings => msg!("aspis-cu:atomic59_openings"),
        Profile23TraceEvent::Layer0Queries => msg!("aspis-cu:atomic59_layer0_queries"),
        Profile23TraceEvent::LaterQueries => msg!("aspis-cu:atomic59_later_queries"),
        Profile23TraceEvent::Complete => msg!("aspis-cu:atomic59_core_complete"),
    }
    sol_log_compute_units();
}

#[cfg(feature = "diagnostic-unmined-profile23-mutation")]
fn trace_atomic_profile23_mutation_phase(
    event: aspis_statement::state_only_profile23::Profile23TraceEvent,
) {
    use aspis_statement::state_only_profile23::Profile23TraceEvent;
    match event {
        Profile23TraceEvent::Parsed => msg!("aspis-cu:atomic61_parsed"),
        Profile23TraceEvent::Transcript => msg!("aspis-cu:atomic61_transcript"),
        Profile23TraceEvent::Terminal => msg!("aspis-cu:atomic61_terminal"),
        Profile23TraceEvent::Relation => msg!("aspis-cu:atomic61_relation"),
        Profile23TraceEvent::Openings => msg!("aspis-cu:atomic61_openings"),
        Profile23TraceEvent::Layer0Queries => msg!("aspis-cu:atomic61_layer0_queries"),
        Profile23TraceEvent::LaterQueries => msg!("aspis-cu:atomic61_later_queries"),
        Profile23TraceEvent::Complete => msg!("aspis-cu:atomic61_core_complete"),
    }
    sol_log_compute_units();
}

#[cfg(feature = "diagnostic-unmined-profile23-mutation")]
fn trace_atomic_profile23_mutation_event(event: atomic_payment::AtomicPaymentTransitionTraceEvent) {
    use atomic_payment::AtomicPaymentTransitionTraceEvent;
    match event {
        AtomicPaymentTransitionTraceEvent::AccountsValidatedProgramOwned => {
            msg!("aspis-cu:atomic61_accounts_validated_program_owned")
        }
        AtomicPaymentTransitionTraceEvent::AccountsValidatedSystemOwned => {
            msg!("aspis-cu:atomic61_accounts_validated_system_owned")
        }
        AtomicPaymentTransitionTraceEvent::StatementDigestDone => {
            msg!("aspis-cu:atomic61_statement_digest_done")
        }
        AtomicPaymentTransitionTraceEvent::ProofVerified => {
            msg!("aspis-cu:atomic61_proof_verified")
        }
        AtomicPaymentTransitionTraceEvent::ProgramOwnedMarkerReady => {
            msg!("aspis-cu:atomic61_program_marker_ready")
        }
        AtomicPaymentTransitionTraceEvent::SystemOwnedMarkerCreated => {
            msg!("aspis-cu:atomic61_system_marker_created")
        }
        AtomicPaymentTransitionTraceEvent::MutableStateRechecked => {
            msg!("aspis-cu:atomic61_state_rechecked")
        }
        AtomicPaymentTransitionTraceEvent::StateApplied => {
            msg!("aspis-cu:atomic61_state_applied")
        }
    }
    sol_log_compute_units();
}

#[cfg(feature = "diagnostic-unmined-profile22-mutation")]
fn trace_atomic_profile22_mutation_event(event: atomic_payment::AtomicPaymentTransitionTraceEvent) {
    use atomic_payment::AtomicPaymentTransitionTraceEvent;
    match event {
        AtomicPaymentTransitionTraceEvent::AccountsValidatedProgramOwned => {
            msg!("aspis-cu:atomic58_accounts_validated_program_owned")
        }
        AtomicPaymentTransitionTraceEvent::AccountsValidatedSystemOwned => {
            msg!("aspis-cu:atomic58_accounts_validated_system_owned")
        }
        AtomicPaymentTransitionTraceEvent::StatementDigestDone => {
            msg!("aspis-cu:atomic58_statement_digest_done")
        }
        AtomicPaymentTransitionTraceEvent::ProofVerified => {
            msg!("aspis-cu:atomic58_proof_verified")
        }
        AtomicPaymentTransitionTraceEvent::ProgramOwnedMarkerReady => {
            msg!("aspis-cu:atomic58_program_marker_ready")
        }
        AtomicPaymentTransitionTraceEvent::SystemOwnedMarkerCreated => {
            msg!("aspis-cu:atomic58_system_marker_created")
        }
        AtomicPaymentTransitionTraceEvent::MutableStateRechecked => {
            msg!("aspis-cu:atomic58_state_rechecked")
        }
        AtomicPaymentTransitionTraceEvent::StateApplied => {
            msg!("aspis-cu:atomic58_state_applied")
        }
    }
    sol_log_compute_units();
}

#[cfg(feature = "diagnostic-unmined-mutation")]
fn trace_atomic_profile20_mutation_event(event: atomic_payment::AtomicPaymentTransitionTraceEvent) {
    use atomic_payment::AtomicPaymentTransitionTraceEvent;
    match event {
        AtomicPaymentTransitionTraceEvent::AccountsValidatedProgramOwned => {
            msg!("aspis-cu:atomic48_accounts_validated_program_owned")
        }
        AtomicPaymentTransitionTraceEvent::AccountsValidatedSystemOwned => {
            msg!("aspis-cu:atomic48_accounts_validated_system_owned")
        }
        AtomicPaymentTransitionTraceEvent::StatementDigestDone => {
            msg!("aspis-cu:atomic48_statement_digest_done")
        }
        AtomicPaymentTransitionTraceEvent::ProofVerified => {
            msg!("aspis-cu:atomic48_proof_verified")
        }
        AtomicPaymentTransitionTraceEvent::ProgramOwnedMarkerReady => {
            msg!("aspis-cu:atomic48_program_marker_ready")
        }
        AtomicPaymentTransitionTraceEvent::SystemOwnedMarkerCreated => {
            msg!("aspis-cu:atomic48_system_marker_created")
        }
        AtomicPaymentTransitionTraceEvent::MutableStateRechecked => {
            msg!("aspis-cu:atomic48_state_rechecked")
        }
        AtomicPaymentTransitionTraceEvent::StateApplied => {
            msg!("aspis-cu:atomic48_state_applied")
        }
    }
    sol_log_compute_units();
}

#[inline(never)]
fn verify_atomic_profile20_proof_bytes_v3(
    proof: &[u8],
    statement: &aspis_statement::AtomicPaymentStatementV3,
    diagnostic_unmined: bool,
) -> ProgramResult {
    if diagnostic_unmined {
        aspis_statement::verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
            proof,
            statement,
            sbf_hashv,
            Some(trace_atomic_profile20_acceptance_phase),
        )
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    } else {
        aspis_statement::verify_atomic_state_only_candidate_v3(proof, statement, sbf_hashv)
            .map_err(|_| ProgramError::InvalidInstructionData)?;
    }
    Ok(())
}

fn uploaded_proof_bounds(data: &[u8]) -> Result<(usize, usize), ProgramError> {
    let total_len = proof_len(data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof_end > data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok((PROOF_ACCOUNT_HEADER_LEN, proof_end))
}

#[cfg(feature = "profile21-integrated-candidate")]
#[inline(never)]
fn verify_atomic_profile21_proof_bytes_v3(
    proof: &[u8],
    statement: &aspis_statement::AtomicPaymentStatementV3,
    diagnostic_unmined: bool,
    trace: Option<aspis_statement::state_only_profile21::Profile21Trace>,
) -> ProgramResult {
    // This check is redundant with the compile-time assertion above but keeps
    // the basis/version dependency explicit at the acceptance seam.
    if aspis_core::state_only_masked_switch_basis::MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT
        != ATOMIC_PROFILE21_MASKED_SWITCH_BASIS_FINGERPRINT
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    if diagnostic_unmined {
        aspis_statement::state_only_profile21::verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
            proof,
            statement,
            sbf_hashv,
            trace,
        )
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    } else {
        aspis_statement::state_only_profile21::verify_atomic_state_only_profile21_v3(
            proof, statement, sbf_hashv, trace,
        )
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    }
    Ok(())
}

#[cfg(feature = "profile21-integrated-candidate")]
#[inline(never)]
fn verify_uploaded_atomic_profile21_acceptance_v3(
    proof_account: &AccountInfo,
    pool: [u8; 32],
    sequence: u64,
    public_input: &[u8; 104],
    output_anchor: [u8; 32],
    diagnostic_unmined: bool,
) -> ProgramResult {
    msg!("aspis-cu:atomic50_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let output_anchor = aspis_statement::decode_digest_canonical(&output_anchor)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let statement = aspis_statement::AtomicPaymentStatementV3 {
        pool,
        sequence,
        spend: public,
        output_anchor,
    };
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic50_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile21_proof_bytes_v3(
        &data[proof_start..proof_end],
        &statement,
        diagnostic_unmined,
        Some(trace_atomic_profile21_acceptance_phase),
    )?;
    msg!("aspis-cu:atomic50_done");
    sol_log_compute_units();
    Ok(())
}

#[cfg(feature = "profile21-mutation-candidate")]
#[inline(never)]
fn verify_uploaded_atomic_profile21_production_statement_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    verify_atomic_profile21_proof_bytes_v3(&data[proof_start..proof_end], statement, false, None)
}

#[cfg(feature = "diagnostic-unmined-profile21-mutation")]
#[inline(never)]
fn verify_uploaded_atomic_profile21_mutation_diagnostic_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic52_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile21_proof_bytes_v3(
        &data[proof_start..proof_end],
        statement,
        true,
        Some(trace_atomic_profile21_mutation_phase),
    )
}

#[cfg(feature = "profile22-integrated-candidate")]
#[inline(never)]
fn verify_atomic_profile22_proof_bytes_v3(
    proof: &[u8],
    statement: &aspis_statement::AtomicPaymentStatementV3,
    diagnostic_unmined: bool,
    trace: Option<aspis_statement::state_only_profile22::Profile22Trace>,
) -> ProgramResult {
    if diagnostic_unmined {
        #[cfg(feature = "diagnostic-unmined-profile22-acceptance")]
        {
            aspis_statement::state_only_profile22::verify_atomic_state_only_profile22_unmined_for_diagnostics_v3(
                proof,
                statement,
                sbf_hashv,
                trace,
            )
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        }
        #[cfg(not(feature = "diagnostic-unmined-profile22-acceptance"))]
        {
            let _ = (proof, statement, trace);
            return Err(ProgramError::InvalidInstructionData);
        }
    } else {
        aspis_statement::state_only_profile22::verify_atomic_state_only_profile22_v3(
            proof, statement, sbf_hashv, trace,
        )
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    }
    Ok(())
}

#[cfg(feature = "profile22-integrated-candidate")]
#[inline(never)]
fn verify_uploaded_atomic_profile22_acceptance_v3(
    proof_account: &AccountInfo,
    pool: [u8; 32],
    sequence: u64,
    public_input: &[u8; 104],
    output_anchor: [u8; 32],
    diagnostic_unmined: bool,
) -> ProgramResult {
    msg!("aspis-cu:atomic56_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let output_anchor = aspis_statement::decode_digest_canonical(&output_anchor)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let statement = aspis_statement::AtomicPaymentStatementV3 {
        pool,
        sequence,
        spend: public,
        output_anchor,
    };
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic56_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile22_proof_bytes_v3(
        &data[proof_start..proof_end],
        &statement,
        diagnostic_unmined,
        Some(trace_atomic_profile22_acceptance_phase),
    )?;
    msg!("aspis-cu:atomic56_done");
    sol_log_compute_units();
    Ok(())
}

#[cfg(feature = "profile22-mutation-candidate")]
#[inline(never)]
fn verify_uploaded_atomic_profile22_production_statement_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    verify_atomic_profile22_proof_bytes_v3(&data[proof_start..proof_end], statement, false, None)
}

#[cfg(feature = "diagnostic-unmined-profile22-mutation")]
#[inline(never)]
fn verify_uploaded_atomic_profile22_mutation_diagnostic_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic58_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile22_proof_bytes_v3(
        &data[proof_start..proof_end],
        statement,
        true,
        Some(trace_atomic_profile22_mutation_phase),
    )
}

#[cfg(feature = "profile23-integrated-candidate")]
#[inline(never)]
fn verify_atomic_profile23_proof_bytes_v3(
    proof: &[u8],
    statement: &aspis_statement::AtomicPaymentStatementV3,
    diagnostic_unmined: bool,
    trace: Option<aspis_statement::state_only_profile23::Profile23Trace>,
) -> ProgramResult {
    if diagnostic_unmined {
        #[cfg(feature = "diagnostic-unmined-profile23-acceptance")]
        {
            aspis_statement::state_only_profile23::verify_atomic_state_only_profile23_unmined_for_diagnostics_v3(
                proof,
                statement,
                sbf_hashv,
                trace,
            )
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        }
        #[cfg(not(feature = "diagnostic-unmined-profile23-acceptance"))]
        {
            let _ = (proof, statement, trace);
            return Err(ProgramError::InvalidInstructionData);
        }
    } else {
        #[cfg(feature = "profile23-dynamic-rate512")]
        aspis_statement::state_only_profile23::verify_atomic_state_only_profile23_v3_with_inverse(
            proof,
            statement,
            sbf_hashv,
            trace,
            m31_inverse_syscall,
        )
        .map_err(|_| ProgramError::InvalidInstructionData)?;
        #[cfg(not(feature = "profile23-dynamic-rate512"))]
        aspis_statement::state_only_profile23::verify_atomic_state_only_profile23_v3(
            proof, statement, sbf_hashv, trace,
        )
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    }
    Ok(())
}

#[cfg(feature = "profile23-integrated-candidate")]
#[inline(never)]
fn verify_uploaded_atomic_profile23_acceptance_v3(
    proof_account: &AccountInfo,
    pool: [u8; 32],
    sequence: u64,
    public_input: &[u8; 104],
    output_anchor: [u8; 32],
    diagnostic_unmined: bool,
) -> ProgramResult {
    msg!("aspis-cu:atomic59_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let output_anchor = aspis_statement::decode_digest_canonical(&output_anchor)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let statement = aspis_statement::AtomicPaymentStatementV3 {
        pool,
        sequence,
        spend: public,
        output_anchor,
    };
    let data = proof_account.try_borrow_data()?;
    if !diagnostic_unmined && !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic59_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile23_proof_bytes_v3(
        &data[proof_start..proof_end],
        &statement,
        diagnostic_unmined,
        Some(trace_atomic_profile23_acceptance_phase),
    )?;
    msg!("aspis-cu:atomic59_done");
    sol_log_compute_units();
    Ok(())
}

#[cfg(feature = "profile23-mutation-candidate")]
#[inline(never)]
fn verify_uploaded_atomic_profile23_production_statement_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    verify_atomic_profile23_proof_bytes_v3(&data[proof_start..proof_end], statement, false, None)
}

#[cfg(feature = "diagnostic-unmined-profile23-mutation")]
#[inline(never)]
fn verify_uploaded_atomic_profile23_mutation_diagnostic_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic61_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile23_proof_bytes_v3(
        &data[proof_start..proof_end],
        statement,
        true,
        Some(trace_atomic_profile23_mutation_phase),
    )
}

#[inline(never)]
fn verify_uploaded_atomic_profile20_acceptance_v3(
    proof_account: &AccountInfo,
    pool: [u8; 32],
    sequence: u64,
    public_input: &[u8; 104],
    output_anchor: [u8; 32],
    diagnostic_unmined: bool,
) -> ProgramResult {
    msg!("aspis-cu:atomic46_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let output_anchor = aspis_statement::decode_digest_canonical(&output_anchor)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let statement = aspis_statement::AtomicPaymentStatementV3 {
        pool,
        sequence,
        spend: public,
        output_anchor,
    };
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    let proof = &data[proof_start..proof_end];
    msg!("aspis-cu:atomic46_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile20_proof_bytes_v3(proof, &statement, diagnostic_unmined)?;
    msg!("aspis-cu:atomic46_done");
    sol_log_compute_units();
    Ok(())
}

#[cfg(feature = "profile20-mutation-candidate")]
#[inline(never)]
fn verify_uploaded_atomic_profile20_production_statement_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    verify_atomic_profile20_proof_bytes_v3(&data[proof_start..proof_end], statement, false)
}

#[cfg(feature = "diagnostic-unmined-mutation")]
#[inline(never)]
fn verify_uploaded_atomic_profile20_mutation_diagnostic_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic48_proof_loaded");
    sol_log_compute_units();
    verify_atomic_profile20_proof_bytes_v3(&data[proof_start..proof_end], statement, true)
}

#[inline(never)]
fn verify_uploaded_state_only_width28(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    public_input: &[u8; 104],
    diagnostic_unmined: bool,
) -> ProgramResult {
    msg!("aspis-cu:state28_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..proof_end)
        .ok_or(ProgramError::InvalidAccountData)?;
    msg!("aspis-cu:state28_proof_loaded");
    sol_log_compute_units();
    let result = if diagnostic_unmined {
        aspis_statement::verify_state_only_candidate_unmined_for_diagnostics_traced(
            proof,
            &public,
            &statement_digest,
            sbf_hashv,
            trace_state_only_width28_phase,
        )
    } else {
        aspis_statement::verify_state_only_candidate(proof, &public, &statement_digest, sbf_hashv)
    };
    result.map_err(|_| ProgramError::InvalidInstructionData)?;
    msg!("aspis-cu:state28_done");
    sol_log_compute_units();
    Ok(())
}

#[inline(never)]
fn measure_uploaded_state_only_width28(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    public_input: &[u8; 104],
    phase: StateOnlyWidth28DiagnosticPhase,
) -> ProgramResult {
    msg!("aspis-cu:state28_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..proof_end)
        .ok_or(ProgramError::InvalidAccountData)?;
    msg!("aspis-cu:state28_proof_loaded");
    sol_log_compute_units();
    let phase = match phase {
        StateOnlyWidth28DiagnosticPhase::PreparedBase => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::PreparedBase
        }
        StateOnlyWidth28DiagnosticPhase::Terminal => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::Terminal
        }
        StateOnlyWidth28DiagnosticPhase::Relation => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::Relation
        }
        StateOnlyWidth28DiagnosticPhase::Openings => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::Openings
        }
        StateOnlyWidth28DiagnosticPhase::Queries => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::Queries
        }
        StateOnlyWidth28DiagnosticPhase::QueryLayer0 => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::QueryLayer0
        }
        StateOnlyWidth28DiagnosticPhase::QueryLaterAll => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::QueryLaterAll
        }
        StateOnlyWidth28DiagnosticPhase::TerminalBreakdown => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::TerminalBreakdown
        }
        StateOnlyWidth28DiagnosticPhase::TerminalNoMask => {
            aspis_statement::StateOnlyVerifyDiagnosticPhase::TerminalNoMask
        }
    };
    aspis_statement::verify_state_only_candidate_phase_unmined_for_diagnostics(
        proof,
        &public,
        &statement_digest,
        sbf_hashv,
        phase,
        trace_state_only_width28_phase,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    msg!("aspis-cu:state28_done");
    sol_log_compute_units();
    Ok(())
}

fn measure_uploaded_payment_hiding_profile15(
    proof_account: &AccountInfo,
    statement_digest: [u8; 32],
    public_input: &[u8; 104],
    phase: JohnsonM31CircleDiagnosticPhase,
    start: u16,
    end: u16,
) -> ProgramResult {
    let segment = match phase {
        JohnsonM31CircleDiagnosticPhase::PreparedBase => {
            aspis_core::circle_openings::CircleQuerySegment::PreparedBase
        }
        JohnsonM31CircleDiagnosticPhase::Layer0Range => {
            aspis_core::circle_openings::CircleQuerySegment::Layer0Range {
                start: usize::from(start),
                end: usize::from(end),
            }
        }
        JohnsonM31CircleDiagnosticPhase::LaterAll => {
            aspis_core::circle_openings::CircleQuerySegment::LaterAll
        }
        JohnsonM31CircleDiagnosticPhase::Full => {
            aspis_core::circle_openings::CircleQuerySegment::Full
        }
    };
    let data = proof_account.try_borrow_data()?;
    let total_len = proof_len(&data)?;
    let proof_end = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(total_len)
        .ok_or(ProgramError::InvalidAccountData)?;
    let proof = data
        .get(PROOF_ACCOUNT_HEADER_LEN..proof_end)
        .ok_or(ProgramError::InvalidAccountData)?;
    msg!("aspis-cu:h15_start");
    sol_log_compute_units();
    let verified = aspis_core::circle_hiding_verify::verify_payment_hiding_candidate_unmined_for_diagnostics_with_trace(
        proof,
        &statement_digest,
        sbf_hashv,
        segment,
        Some(trace_payment_hiding_profile15_cu),
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    msg!("aspis-cu:h15_statement_start");
    sol_log_compute_units();
    verify_payment_hiding_profile15_statement(&verified, public_input)?;
    msg!("aspis-cu:h15_statement_done");
    sol_log_compute_units();
    msg!("aspis-cu:h15_done");
    sol_log_compute_units();
    Ok(())
}

fn require_upload_authority(data: &[u8], authority: &AccountInfo) -> ProgramResult {
    if !authority.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if data.len() < PROOF_ACCOUNT_HEADER_LEN || data[0..4] != PROOF_ACCOUNT_MAGIC {
        return Err(ProgramError::InvalidAccountData);
    }
    if data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32] != authority.key.to_bytes() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[cfg(all(not(feature = "no-entrypoint"), feature = "profile23-minimal-dispatch"))]
entrypoint!(process_profile23_production_instruction);

#[cfg(all(
    not(feature = "no-entrypoint"),
    not(feature = "profile23-minimal-dispatch")
))]
entrypoint!(process_instruction);

/// Parse exactly one fixed-width byte array from the production wire.
///
/// The historical Borsh enum is intentionally not referenced by the minimal
/// entrypoint.  Avoiding that reference lets the SBF linker discard every
/// diagnostic and superseded verifier arm while retaining byte-for-byte wire
/// compatibility for the six lifecycle tags used by Profile23.
#[cfg(feature = "profile23-minimal-dispatch")]
fn production_take<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<N>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(*head)
}

#[cfg(feature = "profile23-minimal-dispatch")]
fn production_u32(input: &mut &[u8]) -> Result<u32, ProgramError> {
    Ok(u32::from_le_bytes(production_take::<4>(input)?))
}

#[cfg(feature = "profile23-minimal-dispatch")]
fn production_u64(input: &mut &[u8]) -> Result<u64, ProgramError> {
    Ok(u64::from_le_bytes(production_take::<8>(input)?))
}

#[cfg(feature = "profile23-minimal-dispatch")]
fn production_require_empty(input: &[u8]) -> ProgramResult {
    if input.is_empty() {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

/// Profile23's deployment-only wire surface.
///
/// Accepted append-only tags:
///
/// - 0: initialize a fresh proof account;
/// - 1: upload one proof chunk;
/// - 59: production read-only verification;
/// - 60: production verification plus atomic state transition;
/// - 62: irreversibly finalize the proof account; and
/// - 63: initialize a fresh atomic pool.
///
/// Every other historical or diagnostic tag fails before account access.  The
/// implementation duplicates the small account-lifecycle shell on purpose:
/// calling the generic Borsh dispatcher would retain its entire code and
/// constant graph in the deployed ELF.
#[cfg(feature = "profile23-minimal-dispatch")]
pub fn process_profile23_production_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let (&tag, mut wire) = instruction_data
        .split_first()
        .ok_or(ProgramError::InvalidInstructionData)?;

    match tag {
        0 => {
            let total_len = production_u32(&mut wire)?;
            production_require_empty(wire)?;
            let account_iter = &mut accounts.iter();
            let proof_account = next_account_info(account_iter)?;
            let authority = next_account_info(account_iter)?;
            if proof_account.owner != program_id {
                return Err(ProgramError::IncorrectProgramId);
            }
            if !authority.is_signer {
                return Err(ProgramError::MissingRequiredSignature);
            }
            if !proof_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            let mut data = proof_account.try_borrow_mut_data()?;
            let required_len = PROOF_ACCOUNT_HEADER_LEN
                .checked_add(total_len as usize)
                .ok_or(ProgramError::InvalidInstructionData)?;
            if data.len() < required_len {
                return Err(ProgramError::AccountDataTooSmall);
            }
            if proof_account_initialized(&data) {
                if data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32] != authority.key.to_bytes() {
                    return Err(ProgramError::InvalidAccountData);
                }
            } else {
                if !proof_account.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                if !data.iter().all(|byte| *byte == 0) {
                    return Err(ProgramError::InvalidAccountData);
                }
            }
            data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
            data[4..8].copy_from_slice(&total_len.to_le_bytes());
            data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority.key.as_ref());
            Ok(())
        }
        1 => {
            let offset = production_u32(&mut wire)?;
            let chunk_len = production_u32(&mut wire)? as usize;
            if wire.len() != chunk_len {
                return Err(ProgramError::InvalidInstructionData);
            }
            let account_iter = &mut accounts.iter();
            let proof_account = next_account_info(account_iter)?;
            let authority = next_account_info(account_iter)?;
            if proof_account.owner != program_id {
                return Err(ProgramError::IncorrectProgramId);
            }
            if !proof_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            let mut data = proof_account.try_borrow_mut_data()?;
            require_upload_authority(&data, authority)?;
            let total_len = proof_len(&data)?;
            let relative_end = (offset as usize)
                .checked_add(chunk_len)
                .ok_or(ProgramError::InvalidInstructionData)?;
            let start = PROOF_ACCOUNT_HEADER_LEN
                .checked_add(offset as usize)
                .ok_or(ProgramError::InvalidInstructionData)?;
            let end = start
                .checked_add(chunk_len)
                .ok_or(ProgramError::InvalidInstructionData)?;
            if relative_end > total_len || end > data.len() {
                return Err(ProgramError::InvalidInstructionData);
            }
            data[start..end].copy_from_slice(wire);
            Ok(())
        }
        59 => {
            let pool = production_take::<32>(&mut wire)?;
            let sequence = production_u64(&mut wire)?;
            let public_input = production_take::<104>(&mut wire)?;
            let output_anchor = production_take::<32>(&mut wire)?;
            let diagnostic_unmined = production_take::<1>(&mut wire)?[0];
            production_require_empty(wire)?;
            if diagnostic_unmined != 0 {
                return Err(ProgramError::InvalidInstructionData);
            }
            let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
            if proof_account.owner != program_id || proof_account.is_writable {
                return Err(ProgramError::IncorrectProgramId);
            }
            verify_uploaded_atomic_profile23_acceptance_v3(
                proof_account,
                pool,
                sequence,
                &public_input,
                output_anchor,
                false,
            )
        }
        60 => {
            let current_anchor = production_take::<32>(&mut wire)?;
            let nullifier = production_take::<32>(&mut wire)?;
            let output_commitment = production_take::<32>(&mut wire)?;
            let output_anchor = production_take::<32>(&mut wire)?;
            let asset_id = production_u32(&mut wire)?;
            let fee = production_u32(&mut wire)?;
            production_require_empty(wire)?;
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            };
            atomic_payment::verify_and_apply_atomic_payment_state(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify_uploaded_atomic_profile23_production_statement_v3(
                        proof_account,
                        statement,
                    )
                },
            )
        }
        // Keep the frozen production API's explicit fail-closed result for
        // the former Profile23 diagnostic mutation tag.  Returning the same
        // custom error preserves the release tooth without rooting its
        // diagnostic verifier or CU-marker graph in the ELF.
        61 => Err(ProgramError::Custom(
            atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
        )),
        62 => {
            production_require_empty(wire)?;
            let account_iter = &mut accounts.iter();
            let proof_account = next_account_info(account_iter)?;
            let authority = next_account_info(account_iter)?;
            if proof_account.owner != program_id {
                return Err(ProgramError::IncorrectProgramId);
            }
            if !proof_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            let mut data = proof_account.try_borrow_mut_data()?;
            require_upload_authority(&data, authority)?;
            data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
            Ok(())
        }
        63 => {
            let sequence = production_u64(&mut wire)?;
            let anchor = production_take::<32>(&mut wire)?;
            production_require_empty(wire)?;
            let pool_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
            if pool_account.owner != program_id {
                return Err(ProgramError::IncorrectProgramId);
            }
            if !pool_account.is_signer {
                return Err(ProgramError::MissingRequiredSignature);
            }
            if !pool_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            aspis_statement::decode_digest_canonical(&anchor)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            sequence
                .checked_add(1)
                .ok_or(ProgramError::ArithmeticOverflow)?;
            let mut data = pool_account.try_borrow_mut_data()?;
            if data.len() != atomic_payment::ATOMIC_POOL_STATE_LEN
                || !data.iter().all(|byte| *byte == 0)
            {
                return Err(ProgramError::InvalidAccountData);
            }
            atomic_payment::AtomicPoolStateV1 { sequence, anchor }.encode(&mut data)
        }
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let instruction = AspisInstruction::try_from_slice(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;

    // Pure-compute diagnostic: no accounts required.
    if let AspisInstruction::TranscriptKat { expected } = instruction {
        let digest = aspis_core::transcript::transcript_kat(sbf_hashv);
        return if digest == expected {
            msg!("aspis: transcript KAT matched");
            Ok(())
        } else {
            msg!("aspis: transcript KAT MISMATCH (host/SBF divergence)");
            Err(ProgramError::InvalidInstructionData)
        };
    }
    if let AspisInstruction::ConstraintCompositionProbe {
        opened_values,
        poseidon_sbox_terms,
        poseidon_linear_terms,
        logup_degree3_terms,
        range_bit_terms,
        eq_variables,
        optimized,
    } = instruction
    {
        return run_constraint_composition_probe(
            aspis_statement::CompositionProbe {
                opened_values,
                poseidon_sbox_terms,
                poseidon_linear_terms,
                logup_degree3_terms,
                range_bit_terms,
                eq_variables,
            },
            optimized,
        );
    }
    if let AspisInstruction::Poseidon2Probe { permutations } = instruction {
        return run_poseidon2_probe(permutations, false);
    }
    if let AspisInstruction::Poseidon2OptimizedProbe { permutations } = instruction {
        return run_poseidon2_probe(permutations, true);
    }
    if let AspisInstruction::ZkKernelProbe { kind, iterations } = instruction {
        return run_zk_kernel_probe(kind, iterations);
    }
    if let AspisInstruction::WideRlcProbe {
        columns,
        query_count,
        kernel,
    } = instruction
    {
        return run_wide_rlc_probe(columns, query_count, kernel);
    }
    if let AspisInstruction::MerkleArityProbe {
        depth,
        query_count,
        arity,
    } = instruction
    {
        return run_merkle_arity_probe(depth, query_count, arity);
    }
    if let AspisInstruction::Radix8MerkleDepth12Probe {
        arity,
        corrupt_frontier,
    } = instruction
    {
        return run_radix8_merkle_depth12_probe(arity, corrupt_frontier);
    }
    if let AspisInstruction::MerkleForestProbe {
        fused,
        corrupt_lane,
    } = instruction
    {
        return run_merkle_forest_probe(fused, corrupt_lane);
    }
    if let AspisInstruction::Layer0DotWidthProbe {
        columns,
        corrupt,
        expected_sink,
    } = instruction
    {
        return run_layer0_dot_width_probe(columns, corrupt, expected_sink);
    }
    if let AspisInstruction::AtomicRoutingPartitionProbe {
        optimized,
        seed,
        expected_sink,
    } = instruction
    {
        return run_atomic_routing_partition_probe(optimized, seed, expected_sink);
    }
    if let AspisInstruction::StatementSumcheckProbe {
        rounds,
        coefficients,
        claims,
        selector_terms,
        selector_exceptions,
    } = instruction
    {
        return run_statement_sumcheck_probe(
            rounds,
            coefficients,
            claims,
            selector_terms,
            selector_exceptions,
        );
    }
    if let AspisInstruction::LogUpCompressionKat { expected_phi } = instruction {
        let mut actual_phi = [0u8; 16];
        aspis_statement::logup_compression_kat().write_le_bytes(&mut actual_phi);
        return if actual_phi == expected_phi {
            msg!("aspis: LogUp compression KAT matched");
            Ok(())
        } else {
            msg!("aspis: LogUp compression KAT MISMATCH (host/SBF divergence)");
            Err(ProgramError::InvalidInstructionData)
        };
    }
    if let AspisInstruction::OodSampleRelationProbe {
        samples_per_round,
        expected_sink,
    } = instruction
    {
        return run_ood_sample_relation_probe(samples_per_round, expected_sink);
    }
    if let AspisInstruction::TwoPointBatchingDiagnostic {
        mode,
        expected_sink,
    } = instruction
    {
        return run_two_point_batching_diagnostic(mode, expected_sink);
    }
    if let AspisInstruction::TranscriptKatV4S2PcsScaffold { expected } = instruction {
        let digest = aspis_core::transcript::transcript_kat_v4_s2_pcs_scaffold(sbf_hashv);
        return if digest == expected {
            msg!("aspis: v4/s=2 PCS-scaffold transcript KAT matched");
            Ok(())
        } else {
            msg!("aspis: v4/s=2 PCS-scaffold transcript KAT MISMATCH");
            Err(ProgramError::InvalidInstructionData)
        };
    }
    if let AspisInstruction::FinalPaymentTranscriptKatV4 { expected } = instruction {
        let digest = aspis_core::transcript::transcript_kat_final_payment_v4(sbf_hashv);
        return if digest == expected {
            msg!("aspis: final payment-v4 transcript KAT matched");
            Ok(())
        } else {
            msg!("aspis: final payment-v4 transcript KAT MISMATCH");
            Err(ProgramError::InvalidInstructionData)
        };
    }
    if let AspisInstruction::ExactWideV4Diagnostic {
        mode,
        expected_sink,
    } = instruction
    {
        let fixture_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if fixture_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return run_exact_wide_v4_diagnostic(fixture_account, mode, expected_sink);
    }
    if let AspisInstruction::M31CircleBasisDiagnostic {
        mode,
        expected_sink,
    } = instruction
    {
        let fixture_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if fixture_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return run_m31_circle_basis_diagnostic(fixture_account, mode, expected_sink);
    }
    if let AspisInstruction::VerifyM31CircleV4Diagnostic {
        statement_digest: _,
        claim_z,
        statement_evaluations_digest: _,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        validate_m31_circle_v4_diagnostic_public_inputs(claim_z)?;
        validate_uploaded_m31_circle_v4_diagnostic_header(proof_account)?;
        msg!("aspis: M31-circle v4 diagnostic verifier is framed, not implemented");
        return Err(ProgramError::InvalidInstructionData);
    }
    if let AspisInstruction::VerifyM31CircleFreshKappa {
        statement_digest,
        claim_z,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return verify_uploaded_m31_circle_fresh_kappa(proof_account, *statement_digest, claim_z);
    }
    if let AspisInstruction::MeasureM31CircleJohnson {
        statement_digest,
        claim_z,
        phase,
        start,
        end,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return measure_uploaded_m31_circle_johnson(
            proof_account,
            *statement_digest,
            claim_z,
            *phase,
            *start,
            *end,
        );
    }
    if let AspisInstruction::MeasureM31CircleRate16 {
        statement_digest,
        claim_z,
        phase,
        start,
        end,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return measure_uploaded_m31_circle_rate16(
            proof_account,
            *statement_digest,
            claim_z,
            *phase,
            *start,
            *end,
        );
    }
    if let AspisInstruction::MeasureM31CircleRate16Composition {
        statement_digest,
        claim_z,
        stress,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        measure_uploaded_m31_circle_rate16(
            proof_account,
            *statement_digest,
            claim_z,
            JohnsonM31CircleDiagnosticPhase::Full,
            0,
            0,
        )?;
        return run_constraint_composition_probe(
            aspis_statement::CompositionProbe {
                opened_values: 0,
                poseidon_sbox_terms: 32,
                poseidon_linear_terms: if *stress { 70 } else { 38 },
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        );
    }
    if let AspisInstruction::MeasureM31CircleRate16Hardened {
        statement_digest,
        claim_z,
        phase,
        start,
        end,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return measure_uploaded_m31_circle_rate16_hardened(
            proof_account,
            *statement_digest,
            claim_z,
            *phase,
            *start,
            *end,
        );
    }
    if let AspisInstruction::MeasurePaymentHidingProfile15 {
        statement_digest,
        public_input,
        phase,
        start,
        end,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return measure_uploaded_payment_hiding_profile15(
            proof_account,
            *statement_digest,
            public_input,
            *phase,
            *start,
            *end,
        );
    }
    if let AspisInstruction::VerifyStateOnlyWidth28 {
        statement_digest,
        public_input,
        diagnostic_unmined,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return verify_uploaded_state_only_width28(
            proof_account,
            *statement_digest,
            public_input,
            *diagnostic_unmined,
        );
    }
    if let AspisInstruction::MeasureStateOnlyWidth28 {
        statement_digest,
        public_input,
        phase,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return measure_uploaded_state_only_width28(
            proof_account,
            *statement_digest,
            public_input,
            *phase,
        );
    }
    if let AspisInstruction::AtomicStateOnlyProfile20CostCandidate {
        statement_digest,
        public_input,
        output_anchor,
        expected_atomic_terminal,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return verify_uploaded_atomic_profile20_cost_candidate(
            proof_account,
            *statement_digest,
            public_input,
            *output_anchor,
            *expected_atomic_terminal,
        );
    }
    if let AspisInstruction::StateOnlyRelationStructuralProbe {
        statement_digest,
        deferred_binary_copy,
        corrupt_claim,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return run_state_only_relation_structural_probe(
            proof_account,
            *statement_digest,
            *deferred_binary_copy,
            *corrupt_claim,
        );
    }
    if let AspisInstruction::StateOnlyMaskedSwitchProfile21Probe {
        statement_digest,
        diagnostic_unmined,
        direct_u_query_evaluation,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        return run_state_only_masked_switch_profile21_probe(
            proof_account,
            *statement_digest,
            *diagnostic_unmined,
            *direct_u_query_evaluation,
        );
    }
    if let AspisInstruction::VerifyAtomicStateOnlyProfile20V3 {
        pool,
        sequence,
        public_input,
        output_anchor,
        diagnostic_unmined,
    } = &instruction
    {
        let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
        if proof_account.owner != program_id || proof_account.is_writable {
            return Err(ProgramError::IncorrectProgramId);
        }
        return verify_uploaded_atomic_profile20_acceptance_v3(
            proof_account,
            *pool,
            *sequence,
            public_input,
            *output_anchor,
            *diagnostic_unmined,
        );
    }
    if let AspisInstruction::ApplyAtomicStateOnlyProfile20V3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "profile20-mutation-candidate")]
        {
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    // No diagnostic selector reaches this closure. The
                    // candidate verifier checks every configured PoW
                    // predicate. Default builds never reach this arm while
                    // complete-view hiding remains open.
                    verify_uploaded_atomic_profile20_production_statement_v3(
                        proof_account,
                        statement,
                    )
                },
            );
        }
        #[cfg(not(feature = "profile20-mutation-candidate"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::MeasureAtomicStateOnlyProfile20MutationV3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "diagnostic-unmined-mutation")]
        {
            msg!("aspis-cu:atomic48_instruction_start");
            sol_log_compute_units();
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state_traced(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify_uploaded_atomic_profile20_mutation_diagnostic_v3(
                        proof_account,
                        statement,
                    )
                },
                trace_atomic_profile20_mutation_event,
            );
        }
        #[cfg(not(feature = "diagnostic-unmined-mutation"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::MeasurePaymentHidingPlacementV4 {
        placement,
        expected_sink,
    } = instruction
    {
        return run_payment_hiding_placement_v4(placement, expected_sink);
    }
    if let AspisInstruction::MeasurePaymentHidingAggregateRelationV4 {
        phase,
        expected_sink,
    } = instruction
    {
        return run_payment_hiding_aggregate_relation_v4(phase, expected_sink);
    }
    if let AspisInstruction::AtomicPaymentStateTransitionV1 { .. } = &instruction {
        // Fail before either the reference Poseidon update or any account
        // access. The direct update alone exceeds the transaction cap; this
        // tag cannot be enabled by swapping in a proof-verifier closure.
        return Err(ProgramError::Custom(
            atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
        ));
    }
    if let AspisInstruction::HvzkWhirMaskProbe {
        mask_log_inv_rate,
        mask_queries,
        scope,
        mode,
        phase,
        start,
        end,
    } = instruction
    {
        return run_hvzk_whir_mask_probe(
            mask_log_inv_rate,
            mask_queries,
            scope,
            mode,
            phase,
            start,
            end,
        );
    }
    if let AspisInstruction::StateOnlyPrivateMerkleSaltProbe {
        mode,
        expected_sink,
    } = instruction
    {
        return run_state_only_private_merkle_salt_probe(mode, expected_sink);
    }
    if let AspisInstruction::StateOnlyHelperDot2Probe {
        fused_helpers,
        corrupt,
        expected_sink,
    } = &instruction
    {
        return run_state_only_helper_dot2_probe(*fused_helpers, *corrupt, *expected_sink);
    }
    if let AspisInstruction::StateOnlyHelperDot3Probe {
        fused_helpers,
        corrupt,
        expected_sink,
    } = &instruction
    {
        return run_state_only_helper_dot3_probe(*fused_helpers, *corrupt, *expected_sink);
    }
    if let AspisInstruction::StateOnlyFoldPolynomialProbe {
        polynomial_basis,
        corrupt,
        expected_sink,
    } = &instruction
    {
        return run_state_only_fold_polynomial_probe(*polynomial_basis, *corrupt, *expected_sink);
    }
    if let AspisInstruction::VerifyAtomicStateOnlyProfile21V3 {
        pool,
        sequence,
        public_input,
        output_anchor,
        diagnostic_unmined,
    } = &instruction
    {
        #[cfg(feature = "profile21-integrated-candidate")]
        {
            let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
            if proof_account.owner != program_id || proof_account.is_writable {
                return Err(ProgramError::IncorrectProgramId);
            }
            return verify_uploaded_atomic_profile21_acceptance_v3(
                proof_account,
                *pool,
                *sequence,
                public_input,
                *output_anchor,
                *diagnostic_unmined,
            );
        }
        #[cfg(not(feature = "profile21-integrated-candidate"))]
        {
            let _ = (
                pool,
                sequence,
                public_input,
                output_anchor,
                diagnostic_unmined,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::ApplyAtomicStateOnlyProfile21V3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "profile21-mutation-candidate")]
        {
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    // No bypass selector reaches tag 51. This calls the same
                    // integrated proof parser as tag 50 with production PoW.
                    verify_uploaded_atomic_profile21_production_statement_v3(
                        proof_account,
                        statement,
                    )
                },
            );
        }
        #[cfg(not(feature = "profile21-mutation-candidate"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::MeasureAtomicStateOnlyProfile21MutationV3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "diagnostic-unmined-profile21-mutation")]
        {
            msg!("aspis-cu:atomic52_instruction_start");
            sol_log_compute_units();
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state_traced(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify_uploaded_atomic_profile21_mutation_diagnostic_v3(
                        proof_account,
                        statement,
                    )
                },
                trace_atomic_profile21_mutation_event,
            );
        }
        #[cfg(not(feature = "diagnostic-unmined-profile21-mutation"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::VerifyAtomicStateOnlyProfile22V3 {
        pool,
        sequence,
        public_input,
        output_anchor,
        diagnostic_unmined,
    } = &instruction
    {
        #[cfg(feature = "profile22-integrated-candidate")]
        {
            #[cfg(not(feature = "diagnostic-unmined-profile22-acceptance"))]
            if *diagnostic_unmined {
                // Never let a production-capable binary expose the local
                // unmined verifier through the read-only/CPI surface.
                return Err(ProgramError::InvalidInstructionData);
            }
            let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
            if proof_account.owner != program_id || proof_account.is_writable {
                return Err(ProgramError::IncorrectProgramId);
            }
            return verify_uploaded_atomic_profile22_acceptance_v3(
                proof_account,
                *pool,
                *sequence,
                public_input,
                *output_anchor,
                *diagnostic_unmined,
            );
        }
        #[cfg(not(feature = "profile22-integrated-candidate"))]
        {
            let _ = (
                pool,
                sequence,
                public_input,
                output_anchor,
                diagnostic_unmined,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::ApplyAtomicStateOnlyProfile22V3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "profile22-mutation-candidate")]
        {
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify_uploaded_atomic_profile22_production_statement_v3(
                        proof_account,
                        statement,
                    )
                },
            );
        }
        #[cfg(not(feature = "profile22-mutation-candidate"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::MeasureAtomicStateOnlyProfile22MutationV3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "diagnostic-unmined-profile22-mutation")]
        {
            msg!("aspis-cu:atomic58_instruction_start");
            sol_log_compute_units();
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state_traced(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify_uploaded_atomic_profile22_mutation_diagnostic_v3(
                        proof_account,
                        statement,
                    )
                },
                trace_atomic_profile22_mutation_event,
            );
        }
        #[cfg(not(feature = "diagnostic-unmined-profile22-mutation"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::VerifyAtomicStateOnlyProfile23V3 {
        pool,
        sequence,
        public_input,
        output_anchor,
        diagnostic_unmined,
    } = &instruction
    {
        #[cfg(feature = "profile23-integrated-candidate")]
        {
            #[cfg(not(feature = "diagnostic-unmined-profile23-acceptance"))]
            if *diagnostic_unmined {
                return Err(ProgramError::InvalidInstructionData);
            }
            let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
            if proof_account.owner != program_id || proof_account.is_writable {
                return Err(ProgramError::IncorrectProgramId);
            }
            return verify_uploaded_atomic_profile23_acceptance_v3(
                proof_account,
                *pool,
                *sequence,
                public_input,
                *output_anchor,
                *diagnostic_unmined,
            );
        }
        #[cfg(not(feature = "profile23-integrated-candidate"))]
        {
            let _ = (
                pool,
                sequence,
                public_input,
                output_anchor,
                diagnostic_unmined,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::ApplyAtomicStateOnlyProfile23V3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "profile23-mutation-candidate")]
        {
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify_uploaded_atomic_profile23_production_statement_v3(
                        proof_account,
                        statement,
                    )
                },
            );
        }
        #[cfg(not(feature = "profile23-mutation-candidate"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }
    if let AspisInstruction::MeasureAtomicStateOnlyProfile23MutationV3 {
        current_anchor,
        nullifier,
        output_commitment,
        output_anchor,
        asset_id,
        fee,
    } = &instruction
    {
        #[cfg(feature = "diagnostic-unmined-profile23-mutation")]
        {
            msg!("aspis-cu:atomic61_instruction_start");
            sol_log_compute_units();
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor: *current_anchor,
                nullifier: *nullifier,
                output_commitment: *output_commitment,
                output_anchor: *output_anchor,
                asset_id: *asset_id,
                fee: *fee,
            };
            return atomic_payment::verify_and_apply_atomic_payment_state_traced(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify_uploaded_atomic_profile23_mutation_diagnostic_v3(
                        proof_account,
                        statement,
                    )
                },
                trace_atomic_profile23_mutation_event,
            );
        }
        #[cfg(not(feature = "diagnostic-unmined-profile23-mutation"))]
        {
            let _ = (
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
            );
            return Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
        }
    }

    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }

    match instruction {
        AspisInstruction::InitProof { total_len } => {
            let authority = next_account_info(account_iter)?;
            if !authority.is_signer {
                return Err(ProgramError::MissingRequiredSignature);
            }
            if !proof_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            let mut data = proof_account.try_borrow_mut_data()?;
            let required_len = PROOF_ACCOUNT_HEADER_LEN
                .checked_add(total_len as usize)
                .ok_or(ProgramError::InvalidInstructionData)?;
            if data.len() < required_len {
                return Err(ProgramError::AccountDataTooSmall);
            }
            if proof_account_initialized(&data) {
                if data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32] != authority.key.to_bytes() {
                    return Err(ProgramError::InvalidAccountData);
                }
            } else {
                if !proof_account.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                // A fresh program-owned account is zero-filled by the System
                // Program. Requiring that complete image prevents a signer for
                // another Aspis account type (notably an initialized pool) from
                // retyping and bricking it through the proof initializer.
                if !data.iter().all(|byte| *byte == 0) {
                    return Err(ProgramError::InvalidAccountData);
                }
            }
            data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
            data[4..8].copy_from_slice(&total_len.to_le_bytes());
            data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority.key.as_ref());
            Ok(())
        }
        AspisInstruction::UploadChunk { offset, chunk } => {
            let authority = next_account_info(account_iter)?;
            if !proof_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            let mut data = proof_account.try_borrow_mut_data()?;
            require_upload_authority(&data, authority)?;
            let total_len = proof_len(&data)?;
            let start = PROOF_ACCOUNT_HEADER_LEN
                .checked_add(offset as usize)
                .ok_or(ProgramError::InvalidInstructionData)?;
            let end = start
                .checked_add(chunk.len())
                .ok_or(ProgramError::InvalidInstructionData)?;
            if offset as usize + chunk.len() > total_len || end > data.len() {
                return Err(ProgramError::InvalidInstructionData);
            }
            data[start..end].copy_from_slice(&chunk);
            Ok(())
        }
        AspisInstruction::FinalizeProof => {
            let authority = next_account_info(account_iter)?;
            if !proof_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            let mut data = proof_account.try_borrow_mut_data()?;
            require_upload_authority(&data, authority)?;
            data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
            Ok(())
        }
        AspisInstruction::InitializeAtomicPool { sequence, anchor } => {
            if !proof_account.is_signer {
                return Err(ProgramError::MissingRequiredSignature);
            }
            if !proof_account.is_writable {
                return Err(ProgramError::InvalidAccountData);
            }
            aspis_statement::decode_digest_canonical(&anchor)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            sequence
                .checked_add(1)
                .ok_or(ProgramError::ArithmeticOverflow)?;
            let mut data = proof_account.try_borrow_mut_data()?;
            if data.len() != atomic_payment::ATOMIC_POOL_STATE_LEN
                || !data.iter().all(|byte| *byte == 0)
            {
                return Err(ProgramError::InvalidAccountData);
            }
            atomic_payment::AtomicPoolStateV1 { sequence, anchor }.encode(&mut data)
        }
        AspisInstruction::Verify { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false, 1, false)
        }
        AspisInstruction::VerifyFast { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false, 1, false)
        }
        AspisInstruction::VerifySyscallInverse { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false, 2, false)
        }
        AspisInstruction::VerifyProfile { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, true, 1, false)
        }
        AspisInstruction::VerifyWithClaim {
            statement_digest,
            claim_z,
            claim_v,
        } => {
            let z = claim_z
                .iter()
                .map(|bytes| aspis_core::field::QM31::from_le_bytes(bytes))
                .collect::<Option<Vec<_>>>()
                .ok_or(ProgramError::InvalidInstructionData)?;
            let v = aspis_core::field::QM31::from_le_bytes(&claim_v)
                .ok_or(ProgramError::InvalidInstructionData)?;
            let claim = aspis_core::EvaluationClaim { z, v };
            verify_uploaded_proof(
                proof_account,
                statement_digest,
                Some(&claim),
                false,
                1,
                false,
            )
        }
        AspisInstruction::VerifyExactWideV4Scaffold {
            statement_digest,
            claim_z,
            claim_v,
        } => {
            let z = claim_z
                .iter()
                .map(|bytes| aspis_core::field::QM31::from_le_bytes(bytes))
                .collect::<Option<Vec<_>>>()
                .ok_or(ProgramError::InvalidInstructionData)?;
            let v = aspis_core::field::QM31::from_le_bytes(&claim_v)
                .ok_or(ProgramError::InvalidInstructionData)?;
            let claim = aspis_core::EvaluationClaim { z, v };
            verify_uploaded_proof(
                proof_account,
                statement_digest,
                Some(&claim),
                false,
                1,
                true,
            )
        }
        AspisInstruction::VerifyLegacySoftware { statement_digest } => {
            verify_uploaded_proof(proof_account, statement_digest, None, false, 0, false)
        }
        AspisInstruction::LayoutProbe {
            log_rows,
            columns,
            query_count,
            leaf_bytes,
        } => run_layout_probe(log_rows, columns, query_count, leaf_bytes),
        // handled before account resolution above
        AspisInstruction::TranscriptKat { .. } => unreachable!(),
        AspisInstruction::ConstraintCompositionProbe { .. } => unreachable!(),
        AspisInstruction::Poseidon2Probe { .. } => unreachable!(),
        AspisInstruction::Poseidon2OptimizedProbe { .. } => unreachable!(),
        AspisInstruction::ZkKernelProbe { .. } => unreachable!(),
        AspisInstruction::WideRlcProbe { .. } => unreachable!(),
        AspisInstruction::MerkleArityProbe { .. } => unreachable!(),
        AspisInstruction::StatementSumcheckProbe { .. } => unreachable!(),
        AspisInstruction::LogUpCompressionKat { .. } => unreachable!(),
        AspisInstruction::OodSampleRelationProbe { .. } => unreachable!(),
        AspisInstruction::TranscriptKatV4S2PcsScaffold { .. } => unreachable!(),
        AspisInstruction::FinalPaymentTranscriptKatV4 { .. } => unreachable!(),
        AspisInstruction::ExactWideV4Diagnostic { .. } => unreachable!(),
        AspisInstruction::M31CircleBasisDiagnostic { .. } => unreachable!(),
        AspisInstruction::VerifyM31CircleV4Diagnostic { .. } => unreachable!(),
        AspisInstruction::TwoPointBatchingDiagnostic { .. } => unreachable!(),
        AspisInstruction::VerifyM31CircleFreshKappa { .. } => unreachable!(),
        AspisInstruction::MeasureM31CircleJohnson { .. } => unreachable!(),
        AspisInstruction::MeasureM31CircleRate16 { .. } => unreachable!(),
        AspisInstruction::MeasureM31CircleRate16Composition { .. } => unreachable!(),
        AspisInstruction::MeasureM31CircleRate16Hardened { .. } => unreachable!(),
        AspisInstruction::MeasurePaymentHidingPlacementV4 { .. } => unreachable!(),
        AspisInstruction::MeasurePaymentHidingAggregateRelationV4 { .. } => unreachable!(),
        AspisInstruction::MeasurePaymentHidingProfile15 { .. } => unreachable!(),
        AspisInstruction::Radix8MerkleDepth12Probe { .. } => unreachable!(),
        AspisInstruction::MerkleForestProbe { .. } => unreachable!(),
        AspisInstruction::Layer0DotWidthProbe { .. } => unreachable!(),
        AspisInstruction::AtomicPaymentStateTransitionV1 { .. } => unreachable!(),
        AspisInstruction::VerifyStateOnlyWidth28 { .. } => unreachable!(),
        AspisInstruction::MeasureStateOnlyWidth28 { .. } => unreachable!(),
        // Temporary fail-closed arm while the append-only tag-41 diagnostic
        // handler is being completed in parallel. It cannot authorize state.
        AspisInstruction::HvzkWhirMaskProbe { .. } => unreachable!(),
        AspisInstruction::AtomicRoutingPartitionProbe { .. } => unreachable!(),
        AspisInstruction::AtomicStateOnlyProfile20CostCandidate { .. } => unreachable!(),
        AspisInstruction::StateOnlyRelationStructuralProbe { .. } => unreachable!(),
        AspisInstruction::StateOnlyMaskedSwitchProfile21Probe { .. } => unreachable!(),
        AspisInstruction::VerifyAtomicStateOnlyProfile20V3 { .. } => unreachable!(),
        AspisInstruction::ApplyAtomicStateOnlyProfile20V3 { .. } => unreachable!(),
        AspisInstruction::MeasureAtomicStateOnlyProfile20MutationV3 { .. } => unreachable!(),
        AspisInstruction::StateOnlyPrivateMerkleSaltProbe { .. } => unreachable!(),
        AspisInstruction::VerifyAtomicStateOnlyProfile21V3 { .. } => unreachable!(),
        AspisInstruction::ApplyAtomicStateOnlyProfile21V3 { .. } => unreachable!(),
        AspisInstruction::MeasureAtomicStateOnlyProfile21MutationV3 { .. } => unreachable!(),
        AspisInstruction::StateOnlyHelperDot2Probe { .. } => unreachable!(),
        AspisInstruction::StateOnlyHelperDot3Probe { .. } => unreachable!(),
        AspisInstruction::StateOnlyFoldPolynomialProbe { .. } => unreachable!(),
        AspisInstruction::VerifyAtomicStateOnlyProfile22V3 { .. } => unreachable!(),
        AspisInstruction::ApplyAtomicStateOnlyProfile22V3 { .. } => unreachable!(),
        AspisInstruction::MeasureAtomicStateOnlyProfile22MutationV3 { .. } => unreachable!(),
        AspisInstruction::VerifyAtomicStateOnlyProfile23V3 { .. } => unreachable!(),
        AspisInstruction::ApplyAtomicStateOnlyProfile23V3 { .. } => unreachable!(),
        AspisInstruction::MeasureAtomicStateOnlyProfile23MutationV3 { .. } => unreachable!(),
        AspisInstruction::MeasurePaymentStatementV4 => {
            measure_uploaded_payment_statement_v4(proof_account)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use solana_program::{account_info::AccountInfo, clock::Epoch};

    #[cfg(feature = "profile23-minimal-dispatch")]
    #[test]
    fn profile23_minimal_dispatch_preserves_required_borsh_wires_only() {
        let required = [
            AspisInstruction::InitProof { total_len: 61_599 },
            AspisInstruction::UploadChunk {
                offset: 17,
                chunk: vec![1, 2, 3, 4],
            },
            AspisInstruction::VerifyAtomicStateOnlyProfile23V3 {
                pool: [1u8; 32],
                sequence: 73,
                public_input: [2u8; 104],
                output_anchor: [3u8; 32],
                diagnostic_unmined: false,
            },
            AspisInstruction::ApplyAtomicStateOnlyProfile23V3 {
                current_anchor: [1u8; 32],
                nullifier: [2u8; 32],
                output_commitment: [3u8; 32],
                output_anchor: [4u8; 32],
                asset_id: 17,
                fee: 1,
            },
            AspisInstruction::FinalizeProof,
            AspisInstruction::InitializeAtomicPool {
                sequence: 0,
                anchor: [0u8; 32],
            },
        ];

        for instruction in required {
            let wire = borsh::to_vec(&instruction).unwrap();
            assert!(matches!(wire[0], 0 | 1 | 59 | 60 | 62 | 63));
            assert_eq!(
                process_profile23_production_instruction(&id(), &[], &wire),
                Err(ProgramError::NotEnoughAccountKeys),
                "required tag {} was not parsed through the minimal wire",
                wire[0]
            );
        }

        let historical = borsh::to_vec(&AspisInstruction::Verify {
            statement_digest: [0u8; 32],
        })
        .unwrap();
        assert_eq!(
            process_profile23_production_instruction(&id(), &[], &historical),
            Err(ProgramError::InvalidInstructionData)
        );

        let mut trailing = borsh::to_vec(&AspisInstruction::FinalizeProof).unwrap();
        trailing.push(0);
        assert_eq!(
            process_profile23_production_instruction(&id(), &[], &trailing),
            Err(ProgramError::InvalidInstructionData)
        );

        let diagnostic = borsh::to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile23V3 {
            pool: [1u8; 32],
            sequence: 73,
            public_input: [2u8; 104],
            output_anchor: [3u8; 32],
            diagnostic_unmined: true,
        })
        .unwrap();
        assert_eq!(
            process_profile23_production_instruction(&id(), &[], &diagnostic),
            Err(ProgramError::InvalidInstructionData)
        );

        let diagnostic_mutation = borsh::to_vec(
            &AspisInstruction::MeasureAtomicStateOnlyProfile23MutationV3 {
                current_anchor: [1u8; 32],
                nullifier: [2u8; 32],
                output_commitment: [3u8; 32],
                output_anchor: [4u8; 32],
                asset_id: 17,
                fee: 1,
            },
        )
        .unwrap();
        assert_eq!(
            process_profile23_production_instruction(&id(), &[], &diagnostic_mutation),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
    }

    #[test]
    fn constraint_composition_probe_requires_no_accounts() {
        let probe = aspis_statement::CompositionProbe::OPTIMISTIC;
        let instruction = AspisInstruction::ConstraintCompositionProbe {
            opened_values: probe.opened_values,
            poseidon_sbox_terms: probe.poseidon_sbox_terms,
            poseidon_linear_terms: probe.poseidon_linear_terms,
            logup_degree3_terms: probe.logup_degree3_terms,
            range_bit_terms: probe.range_bit_terms,
            eq_variables: probe.eq_variables,
            optimized: false,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Ok(())
        );
    }

    #[test]
    fn poseidon2_probe_requires_no_accounts() {
        for instruction in [
            AspisInstruction::Poseidon2Probe { permutations: 2 },
            AspisInstruction::Poseidon2OptimizedProbe { permutations: 2 },
        ] {
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
    }

    #[test]
    fn zk_kernel_probes_require_no_accounts() {
        for kind in [
            ZkKernelKind::M31InverseSoftware,
            ZkKernelKind::M31InverseSyscall,
            ZkKernelKind::Qm31SquareGeneric,
            ZkKernelKind::Qm31SquareSpecialized,
            ZkKernelKind::M31Pow2Generic,
            ZkKernelKind::M31Pow2Shift,
            ZkKernelKind::Sha256AppendChain,
        ] {
            let instruction = AspisInstruction::ZkKernelProbe {
                kind,
                iterations: 8,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
    }

    #[test]
    fn wide_rlc_kernels_require_no_accounts() {
        for kernel in 0..=6 {
            let instruction = AspisInstruction::WideRlcProbe {
                columns: 8,
                query_count: 3,
                kernel,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
    }

    #[test]
    fn merkle_arity_probes_require_no_accounts() {
        for arity in [2, 4] {
            let instruction = AspisInstruction::MerkleArityProbe {
                depth: 10,
                query_count: 8,
                arity,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }
    }

    #[test]
    fn radix8_depth12_probe_requires_no_accounts_and_has_frontier_teeth() {
        for arity in [4, 8] {
            for corrupt_frontier in [false, true] {
                let instruction = AspisInstruction::Radix8MerkleDepth12Probe {
                    arity,
                    corrupt_frontier,
                };
                assert_eq!(
                    process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                    Ok(())
                );
            }
        }
        let invalid = AspisInstruction::Radix8MerkleDepth12Probe {
            arity: 2,
            corrupt_frontier: false,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&invalid).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn merkle_forest_probe_requires_no_accounts_and_has_per_lane_teeth() {
        for fused in [false, true] {
            for corrupt_lane in [u8::MAX, 0, 1, 2, 3, 4] {
                let instruction = AspisInstruction::MerkleForestProbe {
                    fused,
                    corrupt_lane,
                };
                assert_eq!(
                    process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                    Ok(())
                );
            }
        }
        let invalid = AspisInstruction::MerkleForestProbe {
            fused: true,
            corrupt_lane: 5,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&invalid).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn layer0_dot_width_probe_is_tag37_and_has_sink_and_canonicality_teeth() {
        for columns in [49u8, 33, 17, 16] {
            let expected_sink = match columns {
                49 => layer0_dot_width_sink::<49>(0).unwrap(),
                33 => layer0_dot_width_sink::<33>(0).unwrap(),
                17 => layer0_dot_width_sink::<17>(0).unwrap(),
                16 => layer0_dot_width_sink::<16>(0).unwrap(),
                _ => unreachable!(),
            };
            let clean = AspisInstruction::Layer0DotWidthProbe {
                columns,
                corrupt: 0,
                expected_sink,
            };
            let encoded = borsh::to_vec(&clean).unwrap();
            assert_eq!(encoded[0], 37);
            assert_eq!(process_instruction(&id(), &[], &encoded), Ok(()));

            for corrupt in [1, 2] {
                let instruction = AspisInstruction::Layer0DotWidthProbe {
                    columns,
                    corrupt,
                    expected_sink,
                };
                assert_eq!(
                    process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                    Ok(())
                );
            }

            let mut wrong_sink = expected_sink;
            wrong_sink[0] ^= 1;
            let wrong = AspisInstruction::Layer0DotWidthProbe {
                columns,
                corrupt: 0,
                expected_sink: wrong_sink,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&wrong).unwrap()),
                Err(ProgramError::InvalidInstructionData)
            );
        }

        for invalid in [
            AspisInstruction::Layer0DotWidthProbe {
                columns: 48,
                corrupt: 0,
                expected_sink: [0u8; 32],
            },
            AspisInstruction::Layer0DotWidthProbe {
                columns: 49,
                corrupt: 3,
                expected_sink: [0u8; 32],
            },
        ] {
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&invalid).unwrap()),
                Err(ProgramError::InvalidInstructionData)
            );
        }
    }

    #[test]
    fn atomic_routing_partition_probe_is_tag42_and_both_paths_are_identical() {
        for seed in [1u32, 7, 0x4154_4f4d] {
            let legacy = atomic_routing_partition_probe_sink(false, seed);
            let optimized = atomic_routing_partition_probe_sink(true, seed);
            assert_eq!(legacy, optimized);
            for mode in [false, true] {
                let instruction = AspisInstruction::AtomicRoutingPartitionProbe {
                    optimized: mode,
                    seed,
                    expected_sink: legacy,
                };
                let encoded = borsh::to_vec(&instruction).unwrap();
                assert_eq!(encoded[0], 42);
                assert_eq!(process_instruction(&id(), &[], &encoded), Ok(()));

                let mut wrong = legacy;
                wrong[0] ^= 1;
                let wrong = AspisInstruction::AtomicRoutingPartitionProbe {
                    optimized: mode,
                    seed,
                    expected_sink: wrong,
                };
                assert_eq!(
                    process_instruction(&id(), &[], &borsh::to_vec(&wrong).unwrap()),
                    Err(ProgramError::InvalidInstructionData)
                );
            }
        }
    }

    #[test]
    fn atomic_state_only_profile20_acceptance_is_append_only_tag46() {
        let instruction = AspisInstruction::VerifyAtomicStateOnlyProfile20V3 {
            pool: [0x5a; 32],
            sequence: 73,
            public_input: [0u8; 104],
            output_anchor: [0u8; 32],
            diagnostic_unmined: true,
        };
        assert_eq!(borsh::to_vec(&instruction).unwrap()[0], 46);
    }

    #[test]
    fn atomic_profile20_mutation_tags_are_append_only_and_diagnostic_is_fail_closed_by_default() {
        let production = AspisInstruction::ApplyAtomicStateOnlyProfile20V3 {
            current_anchor: [1; 32],
            nullifier: [2; 32],
            output_commitment: [3; 32],
            output_anchor: [4; 32],
            asset_id: 5,
            fee: 6,
        };
        let diagnostic = AspisInstruction::MeasureAtomicStateOnlyProfile20MutationV3 {
            current_anchor: [1; 32],
            nullifier: [2; 32],
            output_commitment: [3; 32],
            output_anchor: [4; 32],
            asset_id: 5,
            fee: 6,
        };
        let production_encoded = borsh::to_vec(&production).unwrap();
        assert_eq!(production_encoded[0], 47);
        let encoded = borsh::to_vec(&diagnostic).unwrap();
        assert_eq!(encoded[0], 48);
        #[cfg(not(feature = "profile20-mutation-candidate"))]
        assert_eq!(
            process_instruction(&id(), &[], &production_encoded),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
        #[cfg(not(feature = "diagnostic-unmined-mutation"))]
        assert_eq!(
            process_instruction(&id(), &[], &encoded),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
    }

    #[test]
    fn private_merkle_salt_probe_is_append_only_tag49() {
        let instruction = AspisInstruction::StateOnlyPrivateMerkleSaltProbe {
            mode: 0,
            expected_sink: [0u8; 32],
        };
        assert_eq!(borsh::to_vec(&instruction).unwrap()[0], 49);
        assert_eq!(
            process_instruction(
                &id(),
                &[],
                &borsh::to_vec(&AspisInstruction::StateOnlyPrivateMerkleSaltProbe {
                    mode: 4,
                    expected_sink: [0u8; 32],
                })
                .unwrap(),
            ),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn integrated_atomic_profile21_wrapper_is_reserved_tag50_and_fail_closed() {
        assert_eq!(
            aspis_core::state_only_masked_switch_basis::MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT,
            ATOMIC_PROFILE21_MASKED_SWITCH_BASIS_FINGERPRINT,
        );
        let instruction = AspisInstruction::VerifyAtomicStateOnlyProfile21V3 {
            pool: [0x5a; 32],
            sequence: 73,
            public_input: [0u8; 104],
            output_anchor: [0u8; 32],
            diagnostic_unmined: true,
        };
        let encoded = borsh::to_vec(&instruction).unwrap();
        assert_eq!(encoded[0], 50);
        #[cfg(not(feature = "profile21-integrated-candidate"))]
        assert_eq!(
            process_instruction(&id(), &[], &encoded),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
    }

    #[test]
    fn atomic_profile21_mutation_tags_are_append_only_and_fail_closed() {
        let production = AspisInstruction::ApplyAtomicStateOnlyProfile21V3 {
            current_anchor: [1u8; 32],
            nullifier: [2u8; 32],
            output_commitment: [3u8; 32],
            output_anchor: [4u8; 32],
            asset_id: 17,
            fee: 1,
        };
        let diagnostic = AspisInstruction::MeasureAtomicStateOnlyProfile21MutationV3 {
            current_anchor: [1u8; 32],
            nullifier: [2u8; 32],
            output_commitment: [3u8; 32],
            output_anchor: [4u8; 32],
            asset_id: 17,
            fee: 1,
        };
        let production = borsh::to_vec(&production).unwrap();
        let diagnostic = borsh::to_vec(&diagnostic).unwrap();
        assert_eq!(production[0], 51);
        assert_eq!(diagnostic[0], 52);
        #[cfg(not(feature = "profile21-mutation-candidate"))]
        assert_eq!(
            process_instruction(&id(), &[], &production),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
        #[cfg(not(feature = "diagnostic-unmined-profile21-mutation"))]
        assert_eq!(
            process_instruction(&id(), &[], &diagnostic),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
    }

    #[test]
    fn atomic_profile22_tags_are_append_only_and_fail_closed() {
        let verify = borsh::to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile22V3 {
            pool: [0x5a; 32],
            sequence: 73,
            public_input: [0u8; 104],
            output_anchor: [0u8; 32],
            diagnostic_unmined: true,
        })
        .unwrap();
        let production = borsh::to_vec(&AspisInstruction::ApplyAtomicStateOnlyProfile22V3 {
            current_anchor: [1u8; 32],
            nullifier: [2u8; 32],
            output_commitment: [3u8; 32],
            output_anchor: [4u8; 32],
            asset_id: 17,
            fee: 1,
        })
        .unwrap();
        let diagnostic = borsh::to_vec(
            &AspisInstruction::MeasureAtomicStateOnlyProfile22MutationV3 {
                current_anchor: [1u8; 32],
                nullifier: [2u8; 32],
                output_commitment: [3u8; 32],
                output_anchor: [4u8; 32],
                asset_id: 17,
                fee: 1,
            },
        )
        .unwrap();
        assert_eq!(verify[0], 56);
        assert_eq!(production[0], 57);
        assert_eq!(diagnostic[0], 58);
        #[cfg(not(feature = "profile22-integrated-candidate"))]
        assert_eq!(
            process_instruction(&id(), &[], &verify),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
        #[cfg(all(
            feature = "profile22-integrated-candidate",
            not(feature = "diagnostic-unmined-profile22-acceptance")
        ))]
        assert_eq!(
            process_instruction(&id(), &[], &verify),
            Err(ProgramError::InvalidInstructionData),
            "a production-capable profile22 build exposed the unmined tag56 bypass"
        );
        #[cfg(not(feature = "profile22-mutation-candidate"))]
        assert_eq!(
            process_instruction(&id(), &[], &production),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
        #[cfg(not(feature = "diagnostic-unmined-profile22-mutation"))]
        assert_eq!(
            process_instruction(&id(), &[], &diagnostic),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
    }

    #[test]
    fn atomic_profile23_tags_are_append_only_and_fail_closed() {
        let verify = borsh::to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile23V3 {
            pool: [0x5a; 32],
            sequence: 73,
            public_input: [0u8; 104],
            output_anchor: [0u8; 32],
            diagnostic_unmined: true,
        })
        .unwrap();
        let production = borsh::to_vec(&AspisInstruction::ApplyAtomicStateOnlyProfile23V3 {
            current_anchor: [1u8; 32],
            nullifier: [2u8; 32],
            output_commitment: [3u8; 32],
            output_anchor: [4u8; 32],
            asset_id: 17,
            fee: 1,
        })
        .unwrap();
        let diagnostic = borsh::to_vec(
            &AspisInstruction::MeasureAtomicStateOnlyProfile23MutationV3 {
                current_anchor: [1u8; 32],
                nullifier: [2u8; 32],
                output_commitment: [3u8; 32],
                output_anchor: [4u8; 32],
                asset_id: 17,
                fee: 1,
            },
        )
        .unwrap();
        let finalize = borsh::to_vec(&AspisInstruction::FinalizeProof).unwrap();
        let initialize_pool = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 0,
            anchor: [0u8; 32],
        })
        .unwrap();
        assert_eq!(verify[0], 59);
        assert_eq!(production[0], 60);
        assert_eq!(diagnostic[0], 61);
        assert_eq!(finalize[0], 62);
        assert_eq!(initialize_pool[0], 63);
        #[cfg(not(feature = "profile23-integrated-candidate"))]
        assert_eq!(
            process_instruction(&id(), &[], &verify),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
        #[cfg(all(
            feature = "profile23-integrated-candidate",
            not(feature = "diagnostic-unmined-profile23-acceptance")
        ))]
        assert_eq!(
            process_instruction(&id(), &[], &verify),
            Err(ProgramError::InvalidInstructionData)
        );
        #[cfg(not(feature = "profile23-mutation-candidate"))]
        assert_eq!(
            process_instruction(&id(), &[], &production),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
        #[cfg(feature = "profile23-mutation-candidate")]
        assert_eq!(
            process_instruction(&id(), &[], &production),
            Err(ProgramError::NotEnoughAccountKeys),
            "an enabled Profile23 production build did not dispatch tag60 into the atomic wrapper"
        );
        #[cfg(not(feature = "diagnostic-unmined-profile23-mutation"))]
        assert_eq!(
            process_instruction(&id(), &[], &diagnostic),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );
    }

    #[test]
    fn helper_dot2_probe_is_append_only_tag53_and_exact_on_teeth() {
        let reference = state_only_helper_dot2_probe_sink(false, 0).unwrap();
        let fused = state_only_helper_dot2_probe_sink(true, 0).unwrap();
        assert_eq!(fused, reference);
        for fused_helpers in [false, true] {
            let clean = AspisInstruction::StateOnlyHelperDot2Probe {
                fused_helpers,
                corrupt: 0,
                expected_sink: reference,
            };
            let encoded = borsh::to_vec(&clean).unwrap();
            assert_eq!(encoded[0], 53);
            assert_eq!(process_instruction(&id(), &[], &encoded), Ok(()));
            for corrupt in [1, 2] {
                let tooth = AspisInstruction::StateOnlyHelperDot2Probe {
                    fused_helpers,
                    corrupt,
                    expected_sink: [0u8; 32],
                };
                assert_eq!(
                    process_instruction(&id(), &[], &borsh::to_vec(&tooth).unwrap()),
                    Ok(())
                );
            }
        }
        let wrong = AspisInstruction::StateOnlyHelperDot2Probe {
            fused_helpers: true,
            corrupt: 0,
            expected_sink: [0u8; 32],
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&wrong).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn helper_dot3_probe_is_append_only_tag54_and_exact_on_tooth() {
        let reference = state_only_helper_dot3_probe_sink(false, 0).unwrap();
        let fused = state_only_helper_dot3_probe_sink(true, 0).unwrap();
        assert_eq!(fused, reference);
        for fused_helpers in [false, true] {
            let clean = AspisInstruction::StateOnlyHelperDot3Probe {
                fused_helpers,
                corrupt: 0,
                expected_sink: reference,
            };
            let encoded = borsh::to_vec(&clean).unwrap();
            assert_eq!(encoded[0], 54);
            assert_eq!(process_instruction(&id(), &[], &encoded), Ok(()));
            let tooth = AspisInstruction::StateOnlyHelperDot3Probe {
                fused_helpers,
                corrupt: 1,
                expected_sink: [0u8; 32],
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&tooth).unwrap()),
                Ok(())
            );
        }
        let wrong = AspisInstruction::StateOnlyHelperDot3Probe {
            fused_helpers: true,
            corrupt: 0,
            expected_sink: [0u8; 32],
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&wrong).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn fold_polynomial_probe_is_append_only_tag55_and_exact_on_tooth() {
        let nested = state_only_fold_polynomial_probe_sink(false, 0).unwrap();
        let polynomial = state_only_fold_polynomial_probe_sink(true, 0).unwrap();
        assert_eq!(polynomial, nested);
        for polynomial_basis in [false, true] {
            let clean = AspisInstruction::StateOnlyFoldPolynomialProbe {
                polynomial_basis,
                corrupt: 0,
                expected_sink: nested,
            };
            let encoded = borsh::to_vec(&clean).unwrap();
            assert_eq!(encoded[0], 55);
            assert_eq!(process_instruction(&id(), &[], &encoded), Ok(()));
            let tooth = AspisInstruction::StateOnlyFoldPolynomialProbe {
                polynomial_basis,
                corrupt: 1,
                expected_sink: [0u8; 32],
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&tooth).unwrap()),
                Ok(())
            );
        }
        let wrong = AspisInstruction::StateOnlyFoldPolynomialProbe {
            polynomial_basis: true,
            corrupt: 0,
            expected_sink: [0u8; 32],
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&wrong).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn logup_compression_kat_requires_no_accounts_and_rejects_drift() {
        let instruction = AspisInstruction::LogUpCompressionKat {
            expected_phi: aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Ok(())
        );

        let mut drifted = aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED;
        drifted[0] ^= 1;
        let instruction = AspisInstruction::LogUpCompressionKat {
            expected_phi: drifted,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn ood_sample_relation_probe_requires_no_accounts_and_pins_both_sinks() {
        for (samples_per_round, expected_sink) in [
            (1, aspis_core::verify::OOD_SAMPLE_PROBE_S1_EXPECTED),
            (2, aspis_core::verify::OOD_SAMPLE_PROBE_S2_EXPECTED),
        ] {
            let instruction = AspisInstruction::OodSampleRelationProbe {
                samples_per_round,
                expected_sink,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );
        }

        let mut drifted = aspis_core::verify::OOD_SAMPLE_PROBE_S2_EXPECTED;
        drifted[0] ^= 1;
        let instruction = AspisInstruction::OodSampleRelationProbe {
            samples_per_round: 2,
            expected_sink: drifted,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );

        let instruction = AspisInstruction::OodSampleRelationProbe {
            samples_per_round: 3,
            expected_sink: [0u8; 16],
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn two_point_batching_diagnostic_requires_no_accounts_and_pins_all_sinks() {
        let modes = [
            TwoPointBatchingDiagnosticMode::OnePointBaseline,
            TwoPointBatchingDiagnosticMode::FreshKappaSingleLane,
            TwoPointBatchingDiagnosticMode::TwoIndependentRelationLanes,
            TwoPointBatchingDiagnosticMode::DisjointGamma51SingleLane,
        ];
        for mode in modes {
            let expected_sink =
                aspis_core::two_point::TWO_POINT_BATCHING_EXPECTED_SINKS[mode.index()];
            let instruction = AspisInstruction::TwoPointBatchingDiagnostic {
                mode,
                expected_sink,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Ok(())
            );

            let mut drifted = expected_sink;
            drifted[0] ^= 1;
            let instruction = AspisInstruction::TwoPointBatchingDiagnostic {
                mode,
                expected_sink: drifted,
            };
            assert_eq!(
                process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
                Err(ProgramError::InvalidInstructionData)
            );
        }
    }

    #[test]
    fn transcript_kat_v4_s2_pcs_scaffold_requires_no_accounts_and_rejects_drift() {
        let instruction = AspisInstruction::TranscriptKatV4S2PcsScaffold {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Ok(())
        );

        let mut drifted = aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED;
        drifted[0] ^= 1;
        let instruction = AspisInstruction::TranscriptKatV4S2PcsScaffold { expected: drifted };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&instruction).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn final_payment_kat_requires_no_accounts_rejects_drift_and_exact_wide_needs_a_fixture() {
        let kat = AspisInstruction::FinalPaymentTranscriptKatV4 {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_FINAL_PAYMENT_V4_EXPECTED,
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&kat).unwrap()),
            Ok(())
        );
        let mut drifted = aspis_core::transcript::TRANSCRIPT_KAT_FINAL_PAYMENT_V4_EXPECTED;
        drifted[0] ^= 1;
        let bad = AspisInstruction::FinalPaymentTranscriptKatV4 { expected: drifted };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&bad).unwrap()),
            Err(ProgramError::InvalidInstructionData)
        );

        let diagnostic = AspisInstruction::ExactWideV4Diagnostic {
            mode: ExactWideV4DiagnosticMode::BaselineFourDots,
            expected_sink: [0u8; 32],
        };
        assert_eq!(
            process_instruction(&id(), &[], &borsh::to_vec(&diagnostic).unwrap()),
            Err(ProgramError::NotEnoughAccountKeys)
        );
    }

    #[test]
    fn instruction_wire_discriminants_are_append_only() {
        let digest = [0u8; 32];
        let variants = vec![
            (AspisInstruction::InitProof { total_len: 0 }, 0),
            (
                AspisInstruction::UploadChunk {
                    offset: 0,
                    chunk: vec![],
                },
                1,
            ),
            (
                AspisInstruction::Verify {
                    statement_digest: digest,
                },
                2,
            ),
            (
                AspisInstruction::VerifyProfile {
                    statement_digest: digest,
                },
                3,
            ),
            (
                AspisInstruction::LayoutProbe {
                    log_rows: 0,
                    columns: 0,
                    query_count: 0,
                    leaf_bytes: 0,
                },
                4,
            ),
            (AspisInstruction::TranscriptKat { expected: digest }, 5),
            (
                AspisInstruction::VerifyWithClaim {
                    statement_digest: digest,
                    claim_z: vec![],
                    claim_v: [0u8; 16],
                },
                6,
            ),
            (
                AspisInstruction::ConstraintCompositionProbe {
                    opened_values: 0,
                    poseidon_sbox_terms: 0,
                    poseidon_linear_terms: 0,
                    logup_degree3_terms: 0,
                    range_bit_terms: 0,
                    eq_variables: 0,
                    optimized: false,
                },
                7,
            ),
            (AspisInstruction::Poseidon2Probe { permutations: 0 }, 8),
            (
                AspisInstruction::VerifyFast {
                    statement_digest: digest,
                },
                9,
            ),
            (
                AspisInstruction::VerifySyscallInverse {
                    statement_digest: digest,
                },
                10,
            ),
            (
                AspisInstruction::Poseidon2OptimizedProbe { permutations: 0 },
                11,
            ),
            (
                AspisInstruction::ZkKernelProbe {
                    kind: ZkKernelKind::M31InverseSoftware,
                    iterations: 0,
                },
                12,
            ),
            (
                AspisInstruction::WideRlcProbe {
                    columns: 0,
                    query_count: 0,
                    kernel: 0,
                },
                13,
            ),
            (
                AspisInstruction::MerkleArityProbe {
                    depth: 0,
                    query_count: 0,
                    arity: 0,
                },
                14,
            ),
            (
                AspisInstruction::VerifyLegacySoftware {
                    statement_digest: digest,
                },
                15,
            ),
            (
                AspisInstruction::StatementSumcheckProbe {
                    rounds: 0,
                    coefficients: 0,
                    claims: 0,
                    selector_terms: 0,
                    selector_exceptions: 0,
                },
                16,
            ),
            (
                AspisInstruction::LogUpCompressionKat {
                    expected_phi: [0u8; 16],
                },
                17,
            ),
            (
                AspisInstruction::OodSampleRelationProbe {
                    samples_per_round: 1,
                    expected_sink: [0u8; 16],
                },
                18,
            ),
            (
                AspisInstruction::TranscriptKatV4S2PcsScaffold { expected: digest },
                19,
            ),
            (
                AspisInstruction::FinalPaymentTranscriptKatV4 { expected: digest },
                20,
            ),
            (
                AspisInstruction::ExactWideV4Diagnostic {
                    mode: ExactWideV4DiagnosticMode::BaselineFourDots,
                    expected_sink: digest,
                },
                21,
            ),
            (
                AspisInstruction::VerifyExactWideV4Scaffold {
                    statement_digest: digest,
                    claim_z: vec![],
                    claim_v: [0u8; 16],
                },
                22,
            ),
            (
                AspisInstruction::M31CircleBasisDiagnostic {
                    mode: M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
                    expected_sink: digest,
                },
                23,
            ),
            (
                AspisInstruction::VerifyM31CircleV4Diagnostic {
                    statement_digest: digest,
                    claim_z: vec![],
                    statement_evaluations_digest: digest,
                },
                24,
            ),
            (
                AspisInstruction::TwoPointBatchingDiagnostic {
                    mode: TwoPointBatchingDiagnosticMode::OnePointBaseline,
                    expected_sink: [0u8; 16],
                },
                25,
            ),
            (
                AspisInstruction::VerifyM31CircleFreshKappa {
                    statement_digest: digest,
                    claim_z: vec![],
                },
                26,
            ),
            (
                AspisInstruction::MeasureM31CircleJohnson {
                    statement_digest: digest,
                    claim_z: vec![],
                    phase: JohnsonM31CircleDiagnosticPhase::PreparedBase,
                    start: 0,
                    end: 0,
                },
                27,
            ),
            (
                AspisInstruction::MeasureM31CircleRate16 {
                    statement_digest: digest,
                    claim_z: vec![],
                    phase: JohnsonM31CircleDiagnosticPhase::PreparedBase,
                    start: 0,
                    end: 0,
                },
                28,
            ),
            (
                AspisInstruction::MeasureM31CircleRate16Composition {
                    statement_digest: digest,
                    claim_z: vec![],
                    stress: false,
                },
                29,
            ),
            (
                AspisInstruction::MeasureM31CircleRate16Hardened {
                    statement_digest: digest,
                    claim_z: vec![],
                    phase: JohnsonM31CircleDiagnosticPhase::PreparedBase,
                    start: 0,
                    end: 0,
                },
                30,
            ),
            (AspisInstruction::MeasurePaymentStatementV4, 31),
            (
                AspisInstruction::MeasurePaymentHidingPlacementV4 {
                    placement: 0,
                    expected_sink: [0u8; 16],
                },
                32,
            ),
            (
                AspisInstruction::MeasurePaymentHidingAggregateRelationV4 {
                    phase: 0,
                    expected_sink: [0u8; 16],
                },
                33,
            ),
            (
                AspisInstruction::MeasurePaymentHidingProfile15 {
                    statement_digest: digest,
                    public_input: [0u8; 104],
                    phase: JohnsonM31CircleDiagnosticPhase::PreparedBase,
                    start: 0,
                    end: 0,
                },
                34,
            ),
            (
                AspisInstruction::Radix8MerkleDepth12Probe {
                    arity: 8,
                    corrupt_frontier: false,
                },
                35,
            ),
            (
                AspisInstruction::MerkleForestProbe {
                    fused: true,
                    corrupt_lane: u8::MAX,
                },
                36,
            ),
            (
                AspisInstruction::Layer0DotWidthProbe {
                    columns: 16,
                    corrupt: 0,
                    expected_sink: digest,
                },
                37,
            ),
            (
                AspisInstruction::AtomicPaymentStateTransitionV1 {
                    current_anchor: digest,
                    nullifier: digest,
                    output_commitment: digest,
                    output_anchor: digest,
                    asset_id: 7,
                    fee: 1,
                },
                38,
            ),
            (
                AspisInstruction::VerifyStateOnlyWidth28 {
                    statement_digest: digest,
                    public_input: [0u8; 104],
                    diagnostic_unmined: true,
                },
                39,
            ),
            (
                AspisInstruction::MeasureStateOnlyWidth28 {
                    statement_digest: digest,
                    public_input: [0u8; 104],
                    phase: StateOnlyWidth28DiagnosticPhase::PreparedBase,
                },
                40,
            ),
        ];
        for (variant, expected_tag) in variants {
            assert_eq!(borsh::to_vec(&variant).unwrap()[0], expected_tag);
        }
        assert_eq!(
            borsh::to_vec(&M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4).unwrap()[0],
            7
        );
        assert_eq!(
            borsh::to_vec(&M31CircleBasisDiagnosticMode::RlcStreamingFourDots).unwrap()[0],
            8
        );
        assert_eq!(
            borsh::to_vec(&M31CircleBasisDiagnosticMode::RlcPreparedLimbs49).unwrap()[0],
            9
        );
        assert_eq!(
            borsh::to_vec(&M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows).unwrap()[0],
            10
        );
        for (mode, expected) in [
            (TwoPointBatchingDiagnosticMode::OnePointBaseline, 0),
            (TwoPointBatchingDiagnosticMode::FreshKappaSingleLane, 1),
            (
                TwoPointBatchingDiagnosticMode::TwoIndependentRelationLanes,
                2,
            ),
            (TwoPointBatchingDiagnosticMode::DisjointGamma51SingleLane, 3),
        ] {
            assert_eq!(borsh::to_vec(&mode).unwrap()[0], expected);
        }
        for (phase, expected) in [
            (JohnsonM31CircleDiagnosticPhase::PreparedBase, 0),
            (JohnsonM31CircleDiagnosticPhase::Layer0Range, 1),
            (JohnsonM31CircleDiagnosticPhase::LaterAll, 2),
            (JohnsonM31CircleDiagnosticPhase::Full, 3),
        ] {
            assert_eq!(borsh::to_vec(&phase).unwrap()[0], expected);
        }
    }

    #[test]
    fn tag24_header_and_public_input_frame_is_exact() {
        use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
        use aspis_core::proof::{
            Header, FLAG_EVALUATION_CLAIM, FLAG_EXACT_WIDE_C1, FLAG_M31_CIRCLE_C1_DIAGNOSTIC,
            FLAG_SECOND_PHASE, HEADER_LEN, VERSION_V3, VERSION_V4_S2,
        };

        let required_flags =
            FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;
        let header = Header {
            version: VERSION_V4_S2,
            profile_id: PROFILE.id,
            log_rows: PROFILE.log_rows,
            log_blowup: PROFILE.log_blowup,
            query_count: PROFILE.query_count,
            grinding_bits: PROFILE.grinding_bits,
            fold_payload: aspis_core::FoldPayload::RawFibers as u8,
            merkle_mode: aspis_core::MerkleMode::Radix4MinimalSubtree as u8,
            num_rounds: PROFILE.num_rounds(),
            final_poly_log_len: aspis_core::params::FINAL_POLY_LOG_LEN,
            flags: required_flags,
        };
        let encode = |candidate: Header| {
            let mut bytes = [0u8; HEADER_LEN];
            candidate.write(&mut bytes);
            bytes
        };
        assert!(validate_m31_circle_v4_diagnostic_header(&encode(header)).is_ok());

        for invalid in [
            Header {
                version: VERSION_V3,
                ..header
            },
            Header {
                profile_id: PROFILE.id + 1,
                ..header
            },
            Header {
                query_count: PROFILE.query_count + 1,
                ..header
            },
            Header {
                fold_payload: aspis_core::FoldPayload::ProofCarriedRoundLocal as u8,
                ..header
            },
            Header {
                merkle_mode: aspis_core::MerkleMode::MinimalSubtree as u8,
                ..header
            },
            Header {
                num_rounds: PROFILE.num_rounds() - 1,
                ..header
            },
            Header {
                final_poly_log_len: aspis_core::params::FINAL_POLY_LOG_LEN + 1,
                ..header
            },
            Header {
                flags: required_flags | FLAG_EXACT_WIDE_C1,
                ..header
            },
        ] {
            assert!(matches!(
                validate_m31_circle_v4_diagnostic_header(&encode(invalid)),
                Err(ProgramError::Custom(code))
                    if code == aspis_core::VerifyError::BadHeader.code()
            ));
        }

        let canonical_z = vec![[0u8; 16]; 10];
        assert_eq!(
            validate_m31_circle_v4_diagnostic_public_inputs(&canonical_z),
            Ok(())
        );
        assert_eq!(
            validate_m31_circle_v4_diagnostic_public_inputs(&canonical_z[..9]),
            Err(ProgramError::InvalidInstructionData)
        );
        let mut noncanonical_z = canonical_z;
        noncanonical_z[0][..4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
        assert_eq!(
            validate_m31_circle_v4_diagnostic_public_inputs(&noncanonical_z),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    fn make_account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        is_signer: bool,
        is_writable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            is_signer,
            is_writable,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }

    #[test]
    fn init_requires_authority_signature() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            true,
            true,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            false,
            false,
        );
        let ix = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &ix),
            Err(ProgramError::MissingRequiredSignature)
        );

        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            true,
            false,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &ix),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn upload_rejects_wrong_authority() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let wrong_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut wrong_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let mut wrong_data = [];

        let init_ix = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &init_ix),
                Ok(())
            );
        }

        let upload_ix = borsh::to_vec(&AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![1, 2, 3, 4],
        })
        .unwrap();
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            true,
        );
        let wrong = make_account(
            &wrong_key,
            &program_id,
            &mut wrong_lamports,
            &mut wrong_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, wrong], &upload_ix),
            Err(ProgramError::InvalidAccountData)
        );

        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &upload_ix),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn finalize_proof_is_authority_bound_and_irreversible() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let wrong_authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut authority_lamports = 0;
        let mut wrong_authority_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 8];
        let mut authority_data = [];
        let mut wrong_authority_data = [];

        let init = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &init),
                Ok(())
            );
        }

        let initialize_pool = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 0,
            anchor: [0u8; 32],
        })
        .unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof], &initialize_pool),
                Err(ProgramError::InvalidAccountData),
                "an initialized proof must not be retyped as a pool"
            );
        }

        let finalize = borsh::to_vec(&AspisInstruction::FinalizeProof).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                true,
            );
            let wrong_authority = make_account(
                &wrong_authority_key,
                &program_id,
                &mut wrong_authority_lamports,
                &mut wrong_authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, wrong_authority], &finalize),
                Err(ProgramError::InvalidAccountData)
            );
        }
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &finalize),
                Err(ProgramError::InvalidAccountData)
            );
        }
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &finalize),
                Ok(())
            );
        }
        assert!(proof_account_finalized(&proof_data));

        let upload = borsh::to_vec(&AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![1],
        })
        .unwrap();
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            true,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[proof, authority], &upload),
            Err(ProgramError::InvalidAccountData)
        );

        let reinitialize = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                true,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &reinitialize),
                Err(ProgramError::InvalidAccountData)
            );
        }
        {
            let proof = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                true,
            );
            let authority = make_account(
                &authority_key,
                &program_id,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
            );
            assert_eq!(
                process_instruction(&program_id, &[proof, authority], &finalize),
                Err(ProgramError::InvalidAccountData)
            );
        }
    }

    #[test]
    fn initialize_atomic_pool_is_signed_canonical_and_one_shot() {
        let program_id = id();
        let pool_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut pool_lamports = 0;
        let mut authority_lamports = 0;
        let mut pool_data = [0u8; atomic_payment::ATOMIC_POOL_STATE_LEN];
        let mut authority_data = [];
        let anchor = [0u8; 32];
        let initialize = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 73,
            anchor,
        })
        .unwrap();

        {
            let unsigned_pool = make_account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[unsigned_pool], &initialize),
                Err(ProgramError::MissingRequiredSignature)
            );
        }
        {
            let pool = make_account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                true,
                true,
            );
            assert_eq!(
                process_instruction(&program_id, &[pool], &initialize),
                Ok(())
            );
        }
        assert_eq!(
            atomic_payment::AtomicPoolStateV1::decode(&pool_data).unwrap(),
            atomic_payment::AtomicPoolStateV1 {
                sequence: 73,
                anchor,
            }
        );

        let pool = make_account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            true,
            true,
        );
        assert_eq!(
            process_instruction(&program_id, &[pool], &initialize),
            Err(ProgramError::InvalidAccountData)
        );

        let pool_before = pool_data;
        let init_proof = borsh::to_vec(&AspisInstruction::InitProof { total_len: 8 }).unwrap();
        let pool = make_account(
            &pool_key,
            &program_id,
            &mut pool_lamports,
            &mut pool_data,
            true,
            true,
        );
        let authority = make_account(
            &authority_key,
            &program_id,
            &mut authority_lamports,
            &mut authority_data,
            true,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[pool, authority], &init_proof),
            Err(ProgramError::InvalidAccountData),
            "an initialized pool must not be retyped as a proof account"
        );
        assert_eq!(pool_data, pool_before);

        let overflow_pool_key = Pubkey::new_unique();
        let mut overflow_pool_lamports = 0;
        let mut overflow_pool_data = [0u8; atomic_payment::ATOMIC_POOL_STATE_LEN];
        let overflow_initialize = borsh::to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: u64::MAX,
            anchor,
        })
        .unwrap();
        let overflow_pool = make_account(
            &overflow_pool_key,
            &program_id,
            &mut overflow_pool_lamports,
            &mut overflow_pool_data,
            true,
            true,
        );
        assert_eq!(
            process_instruction(&program_id, &[overflow_pool], &overflow_initialize),
            Err(ProgramError::ArithmeticOverflow)
        );
        assert!(overflow_pool_data.iter().all(|byte| *byte == 0));
    }

    #[cfg(feature = "profile23-mutation-candidate")]
    #[test]
    fn production_profile23_read_and_mutation_paths_require_finalized_proofs() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 1];
        proof_data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&1u32.to_le_bytes());
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority_key.as_ref());

        let public_input = [0u8; 104];
        let statement = aspis_statement::AtomicPaymentStatementV3 {
            pool: [0u8; 32],
            sequence: 0,
            spend: aspis_statement::SpendPublic {
                anchor: [aspis_core::field::M31::ZERO; 8],
                nullifier: [aspis_core::field::M31::ZERO; 8],
                output_commitment: [aspis_core::field::M31::ZERO; 8],
                asset_id: aspis_core::field::M31::ZERO,
                fee: 0,
            },
            output_anchor: [aspis_core::field::M31::ZERO; 8],
        };

        for finalized in [false, true] {
            if finalized {
                proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
            }
            let expected = if finalized {
                Err(ProgramError::InvalidInstructionData)
            } else {
                Err(ProgramError::InvalidAccountData)
            };
            {
                let proof = make_account(
                    &proof_key,
                    &program_id,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                );
                assert_eq!(
                    verify_uploaded_atomic_profile23_acceptance_v3(
                        &proof,
                        [0u8; 32],
                        0,
                        &public_input,
                        [0u8; 32],
                        false,
                    ),
                    expected
                );
            }
            {
                let proof = make_account(
                    &proof_key,
                    &program_id,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                );
                assert_eq!(
                    verify_uploaded_atomic_profile23_production_statement_v3(&proof, &statement),
                    expected
                );
            }
        }
    }

    #[test]
    fn verify_rejects_short_account_without_panicking() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = [0u8; 2];
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        let ix = borsh::to_vec(&AspisInstruction::Verify {
            statement_digest: [0u8; 32],
        })
        .unwrap();
        assert_eq!(
            process_instruction(&program_id, &[proof], &ix),
            Err(ProgramError::InvalidAccountData)
        );
    }

    /// End-to-end instruction-path test for `VerifyWithClaim` (review Low):
    /// a real claim-carrying proof through the program dispatch, with the
    /// non-SBF hashv fallback standing in for the syscall (the transcript
    /// KAT covers host/SBF hash equivalence separately).
    #[test]
    fn verify_with_claim_instruction_paths() {
        use aspis_core::params::PROFILE_CAPACITY_LR10_Q32_G16 as PROFILE;
        use aspis_prover::{multilinear_eval, prove_with_claim, seeded_coeffs, ProveOptions};

        let coeffs = seeded_coeffs(PROFILE.log_rows, 5);
        let statement_digest = [0x42u8; 32];
        let z: Vec<aspis_core::field::QM31> = (0..PROFILE.log_rows)
            .map(|i| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(1000 + i),
                ))
            })
            .collect();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &z),
            z,
        };
        let proof = prove_with_claim(
            &PROFILE,
            &coeffs,
            &statement_digest,
            &claim,
            &ProveOptions {
                fold_payload: aspis_core::FoldPayload::RawFibers,
                merkle_mode: aspis_core::MerkleMode::MinimalSubtree,
            },
            aspis_prover::HOST_HASH,
        );

        // proof account: ASPU magic, len, authority, proof bytes
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
        proof_data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
        proof_data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&proof);

        let claim_z: Vec<[u8; 16]> = claim
            .z
            .iter()
            .map(|zi| {
                let mut b = [0u8; 16];
                zi.write_le_bytes(&mut b);
                b
            })
            .collect();
        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);

        // correct claim accepts through the instruction path
        {
            let account = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let ix = borsh::to_vec(&AspisInstruction::VerifyWithClaim {
                statement_digest,
                claim_z: claim_z.clone(),
                claim_v,
            })
            .unwrap();
            assert_eq!(process_instruction(&program_id, &[account], &ix), Ok(()));
        }

        // perturbed claim value rejects (transcript binding)
        {
            let account = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let mut wrong_v = claim_v;
            wrong_v[0] ^= 1;
            let ix = borsh::to_vec(&AspisInstruction::VerifyWithClaim {
                statement_digest,
                claim_z: claim_z.clone(),
                claim_v: wrong_v,
            })
            .unwrap();
            assert!(matches!(
                process_instruction(&program_id, &[account], &ix),
                Err(ProgramError::Custom(_))
            ));
        }

        // claim-carrying proof through the plain Verify path rejects with
        // ClaimMissing (code 14)
        {
            let account = make_account(
                &proof_key,
                &program_id,
                &mut proof_lamports,
                &mut proof_data,
                false,
                false,
            );
            let ix = borsh::to_vec(&AspisInstruction::Verify { statement_digest }).unwrap();
            assert_eq!(
                process_instruction(&program_id, &[account], &ix),
                Err(ProgramError::Custom(
                    aspis_core::VerifyError::ClaimMissing.code()
                ))
            );
        }
    }

    #[test]
    fn production_tag6_rejects_exact_wide_flag_and_tag22_is_diagnostic_only() {
        use aspis_core::params::PROFILE_CAPACITY_LR10_Q32_G16 as PROFILE;
        use aspis_prover::{
            multilinear_eval, prove_exact_wide_v4_scaffold_for_measurement, seeded_coeffs,
            ProveOptions,
        };

        let coeffs = seeded_coeffs(PROFILE.log_rows, 22);
        let statement_digest = [0x22u8; 32];
        let z = (0..PROFILE.log_rows)
            .map(|index| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(2_200 + index),
                ))
            })
            .collect::<Vec<_>>();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &z),
            z,
        };
        let proof = prove_exact_wide_v4_scaffold_for_measurement(
            &PROFILE,
            &coeffs,
            &statement_digest,
            &claim,
            &ProveOptions {
                fold_payload: aspis_core::FoldPayload::RawFibers,
                merkle_mode: aspis_core::MerkleMode::Radix4MinimalSubtree,
            },
            aspis_prover::HOST_HASH,
        );
        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);
        let claim_z = claim
            .z
            .iter()
            .map(|coordinate| {
                let mut bytes = [0u8; 16];
                coordinate.write_le_bytes(&mut bytes);
                bytes
            })
            .collect::<Vec<_>>();

        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
        proof_data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
        proof_data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&proof);

        let production = borsh::to_vec(&AspisInstruction::VerifyWithClaim {
            statement_digest,
            claim_z: claim_z.clone(),
            claim_v,
        })
        .unwrap();
        let account = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[account], &production),
            Err(ProgramError::Custom(
                aspis_core::VerifyError::BadHeader.code()
            ))
        );

        let diagnostic = borsh::to_vec(&AspisInstruction::VerifyExactWideV4Scaffold {
            statement_digest,
            claim_z,
            claim_v,
        })
        .unwrap();
        let account = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[account], &diagnostic),
            Ok(())
        );
    }

    #[test]
    fn production_tag6_rejects_m31_circle_flag_with_weakened_acceptance_teeth() {
        use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
        use aspis_core::proof::{
            Header, FLAG_EVALUATION_CLAIM, FLAG_M31_CIRCLE_C1_DIAGNOSTIC, FLAG_SECOND_PHASE,
            VERSION_V4_S2,
        };
        use aspis_prover::{
            multilinear_eval, prove_with_claim_v4_m31_circle_flag_legacy_basis_for_tests,
            seeded_coeffs, ProveOptions, HOST_HASH,
        };

        let coeffs = seeded_coeffs(PROFILE.log_rows, 24);
        let statement_digest = [0x24u8; 32];
        let z = (0..PROFILE.log_rows)
            .map(|index| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(2_400 + index),
                ))
            })
            .collect::<Vec<_>>();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &z),
            z,
        };
        let proof = prove_with_claim_v4_m31_circle_flag_legacy_basis_for_tests(
            &PROFILE,
            &coeffs,
            &statement_digest,
            &claim,
            &ProveOptions {
                fold_payload: aspis_core::FoldPayload::RawFibers,
                merkle_mode: aspis_core::MerkleMode::Radix4MinimalSubtree,
            },
            HOST_HASH,
        );
        let header = Header::parse(&proof).expect("recognized diagnostic header");
        assert_eq!(header.version, VERSION_V4_S2);
        assert_eq!(
            header.flags,
            FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC
        );
        assert!(validate_m31_circle_v4_diagnostic_header(&proof).is_ok());

        // The same flagged bytes are accepted only when the basis guard is
        // deliberately weakened to reinterpret them as the legacy CM31 PCS.
        assert_eq!(
            aspis_core::verify_with_insecure_m31_circle_as_legacy_for_tests(
                &proof,
                &statement_digest,
                Some(&claim),
                HOST_HASH,
            ),
            Ok(())
        );

        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);
        let claim_z = claim
            .z
            .iter()
            .map(|coordinate| {
                let mut bytes = [0u8; 16];
                coordinate.write_le_bytes(&mut bytes);
                bytes
            })
            .collect::<Vec<_>>();
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
        proof_data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
        proof_data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&proof);

        // Production tag 6 rejects at the header/basis allow-list boundary.
        let production = borsh::to_vec(&AspisInstruction::VerifyWithClaim {
            statement_digest,
            claim_z: claim_z.clone(),
            claim_v,
        })
        .unwrap();
        let account = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[account], &production),
            Err(ProgramError::Custom(
                aspis_core::VerifyError::BadHeader.code()
            ))
        );

        // Tag 24 owns this exact frame, but remains deliberately rejecting
        // until the genuine circle PCS parser/verifier is implemented.
        let diagnostic = borsh::to_vec(&AspisInstruction::VerifyM31CircleV4Diagnostic {
            statement_digest,
            claim_z,
            statement_evaluations_digest: [0x42u8; 32],
        })
        .unwrap();
        let account = make_account(
            &proof_key,
            &program_id,
            &mut proof_lamports,
            &mut proof_data,
            false,
            false,
        );
        assert_eq!(
            process_instruction(&program_id, &[account], &diagnostic),
            Err(ProgramError::InvalidInstructionData)
        );
    }
}
