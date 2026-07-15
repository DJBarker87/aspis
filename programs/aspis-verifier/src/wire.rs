//! The frozen Aspis instruction wire.
//!
//! The Borsh enum discriminant is the variant index; on-chain accounts and
//! recorded release evidence pin these tags, so the variant order must never
//! change. Superseded diagnostic and profile tags keep their wire shapes and
//! fail closed in the production dispatcher; their handlers were removed
//! with the research tree (git tags `research-archive-2026-07-14` and
//! `research-archive-2026-07-15`).

use borsh::{BorshDeserialize, BorshSerialize};

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

/// Neutral, measurement-only two-point relation shapes; the ordinals are
/// pinned inside append-only instruction tag 25.
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

/// Frozen wire format: the Borsh enum discriminant is the variant index and
/// on-chain accounts and recorded release evidence pin these tags, so the
/// variant order must never change. The deployed entrypoint accepts only tags
/// 0, 1, 59, 60, 62, 63, 64, and 65; superseded profile tags fail closed.
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
    /// Legacy batch-denominator verifier using the cluster-portable software
    /// inverse backend. Measurement-only comparison path.
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
    /// Append-only tag 59. Complete read-only Spend H26/G27/D28
    /// verifier. The diagnostic selector bypasses only PoW in an explicitly
    /// nondefault build; default binaries reject before proof interpretation.
    VerifyAtomicStateOnlySpendV4 {
        pool: [u8; 32],
        sequence: u64,
        public_input: [u8; 104],
        output_anchor: [u8; 32],
        deployment_domain: [u8; 32],
        diagnostic_unmined: bool,
    },
    /// Append-only tag 60. Production-PoW Spend mutation wrapper. This
    /// remains feature-gated and has no unmined selector on its wire.
    ApplyAtomicStateOnlySpendV4 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
        deployment_domain: [u8; 32],
    },
    /// Append-only tag 61. Local-validator-only mutation measurement that
    /// reuses tag 59's parser and bypasses transcript PoW only.
    MeasureAtomicStateOnlySpendMutationV3 {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
    },
    /// Append-only tag 62. Irreversibly seals an uploaded proof account by
    /// replacing its upload-authority field with the all-zero sentinel.
    /// Production Spend tags 59/60 accept only sealed accounts.
    FinalizeProof,
    /// Append-only tag 63. Initializes a newly created, program-owned pool
    /// account. The pool key must sign, the exact 80-byte account must still
    /// be all zero, and the initial anchor must be canonically encoded. The
    /// program derives and stores the pool's deployment domain as
    /// `sha256("aspis-spend-deployment-domain-v1" || runtime_program_id ||
    /// domain_tag)`.
    InitializeAtomicPool {
        sequence: u64,
        anchor: [u8; 32],
        domain_tag: Vec<u8>,
    },
    /// Append-only tag 64. Close a sealed proof account and refund every
    /// lamport to a writable System account. Both accounts must sign, so only
    /// the holder of the proof-account key can reclaim its rent.
    CloseFinalizedProof,
    /// Append-only tag 65. Production-PoW Spend mutation wrapper with an
    /// atomic proof-rent refund. This preserves tag 60's original read-only,
    /// proof-retaining ABI while allowing a proof holder to opt into closure
    /// by supplying the proof and refund accounts as writable signers.
    ApplyAtomicStateOnlySpendV4WithProofRefund {
        current_anchor: [u8; 32],
        nullifier: [u8; 32],
        output_commitment: [u8; 32],
        output_anchor: [u8; 32],
        asset_id: u32,
        fee: u32,
        deployment_domain: [u8; 32],
    },
}

#[cfg(test)]
mod tests {
    use super::*;

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

    /// The tags above 40 are pinned by construction as well; together with
    /// `instruction_wire_discriminants_are_append_only` this covers the full
    /// frozen table, including the production lifecycle tags 0, 1, 59, 60,
    /// 62, 63, 64, and 65.
    #[test]
    fn instruction_wire_discriminants_cover_the_full_frozen_table() {
        let (current_anchor, nullifier, output_commitment, output_anchor, asset_id, fee) =
            ([1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32], 17u32, 1u32);
        let variants: Vec<(AspisInstruction, u8)> = vec![
            (
                AspisInstruction::HvzkWhirMaskProbe {
                    mask_log_inv_rate: 1,
                    mask_queries: 1,
                    scope: 0,
                    mode: 0,
                    phase: 0,
                    start: 0,
                    end: 0,
                },
                41,
            ),
            (
                AspisInstruction::AtomicRoutingPartitionProbe {
                    optimized: false,
                    seed: 0,
                    expected_sink: [0u8; 16],
                },
                42,
            ),
            (
                AspisInstruction::AtomicStateOnlyProfile20CostCandidate {
                    statement_digest: [0u8; 32],
                    public_input: [0u8; 104],
                    output_anchor: [0u8; 32],
                    expected_atomic_terminal: [0u8; 16],
                },
                43,
            ),
            (
                AspisInstruction::StateOnlyRelationStructuralProbe {
                    statement_digest: [0u8; 32],
                    deferred_binary_copy: false,
                    corrupt_claim: false,
                },
                44,
            ),
            (
                AspisInstruction::StateOnlyMaskedSwitchProfile21Probe {
                    statement_digest: [0u8; 32],
                    diagnostic_unmined: true,
                    direct_u_query_evaluation: false,
                },
                45,
            ),
            (
                AspisInstruction::VerifyAtomicStateOnlyProfile20V3 {
                    pool: [0u8; 32],
                    sequence: 0,
                    public_input: [0u8; 104],
                    output_anchor: [0u8; 32],
                    diagnostic_unmined: true,
                },
                46,
            ),
            (
                AspisInstruction::ApplyAtomicStateOnlyProfile20V3 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                },
                47,
            ),
            (
                AspisInstruction::MeasureAtomicStateOnlyProfile20MutationV3 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                },
                48,
            ),
            (
                AspisInstruction::StateOnlyPrivateMerkleSaltProbe {
                    mode: 0,
                    expected_sink: [0u8; 32],
                },
                49,
            ),
            (
                AspisInstruction::VerifyAtomicStateOnlyProfile21V3 {
                    pool: [0u8; 32],
                    sequence: 0,
                    public_input: [0u8; 104],
                    output_anchor: [0u8; 32],
                    diagnostic_unmined: true,
                },
                50,
            ),
            (
                AspisInstruction::ApplyAtomicStateOnlyProfile21V3 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                },
                51,
            ),
            (
                AspisInstruction::MeasureAtomicStateOnlyProfile21MutationV3 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                },
                52,
            ),
            (
                AspisInstruction::StateOnlyHelperDot2Probe {
                    fused_helpers: false,
                    corrupt: 0,
                    expected_sink: [0u8; 32],
                },
                53,
            ),
            (
                AspisInstruction::StateOnlyHelperDot3Probe {
                    fused_helpers: false,
                    corrupt: 0,
                    expected_sink: [0u8; 32],
                },
                54,
            ),
            (
                AspisInstruction::StateOnlyFoldPolynomialProbe {
                    polynomial_basis: false,
                    corrupt: 0,
                    expected_sink: [0u8; 32],
                },
                55,
            ),
            (
                AspisInstruction::VerifyAtomicStateOnlyProfile22V3 {
                    pool: [0u8; 32],
                    sequence: 0,
                    public_input: [0u8; 104],
                    output_anchor: [0u8; 32],
                    diagnostic_unmined: true,
                },
                56,
            ),
            (
                AspisInstruction::ApplyAtomicStateOnlyProfile22V3 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                },
                57,
            ),
            (
                AspisInstruction::MeasureAtomicStateOnlyProfile22MutationV3 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                },
                58,
            ),
            (
                AspisInstruction::VerifyAtomicStateOnlySpendV4 {
                    pool: [0u8; 32],
                    sequence: 0,
                    public_input: [0u8; 104],
                    output_anchor: [0u8; 32],
                    deployment_domain: [0u8; 32],
                    diagnostic_unmined: false,
                },
                59,
            ),
            (
                AspisInstruction::ApplyAtomicStateOnlySpendV4 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                    deployment_domain: [0u8; 32],
                },
                60,
            ),
            (
                AspisInstruction::MeasureAtomicStateOnlySpendMutationV3 {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                },
                61,
            ),
            (AspisInstruction::FinalizeProof, 62),
            (
                AspisInstruction::InitializeAtomicPool {
                    sequence: 0,
                    anchor: [0u8; 32],
                    domain_tag: b"mainnet-beta".to_vec(),
                },
                63,
            ),
            (AspisInstruction::CloseFinalizedProof, 64),
            (
                AspisInstruction::ApplyAtomicStateOnlySpendV4WithProofRefund {
                    current_anchor,
                    nullifier,
                    output_commitment,
                    output_anchor,
                    asset_id,
                    fee,
                    deployment_domain: [0u8; 32],
                },
                65,
            ),
        ];
        for (variant, expected_tag) in variants {
            assert_eq!(borsh::to_vec(&variant).unwrap()[0], expected_tag);
        }
    }
}
