import V5AcceptedRelationSourceClosure
import V5AcceptedTranscriptWorkClosure
import V5AcceptedEntryMerkleConsumerClosure
import V5AcceptedProductionFriClosure
import V5AcceptedExecutionFinalClosure
import V5FriCallerAcceptedResolverBridge
import V5AcceptedClaimTableExact
import V5AcceptedDeterministicRelationTail
import V5AtomicTerminalPrefixWrapperComplete.FunsExternal

/-!
# One accepted production run to the released security event

This is the final assembly file for the selected released proof-checker path.
All deterministic witnesses are obtained from one successful translated call.
The theorem leaves only the named mathematical and cryptographic events in its
conclusion; executable Rust/model equalities are not caller-supplied premises.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace AspisV5AcceptedOneRunSecurityClosure

open Aeneas Aeneas.Std Result
open AspisCircleGroupOrder
open AspisFormal.HashMerkleModel
open AspisV5AcceptedEntryMerkleConsumerClosure
open AspisV5AcceptedEntryMerkleConsumerAdapter
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedExecutionFinalClosure
open AspisV5AcceptedExecutionReleasedSecurity
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedExecutionDerivedQueries
open AspisV5AcceptedClaimTableExact
open AspisV5AcceptedDeterministicRelationTail
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedProductionFriClosure
open AspisV5AcceptedRelationSourceClosure
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5AcceptedTranscriptWorkClosure
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAcceptedForestChecks
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConsumerObservationBridge
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleTranscriptProjection
open AspisV5ProductionFiatShamirBridge
open AspisV5RelationStressSourceBridge
open AspisV5SourceCandidateFamily
open AspisV5Tag67CandidateTraceExtraction
open AspisV5TranscriptConnection

abbrev K := AspisV5FriAcceptedForestChecks.K
abbrev Digest32 := AspisV5MerkleRustBridge.Digest32

/-- A fixed accepted body determines one causal family: its first two roots
are fixed before the FRI challenges; each later root and the final polynomial
is the value already present in that same body. -/
def acceptedBodyCausalRoots
    (roots : V5PrivateRoots Digest32) (publishedFinal : Fin 4 → K) :
    CausalMerkleRoots K Digest32 where
  c1 := roots.c1
  c2 := roots.c2
  line1 := fun _ => roots.line1
  line2 := fun _ _ => roots.line2
  line3 := fun _ _ _ => roots.line3
  final := fun _ _ _ _ => publishedFinal

noncomputable def acceptedBodyCausalFamily
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest32)
    (roots : V5PrivateRoots Digest32) (publishedFinal : Fin 4 → K) :
    CausalTranscriptFamily K :=
  committedCausalFamily decoder hashing
    (acceptedBodyCausalRoots roots publishedFinal)

@[simp] theorem acceptedBodyCausalRoots_at
    (roots : V5PrivateRoots Digest32) (publishedFinal : Fin 4 → K)
    (z0 z1 z2 : K) :
    (acceptedBodyCausalRoots roots publishedFinal).at z0 z1 z2 = roots := by
  rfl

@[simp] theorem acceptedBodyCausalRoots_final
    (roots : V5PrivateRoots Digest32) (publishedFinal : Fin 4 → K)
    (z0 z1 z2 z3 : K) :
    (acceptedBodyCausalRoots roots publishedFinal).final z0 z1 z2 z3 =
      publishedFinal := by
  rfl

noncomputable def acceptedRunDecoder
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    ProductionOpeningDecoder K :=
  productionOpeningFibreDecoder snapshot.acceptedFriCall.prepared

def acceptedRunCall
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (blocks : List (FixedBytes 32))
    (hdecode : derive18Queries blocks =
      some (snapshot.queries.val.map UScalar.val))
    (roots : V5PrivateRoots Digest32) : V5ProductionCall where
  roots := roots
  queries := decodedQuerySet blocks
    (snapshot.queries.val.map UScalar.val) hdecode
  proofBytes := parsed.v5_private_proof.val.map
    AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte

noncomputable def acceptedRunCausalFamily
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (roots : V5PrivateRoots Digest32) : CausalTranscriptFamily K :=
  acceptedBodyCausalFamily (acceptedRunDecoder snapshot)
    (sha256MerkleHashing sha256) roots (snapshotPublishedFinal snapshot)

noncomputable def acceptedRunExpectedC2
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (roots : V5PrivateRoots Digest32) : V5Query → Fin 4 → K :=
  committedC2 (acceptedRunDecoder snapshot) (sha256MerkleHashing sha256) roots

@[simp] theorem acceptedRunCall_roots
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (blocks : List (FixedBytes 32))
    (hdecode : derive18Queries blocks =
      some (snapshot.queries.val.map UScalar.val))
    (roots : V5PrivateRoots Digest32) :
    (acceptedRunCall snapshot blocks hdecode roots).roots = roots := by
  rfl

@[simp] theorem acceptedRunCall_queries
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (blocks : List (FixedBytes 32))
    (hdecode : derive18Queries blocks =
      some (snapshot.queries.val.map UScalar.val))
    (roots : V5PrivateRoots Digest32) :
    (acceptedRunCall snapshot blocks hdecode roots).queries =
      decodedQuerySet blocks (snapshot.queries.val.map UScalar.val) hdecode := by
  rfl

@[simp] theorem acceptedRunCall_proofBytes
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (blocks : List (FixedBytes 32))
    (hdecode : derive18Queries blocks =
      some (snapshot.queries.val.map UScalar.val))
    (roots : V5PrivateRoots Digest32) :
    (acceptedRunCall snapshot blocks hdecode roots).proofBytes =
      parsed.v5_private_proof.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte := by
  rfl

/-- Evaluating the causal family fixed by one accepted body at any four
challenge values returns the transcript committed by that body's five roots
and public final polynomial. -/
@[simp] theorem acceptedRunCausalFamily_transcript
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (roots : V5PrivateRoots Digest32) (input : SourceRelationInput K) :
    acceptedTranscript (acceptedRunCausalFamily sha256 snapshot roots) input =
      committedTranscript (acceptedRunDecoder snapshot)
        (sha256MerkleHashing sha256) roots
        (snapshotPublishedFinal snapshot) := by
  rfl

/-- Outside a collision, every accepted forest from this production run
projects to the exact causal transcript used by the security reduction. -/
theorem accepted_run_forest_projects_to_transcript
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (roots : V5PrivateRoots Digest32) (input : SourceRelationInput K)
    {querySet : Finset V5Query}
    (forest : AcceptedV5Forest (sha256MerkleHashing sha256) roots querySet)
    (hfree : CollisionFree (sha256MerkleHashing sha256)) :
    ForestProjectsToTranscript (acceptedRunDecoder snapshot)
      (sha256MerkleHashing sha256) forest
      (acceptedTranscript (acceptedRunCausalFamily sha256 snapshot roots) input)
      (acceptedRunExpectedC2 sha256 snapshot roots) := by
  simpa [acceptedRunCausalFamily_transcript, acceptedRunExpectedC2] using
    forest_projects_to_committedTranscript (acceptedRunDecoder snapshot)
      (sha256MerkleHashing sha256) hfree forest
      (snapshotPublishedFinal snapshot)

/-- Deterministic composition after the relation adapter has supplied the
exact caller data.  Merkle parsing, the FRI consumer, transcript projection,
work checks, and reference-forest projection are all constructed here from
the same accepted snapshot.  The two relation premises are discharged by the
snapshot-only source adapter in the final wrapper theorem below. -/
theorem accepted_snapshot_leaves_only_security_events_of_relation
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData K)
    (alphaValue : ∀ layer : Fin 4,
      entryToK snapshot.alphas.val[layer.val]! = data.alphas layer)
    {terminalClaim : K}
    (hcaller : runSourceMode9RelationCaller data
      (snapshotPublishedFinal snapshot) = some terminalClaim) :
    ∃ (blocks : List (FixedBytes 32))
        (hdecode : derive18Queries blocks =
          some (snapshot.queries.val.map UScalar.val))
        (modelRoots : V5PrivateRoots Digest32),
      let causalFamily := acceptedRunCausalFamily sha256 snapshot modelRoots
      let input := sourceMode9RelationInput data
      let queries := decodedQuerySchedule blocks
        (snapshot.queries.val.map UScalar.val) hdecode
      ∀ (records : CandidateRecords
            (AcceptedCandidate base causalFamily input) K)
          (statement : V5PublicStatement),
        (¬ StatementHasSpendWitness statement deployedOwner deployedNote
          deployedNullifier deployedNode) →
        ReleasedAcceptedExecutionSecurityEvent
          False False False False False False
          (HashCollision (sha256MerkleHashing sha256)) False False
          (QueryPhaseFailure (acceptedSchedule base input)
            (acceptedTranscript causalFamily input) queries)
          (∃ (hfinal : FinalXMatchesReleasedDomain base)
              (htables : InverseTablesMatch base releasedEvaluationPoints)
              (hdecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
            (adaptiveBadSets base causalFamily hfinal htables hdecoding
              (constructedAdaptiveStrategies base causalFamily)).Occurs
              input.round0.alpha input.round1.alpha input.round2.alpha
                input.round3.alpha)
          (∃ candidate : AcceptedCandidate base causalFamily input,
            CandidateEarlierFailure rc
              ((releasedSourceCandidateFamily base causalFamily data).execution
                candidate)
              input.challenges statement (records candidate))
          (Fintype.card (AcceptedCandidate base causalFamily input) ≤ 240 ∧
            input.challenges ∈ boundedCandidateRepairEvent
              (fun candidate =>
                ((releasedSourceCandidateFamily base causalFamily data).execution
                  candidate).adaptiveData))
          (¬ Poseidon2Faithful rc deployedOwner deployedNote deployedNullifier
            deployedNode) := by
  obtain ⟨blocks, hdecode, _rootsArray, modelRoots, _merkleRun, _rootsEq,
      _rootsMatch, _proofBytes, hresolver, hconsumer⟩ :=
    accepted_snapshot_builds_exact_merkle_consumer snapshot sha256 hhash
  refine ⟨blocks, hdecode, modelRoots, ?_⟩
  dsimp only
  intro records statement noWitness
  let rustCall := acceptedRunCall snapshot blocks hdecode modelRoots
  let resolver := singleAcceptedEntryResolver rustCall snapshot.acceptedFriCall
  let rustObservation := observationFromAcceptedResolver resolver
  have hobservation : rustObservation rustCall =
      some snapshot.acceptedFriCall.observation := by
    simpa [rustObservation, resolver, observationFromAcceptedResolver] using
      congrArg (Option.map AcceptedFriCall.observation) hresolver
  have transcriptWork := accepted_snapshot_builds_transcript_work_evidence
    snapshot data blocks hdecode
  let causalFamily := acceptedRunCausalFamily sha256 snapshot modelRoots
  let input := sourceMode9RelationInput data
  let schedule := acceptedSchedule base input
  let transcript := acceptedTranscript causalFamily input
  let queries := decodedQuerySchedule blocks
    (snapshot.queries.val.map UScalar.val) hdecode
  have scheduleAlpha : ∀ layer : Fin 4,
      entryToK snapshot.alphas.val[layer.val]! = schedule.alpha layer := by
    intro layer
    have halpha := alphaValue layer
    fin_cases layer <;>
      simpa [schedule, input, acceptedSchedule, scheduleAt,
        sourceMode9RelationInput, sourceCallerRound] using halpha
  have transcriptFinal : ∀ slot : Fin 4,
      entryToK snapshot.finalPolynomial.val[slot.val]! =
        transcript.publishedFinal slot := by
    intro slot
    change entryToK snapshot.finalPolynomial.val[slot.val]! =
      snapshotPublishedFinal snapshot slot
    rfl
  have binding := accepted_snapshot_builds_fri_model_input_binding snapshot
    schedule transcript scheduleAlpha transcriptFinal
  have releasedSchedule : ProductionUsesReleasedFriTables schedule := by
    refine {
      finalX := ?_
      circleInv2x := ?_
      circleInv2y := ?_
      line1Inverse := ?_
      line2Inverse := ?_
      line3Inverse := ?_ }
    · intro i
      simpa [schedule, acceptedSchedule, scheduleAt] using hproduction.finalX i
    · intro i
      simpa [schedule, acceptedSchedule, scheduleAt] using
        hproduction.circleInv2x i
    · intro i
      simpa [schedule, acceptedSchedule, scheduleAt] using
        hproduction.circleInv2y i
    · intro i slot
      simpa [schedule, acceptedSchedule, scheduleAt] using
        hproduction.line1Inverse i slot
    · intro i slot
      simpa [schedule, acceptedSchedule, scheduleAt] using
        hproduction.line2Inverse i slot
    · intro i slot
      simpa [schedule, acceptedSchedule, scheduleAt] using
        hproduction.line3Inverse i slot
  obtain ⟨reference, _referenceBytes, referenceChecks⟩ :=
    accepted_call_yields_authenticated_released_fri_checks_same_inputs
      sha256 rustObservation rustCall snapshot.acceptedFriCall hconsumer
      hobservation schedule releasedSchedule transcript queries input
      (snapshotTranscriptInput snapshot) (acceptedDerivedValues snapshot data)
      (acceptedDriverResult snapshot data) transcriptWork.transcriptProjection
      binding
  by_cases collision : HashCollision (sha256MerkleHashing sha256)
  · exact .merkleHashCollision collision
  · have referenceProjection := accepted_run_forest_projects_to_transcript
      sha256 snapshot modelRoots input reference.forest collision
    have callerAtTranscript : runSourceMode9RelationCaller data
        transcript.publishedFinal = some terminalClaim := by
      have publishedExact : transcript.publishedFinal =
          snapshotPublishedFinal snapshot := by
        rfl
      rw [publishedExact]
      exact hcaller
    exact accepted_false_constructed_execution_leaves_only_security_events
      rc sha256 rustObservation rustCall snapshot.acceptedFriCall.observation
      hconsumer hobservation base hproduction hpublished causalFamily data
      records statement (acceptedRunDecoder snapshot)
      (acceptedRunExpectedC2 sha256 snapshot modelRoots)
      (snapshotTranscriptInput snapshot) (acceptedDerivedValues snapshot data)
      (acceptedDriverResult snapshot data) blocks hdecode
      (acceptedWorkFunctions snapshot data) (acceptedWorkInputs snapshot data)
      callerAtTranscript transcriptWork.transcriptProjection
      transcriptWork.workProjection transcriptWork.workAccepted reference.forest
      referenceProjection referenceChecks noWitness

/-- The security conclusion for one fixed source-level caller data set.  This
name lets the final snapshot-only theorem choose the main-weight schedule
inside its proof instead of asking the caller to provide verifier data. -/
def AcceptedSnapshotSecurityConclusion
    (rc : RoundConstants)
    (deployedOwner : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest)
    (deployedNote : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest)
    (deployedNullifier : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest)
    (deployedNode : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest)
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (base : FixedSchedule (ZMod P) K)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData K) : Prop :=
  ∃ (blocks : List (FixedBytes 32))
      (hdecode : derive18Queries blocks =
        some (snapshot.queries.val.map UScalar.val))
      (modelRoots : V5PrivateRoots Digest32),
    let causalFamily := acceptedRunCausalFamily sha256 snapshot modelRoots
    let input := sourceMode9RelationInput data
    let queries := decodedQuerySchedule blocks
      (snapshot.queries.val.map UScalar.val) hdecode
    ∀ (records : CandidateRecords
          (AcceptedCandidate base causalFamily input) K)
        (statement : V5PublicStatement),
      (¬ StatementHasSpendWitness statement deployedOwner deployedNote
        deployedNullifier deployedNode) →
      ReleasedAcceptedExecutionSecurityEvent
        False False False False False False
        (HashCollision (sha256MerkleHashing sha256)) False False
        (QueryPhaseFailure (acceptedSchedule base input)
          (acceptedTranscript causalFamily input) queries)
        (∃ (hfinal : FinalXMatchesReleasedDomain base)
            (htables : InverseTablesMatch base releasedEvaluationPoints)
            (hdecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
          (adaptiveBadSets base causalFamily hfinal htables hdecoding
            (constructedAdaptiveStrategies base causalFamily)).Occurs
            input.round0.alpha input.round1.alpha input.round2.alpha
              input.round3.alpha)
        (∃ candidate : AcceptedCandidate base causalFamily input,
          CandidateEarlierFailure rc
            ((releasedSourceCandidateFamily base causalFamily data).execution
              candidate)
            input.challenges statement (records candidate))
        (Fintype.card (AcceptedCandidate base causalFamily input) ≤ 240 ∧
          input.challenges ∈ boundedCandidateRepairEvent
            (fun candidate =>
              ((releasedSourceCandidateFamily base causalFamily data).execution
                candidate).adaptiveData))
        (¬ Poseidon2Faithful rc deployedOwner deployedNote deployedNullifier
          deployedNode)

/-- Repackage the already-proved relation-level theorem under the named
security conclusion. -/
theorem accepted_snapshot_security_conclusion_of_relation
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData K)
    (alphaValue : ∀ layer : Fin 4,
      entryToK snapshot.alphas.val[layer.val]! = data.alphas layer)
    {terminalClaim : K}
    (hcaller : runSourceMode9RelationCaller data
      (snapshotPublishedFinal snapshot) = some terminalClaim) :
    AcceptedSnapshotSecurityConclusion rc deployedOwner deployedNote
      deployedNullifier deployedNode sha256 base snapshot data := by
  exact accepted_snapshot_leaves_only_security_events_of_relation rc sha256
    hhash base hproduction hpublished snapshot data alphaValue hcaller

/-! ## Final deterministic caller join

The only unfinished deterministic join is to construct the released main
weight schedule and prove that the production terminal main and compact dots
are the two dots in `sourceMode9RelationInput`.  The point-claim table and the
initial relation value are no longer part of that gap:
`accepted_snapshot_initial_relation_exact` derives them from the exact bytes
and calls in this same snapshot.

`AcceptedSnapshotExactDeterministicCaller` is a named theorem target, not an
assumption.  The eventual public one-run theorem must prove it internally
from the accepted call; it must not receive it as a premise. -/

/-- Exact statement that remains to be proved once the terminal main-weight
and compact-dot source equalities are available. -/
def AcceptedSnapshotExactDeterministicCaller
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) : Prop :=
  ∃ mainWeights : SourceMainWeightSchedule K,
    let data := acceptedSnapshotPartialCallerData snapshot
      (acceptedPointClaimTable parsed.relation_claims) mainWeights
    sourceMode9RelationInput data =
        acceptedSourceRelationInput (acceptedSnapshotRounds snapshot) ∧
      runSourceMode9RelationCaller data (snapshotPublishedFinal snapshot) =
        some (AspisV5AcceptedRelationRoundProjection.toField
          snapshot.relationTrace.claim4)

/-- Once the exact source input equality is established, the maintained
caller result follows from the already-proved accepted four-round execution
and the exact final-coefficient identity.  This theorem is the compiled
adapter that the remaining main/compact-dot proof will use. -/
theorem accepted_snapshot_exact_caller_of_relation_input_exact
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (mainWeights : SourceMainWeightSchedule K)
    (inputExact :
      sourceMode9RelationInput
          (acceptedSnapshotPartialCallerData snapshot
            (acceptedPointClaimTable parsed.relation_claims) mainWeights) =
        acceptedSourceRelationInput (acceptedSnapshotRounds snapshot)) :
    runSourceMode9RelationCaller
        (acceptedSnapshotPartialCallerData snapshot
          (acceptedPointClaimTable parsed.relation_claims) mainWeights)
        (snapshotPublishedFinal snapshot) =
      some (AspisV5AcceptedRelationRoundProjection.toField
        snapshot.relationTrace.claim4) := by
  unfold runSourceMode9RelationCaller
  rw [inputExact, acceptedSnapshotRounds_run]
  rw [snapshotPublishedFinal_eq_relationTrace]
  simp

/-- A proved exact deterministic caller is enough to run the complete
snapshot security theorem.  The source caller data and alpha equality are
constructed here and are not public premises. -/
theorem accepted_snapshot_security_conclusion_of_exact_caller
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (exact : AcceptedSnapshotExactDeterministicCaller snapshot) :
    ∃ mainWeights : SourceMainWeightSchedule K,
      AcceptedSnapshotSecurityConclusion rc deployedOwner deployedNote
        deployedNullifier deployedNode sha256 base snapshot
        (acceptedSnapshotPartialCallerData snapshot
          (acceptedPointClaimTable parsed.relation_claims) mainWeights) := by
  unfold AcceptedSnapshotExactDeterministicCaller at exact
  obtain ⟨mainWeights, _inputExact, callerExact⟩ := exact
  let data := acceptedSnapshotPartialCallerData snapshot
    (acceptedPointClaimTable parsed.relation_claims) mainWeights
  have alphaValue : ∀ layer : Fin 4,
      entryToK snapshot.alphas.val[layer.val]! = data.alphas layer := by
    intro layer
    exact (congrFun
      (acceptedSnapshotPartialCallerData_alphas snapshot
        (acceptedPointClaimTable parsed.relation_claims) mainWeights)
      layer).symm
  refine ⟨mainWeights, ?_⟩
  exact accepted_snapshot_security_conclusion_of_relation rc sha256 hhash
    base hproduction hpublished snapshot data alphaValue callerExact

#print axioms accepted_snapshot_exact_caller_of_relation_input_exact
#print axioms accepted_snapshot_security_conclusion_of_exact_caller

end AspisV5AcceptedOneRunSecurityClosure
