import V5AcceptedRelationPreparedAdapter
import V5AcceptedFriModelInputBinding
import V5RelationLinkedFieldProjection
import AspisFormal.V5ProductionFiatShamirBridge
import AspisFormal.V5SourceCandidateFamily
import AspisFormal.V5TerminalCandidateEventBridge

/-!
# One accepted execution supplies both relation and FRI evidence

This file is the value-identity join between the accepted composite verifier,
the complete extracted relation body, and the focused extracted FRI consumer.
All witnesses below come from one successful call of
`verify_mode9_composite_with_live_statement`.  In particular, the relation
and FRI proofs cannot be instantiated with alphas, final coefficients,
prepared claims, queries, or openings taken from different executions.
-/

namespace AspisV5AcceptedSameRunRelationFriSnapshot

open Aeneas Aeneas.Std Result
open AspisFormal.HashMerkleModel
open AspisV5AcceptedCompositeExactEvidence
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedEntryFriPhaseBridge
open AspisV5AcceptedFriModelInputBinding
open AspisV5AcceptedRelationPreparedAdapter
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCPreProjectionDeployed
open AspisV5FriAcceptedForestChecks
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConsumerValueSemantics
open AspisV5FriFoldSemantics
open AspisV5FriConsumerObservationBridge
open AspisV5FriGammaCanonical
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5RelationLinkedFieldProjection
open AspisV5MerkleTranscriptProjection
open AspisV5MerkleAuthenticationBinding
open AspisV5ProductionFiatShamirBridge
open AspisV5RelationStressSourceBridge
open AspisV5SourceCandidateFamily
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5TranscriptConnection

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev SnapshotEntryParsed :=
  AspisV5AcceptedEntrySourceBridge.EntryParsed
abbrev SnapshotEntryStatement :=
  AspisV5AcceptedEntrySourceBridge.EntryStatement
abbrev SnapshotEntryQM31 :=
  AspisV5AcceptedEntrySourceBridge.EntryQM31
abbrev SnapshotEntryVerifiedPrefix :=
  AspisV5AcceptedEntrySourceBridge.EntryVerifiedPrefix
abbrev SnapshotEntryTranscript :=
  AspisV5AcceptedEntrySourceBridge.EntryTranscript
abbrev SnapshotEntryVerifiedTerminal :=
  AspisV5AcceptedEntrySourceBridge.EntryVerifiedTerminal
abbrev SnapshotEntryPreparedClaims :=
  AspisV5AcceptedEntrySourceBridge.EntryPreparedClaims
abbrev SnapshotEntryOpenings :=
  AspisV5AcceptedEntryFriPhaseBridge.EntryOpenings
abbrev SnapshotEntryFriSink :=
  AspisV5AcceptedEntryFriPhaseBridge.EntryFriSink

/-- The mathematical QM31 value represented by an accepted-entry field
element.  This is the same four-limb projection used by both the focused FRI
consumer and the complete relation extraction. -/
def entryToK (value : SnapshotEntryQM31) :
    AspisV5FriAcceptedForestChecks.K :=
  AspisV5FriArithmeticSemantics.qm31View
    (AspisV5FriConsumerValueSemantics.toExactQM31
      (AspisV5AcceptedFriModelInputBinding.entryToConsumerQM31 value))

/-- The accepted-entry and relation-caller namespace adapters preserve the
same exact field value. -/
@[simp] theorem entryToK_eq_relationCallerValue
    (value : SnapshotEntryQM31) :
    entryToK value =
      AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller value) := by
  rfl

/-- Complete relation and FRI evidence obtained from one accepted composite
execution.  The equalities on `acceptedFriCall` preserve the exact shared
values at the focused-consumer namespace boundary. -/
structure AcceptedSameRunRelationFriSnapshot
    (accountData : Slice Std.U8)
    (parsed : SnapshotEntryParsed)
    (liveStatement : SnapshotEntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : SnapshotEntryQM31) : Type where
  terminalBoundary : AspisV5AcceptedEntrySourceBridge.EntryTerminalBoundary
  verifiedPrefix : SnapshotEntryVerifiedPrefix
  prefixTranscript : SnapshotEntryTranscript
  verifiedTerminal : SnapshotEntryVerifiedTerminal
  relationTranscript : SnapshotEntryTranscript
  finalPolynomial : Array SnapshotEntryQM31 4#usize
  queries : Array Std.U32 18#usize
  alphas : Array SnapshotEntryQM31 4#usize
  friSum : SnapshotEntryQM31
  preparedClaims : SnapshotEntryPreparedClaims
  relationSum : SnapshotEntryQM31
  phaseSum : SnapshotEntryQM31
  openings : SnapshotEntryOpenings
  sink : SnapshotEntryFriSink
  relationOutput :
    V5RelationCallerGenerated.v5_relation_stress.VerifiedV5RelationStress
  evidence : AcceptedCompositeExactEvidence terminalBoundary accountData parsed liveStatement
    statementDigest acceptedValue verifiedPrefix prefixTranscript
    verifiedTerminal relationTranscript finalPolynomial queries alphas friSum
    preparedClaims relationSum phaseSum openings sink
  relationGate : AcceptedCallerRelationGate parsed finalPolynomial alphas
    verifiedPrefix.kappa verifiedPrefix.inactive_claim
    verifiedPrefix.round_challenges preparedClaims relationSum relationOutput
  relationTrace :
    AspisV5RelationAcceptanceSourceProof.AcceptedMode9FullRelationTrace
      (parsedToCaller parsed)
      (qm31ArrayToCaller finalPolynomial)
      (qm31ArrayToCaller alphas)
      (qm31ToCaller verifiedPrefix.kappa)
      (qm31ToCaller verifiedPrefix.inactive_claim)
      (qm31ArrayToCaller verifiedPrefix.round_challenges)
      (preparedClaimsToCaller preparedClaims)
      (qm31ToCaller relationSum)
  acceptedFriCall : AcceptedFriCall
  acceptedFriOpenings : acceptedFriCall.openings =
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer openings
  acceptedFriPrepared : acceptedFriCall.prepared =
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedClaimsToConsumer
      preparedClaims
  acceptedFriAlphas : acceptedFriCall.alphas = entryArrayToConsumer alphas
  acceptedFriFinal : acceptedFriCall.finalPolynomial =
    entryArrayToConsumer finalPolynomial
  acceptedFriInverse : acceptedFriCall.inverse =
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.inverseToConsumer
      V5AcceptedEntryGenerated.aspis_core.field.M31.inv
  alphaCanonical : CanonicalQM31Array4
    (mapArray toExactQM31 (entryArrayToConsumer alphas))
  finalCanonical : CanonicalQM31Array4
    (mapArray toExactQM31 (entryArrayToConsumer finalPolynomial))

/-- Preserve every decoded relation-tail field while fixing its public final
polynomial to the exact four values accepted by this execution. -/
def snapshotRelationTail
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K) :
    PhysicalRelationFields AspisV5FriAcceptedForestChecks.K :=
  { tail with
    finalCoefficients := fun slot =>
      entryToK snapshot.finalPolynomial.val[slot.val]! }

/-- The maintained caller data selected by one accepted execution.  The
point-claim table, decoded relation tail, and weight schedule are explicit
arguments because their source bridges are proved independently; all public
prefix values, alphas, component-B point values, and final coefficients come
directly from this same accepted snapshot. -/
def snapshotCallerData
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → AspisV5FriAcceptedForestChecks.K)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K)
    (mainWeights : SourceMainWeightSchedule
      AspisV5FriAcceptedForestChecks.K) :
    SourceMode9CallerData AspisV5FriAcceptedForestChecks.K where
  inactiveClaim := entryToK snapshot.verifiedPrefix.inactive_claim
  kappa := entryToK snapshot.verifiedPrefix.kappa
  gamma := entryToK snapshot.verifiedPrefix.gamma
  pointMajorClaims := pointMajorClaims
  relationTail := snapshotRelationTail snapshot tail
  alphas := fun layer => entryToK snapshot.alphas.val[layer.val]!
  mainWeights := mainWeights
  componentBPoint := fun coordinate =>
    entryToK snapshot.verifiedPrefix.round_challenges.val[coordinate.val]!

/-- The final polynomial supplied to the root-defined transcript is exactly
the one accepted by this execution. -/
def snapshotPublishedFinal
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    Fin 4 → AspisV5FriAcceptedForestChecks.K :=
  fun slot => entryToK snapshot.finalPolynomial.val[slot.val]!

/-- The causal transcript family fixed by the five roots and final polynomial
in this accepted body. -/
noncomputable def snapshotCausalFamily
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (decoder : ProductionOpeningDecoder AspisV5FriAcceptedForestChecks.K)
    (hashing : MerkleHashing AspisV5MerkleRustBridge.Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    CausalTranscriptFamily AspisV5FriAcceptedForestChecks.K :=
  committedCausalFamily decoder hashing
    (fixedBodyCausalRoots
      (entryTranscriptInput parsed statementDigest)
      (snapshotPublishedFinal snapshot))

/-- The exact maintained transcript bytes read from the accepted parsed body. -/
def snapshotTranscriptInput
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (_snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) : V5TranscriptInputs :=
  entryTranscriptInput parsed statementDigest

@[simp] theorem snapshotCallerData_alpha
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → AspisV5FriAcceptedForestChecks.K)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K)
    (mainWeights : SourceMainWeightSchedule
      AspisV5FriAcceptedForestChecks.K)
    (layer : Fin 4) :
    (snapshotCallerData snapshot pointMajorClaims tail mainWeights).alphas layer =
      entryToK snapshot.alphas.val[layer.val]! := by
  rfl

@[simp] theorem snapshotCallerData_final
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → AspisV5FriAcceptedForestChecks.K)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K)
    (mainWeights : SourceMainWeightSchedule
      AspisV5FriAcceptedForestChecks.K)
    (slot : Fin 4) :
    PhysicalRelationFields.finalCoefficients
        (snapshotCallerData snapshot pointMajorClaims tail mainWeights).relationTail
        slot =
      entryToK snapshot.finalPolynomial.val[slot.val]! := by
  rfl

/-- The schedule selected by the maintained relation input uses exactly the
four accepted production alpha values. -/
theorem snapshotCallerData_schedule_alpha
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → AspisV5FriAcceptedForestChecks.K)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K)
    (mainWeights : SourceMainWeightSchedule
      AspisV5FriAcceptedForestChecks.K)
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P)
      AspisV5FriAcceptedForestChecks.K)
    (layer : Fin 4) :
    entryToK snapshot.alphas.val[layer.val]! =
      FixedSchedule.alpha
        (exactReleasedFriTables
          (acceptedSchedule base
            (sourceMode9RelationInput
              (snapshotCallerData snapshot pointMajorClaims tail mainWeights))))
        layer := by
  fin_cases layer <;> rfl

/-- The root-defined transcript selected by the accepted caller has exactly
the accepted production final polynomial. -/
theorem snapshotCallerData_transcript_final
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (decoder : ProductionOpeningDecoder AspisV5FriAcceptedForestChecks.K)
    (hashing : MerkleHashing AspisV5MerkleRustBridge.Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → AspisV5FriAcceptedForestChecks.K)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K)
    (mainWeights : SourceMainWeightSchedule
      AspisV5FriAcceptedForestChecks.K)
    (slot : Fin 4) :
    entryToK snapshot.finalPolynomial.val[slot.val]! =
      IdealTranscript.publishedFinal
        (acceptedTranscript (snapshotCausalFamily decoder hashing snapshot)
          (sourceMode9RelationInput
            (snapshotCallerData snapshot pointMajorClaims tail mainWeights)))
        slot := by
  rfl

/-- Invert one accepted production-composite call once, then retain the
complete extracted relation execution and the accepted focused FRI call with
the exact same values.  No relation/FRI/model correspondence premise is an
argument to this theorem. -/
theorem accepted_composite_builds_same_run_relation_fri_snapshot
    (terminalBoundary :
      AspisV5AcceptedEntrySourceBridge.EntryTerminalBoundary)
    (accountData : Slice Std.U8)
    (parsed : SnapshotEntryParsed)
    (liveStatement : SnapshotEntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : SnapshotEntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          terminalBoundary accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    Nonempty (AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) := by
  obtain ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
      relationTranscript, finalPolynomial, queries, alphas, friSum,
      preparedClaims, relationSum, phaseSum, openings, sink, relationOutput,
      evidence, relationGate⟩ :=
    accepted_composite_reaches_checked_relation_gate terminalBoundary accountData parsed
      liveStatement statementDigest acceptedValue success
  obtain ⟨relationTrace⟩ :=
    AspisV5RelationAcceptanceSourceProof.extracted_mode9_success_exposes_full_relation_trace
      (parsedToCaller parsed) (qm31ArrayToCaller finalPolynomial)
      (qm31ArrayToCaller alphas) (qm31ToCaller verifiedPrefix.kappa)
      (qm31ToCaller verifiedPrefix.inactive_claim)
      (qm31ArrayToCaller verifiedPrefix.round_challenges)
      (preparedClaimsToCaller preparedClaims) (qm31ToCaller relationSum)
      relationGate.callerSuccess
  obtain ⟨acceptedFriCall, acceptedFriOpenings, acceptedFriPrepared,
      acceptedFriAlphas, acceptedFriFinal, acceptedFriInverse⟩ :=
    entry_fri_success_builds_accepted_consumer_call openings preparedClaims
      alphas finalPolynomial sink evidence.exactFriCalls.fullFriCheckSuccess
  have alphaCanonical := decoded_entry_alphas_are_canonical parsed alphas
    evidence.compositeCalls.alphaSuccess
  have finalCanonical := selected_entry_final_polynomial_is_canonical
    relationTranscript parsed verifiedPrefix.round_challenges finalPolynomial
    queries evidence.compositeCalls.querySuccess
  exact ⟨{
    terminalBoundary := terminalBoundary
    verifiedPrefix := verifiedPrefix
    prefixTranscript := prefixTranscript
    verifiedTerminal := verifiedTerminal
    relationTranscript := relationTranscript
    finalPolynomial := finalPolynomial
    queries := queries
    alphas := alphas
    friSum := friSum
    preparedClaims := preparedClaims
    relationSum := relationSum
    phaseSum := phaseSum
    openings := openings
    sink := sink
    relationOutput := relationOutput
    evidence := evidence
    relationGate := relationGate
    relationTrace := relationTrace
    acceptedFriCall := acceptedFriCall
    acceptedFriOpenings := acceptedFriOpenings
    acceptedFriPrepared := acceptedFriPrepared
    acceptedFriAlphas := acceptedFriAlphas
    acceptedFriFinal := acceptedFriFinal
    acceptedFriInverse := acceptedFriInverse
    alphaCanonical := alphaCanonical
    finalCanonical := finalCanonical
  }⟩

/-- Once the accepted alpha and final-polynomial values are identified with
one mathematical schedule and transcript, every remaining field of the FRI
model-input binding follows from executable decoding and arithmetic proofs.
In particular, canonical encodings and the layer-zero gamma combination are
not assumptions of this theorem. -/
theorem accepted_snapshot_builds_fri_model_input_binding
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (schedule : FixedSchedule
      (ZMod AspisCircleGroupOrder.P) AspisV5FriAcceptedForestChecks.K)
    (transcript : IdealTranscript AspisV5FriAcceptedForestChecks.K)
    (alphaValue : ∀ layer : Fin 4,
      entryToK snapshot.alphas.val[layer.val]! = schedule.alpha layer)
    (finalValue : ∀ slot : Fin 4,
      entryToK snapshot.finalPolynomial.val[slot.val]! =
        transcript.publishedFinal slot) :
    AcceptedFriModelInputBinding snapshot.acceptedFriCall.prepared
      snapshot.acceptedFriCall.alphas
      snapshot.acceptedFriCall.finalPolynomial schedule transcript := by
  refine {
    alphaCanonical := ?_
    alphaValue := ?_
    combinedCanonical := ?_
    finalCanonical := ?_
    finalValue := ?_ }
  · intro layer
    rw [snapshot.acceptedFriAlphas]
    simpa [AspisV5FriConsumerValueSemantics.mapArray, layer.isLt] using
      snapshot.alphaCanonical layer.val layer.isLt
  · intro layer
    rw [snapshot.acceptedFriAlphas]
    simpa [entryToK] using alphaValue layer
  · intro c1 c2 combined success
    rw [snapshot.acceptedFriPrepared] at success
    exact gamma_combine_success_canonical c1 c2
      (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedClaimsToConsumer
        snapshot.preparedClaims) combined success
  · rw [snapshot.acceptedFriFinal]
    exact snapshot.finalCanonical
  · intro slot
    rw [snapshot.acceptedFriFinal]
    simpa [entryToK] using finalValue slot

/-- Fully instantiate the FRI model-input binding with the schedule, roots,
and final polynomial selected by this same accepted production execution. -/
theorem accepted_snapshot_builds_same_run_fri_model_input_binding
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (decoder : ProductionOpeningDecoder AspisV5FriAcceptedForestChecks.K)
    (hashing : MerkleHashing AspisV5MerkleRustBridge.Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → AspisV5FriAcceptedForestChecks.K)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K)
    (mainWeights : SourceMainWeightSchedule
      AspisV5FriAcceptedForestChecks.K)
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P)
      AspisV5FriAcceptedForestChecks.K) :
    AcceptedFriModelInputBinding snapshot.acceptedFriCall.prepared
      snapshot.acceptedFriCall.alphas
      snapshot.acceptedFriCall.finalPolynomial
      (exactReleasedFriTables
        (acceptedSchedule base
          (sourceMode9RelationInput
            (snapshotCallerData snapshot pointMajorClaims tail mainWeights))))
      (acceptedTranscript (snapshotCausalFamily decoder hashing snapshot)
        (sourceMode9RelationInput
          (snapshotCallerData snapshot pointMajorClaims tail mainWeights))) := by
  apply accepted_snapshot_builds_fri_model_input_binding snapshot
  · exact snapshotCallerData_schedule_alpha snapshot pointMajorClaims tail
      mainWeights base
  · exact snapshotCallerData_transcript_final decoder hashing snapshot
      pointMajorClaims tail mainWeights

/-- The caller input built from the accepted values agrees with its
constructed candidate family, and that family uses the same root-defined FRI
transcript.  These are consequences of the concrete constructors, not extra
premises. -/
theorem accepted_snapshot_builds_same_run_relation_family_projections
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (decoder : ProductionOpeningDecoder AspisV5FriAcceptedForestChecks.K)
    (hashing : MerkleHashing AspisV5MerkleRustBridge.Digest32)
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → AspisV5FriAcceptedForestChecks.K)
    (tail : PhysicalRelationFields AspisV5FriAcceptedForestChecks.K)
    (mainWeights : SourceMainWeightSchedule
      AspisV5FriAcceptedForestChecks.K)
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P)
      AspisV5FriAcceptedForestChecks.K) :
    let data := snapshotCallerData snapshot pointMajorClaims tail mainWeights
    let family := snapshotCausalFamily decoder hashing snapshot
    SourceRelationInputMatchesFamily (sourceMode9RelationInput data)
        (releasedSourceCandidateFamily base family data) ∧
      FamilyMatchesFriTranscript
        (concreteCodeEncoders base
          AspisV5FriReleasedLineGeometry.releasedEvaluationPoints)
        (acceptedTranscript family (sourceMode9RelationInput data))
        (releasedSourceCandidateFamily base family data)
        (sourceMode9RelationInput data).challenges := by
  dsimp only
  exact released_source_relation_and_family_projections base
    (snapshotCausalFamily decoder hashing snapshot)
    (snapshotCallerData snapshot pointMajorClaims tail mainWeights) (by rfl)

#print axioms accepted_composite_builds_same_run_relation_fri_snapshot
#print axioms entryToK_eq_relationCallerValue
#print axioms accepted_snapshot_builds_fri_model_input_binding
#print axioms accepted_snapshot_builds_same_run_fri_model_input_binding
#print axioms accepted_snapshot_builds_same_run_relation_family_projections

end AspisV5AcceptedSameRunRelationFriSnapshot
