import V5AcceptedSameRunRelationFriSnapshot
import V5AcceptedRelationRoundInversion
import V5AcceptedPrefixCanonical
import V5AcceptedCompactInputsCanonical
import V5AcceptedPreparedClaimsCanonical
import V5RelationPrepareCanonicalProof
import V5RelationPrepareLogLenProof
import V5RelationTerminalDotCanonical
import V5AcceptedCompactFoldExactBridge

/-!
# Closing the accepted relation execution against the maintained verifier

This file joins the representation facts proved by the accepted composite
snapshot to the exact four-round inversion.  It deliberately keeps the join
separate from the loop proof so neither proof package imports the other in a
cycle.
-/

namespace AspisV5AcceptedRelationSourceClosure

open Aeneas Aeneas.Std Result
open AspisV5AcceptedRelationPreparedAdapter
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5AcceptedPreparedClaimsCanonical
open AspisV5FriConsumerValueSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

@[simp] theorem qm31ArrayToCaller_get_bang
    {count : Std.Usize} (values : Array SnapshotEntryQM31 count)
    (index : Fin count.val) :
    (qm31ArrayToCaller values).val[index.val]! =
      qm31ToCaller values.val[index.val]! := by
  simp [AspisV5AcceptedRelationPreparedAdapter.qm31ArrayToCaller,
    AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller,
    V5AcceptedEntryGenerated.v5_cu_probe.relationCallerMapFixedArray,
    index.isLt]

@[simp] theorem qm31ArrayToCaller_get
    {count : Std.Usize} (values : Array SnapshotEntryQM31 count)
    (index : Fin count.val) :
    (qm31ArrayToCaller values).val[index.val] =
      qm31ToCaller values.val[index.val] := by
  simp [AspisV5AcceptedRelationPreparedAdapter.qm31ArrayToCaller,
    AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller,
    V5AcceptedEntryGenerated.v5_cu_probe.relationCallerMapFixedArray,
    index.isLt]

theorem entry_canonical_to_relation_caller
    (value : SnapshotEntryQM31)
    (canonical : EntryCanonicalQM31 value) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31
      (qm31ToCaller value) := by
  rcases qm31ToCaller_components value with ⟨c0a, c0b, c1a, c1b⟩
  unfold AspisV5RelationGeneratedFieldProjection.CanonicalQM31
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31
  rw [c0a, c0b, c1a, c1b]
  exact ⟨⟨canonical.1, canonical.2.1⟩,
    ⟨canonical.2.2.1, canonical.2.2.2⟩⟩

/-- The caller-namespace alpha used by every inverted production round has
the canonical representation already proved from the accepted entry's
decoder. -/
theorem accepted_snapshot_relation_alphas_are_canonical
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    ∀ slot : Fin 4,
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        (acceptedAlphaAt (qm31ArrayToCaller snapshot.alphas) slot) := by
  intro slot
  have canonical := snapshot.alphaCanonical slot.val slot.isLt
  have entryCanonical : EntryCanonicalQM31
      snapshot.alphas.val[slot.val]! := by
    simpa [AspisV5FriConsumerValueSemantics.mapArray,
    AspisV5FriFoldSemantics.CanonicalQM31Array4,
    AspisV5FriArithmeticSemantics.canonicalQM31,
    AspisV5FriArithmeticSemantics.canonicalCM31,
    AspisV5FriArithmeticSemantics.canonicalM31,
    AspisV5FriConsumerValueSemantics.toExactQM31,
    AspisV5FriConsumerValueSemantics.toExactCM31,
    AspisV5AcceptedFriModelInputBinding.entryArrayToConsumer,
    AspisV5AcceptedFriModelInputBinding.entryToConsumerQM31,
    AspisV5AcceptedFriModelInputBinding.entryToConsumerCM31,
    EntryCanonicalQM31,
    slot.isLt] using canonical
  have mapped := entry_canonical_to_relation_caller
    snapshot.alphas.val[slot.val]! entryCanonical
  unfold AspisV5AcceptedRelationRoundInversion.acceptedAlphaAt
  rw [qm31ArrayToCaller_get]
  simpa [slot.isLt] using mapped

theorem entry_prepared_claims_to_caller_canonical
    (claims : SnapshotEntryPreparedClaims)
    (canonical : PreparedClaimsCanonical claims) :
    AspisV5RelationPrepareCanonicalProof.CallerClaimsCanonical
      (preparedClaimsToCaller claims) := by
  unfold AspisV5RelationPrepareCanonicalProof.CallerClaimsCanonical
  change
    (claims.inner.claims.val.map qm31ToCaller).length = 4 ∧
      ∀ (index : Nat)
        (bound : index < (claims.inner.claims.val.map qm31ToCaller).length),
        AspisV5RelationGeneratedFieldProjection.CanonicalQM31
          (claims.inner.claims.val.map qm31ToCaller)[index]
  constructor
  · simpa using canonical.1
  · intro index bound
    have sourceBound : index < claims.inner.claims.val.length := by
      simpa using bound
    have finBound : index < 4 := by
      rw [canonical.1] at sourceBound
      exact sourceBound
    have bangEquality : claims.inner.claims.val[index]! =
        claims.inner.claims.val[index] := by
      apply List.getElem!_of_getElem?
      simp [sourceBound]
    have sourceCanonical := canonical.2 ⟨index, finBound⟩
    rw [bangEquality] at sourceCanonical
    have mapped := entry_canonical_to_relation_caller
      claims.inner.claims.val[index] sourceCanonical
    simpa [sourceBound] using mapped

/-- Every compact Component-B point coordinate supplied to the accepted
relation caller comes from the successful ten-round semantic sumcheck and is
canonical in the caller namespace. -/
theorem accepted_snapshot_round_challenges_are_canonical
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    ∀ index : Fin 10,
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        (qm31ArrayToCaller snapshot.verifiedPrefix.round_challenges).val[
          index.val]! := by
  have entryCanonical :=
    AspisV5AcceptedCompactInputsCanonical.accepted_prefix_round_challenges_canonical
      parsed liveStatement statementDigest
      V5AcceptedEntryGenerated.verify.sbf_hashv snapshot.verifiedPrefix
      snapshot.prefixTranscript snapshot.evidence.compositeCalls.prefixSuccess
  intro index
  rw [qm31ArrayToCaller_get_bang]
  exact entry_canonical_to_relation_caller
    snapshot.verifiedPrefix.round_challenges.val[index.val]!
    (entryCanonical index)

/-- The compact constructor scale in one accepted relation trace is the
canonical `kappa³` value returned by that same successful preparation call. -/
theorem accepted_snapshot_dense_scale_is_canonical
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31
      snapshot.relationTrace.calls.denseScale := by
  have prefixCanonical :=
    AspisV5AcceptedPrefixCanonical.accepted_prefix_gamma_and_inactive_canonical
      parsed liveStatement statementDigest
      V5AcceptedEntryGenerated.verify.sbf_hashv snapshot.verifiedPrefix
      snapshot.prefixTranscript snapshot.evidence.compositeCalls.prefixSuccess
  exact
    AspisV5RelationPrepareCanonicalProof.caller_prepare_success_dense_scale_canonical
      (parsedToCaller parsed) (qm31ToCaller snapshot.verifiedPrefix.kappa)
      (qm31ToCaller snapshot.verifiedPrefix.inactive_claim)
      (preparedClaimsToCaller snapshot.preparedClaims)
      snapshot.relationTrace.calls.relation
      snapshot.relationTrace.calls.ignoredAlphas
      snapshot.relationTrace.calls.denseScale
      (entry_canonical_to_relation_caller snapshot.verifiedPrefix.kappa
        prefixCanonical.2.2)
      snapshot.relationTrace.calls.prepareSuccess

/-- The accepted compact constructor scale is not merely canonical: its
maintained-field value is exactly the cube of the accepted kappa challenge. -/
theorem accepted_snapshot_dense_scale_is_kappa_cube
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AspisV5RelationGeneratedFieldProjection.toMaintainedExact
        snapshot.relationTrace.calls.denseScale =
      AspisV5RelationGeneratedFieldProjection.toMaintainedExact
          (qm31ToCaller snapshot.verifiedPrefix.kappa) ^ 3 := by
  have prefixCanonical :=
    AspisV5AcceptedPrefixCanonical.accepted_prefix_gamma_and_inactive_canonical
      parsed liveStatement statementDigest
      V5AcceptedEntryGenerated.verify.sbf_hashv snapshot.verifiedPrefix
      snapshot.prefixTranscript snapshot.evidence.compositeCalls.prefixSuccess
  exact
    AspisV5RelationPrepareCanonicalProof.caller_prepare_success_dense_scale_exact
      (parsedToCaller parsed) (qm31ToCaller snapshot.verifiedPrefix.kappa)
      (qm31ToCaller snapshot.verifiedPrefix.inactive_claim)
      (preparedClaimsToCaller snapshot.preparedClaims)
      snapshot.relationTrace.calls.relation
      snapshot.relationTrace.calls.ignoredAlphas
      snapshot.relationTrace.calls.denseScale
      (entry_canonical_to_relation_caller snapshot.verifiedPrefix.kappa
        prefixCanonical.2.2)
      snapshot.relationTrace.calls.prepareSuccess

/-- The initial relation value in one accepted same-run snapshot is
canonical.  Its kappa and inactive claim come from the exact accepted prefix
sampler/decoder, and its four claims come from the exact accepted preparation
call. -/
theorem accepted_snapshot_initial_relation_is_canonical
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31
      snapshot.relationTrace.calls.relation.relation_value := by
  have prefixCanonical :=
    AspisV5AcceptedPrefixCanonical.accepted_prefix_gamma_and_inactive_canonical
      parsed liveStatement statementDigest
      V5AcceptedEntryGenerated.verify.sbf_hashv snapshot.verifiedPrefix
      snapshot.prefixTranscript snapshot.evidence.compositeCalls.prefixSuccess
  have preparedCanonical :=
    prepare_v5_pcs_claims_success_canonical snapshot.verifiedPrefix.gamma
      parsed.relation_claims snapshot.preparedClaims prefixCanonical.1
      snapshot.evidence.exactFriCalls.prepareClaimsSuccess
  exact
    AspisV5RelationPrepareCanonicalProof.caller_prepare_success_relation_value_canonical
      (parsedToCaller parsed) (qm31ToCaller snapshot.verifiedPrefix.kappa)
      (qm31ToCaller snapshot.verifiedPrefix.inactive_claim)
      (preparedClaimsToCaller snapshot.preparedClaims)
      snapshot.relationTrace.calls.relation
      snapshot.relationTrace.calls.ignoredAlphas
      snapshot.relationTrace.calls.denseScale
      (entry_canonical_to_relation_caller snapshot.verifiedPrefix.kappa
        prefixCanonical.2.2)
      (entry_canonical_to_relation_caller snapshot.verifiedPrefix.inactive_claim
        prefixCanonical.2.1)
      (entry_prepared_claims_to_caller_canonical snapshot.preparedClaims
        preparedCanonical)
      snapshot.relationTrace.calls.prepareSuccess

theorem accepted_snapshot_final_coefficients_are_canonical
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    ∀ index, index < 4 →
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        snapshot.relationTrace.finalCoefficients.val[index]! := by
  have finalMatch := snapshot.relationTrace.calls.finalPolynomialMatch
  rw [snapshot.relationTrace.outputExact] at finalMatch
  intro index indexBound
  have inputCanonical := snapshot.finalCanonical index indexBound
  have entryCanonical : EntryCanonicalQM31
      snapshot.finalPolynomial.val[index]! := by
    simpa [AspisV5FriFoldSemantics.CanonicalQM31Array4,
      AspisV5FriArithmeticSemantics.canonicalQM31,
      AspisV5FriArithmeticSemantics.canonicalCM31,
      AspisV5FriArithmeticSemantics.canonicalM31,
      AspisV5FriConsumerValueSemantics.mapArray,
      AspisV5FriConsumerValueSemantics.toExactQM31,
      AspisV5FriConsumerValueSemantics.toExactCM31,
      AspisV5AcceptedFriModelInputBinding.entryArrayToConsumer,
      AspisV5AcceptedFriModelInputBinding.entryToConsumerQM31,
      AspisV5AcceptedFriModelInputBinding.entryToConsumerCM31,
      EntryCanonicalQM31, indexBound] using inputCanonical
  have callerCanonical := entry_canonical_to_relation_caller
    snapshot.finalPolynomial.val[index]! entryCanonical
  have elementMatch := congrArg
    (fun (values : Array V5RelationCallerGenerated.aspis_core.field.QM31
        4#usize) => values.val[index]!) finalMatch
  rw [elementMatch]
  have mappedEntry :
      (qm31ArrayToCaller snapshot.finalPolynomial).val[index]! =
        qm31ToCaller snapshot.finalPolynomial.val[index]! := by
    simp [AspisV5AcceptedRelationPreparedAdapter.qm31ArrayToCaller,
      AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller,
      V5AcceptedEntryGenerated.v5_cu_probe.relationCallerMapFixedArray,
      indexBound]
  rw [mappedEntry]
  exact callerCanonical

/-- The compact terminal contribution computed inside one accepted deployed
relation execution is exactly the maintained optimized compact formula over
the ten accepted transcript coordinates, `kappa³` scale value, four accepted
fold challenges, and four decoded final coefficients. -/
theorem accepted_snapshot_compact_terminal_exact
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        snapshot.relationTrace.additiveDot ∧
      AspisV5RelationGeneratedFieldProjection.toMaintainedExact
          snapshot.relationTrace.additiveDot =
        AspisV5CompactTerminalOptimized.optimizedCompactFinalDot
          (fun index =>
            AspisV5RelationGeneratedFieldProjection.toMaintainedExact
              (qm31ArrayToCaller
                snapshot.verifiedPrefix.round_challenges).val[index.val]!)
          (AspisV5RelationGeneratedFieldProjection.toMaintainedExact
            snapshot.relationTrace.calls.denseScale)
          (fun index =>
            AspisV5RelationGeneratedFieldProjection.toMaintainedExact
              (acceptedAlphaAt (qm31ArrayToCaller snapshot.alphas) index))
          (fun index =>
            AspisV5RelationGeneratedFieldProjection.toMaintainedExact
              snapshot.relationTrace.finalCoefficients.val[index.val]!) := by
  apply
    AspisV5AcceptedCompactExecutionExact.accepted_trace_compact_terminal_exact
      snapshot.relationTrace
      (AspisV5AcceptedCompactFoldExactBridge.accepted_trace_compact_fold_source_equality
        snapshot.relationTrace)
  · intro index
    unfold AspisV5CompactCallerWrapperExact.CallerCanonical
    simpa [AspisV5CompactCallerWrapperExact.callerPointAt] using
      accepted_snapshot_round_challenges_are_canonical snapshot index
  · exact accepted_snapshot_dense_scale_is_canonical snapshot
  · exact accepted_snapshot_relation_alphas_are_canonical snapshot
  · intro index
    exact accepted_snapshot_final_coefficients_are_canonical snapshot
      index.val index.isLt

/-- One accepted production snapshot now constructs the concrete maintained
source relation input and proves that the maintained four-round verifier
accepts it with the exact decoded final coefficients and terminal claim. -/
theorem accepted_snapshot_runs_source_relation_verifier
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    ∃ rounds : AcceptedFourRawRoundProjections snapshot.relationTrace,
      AspisV5RelationStressSourceBridge.runSourceRelationVerifier
          (acceptedSourceRelationInput rounds) =
        some {
          finalCoefficients := fun index =>
            AspisV5AcceptedRelationRoundProjection.toField
              snapshot.relationTrace.finalCoefficients.val[index.val]!
          terminalClaim :=
            AspisV5AcceptedRelationRoundProjection.toField
              snapshot.relationTrace.claim4 } := by
  obtain ⟨rounds⟩ := accepted_full_trace_exposes_four_raw_round_projections
    snapshot.relationTrace
    (accepted_snapshot_initial_relation_is_canonical snapshot)
    (accepted_snapshot_relation_alphas_are_canonical snapshot)
  have initialLog :=
    AspisV5RelationPrepareLogLenProof.Prepare.prepareSuccess_implies_weights_log_len
      (parsedToCaller parsed)
      (qm31ToCaller snapshot.verifiedPrefix.kappa)
      (qm31ToCaller snapshot.verifiedPrefix.inactive_claim)
      (preparedClaimsToCaller snapshot.preparedClaims)
      snapshot.relationTrace.calls.relation
      snapshot.relationTrace.calls.ignoredAlphas
      snapshot.relationTrace.calls.denseScale
      snapshot.relationTrace.calls.prepareSuccess
  have terminalExact :=
    AspisV5RelationTerminalDotCanonical.accepted_trace_terminal_add_exact_of_initial
      snapshot.relationTrace initialLog
      (accepted_snapshot_final_coefficients_are_canonical snapshot)
  exact ⟨rounds,
    accepted_trace_runs_source_relation_verifier rounds terminalExact⟩

#print axioms accepted_snapshot_relation_alphas_are_canonical
#print axioms accepted_snapshot_round_challenges_are_canonical
#print axioms accepted_snapshot_dense_scale_is_canonical
#print axioms accepted_snapshot_dense_scale_is_kappa_cube
#print axioms accepted_snapshot_initial_relation_is_canonical
#print axioms accepted_snapshot_compact_terminal_exact
#print axioms accepted_snapshot_runs_source_relation_verifier

end AspisV5AcceptedRelationSourceClosure
