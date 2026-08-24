import V5AcceptedOneRunSecurityClosure

/-!
# Deterministic accepted-snapshot closure

This file joins the exact initial claim, main accumulator dot, compact
execution, and four accepted relation rounds.  The compact constructor and
folds are already derived from the accepted caller; only the separately proved
main-accumulator result is supplied to this intermediate theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace AspisV5AcceptedOneRunDeterministicClosure

open Aeneas Aeneas.Std Result
open AspisV5AcceptedClaimTableExact
open AspisV5AcceptedCompactExecutionExact
open AspisV5AcceptedDeterministicRelationTail
open AspisV5AcceptedOneRunSecurityClosure
open AspisV5AcceptedRelationSourceClosure
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5RelationStressSourceBridge

abbrev K := AspisV5FriAcceptedForestChecks.K

/-- The terminal main-dot equality completes the exact source caller for this
snapshot; the compact execution is derived internally from the same run. -/
theorem accepted_snapshot_exact_deterministic_caller_of_main_dot
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (mainWeights : SourceMainWeightSchedule K)
    (mainDotExact :
      sourceMainFinalDot mainWeights
        (sourceCallerChallenges
          (acceptedSnapshotPartialCallerData snapshot
            (acceptedPointClaimTable parsed.relation_claims) mainWeights))
        (snapshotPublishedFinal snapshot) =
      AspisV5AcceptedRelationRoundProjection.toField
        snapshot.relationTrace.mainDot) :
    AcceptedSnapshotExactDeterministicCaller snapshot := by
  have initialExact :
      sourceCallerInitialClaim
          (entryToK snapshot.verifiedPrefix.inactive_claim)
          (entryToK snapshot.verifiedPrefix.kappa)
          (entryToK snapshot.verifiedPrefix.gamma)
          (acceptedPointClaimTable parsed.relation_claims) =
        AspisV5AcceptedRelationRoundProjection.toField
          snapshot.relationTrace.calls.relation.relation_value := by
    have relationProjectionExact :
        AspisV5RelationLinkedFieldProjection.toMaintainedExact
            snapshot.relationTrace.calls.relation.relation_value =
          AspisV5AcceptedRelationRoundProjection.toField
            snapshot.relationTrace.calls.relation.relation_value := by
      rfl
    rw [← relationProjectionExact]
    simpa [AspisV5AcceptedClaimTableExact.entryClaimToK] using
      (accepted_snapshot_initial_relation_exact snapshot).symm
  have inputExact :=
    acceptedSnapshotPartialCallerData_relationInput_exact snapshot
      (acceptedPointClaimTable parsed.relation_claims) mainWeights
      initialExact mainDotExact
      (accepted_snapshot_compact_dot_exact snapshot)
  unfold AcceptedSnapshotExactDeterministicCaller
  refine ⟨mainWeights, inputExact, ?_⟩
  exact accepted_snapshot_exact_caller_of_relation_input_exact snapshot
    mainWeights inputExact

/-- Package the exact main-dot witness with the accepted-snapshot security
theorem.  The final wrapper obtains this witness from the source-linked
accumulator proof. -/
theorem accepted_snapshot_security_conclusion_of_main_dot
    (rc : AspisFormal.HashMerkleModel.RoundConstants)
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
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized)
    (base : AspisV5ComponentCConcreteFoldLinearity.FixedSchedule
      (ZMod AspisCircleGroupOrder.P) K)
    (hproduction :
      AspisV5AcceptedExecutionReleasedSchedule.ProductionUsesReleasedFriTables
        base)
    (hpublished :
      AspisV5FriPublishedOutputEncoderDecoding.PublishedOrdinaryPolynomialCurveDecoding
        (K := K))
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (mainDot : ∃ mainWeights : SourceMainWeightSchedule K,
      sourceMainFinalDot mainWeights
        (sourceCallerChallenges
          (acceptedSnapshotPartialCallerData snapshot
            (acceptedPointClaimTable parsed.relation_claims) mainWeights))
        (snapshotPublishedFinal snapshot) =
      AspisV5AcceptedRelationRoundProjection.toField
        snapshot.relationTrace.mainDot) :
    ∃ mainWeights : SourceMainWeightSchedule K,
      AcceptedSnapshotSecurityConclusion rc deployedOwner deployedNote
        deployedNullifier deployedNode sha256 base snapshot
        (acceptedSnapshotPartialCallerData snapshot
          (acceptedPointClaimTable parsed.relation_claims) mainWeights) := by
  obtain ⟨mainWeights, mainDotExact⟩ := mainDot
  apply accepted_snapshot_security_conclusion_of_exact_caller rc sha256 hhash
    base hproduction hpublished snapshot
  exact accepted_snapshot_exact_deterministic_caller_of_main_dot snapshot
    mainWeights mainDotExact

#print axioms accepted_snapshot_exact_deterministic_caller_of_main_dot
#print axioms accepted_snapshot_security_conclusion_of_main_dot

end AspisV5AcceptedOneRunDeterministicClosure
