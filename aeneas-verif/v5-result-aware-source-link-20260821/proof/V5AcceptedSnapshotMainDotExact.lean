import V5AcceptedTerminalAccumulatorWeights
import V5AcceptedDeterministicRelationTail
import V5AcceptedClaimTableExact

/-!
# Exact accepted main-accumulator dot

This module constructs the source main-weight schedule from the same accepted
production execution and identifies its final dot with the value returned by
the production verifier.
-/

namespace AspisV5AcceptedSnapshotMainDotExact

open Aeneas Aeneas.Std Result
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedClaimTableExact
open AspisV5AcceptedDeterministicRelationTail
open AspisV5AcceptedInactiveInitialSemantics
open AspisV5AcceptedInactiveTerminalJourney
open AspisV5AcceptedPrefixCanonical
open AspisV5AcceptedRelationRoundProjection
open AspisV5AcceptedRelationSourceClosure
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5AcceptedStructuredTerminalSchedule
open AspisV5AcceptedTerminalAccumulatorWeights
open AspisV5FriRelationCandidateBridge
open AspisV5RelationAcceptanceSourceProof
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedGroupedRows
open AspisV5RelationLinkedGroupedRowsSemantics
open AspisV5RelationLinkedGroupedRowsStaged
open AspisV5RelationLinkedTerminalDotSemantics
open AspisV5RelationStressSourceBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev K := AspisV5FriAcceptedForestChecks.K

/-- The scalar caller and accumulator schedule consume the same twelve
challenges when both are built from the combined accepted execution. -/
theorem accepted_snapshot_source_challenges_eq_accumulator
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K)
    (schedule : AcceptedFourRoundAccumulatorSchedule snapshot.relationTrace)
    (scheduleRoundsExact :
      schedule.rounds = acceptedSnapshotExecutions snapshot) :
    sourceCallerChallenges
        (acceptedSnapshotPartialCallerData snapshot pointMajorClaims
          mainWeights) =
      acceptedAccumulatorChallenges snapshot.relationTrace schedule := by
  change
    ((((sourceCallerRound
          (acceptedSnapshotPartialCallerData snapshot pointMajorClaims
            mainWeights) 0).challenges,
        (sourceCallerRound
          (acceptedSnapshotPartialCallerData snapshot pointMajorClaims
            mainWeights) 1).challenges),
      (sourceCallerRound
        (acceptedSnapshotPartialCallerData snapshot pointMajorClaims
          mainWeights) 2).challenges),
    (sourceCallerRound
      (acceptedSnapshotPartialCallerData snapshot pointMajorClaims
        mainWeights) 3).challenges) = _
  rw [acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 0,
    acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 1,
    acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 2,
    acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 3]
  change
    (((((toField (acceptedSnapshotRounds snapshot).round0.raw.firstMix,
          toField (acceptedSnapshotRounds snapshot).round0.raw.secondMix),
        toField (acceptedSnapshotRounds snapshot).round0.raw.alpha),
      ((toField (acceptedSnapshotRounds snapshot).round1.raw.firstMix,
          toField (acceptedSnapshotRounds snapshot).round1.raw.secondMix),
        toField (acceptedSnapshotRounds snapshot).round1.raw.alpha)),
    ((toField (acceptedSnapshotRounds snapshot).round2.raw.firstMix,
        toField (acceptedSnapshotRounds snapshot).round2.raw.secondMix),
      toField (acceptedSnapshotRounds snapshot).round2.raw.alpha)),
    ((toField (acceptedSnapshotRounds snapshot).round3.raw.firstMix,
        toField (acceptedSnapshotRounds snapshot).round3.raw.secondMix),
      toField (acceptedSnapshotRounds snapshot).round3.raw.alpha)) = _
  unfold acceptedSnapshotRounds
  rw [(acceptedSnapshotRoundEvidence snapshot).round0FirstMixExact,
    (acceptedSnapshotRoundEvidence snapshot).round0SecondMixExact,
    (acceptedSnapshotRoundEvidence snapshot).round1FirstMixExact,
    (acceptedSnapshotRoundEvidence snapshot).round1SecondMixExact,
    (acceptedSnapshotRoundEvidence snapshot).round2FirstMixExact,
    (acceptedSnapshotRoundEvidence snapshot).round2SecondMixExact,
    (acceptedSnapshotRoundEvidence snapshot).round3FirstMixExact,
    (acceptedSnapshotRoundEvidence snapshot).round3SecondMixExact]
  rw [(acceptedSnapshotRoundEvidence snapshot).projections.round0.alphaExact,
    (acceptedSnapshotRoundEvidence snapshot).projections.round1.alphaExact,
    (acceptedSnapshotRoundEvidence snapshot).projections.round2.alphaExact,
    (acceptedSnapshotRoundEvidence snapshot).projections.round3.alphaExact]
  unfold acceptedAccumulatorChallenges
  rw [scheduleRoundsExact]
  unfold acceptedSnapshotExecutions
  rfl

/-- The accepted production main dot is exactly the source-schedule dot.  The
inactive table is added once to the structured schedule's initial covector;
it is never mixed as an OOD component. -/
theorem accepted_snapshot_main_dot_exact
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    ∃ mainWeights : SourceMainWeightSchedule K,
      sourceMainFinalDot mainWeights
          (sourceCallerChallenges
            (acceptedSnapshotPartialCallerData snapshot
              (acceptedPointClaimTable parsed.relation_claims) mainWeights))
          (snapshotPublishedFinal snapshot) =
        AspisV5AcceptedRelationRoundProjection.toField
          snapshot.relationTrace.mainDot := by
  obtain ⟨schedule, scheduleRoundsExact⟩ :=
    acceptedFourRoundExecutionExposesAccumulatorSchedule
      snapshot.relationTrace (acceptedSnapshotExecutions snapshot)
  have prefixCanonical := accepted_prefix_gamma_and_inactive_canonical
    parsed liveStatement statementDigest
    V5AcceptedEntryGenerated.verify.sbf_hashv snapshot.verifiedPrefix
    snapshot.prefixTranscript snapshot.evidence.compositeCalls.prefixSuccess
  have hkappa : CanonicalQM31
      (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller
        snapshot.verifiedPrefix.kappa) :=
    entry_canonical_to_relation_caller snapshot.verifiedPrefix.kappa
      prefixCanonical.2.2
  have halphas := accepted_snapshot_relation_alphas_are_canonical snapshot
  obtain ⟨terminal⟩ := acceptedStructuredTerminalSchedule_exists
    snapshot.relationTrace schedule hkappa halphas
      (accepted_snapshot_relation_circle_points_are_canonical snapshot)
  obtain ⟨inactive⟩ := acceptedInactiveTerminal_exists
    snapshot.relationTrace schedule halphas
  have sourceAlphasExact :
      sourceRelationAlphas
          (acceptedAccumulatorChallenges snapshot.relationTrace schedule) =
        fun slot => toMaintainedExact
          (AspisV5AcceptedRelationRoundInversion.acceptedAlphaAt
            (AspisV5AcceptedRelationPreparedAdapter.qm31ArrayToCaller
              snapshot.alphas) slot) := by
    funext slot
    fin_cases slot <;>
      rfl
  have inactiveSourceExact :
      sourceFoldOnlyFinal
          (sourceRelationAlphas
            (acceptedAccumulatorChallenges snapshot.relationTrace schedule))
          releasedInactiveInitialWeight =
        representedGroupedWeights releasedRowGroups4
          (releasedFourValues inactive.value0 inactive.value1 inactive.value2
            inactive.value3) := by
    rw [sourceAlphasExact]
    simpa [sourceFoldOnlyFinal, sourceFoldOnly3, sourceFoldOnly2,
      sourceFoldOnly1] using inactive.meaningExact.symm
  have combinedWeightsExact :
      (fun index =>
        functionSum [terminal.initial0.meaning, terminal.initial1.meaning,
          terminal.initial2.meaning, terminal.round0First.meaning,
          terminal.round0Second.meaning, terminal.round1First.meaning,
          terminal.round1Second.meaning, terminal.round2First.meaning,
          terminal.round2Second.meaning, terminal.round3First.meaning,
          terminal.round3Second.meaning] index +
        representedGroupedWeights releasedRowGroups4
          (releasedFourValues inactive.value0 inactive.value1 inactive.value2
            inactive.value3) index) =
        terminalAccumulatorWeights
          (weightsToLinked snapshot.relationTrace.weights4) := by
    rw [acceptedTerminalAccumulatorWeightsExact terminal inactive]
    funext index
    simp [functionSum]
    ring
  let structured := acceptedStructuredSourceSchedule schedule hkappa
  let mainWeights : SourceMainWeightSchedule K :=
    structured.withInitial (fun index =>
      structured.initial index + releasedInactiveInitialWeight index)
  refine ⟨mainWeights, ?_⟩
  unfold sourceMainFinalDot
  rw [sourceMainFinalWeights_add_initial]
  rw [accepted_snapshot_source_challenges_eq_accumulator snapshot
    (acceptedPointClaimTable parsed.relation_claims) mainWeights schedule
    scheduleRoundsExact]
  rw [acceptedStructuredSourceSchedule_terminalWeights terminal]
  rw [inactiveSourceExact]
  have combinedCandidateExact := congrArg
    (fun weights : Fin 4 → K =>
      candidateClaim weights (snapshotPublishedFinal snapshot))
    combinedWeightsExact
  refine combinedCandidateExact.trans ?_
  have logs := acceptedScheduleLogLengths snapshot.relationTrace schedule
  obtain ⟨out, linkedRun, _outCanonical, exactOut⟩ :=
    releasedTerminalDotCandidateExact
      (weightsToLinked snapshot.relationTrace.weights4)
      snapshot.relationTrace.finalCoefficients
      (by simpa [weightsToLinked] using logs.2.2.2.2)
      (acceptedTerminalComponentsReleased terminal inactive)
      (accepted_snapshot_final_coefficients_are_canonical snapshot)
  have mainRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
          (weightsToLinked snapshot.relationTrace.weights4)
          (Array.to_slice snapshot.relationTrace.finalCoefficients) =
        .ok snapshot.relationTrace.mainDot := by
    have fullMainRun := snapshot.relationTrace.mainDotSuccess
    unfold aspis_core.sumcheck.WeightAccumulator.dot at fullMainRun
    change
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
          (weightsToLinked snapshot.relationTrace.weights4)
          (Array.to_slice snapshot.relationTrace.finalCoefficients) =
        .ok snapshot.relationTrace.mainDot at fullMainRun
    exact fullMainRun
  have outExact : out = snapshot.relationTrace.mainDot := by
    exact Result.ok.inj (linkedRun.symm.trans mainRun)
  subst out
  have terminalValuesExact :
      terminalValues
          (Array.to_slice snapshot.relationTrace.finalCoefficients) =
        snapshotPublishedFinal snapshot := by
    funext index
    rw [snapshotPublishedFinal_eq_relationTrace]
    rfl
  have candidateValuesExact := congrArg
    (candidateClaim
      (terminalAccumulatorWeights
        (weightsToLinked snapshot.relationTrace.weights4)))
    terminalValuesExact
  exact candidateValuesExact.symm.trans exactOut.symm

#print axioms accepted_snapshot_main_dot_exact

end AspisV5AcceptedSnapshotMainDotExact
