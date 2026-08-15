import AspisFormal.V5RefinedAcceptedFalseAccounting
import AspisFormal.V5WorkNormalizedApplicabilityRepair

/-!
# Connecting the width-19 event to the refined probability bound

The refined accepted-false theorem names the exact event in which the
nineteen committed columns do not agree with the combined FRI word.  The
published PCS/MCA theorem interface bounds an `actualEventProbability`, but
the two were previously left as separate endpoints.

This file joins them without hiding any assumption.  A caller must still
supply:

* the cited PCS/MCA hypotheses;
* membership of the virtual oracle in the required code;
* the separate grinding-output reduction;
* the Rust sampling/transcript correspondence; and
* equality between the probability of the exact width-19 failure set and the
  event probability to which the cited theorem is applied.

Once those facts are supplied, Lean replaces the previously unbounded
width-19 term by `2^-107` in the refined accepted-false result.
-/

namespace AspisV5RefinedWidth19DeploymentBridge

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5CryptographicAssumptions
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5MaskedBoundaryFailureAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5RefinedAcceptedFalseAccounting
open AspisV5RefinedRawCoreAccounting
open AspisV5StatementBindingFailureAccounting
open AspisV5SumcheckTranscriptBinding
open AspisV5WorkNormalizedApplicabilityRepair

/-- The exact information needed to apply the cited width-19 bound to one
measured failure set.  No source, code-membership, grinding, or sampling fact
is inferred from the algebraic root-count proof. -/
structure Width19MeasuredEventConnection
    {Sample Schedule : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (width19Failure : Set Sample) where
  acceptedSchedule : Schedule → Prop
  citedMCAHypotheses : Schedule → Prop
  virtualOracleAndCodeMembership : Schedule → Prop
  separateGrindingOutputReduction : Schedule → Prop
  rustSamplingAndTranscriptCorrespondence : Schedule → Prop
  actualEventProbability : Schedule → ℝ
  deployment : Width19FStarDeploymentPremises acceptedSchedule
    citedMCAHypotheses virtualOracleAndCodeMembership
    separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
    actualEventProbability
  selectedSchedule : Schedule
  selectedScheduleAccepted : acceptedSchedule selectedSchedule
  exactMeasuredEvent :
    measure.real width19Failure = actualEventProbability selectedSchedule

/-- The exact measured width-19 failure event is at most `2^-107`, conditional
on every named published-theorem and implementation premise above. -/
theorem width19_measured_failure_probability_le_two_pow_neg_107
    {Sample Schedule : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (width19Failure : Set Sample)
    (connection : Width19MeasuredEventConnection
      (Schedule := Schedule) measure width19Failure) :
    measure.real width19Failure ≤ (1 : ℝ) / 2 ^ 107 := by
  rw [connection.exactMeasuredEvent]
  exact width19_fstar_event_bound_of_all_named_premises
    connection.acceptedSchedule connection.citedMCAHypotheses
    connection.virtualOracleAndCodeMembership
    connection.separateGrindingOutputReduction
    connection.rustSamplingAndTranscriptCorrespondence
    connection.actualEventProbability connection.deployment
    connection.selectedSchedule connection.selectedScheduleAccepted

/-- Replace the visible width-19 term in any refined bound after the exact
measured-event connection has been supplied. -/
theorem refined_bound_with_width19_two_pow_neg_107
    {Sample Schedule : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (target width19Failure : Set Sample)
    (remaining : ℝ)
    (base : measure.real target ≤
      (1 : ℝ) / 2 ^ 75 + measure.real width19Failure + remaining)
    (connection : Width19MeasuredEventConnection
      (Schedule := Schedule) measure width19Failure) :
    measure.real target ≤
      (1 : ℝ) / 2 ^ 75 + (1 : ℝ) / 2 ^ 107 + remaining := by
  have widthBound :=
    width19_measured_failure_probability_le_two_pow_neg_107
      measure width19Failure connection
  linarith

/-- Accepted-false form of the refined theorem with the exact width-19 event
replaced by its conditional `2^-107` deployment bound. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_width19_bound
    {Run Coins K Public Root Schedule : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (projection : StatementBindingProjectionData Run Coins K data)
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection)
    (terminalCandidateFailure : Set Coins)
    (coverage : TerminalCandidateFailureCoverage boundary
      terminalCandidateFailure)
    (terminalBound : measure.real terminalCandidateFailure ≤
      rawCandidateTerminalBound)
    (width19Connection : Width19MeasuredEventConnection
      (Schedule := Schedule) measure data.width19Failure) :
    measure.real data.base.acceptedFalse ≤
      (1 : ℝ) / 2 ^ 75 + (1 : ℝ) / 2 ^ 107 +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.hashMerkleResidualFailure := by
  have base := acceptedFalse_probability_le_two_pow_neg_75_nonduplicated
    measure data connections projection boundary terminalCandidateFailure
    coverage terminalBound
  have widthBound :=
    width19_measured_failure_probability_le_two_pow_neg_107
      measure data.width19Failure width19Connection
  linarith

#print axioms width19_measured_failure_probability_le_two_pow_neg_107
#print axioms refined_bound_with_width19_two_pow_neg_107
#print axioms
  acceptedFalse_probability_le_two_pow_neg_75_plus_width19_bound

end AspisV5RefinedWidth19DeploymentBridge
