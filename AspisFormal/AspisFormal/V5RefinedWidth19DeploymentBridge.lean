import AspisFormal.V5RefinedAcceptedFalseAccounting
import AspisFormal.V5WorkNormalizedApplicabilityRepair

/-!
# Connecting the width-19 event to the refined probability bound

The refined accepted-false theorem names the exact event in which the
nineteen committed columns do not agree with the combined FRI word.  This
file records how a published PCS/MCA bound may be connected to the measured
probability of that event.

The distinction between ordinary probability and work-normalized accounting
is essential.  `powersBatchArithmeticFStar 18` contains a division by the
37-bit grind.  That division measures success per unit of grinding work; it
does not reduce the success probability of an attacker who actually performs
the grind.  The theft bound below therefore restores the factor `2^37` and
uses the conservative raw bound `2^-70`.  The work-normalized `2^-107` number
is not used as a theft probability.

A caller must still supply:

* the cited PCS/MCA hypotheses;
* membership of the virtual oracle in the required code;
* random-oracle and Fiat--Shamir applicability;
* the Rust sampling/transcript correspondence; and
* equality between the probability of the exact width-19 failure set and the
  event probability to which the cited theorem is applied.
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

/-- The width-19 arithmetic before dividing by the 37-bit work factor. -/
noncomputable def rawWidth19FStarArithmetic : ℝ :=
  powersBatchArithmeticFStar 18 * 2 ^ 37

/-- Restoring the work factor to the tighter checked arithmetic gives the
raw bound `31 / 2^75`.  This is only arithmetic; applying it to a real event
still requires the named premises below. -/
theorem raw_width19_fstar_arithmetic_le_31_div_two_pow_75 :
    rawWidth19FStarArithmetic ≤ (31 : ℝ) / 2 ^ 75 := by
  have normalized := width19_fstar_powers_batch_arithmetic_bound_tight
  have workNonnegative : (0 : ℝ) ≤ 2 ^ 37 := by positivity
  unfold rawWidth19FStarArithmetic
  calc
    powersBatchArithmeticFStar 18 * 2 ^ 37 ≤
        ((31 : ℝ) / 2 ^ 112) * 2 ^ 37 :=
      mul_le_mul_of_nonneg_right normalized workNonnegative
    _ = (31 : ℝ) / 2 ^ 75 := by norm_num

/-- Coarser power-of-two form of the raw width-19 arithmetic. -/
theorem raw_width19_fstar_arithmetic_le_two_pow_neg_70 :
    rawWidth19FStarArithmetic ≤ (1 : ℝ) / 2 ^ 70 := by
  exact raw_width19_fstar_arithmetic_le_31_div_two_pow_75.trans (by norm_num)

/-- External interface for applying the raw, non-work-normalized width-19
bound.  In contrast to `Width19FStarDeploymentPremises`, this interface does
not divide the event probability by the grind. -/
structure Width19RawDeploymentPremises {Schedule : Type*}
    (acceptedSchedule : Schedule → Prop)
    (citedMCAHypotheses : Schedule → Prop)
    (virtualOracleAndCodeMembership : Schedule → Prop)
    (randomOracleAndFiatShamirApplicability : Schedule → Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule → Prop)
    (actualEventProbability : Schedule → ℝ) : Prop where
  acceptedHasCitedMCAHypotheses :
    ∀ schedule, acceptedSchedule schedule → citedMCAHypotheses schedule
  acceptedHasVirtualOracleAndCodeMembership :
    ∀ schedule, acceptedSchedule schedule →
      virtualOracleAndCodeMembership schedule
  acceptedHasRandomOracleAndFiatShamirApplicability :
    ∀ schedule, acceptedSchedule schedule →
      randomOracleAndFiatShamirApplicability schedule
  acceptedHasRustSamplingAndTranscriptCorrespondence :
    ∀ schedule, acceptedSchedule schedule →
      rustSamplingAndTranscriptCorrespondence schedule
  citedRawEventBound :
    ∀ schedule,
      citedMCAHypotheses schedule →
      virtualOracleAndCodeMembership schedule →
      randomOracleAndFiatShamirApplicability schedule →
      rustSamplingAndTranscriptCorrespondence schedule →
      actualEventProbability schedule ≤ rawWidth19FStarArithmetic

/-- The exact information needed to apply the raw width-19 bound to one
measured failure set.  No source, code-membership, or sampling fact is
inferred from the algebraic root-count proof. -/
structure Width19MeasuredEventConnection
    {Sample Schedule : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (width19Failure : Set Sample) where
  acceptedSchedule : Schedule → Prop
  citedMCAHypotheses : Schedule → Prop
  virtualOracleAndCodeMembership : Schedule → Prop
  randomOracleAndFiatShamirApplicability : Schedule → Prop
  rustSamplingAndTranscriptCorrespondence : Schedule → Prop
  actualEventProbability : Schedule → ℝ
  deployment : Width19RawDeploymentPremises acceptedSchedule
    citedMCAHypotheses virtualOracleAndCodeMembership
    randomOracleAndFiatShamirApplicability
    rustSamplingAndTranscriptCorrespondence actualEventProbability
  selectedSchedule : Schedule
  selectedScheduleAccepted : acceptedSchedule selectedSchedule
  exactMeasuredEvent :
    measure.real width19Failure = actualEventProbability selectedSchedule

/-- The exact measured width-19 failure event is at most `31 / 2^75`,
conditional on every named published-theorem and implementation premise
above. -/
theorem width19_measured_failure_probability_le_31_div_two_pow_75
    {Sample Schedule : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (width19Failure : Set Sample)
    (connection : Width19MeasuredEventConnection
      (Schedule := Schedule) measure width19Failure) :
    measure.real width19Failure ≤ (31 : ℝ) / 2 ^ 75 := by
  have rawBound :
      connection.actualEventProbability connection.selectedSchedule ≤
        rawWidth19FStarArithmetic :=
    connection.deployment.citedRawEventBound connection.selectedSchedule
      (connection.deployment.acceptedHasCitedMCAHypotheses
        connection.selectedSchedule connection.selectedScheduleAccepted)
      (connection.deployment.acceptedHasVirtualOracleAndCodeMembership
        connection.selectedSchedule connection.selectedScheduleAccepted)
      (connection.deployment.acceptedHasRandomOracleAndFiatShamirApplicability
        connection.selectedSchedule connection.selectedScheduleAccepted)
      (connection.deployment.acceptedHasRustSamplingAndTranscriptCorrespondence
        connection.selectedSchedule connection.selectedScheduleAccepted)
  rw [connection.exactMeasuredEvent]
  exact rawBound.trans raw_width19_fstar_arithmetic_le_31_div_two_pow_75

/-- Coarser power-of-two form of the measured width-19 event bound. -/
theorem width19_measured_failure_probability_le_two_pow_neg_70
    {Sample Schedule : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (width19Failure : Set Sample)
    (connection : Width19MeasuredEventConnection
      (Schedule := Schedule) measure width19Failure) :
    measure.real width19Failure ≤ (1 : ℝ) / 2 ^ 70 := by
  exact (width19_measured_failure_probability_le_31_div_two_pow_75
    measure width19Failure connection).trans (by norm_num)

/-- Replace the visible width-19 term in any refined bound after the exact
measured-event connection has been supplied. -/
theorem refined_bound_with_width19_raw_term
    {Sample Schedule : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (target width19Failure : Set Sample)
    (remaining : ℝ)
    (base : measure.real target ≤
      (1 : ℝ) / 2 ^ 75 + measure.real width19Failure + remaining)
    (connection : Width19MeasuredEventConnection
      (Schedule := Schedule) measure width19Failure) :
    measure.real target ≤
      (1 : ℝ) / 2 ^ 75 + (31 : ℝ) / 2 ^ 75 + remaining := by
  have widthBound :=
    width19_measured_failure_probability_le_31_div_two_pow_75
      measure width19Failure connection
  linarith

/-- Accepted-false form of the refined theorem with the exact width-19 event
replaced by its conditional raw `2^-70` deployment bound. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_width19_raw_bound
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
      (1 : ℝ) / 2 ^ 75 + (31 : ℝ) / 2 ^ 75 +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.hashMerkleResidualFailure := by
  have base := acceptedFalse_probability_le_two_pow_neg_75_nonduplicated
    measure data connections projection boundary terminalCandidateFailure
    coverage terminalBound
  have widthBound :=
    width19_measured_failure_probability_le_31_div_two_pow_75
      measure data.width19Failure width19Connection
  linarith

/-- After the raw width-19 connection, the two explicit ideal terms together
are at most `2^-70`: `1/2^75 + 31/2^75 = 1/2^70`. -/
theorem acceptedFalse_probability_le_two_pow_neg_70_plus_remaining
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
      (1 : ℝ) / 2 ^ 70 +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.hashMerkleResidualFailure := by
  have exactTerms :=
    acceptedFalse_probability_le_two_pow_neg_75_plus_width19_raw_bound
      measure data connections projection boundary terminalCandidateFailure
      coverage terminalBound width19Connection
  have combine :
      (1 : ℝ) / 2 ^ 75 + (31 : ℝ) / 2 ^ 75 =
        (1 : ℝ) / 2 ^ 70 := by norm_num
  linarith

#print axioms raw_width19_fstar_arithmetic_le_31_div_two_pow_75
#print axioms raw_width19_fstar_arithmetic_le_two_pow_neg_70
#print axioms width19_measured_failure_probability_le_31_div_two_pow_75
#print axioms width19_measured_failure_probability_le_two_pow_neg_70
#print axioms refined_bound_with_width19_raw_term
#print axioms
  acceptedFalse_probability_le_two_pow_neg_75_plus_width19_raw_bound
#print axioms acceptedFalse_probability_le_two_pow_neg_70_plus_remaining

end AspisV5RefinedWidth19DeploymentBridge
