import AspisFormal.V5RefinedAcceptedFalseAccounting
import AspisFormal.V5HundredBitSecurityMargin
import AspisFormal.V5Width19CorrelatedAgreement
import AspisFormal.V5WorkNormalizedApplicabilityRepair

/-!
# Connecting the width-19 event to the refined probability bound

The refined accepted-false theorem names the event in which an eligible nearby
response has no matching decomposition into the nineteen committed words on
its own agreement support.  This file connects the proved cardinality bound
for that correlated family event to its measured probability.

The distinction between ordinary probability and work-normalized accounting
is essential.  `powersBatchArithmeticFStar 18` contains a division by the
37-bit grind.  That division measures success per unit of grinding work; it
does not reduce the success probability of an attacker who actually performs
the grind.  The theft bound below therefore restores the factor `2^37` and
uses the conservative raw bound `2^-70`.  The work-normalized `2^-107` number
is not used as a theft probability.

A caller must still supply:

* the published curve-decoding statement for the exact encoder;
* an exact identification of the accepted-false failure set with the
  correlated family event;
* the fact that the lanes, decoder family and selection rule are fixed by the
  transcript prefix before the batching challenge is sampled; and
* the prefix-conditioned Fiat--Shamir sampling bound which converts every bad
  set of the proved size into the raw numerical bound.
-/

namespace AspisV5RefinedWidth19DeploymentBridge

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5CryptographicAssumptions
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5HundredBitSecurityMargin
open AspisV5MaskedBoundaryFailureAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5RefinedAcceptedFalseAccounting
open AspisV5RefinedRawCoreAccounting
open AspisV5StatementBindingFailureAccounting
open AspisV5SumcheckTranscriptBinding
open AspisV5Width19CandidateEventBridge
open AspisV5Width19CorrelatedAgreement
open AspisV5WorkNormalizedApplicabilityRepair

/-- The width-19 arithmetic before dividing by the 37-bit work factor. -/
noncomputable def rawWidth19FStarArithmetic : ℝ :=
  powersBatchArithmeticFStar 18 * 2 ^ 37

/-- Restoring the work factor to the checked arithmetic gives the raw bound
`31 / 2^75`.  The `31` is the numerator of a convenient rational ceiling for
the displayed MCA expression; it is not a decoder-list count or union factor.
This is only arithmetic; applying it to a real event still requires the named
premises below. -/
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

/-- Tighter restored form of the maintained width-19 arithmetic. -/
theorem raw_width19_fstar_arithmetic_le_2120_div_two_pow_82 :
    rawWidth19FStarArithmetic ≤ (2120 : ℝ) / 2 ^ 82 := by
  have normalized := corrected_batch_le_2120_div_two_pow_119
  have workNonnegative : (0 : ℝ) ≤ 2 ^ 37 := by positivity
  unfold rawWidth19FStarArithmetic
  calc
    powersBatchArithmeticFStar 18 * 2 ^ 37 ≤
        ((2120 : ℝ) / 2 ^ 119) * 2 ^ 37 :=
      mul_le_mul_of_nonneg_right normalized workNonnegative
    _ = (2120 : ℝ) / 2 ^ 82 := by norm_num

/-- Coarser power-of-two form of the raw width-19 arithmetic. -/
theorem raw_width19_fstar_arithmetic_le_two_pow_neg_70 :
    rawWidth19FStarArithmetic ≤ (1 : ℝ) / 2 ^ 70 := by
  exact raw_width19_fstar_arithmetic_le_31_div_two_pow_75.trans (by norm_num)

/-! ## Exact initial-code domain and support threshold -/

/-- Expanding any accepted-fibre set larger than 6082 to all four symbols per
fibre produces a support larger than the initial circle-code cap 24328.  This
prevents the 6082 fibre threshold from being fed directly to a theorem over
the `2^19` received-word domain. -/
theorem expanded_initial_fibres_exceed_width19_agreement_cap
    (support : Finset (Fin 131072)) (hdense : 6082 < support.card) :
    agreementCap0 < (expandInitialFibres support).card := by
  rw [expandInitialFibres_card]
  unfold agreementCap0
  omega

/-- The exact information needed to turn the correlated-agreement cardinality
theorem into a measured failure bound.

Everything indexed only by `Prefix` is fixed before `gammaAt` is sampled.
`eligible` and `support` may inspect the challenge, as the decoder response
may do, but the functions defining them cannot inspect any other part of the
sample.  `exactFailure` is the implementation/extraction connection.
`prefixConditionedSampling` is the remaining Fiat--Shamir and numerical
sampling premise; unlike the former interface, it must work for every
prefix-indexed bad set satisfying the proved cardinality cap. -/
structure Width19MeasuredEventConnection
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    (measure : Measure Sample) (width19Failure : Set Sample) where
  prefixAt : Sample → Prefix
  gammaAt : Sample → K
  encoder : Prefix → Width19LinearEncoder K
  challengeThreshold : Prefix → Nat
  lanes : Prefix → Fin 19 → Width19ReceivedCoordinate → K
  eligible : Prefix → K → Candidate → Prop
  candidateMessage : Prefix → Candidate → Width19CoefficientMessage K
  support : Prefix → K → Candidate → Finset Width19ReceivedCoordinate
  curveDecoding : ∀ history,
    Width19CurveDecodable (encoder history) agreementCap0
      (challengeThreshold history)
  exactFailure : ∀ sample,
    sample ∈ width19Failure ↔
      gammaAt sample ∈ width19CandidateFamilyBadChallenges
        (encoder (prefixAt sample)) agreementCap0
        (lanes (prefixAt sample)) (eligible (prefixAt sample))
        (candidateMessage (prefixAt sample)) (support (prefixAt sample))
  prefixConditionedSampling : ∀ badAt : Prefix → Finset K,
    (∀ history, (badAt history).card ≤ challengeThreshold history) →
    measure.real {sample |
      gammaAt sample ∈ badAt (prefixAt sample)} ≤ rawWidth19FStarArithmetic

/-- The exact prefix-indexed bad-challenge set used by a measured
connection. -/
noncomputable def Width19MeasuredEventConnection.badChallenges
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    {measure : Measure Sample} {width19Failure : Set Sample}
    (connection : Width19MeasuredEventConnection
      (Prefix := Prefix) (K := K) (Candidate := Candidate)
      measure width19Failure)
    (history : Prefix) : Finset K :=
  width19CandidateFamilyBadChallenges
    (connection.encoder history) agreementCap0
    (connection.lanes history) (connection.eligible history)
    (connection.candidateMessage history) (connection.support history)

/-- The correlated family theorem supplies the cardinality premise required
by prefix-conditioned sampling.  There is no decoder-list-size factor. -/
theorem Width19MeasuredEventConnection.badChallenges_card_le
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    {measure : Measure Sample} {width19Failure : Set Sample}
    (connection : Width19MeasuredEventConnection
      (Prefix := Prefix) (K := K) (Candidate := Candidate)
      measure width19Failure)
    (history : Prefix) :
    (connection.badChallenges history).card ≤
      connection.challengeThreshold history := by
  exact width19_candidate_family_bad_challenges_card_le
    (connection.encoder history) agreementCap0
    (connection.challengeThreshold history) (connection.curveDecoding history)
    (connection.lanes history) (connection.eligible history)
    (connection.candidateMessage history) (connection.support history)

/-- Raw probability for one completed attempt.  The exact correlated family
failure is at most `2120 / 2^82`, conditional on the curve-decoding,
implementation/extraction and prefix-conditioned sampling premises above.
This is an ordinary completed-attempt probability; it is not the separate
work-normalized 100-bit computational endpoint. -/
theorem width19_completed_attempt_failure_probability_le_2120_div_two_pow_82
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    (measure : Measure Sample) (width19Failure : Set Sample)
    (connection : Width19MeasuredEventConnection
      (Prefix := Prefix) (K := K) (Candidate := Candidate)
      measure width19Failure) :
    measure.real width19Failure ≤ (2120 : ℝ) / 2 ^ 82 := by
  have rawBound := connection.prefixConditionedSampling
    connection.badChallenges connection.badChallenges_card_le
  have eventEquality : width19Failure = {sample |
      connection.gammaAt sample ∈
        connection.badChallenges (connection.prefixAt sample)} := by
    ext sample
    exact connection.exactFailure sample
  rw [eventEquality]
  exact rawBound.trans raw_width19_fstar_arithmetic_le_2120_div_two_pow_82

/-- Older, looser ceiling retained for compatibility. -/
theorem width19_completed_attempt_failure_probability_le_31_div_two_pow_75
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    (measure : Measure Sample) (width19Failure : Set Sample)
    (connection : Width19MeasuredEventConnection
      (Prefix := Prefix) (K := K) (Candidate := Candidate)
      measure width19Failure) :
    measure.real width19Failure ≤ (31 : ℝ) / 2 ^ 75 :=
  (width19_completed_attempt_failure_probability_le_2120_div_two_pow_82
    measure width19Failure connection).trans (by norm_num)

/-- Backwards-compatible name for the raw completed-attempt theorem. -/
theorem width19_measured_failure_probability_le_31_div_two_pow_75
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    (measure : Measure Sample) (width19Failure : Set Sample)
    (connection : Width19MeasuredEventConnection
      (Prefix := Prefix) (K := K) (Candidate := Candidate)
      measure width19Failure) :
    measure.real width19Failure ≤ (31 : ℝ) / 2 ^ 75 :=
  width19_completed_attempt_failure_probability_le_31_div_two_pow_75
    measure width19Failure connection

/-- Coarser power-of-two form of the measured width-19 event bound. -/
theorem width19_measured_failure_probability_le_two_pow_neg_70
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    (measure : Measure Sample) (width19Failure : Set Sample)
    (connection : Width19MeasuredEventConnection
      (Prefix := Prefix) (K := K) (Candidate := Candidate)
      measure width19Failure) :
    measure.real width19Failure ≤ (1 : ℝ) / 2 ^ 70 := by
  exact (width19_completed_attempt_failure_probability_le_2120_div_two_pow_82
    measure width19Failure connection).trans (by norm_num)

/-- Replace the visible width-19 term in any refined bound after the exact
measured-event connection has been supplied. -/
theorem refined_bound_with_width19_raw_term
    {Sample Prefix K Candidate : Type*}
    [MeasurableSpace Sample]
    [Field K] [Fintype K] [DecidableEq K]
    [Nonempty Candidate]
    (measure : Measure Sample) (target width19Failure : Set Sample)
    (remaining : ℝ)
    (base : measure.real target ≤
      (1 : ℝ) / 2 ^ 75 + measure.real width19Failure + remaining)
    (connection : Width19MeasuredEventConnection
      (Prefix := Prefix) (K := K) (Candidate := Candidate)
      measure width19Failure) :
    measure.real target ≤
      (1 : ℝ) / 2 ^ 75 + (2120 : ℝ) / 2 ^ 82 + remaining := by
  have widthBound :=
    width19_completed_attempt_failure_probability_le_2120_div_two_pow_82
      measure width19Failure connection
  linarith

/-- Accepted-false form of the refined theorem with the exact width-19 event
replaced by its conditional raw `2^-70` deployment bound. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_width19_raw_bound
    {Run Coins K Public Root WidthPrefix WidthCandidate : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    [Nonempty WidthCandidate]
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
      (Prefix := WidthPrefix) (K := K) (Candidate := WidthCandidate)
      measure data.width19Failure) :
    measure.real data.base.acceptedFalse ≤
      (1 : ℝ) / 2 ^ 75 + (2120 : ℝ) / 2 ^ 82 +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.hashMerkleResidualFailure := by
  have base := acceptedFalse_probability_le_two_pow_neg_75_nonduplicated
    measure data connections projection boundary terminalCandidateFailure
    coverage terminalBound
  have widthBound :=
    width19_completed_attempt_failure_probability_le_2120_div_two_pow_82
      measure data.width19Failure width19Connection
  linarith

/-- After the raw width-19 connection, the two explicit ideal terms together
are at most `2^-70`.  The theorem above retains the tighter width-19 term;
this result is only the convenient power-of-two presentation. -/
theorem acceptedFalse_probability_le_two_pow_neg_70_plus_remaining
    {Run Coins K Public Root WidthPrefix WidthCandidate : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    [Nonempty WidthCandidate]
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
      (Prefix := WidthPrefix) (K := K) (Candidate := WidthCandidate)
      measure data.width19Failure) :
    measure.real data.base.acceptedFalse ≤
      (1 : ℝ) / 2 ^ 70 +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.hashMerkleResidualFailure := by
  have exactTerms :=
    acceptedFalse_probability_le_two_pow_neg_75_plus_width19_raw_bound
      measure data connections projection boundary terminalCandidateFailure
      coverage terminalBound width19Connection
  have combine :
      (1 : ℝ) / 2 ^ 75 + (2120 : ℝ) / 2 ^ 82 ≤
        (1 : ℝ) / 2 ^ 70 := by norm_num
  linarith

#print axioms raw_width19_fstar_arithmetic_le_31_div_two_pow_75
#print axioms raw_width19_fstar_arithmetic_le_2120_div_two_pow_82
#print axioms raw_width19_fstar_arithmetic_le_two_pow_neg_70
#print axioms expanded_initial_fibres_exceed_width19_agreement_cap
#print axioms
  width19_completed_attempt_failure_probability_le_2120_div_two_pow_82
#print axioms
  width19_completed_attempt_failure_probability_le_31_div_two_pow_75
#print axioms width19_measured_failure_probability_le_31_div_two_pow_75
#print axioms width19_measured_failure_probability_le_two_pow_neg_70
#print axioms refined_bound_with_width19_raw_term
#print axioms
  acceptedFalse_probability_le_two_pow_neg_75_plus_width19_raw_bound
#print axioms acceptedFalse_probability_le_two_pow_neg_70_plus_remaining

end AspisV5RefinedWidth19DeploymentBridge
