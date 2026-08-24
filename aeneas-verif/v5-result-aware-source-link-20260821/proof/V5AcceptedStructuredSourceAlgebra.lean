import V5AcceptedStructuredSourceSchedule

/-!
# Four cached source-schedule fold stages

Each theorem below checks one accepted accumulator round.  Keeping the four
rounds separate prevents Lean from expanding the entire eleven-component
schedule while elaborating one proof term.
-/

namespace AspisV5AcceptedStructuredTerminalSchedule

open Aeneas Aeneas.Std Result
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedRelationRoundInversion
open AspisV5RelationAcceptanceSourceProof
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationStressSourceBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

variable {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
variable {finalPolynomial : Array RawQM31 4#usize}
variable {alphas : Array RawQM31 4#usize}
variable {kappa inactiveClaim : RawQM31}
variable {roundChallenges : Array RawQM31 10#usize}
variable {preparedClaims :
  V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
variable {terminalClaim : RawQM31}

/-- The initial three multilinears and the two first-round tensors pass
through the first production challenge exactly. -/
theorem acceptedStructuredSourceSchedule_weights1
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : CanonicalQM31 kappa) :
    sourceMainWeights1 (acceptedStructuredSourceSchedule schedule hkappa)
        (acceptedAccumulatorChallenges trace schedule) =
      functionSum (acceptedStructuredAfter0 schedule hkappa) := by
  have mixed0 := mixedFunctionSumWithAcceptedTensors (n := 256)
    (acceptedStructuredInitialFunctions schedule hkappa)
    schedule.rounds.round0.sample0.mix schedule.rounds.round0.sample1.mix
    (acceptedUnitTensor5 schedule.round0Schedule.firstFactors)
    (acceptedUnitTensor5 schedule.round0Schedule.secondFactors)
    (acceptedScaledTensor5 schedule.rounds.round0.sample0.mix
      schedule.round0Schedule.firstFactors)
    (acceptedScaledTensor5 schedule.rounds.round0.sample1.mix
      schedule.round0Schedule.secondFactors)
    (acceptedMix_times_unitTensor5 schedule.rounds.round0.sample0.mix
      schedule.round0Schedule.firstFactors)
    (acceptedMix_times_unitTensor5 schedule.rounds.round0.sample1.mix
      schedule.round0Schedule.secondFactors)
  unfold sourceMainWeights1 acceptedStructuredSourceSchedule
    acceptedAccumulatorChallenges
  simp only [AspisV5Tag67RelationListInclusion.round0Block]
  rw [mixed0, dualWeightFoldLayer_functionSum]
  rfl

/-- The second pair of tensors and the second production challenge extend
the exact source sum. -/
theorem acceptedStructuredSourceSchedule_weights2
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : CanonicalQM31 kappa) :
    sourceMainWeights2 (acceptedStructuredSourceSchedule schedule hkappa)
        (acceptedAccumulatorChallenges trace schedule) =
      functionSum (acceptedStructuredAfter1 schedule hkappa) := by
  have mixed1 := mixedFunctionSumWithAcceptedTensors (n := 64)
    (acceptedStructuredAfter0 schedule hkappa)
    schedule.rounds.round1.sample0.mix schedule.rounds.round1.sample1.mix
    (acceptedUnitTensor4 schedule.round1Schedule.firstFactors)
    (acceptedUnitTensor4 schedule.round1Schedule.secondFactors)
    (acceptedScaledTensor4 schedule.rounds.round1.sample0.mix
      schedule.round1Schedule.firstFactors)
    (acceptedScaledTensor4 schedule.rounds.round1.sample1.mix
      schedule.round1Schedule.secondFactors)
    (acceptedMix_times_unitTensor4 schedule.rounds.round1.sample0.mix
      schedule.round1Schedule.firstFactors)
    (acceptedMix_times_unitTensor4 schedule.rounds.round1.sample1.mix
      schedule.round1Schedule.secondFactors)
  unfold sourceMainWeights2
  rw [acceptedStructuredSourceSchedule_weights1 trace schedule hkappa]
  unfold acceptedStructuredSourceSchedule acceptedAccumulatorChallenges
  simp only [AspisV5Tag67RelationListInclusion.round1Block]
  rw [mixed1, dualWeightFoldLayer_functionSum]
  rfl

/-- The third pair of tensors and challenge extend the exact source sum. -/
theorem acceptedStructuredSourceSchedule_weights3
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : CanonicalQM31 kappa) :
    sourceMainWeights3 (acceptedStructuredSourceSchedule schedule hkappa)
        (acceptedAccumulatorChallenges trace schedule) =
      functionSum (acceptedStructuredAfter2 schedule hkappa) := by
  have mixed2 := mixedFunctionSumWithAcceptedTensors (n := 16)
    (acceptedStructuredAfter1 schedule hkappa)
    schedule.rounds.round2.sample0.mix schedule.rounds.round2.sample1.mix
    (acceptedUnitTensor3 schedule.round2Schedule.firstFactors)
    (acceptedUnitTensor3 schedule.round2Schedule.secondFactors)
    (acceptedScaledTensor3 schedule.rounds.round2.sample0.mix
      schedule.round2Schedule.firstFactors)
    (acceptedScaledTensor3 schedule.rounds.round2.sample1.mix
      schedule.round2Schedule.secondFactors)
    (acceptedMix_times_unitTensor3 schedule.rounds.round2.sample0.mix
      schedule.round2Schedule.firstFactors)
    (acceptedMix_times_unitTensor3 schedule.rounds.round2.sample1.mix
      schedule.round2Schedule.secondFactors)
  unfold sourceMainWeights3
  rw [acceptedStructuredSourceSchedule_weights2 trace schedule hkappa]
  unfold acceptedStructuredSourceSchedule acceptedAccumulatorChallenges
  simp only [AspisV5Tag67RelationListInclusion.round2Block]
  rw [mixed2, dualWeightFoldLayer_functionSum]
  rfl

/-- The complete source schedule is the pointwise sum of all eleven
structured terminal journeys. -/
theorem acceptedStructuredSourceSchedule_finalWeights
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : CanonicalQM31 kappa) :
    sourceMainFinalWeights (acceptedStructuredSourceSchedule schedule hkappa)
        (acceptedAccumulatorChallenges trace schedule) =
      functionSum (acceptedStructuredAfter3 schedule hkappa) := by
  have mixed3 := mixedFunctionSumWithAcceptedTensors (n := 4)
    (acceptedStructuredAfter2 schedule hkappa)
    schedule.rounds.round3.sample0.mix schedule.rounds.round3.sample1.mix
    (acceptedUnitTensor2 schedule.round3Schedule.firstFactors)
    (acceptedUnitTensor2 schedule.round3Schedule.secondFactors)
    (acceptedScaledTensor2 schedule.rounds.round3.sample0.mix
      schedule.round3Schedule.firstFactors)
    (acceptedScaledTensor2 schedule.rounds.round3.sample1.mix
      schedule.round3Schedule.secondFactors)
    (acceptedMix_times_unitTensor2 schedule.rounds.round3.sample0.mix
      schedule.round3Schedule.firstFactors)
    (acceptedMix_times_unitTensor2 schedule.rounds.round3.sample1.mix
      schedule.round3Schedule.secondFactors)
  unfold sourceMainFinalWeights
  rw [acceptedStructuredSourceSchedule_weights3 trace schedule hkappa]
  unfold acceptedStructuredSourceSchedule acceptedAccumulatorChallenges
  simp only [AspisV5Tag67RelationListInclusion.round3Block]
  rw [mixed3, dualWeightFoldLayer_functionSum]
  rfl

#print axioms acceptedStructuredSourceSchedule_weights1
#print axioms acceptedStructuredSourceSchedule_weights2
#print axioms acceptedStructuredSourceSchedule_weights3
#print axioms acceptedStructuredSourceSchedule_finalWeights

end AspisV5AcceptedStructuredTerminalSchedule
