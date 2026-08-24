import V5AcceptedRelationRoundInversion
import V5RelationCallerInitialComponents
import V5RelationFullTensorAppend

/-!
# Exact accepted relation weight schedule

This module exposes the component list manipulated by the accepted production
relation execution.  Preparation contributes four components.  Each of the
four rounds appends the two tensor components selected by its two accepted
OOD samples, and the round fold preserves that list length.
-/

namespace AspisV5AcceptedAccumulatorSchedule

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationAcceptanceSourceProof
open AspisV5AcceptedRelationRoundInversion
open AspisV5RelationFullTensorAppend
open AspisV5RelationFullLinkedAccumulatorBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev FullComponent :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator

private theorem usizeMaxAboveReleasedComponentCount :
    13 < Std.Usize.max := by
  rw [Std.Usize.max, Std.Usize.numBits, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with bits | bits <;>
    rw [bits] <;> norm_num

/-- Exact tensor appends and final fold made by one accepted two-sample
round. -/
structure AcceptedRoundTensorSchedule {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (additive nextAdditive : A)
    (round : Std.Usize) (alpha : RawQM31)
    (weights0 nextWeights : FullWeights)
    (claim0 nextClaim : RawQM31)
    (trace : AcceptedTwoSampleRoundExecution additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim) :
    Type where
  firstFactors : alloc.vec.Vec RawQM31
  secondFactors : alloc.vec.Vec RawQM31
  firstAppendRun :
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
        weights0 trace.sample0.mix firstFactors =
      .ok (.Ok (), trace.weights1)
  secondAppendRun :
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
        trace.weights1 trace.sample1.mix secondFactors =
      .ok (.Ok (), trace.weights2)
  firstShape :
    trace.weights1.components.val = weights0.components.val ++
      [.Tensor trace.sample0.mix firstFactors]
  secondShape :
    trace.weights2.components.val = weights0.components.val ++
      [.Tensor trace.sample0.mix firstFactors,
       .Tensor trace.sample1.mix secondFactors]
  foldRun :
    aspis_core.sumcheck.WeightAccumulator.fold trace.weights2 alpha =
      .ok nextWeights
  outputLength :
    nextWeights.components.val.length = weights0.components.val.length + 2

/-- The accepted branch itself selects either the circle or line append.
Both branches expose the same exact two-component list extension. -/
theorem acceptedRoundExposesTensorSchedule {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (additive nextAdditive : A)
    (round : Std.Usize) (alpha : RawQM31)
    (weights0 nextWeights : FullWeights)
    (claim0 nextClaim : RawQM31)
    (trace : AcceptedTwoSampleRoundExecution additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim)
    (twoAppendCapacity :
      weights0.components.val.length + 1 < Std.Usize.max) :
    Nonempty (AcceptedRoundTensorSchedule additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim
      trace) := by
  have firstCapacity : weights0.components.val.length < Std.Usize.max := by
    omega
  have exposeFirst : ∃ factors,
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
          weights0 trace.sample0.mix factors =
        .ok (.Ok (), trace.weights1) ∧
      trace.weights1.components.val = weights0.components.val ++
        [.Tensor trace.sample0.mix factors] := by
    by_cases roundZero : round = 0#usize
    · obtain ⟨point, _, appendRun⟩ := trace.sample0WeightUpdate.circle roundZero
      obtain ⟨factors, commonRun, _, shape⟩ :=
        addCircleTensorSuccessExposesFactors weights0 trace.weights1
          trace.sample0.mix point firstCapacity appendRun
      exact ⟨factors, commonRun, shape⟩
    · obtain ⟨_, lineValue, _, _, appendRun⟩ :=
        trace.sample0WeightUpdate.line roundZero
      obtain ⟨factors, commonRun, _, shape⟩ :=
        addLineTensorSuccessExposesFactors weights0 trace.weights1
          trace.sample0.mix lineValue firstCapacity appendRun
      exact ⟨factors, commonRun, shape⟩
  obtain ⟨firstFactors, firstRun, firstShape⟩ := exposeFirst
  have secondCapacity :
      trace.weights1.components.val.length < Std.Usize.max := by
    rw [firstShape]
    simpa using twoAppendCapacity
  have exposeSecond : ∃ factors,
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
          trace.weights1 trace.sample1.mix factors =
        .ok (.Ok (), trace.weights2) ∧
      trace.weights2.components.val = trace.weights1.components.val ++
        [.Tensor trace.sample1.mix factors] := by
    by_cases roundZero : round = 0#usize
    · obtain ⟨point, _, appendRun⟩ := trace.sample1WeightUpdate.circle roundZero
      obtain ⟨factors, commonRun, _, shape⟩ :=
        addCircleTensorSuccessExposesFactors trace.weights1 trace.weights2
          trace.sample1.mix point secondCapacity appendRun
      exact ⟨factors, commonRun, shape⟩
    · obtain ⟨_, lineValue, _, _, appendRun⟩ :=
        trace.sample1WeightUpdate.line roundZero
      obtain ⟨factors, commonRun, _, shape⟩ :=
        addLineTensorSuccessExposesFactors trace.weights1 trace.weights2
          trace.sample1.mix lineValue secondCapacity appendRun
      exact ⟨factors, commonRun, shape⟩
  obtain ⟨secondFactors, secondRun, secondRawShape⟩ := exposeSecond
  have secondShape :
      trace.weights2.components.val = weights0.components.val ++
        [.Tensor trace.sample0.mix firstFactors,
         .Tensor trace.sample1.mix secondFactors] := by
    rw [secondRawShape, firstShape]
    simp only [List.append_assoc]
    rfl
  have foldRun := trace.polynomial.scalar.weightFoldRun
  have foldLength := fullFoldSuccessPreservesComponentLength
    trace.weights2 nextWeights alpha foldRun
  have outputLength :
      nextWeights.components.val.length = weights0.components.val.length + 2 := by
    rw [foldLength, secondShape]
    simp
  exact ⟨{
    firstFactors := firstFactors
    secondFactors := secondFactors
    firstAppendRun := firstRun
    secondAppendRun := secondRun
    firstShape := firstShape
    secondShape := secondShape
    foldRun := foldRun
    outputLength := outputLength }⟩

/-- The complete accepted relation call exposes the exact four prepared
components followed by the two real tensor appends in each of its four
rounds.  The resulting component counts are therefore 4, 6, 8, 10, and 12.
-/
structure AcceptedFourRoundAccumulatorSchedule
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    Type where
  rounds : AcceptedFourRoundExecution trace
  sourceRelation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation
  prepareTrace :
    AspisV5RelationPrepareLogLenProof.Prepare.PrepareRelationArithmeticTrace
      (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 kappa)
      (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 inactiveClaim)
      (AspisV5RelationPrepareCanonicalProof.callerToPrepareClaims preparedClaims)
      sourceRelation
  initialMapped :
    trace.calls.relation.weights.components.val =
      sourceRelation.weights.components.val.map
        AspisV5RelationCallerInitialComponents.prepareComponentToCaller
  initialExact :
    sourceRelation.weights.components.val =
      [V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Multilinear
          V5RelationPrepareGenerated.aspis_core.field.QM31.ONE
          prepareTrace.pointVec0,
       V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Multilinear
          (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 kappa)
          prepareTrace.pointVec1,
       V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Multilinear
          prepareTrace.kappa2 prepareTrace.pointVec2,
       V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Grouped64x16BinaryDeferred
          prepareTrace.groupedRows prepareTrace.groupedMasks none
          (alloc.vec.Vec.new V5RelationPrepareGenerated.aspis_core.field.QM31)]
  round0Schedule : AcceptedRoundTensorSchedule productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.calls.compact
    trace.additive1 0#usize (acceptedAlphaAt alphas 0)
    trace.calls.relation.weights trace.weights1
    trace.calls.relation.relation_value trace.claim1 rounds.round0
  round1Schedule : AcceptedRoundTensorSchedule productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.additive1
    trace.additive2 1#usize (acceptedAlphaAt alphas 1)
    trace.weights1 trace.weights2 trace.claim1 trace.claim2 rounds.round1
  round2Schedule : AcceptedRoundTensorSchedule productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.additive2
    trace.additive3 2#usize (acceptedAlphaAt alphas 2)
    trace.weights2 trace.weights3 trace.claim2 trace.claim3 rounds.round2
  round3Schedule : AcceptedRoundTensorSchedule productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.additive3
    trace.additive4 3#usize (acceptedAlphaAt alphas 3)
    trace.weights3 trace.weights4 trace.claim3 trace.claim4 rounds.round3
  initialLength : trace.calls.relation.weights.components.val.length = 4
  round0Length : trace.weights1.components.val.length = 6
  round1Length : trace.weights2.components.val.length = 8
  round2Length : trace.weights3.components.val.length = 10
  round3Length : trace.weights4.components.val.length = 12

/-- Build the complete accumulator schedule around a specified accepted
four-round execution.  Keeping the execution explicit lets downstream proofs
share one decoder witness with the scalar relation projection. -/
theorem acceptedFourRoundExecutionExposesAccumulatorSchedule
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (rounds : AcceptedFourRoundExecution trace) :
    ∃ schedule : AcceptedFourRoundAccumulatorSchedule trace,
      schedule.rounds = rounds := by
  obtain ⟨sourceRelation, prepareTrace, initialMapped, initialExact⟩ :=
    AspisV5RelationCallerInitialComponents.callerPrepareSuccessExposesSourceComponents
      parsed kappa inactiveClaim preparedClaims trace.calls.relation
      trace.calls.ignoredAlphas trace.calls.denseScale trace.calls.prepareSuccess
  have initialLength :
      trace.calls.relation.weights.components.val.length = 4 := by
    calc
      trace.calls.relation.weights.components.val.length =
          (sourceRelation.weights.components.val.map
            AspisV5RelationCallerInitialComponents.prepareComponentToCaller).length :=
        congrArg List.length initialMapped
      _ = sourceRelation.weights.components.val.length := by simp
      _ = 4 := by simpa using congrArg List.length initialExact
  have maxRoom := usizeMaxAboveReleasedComponentCount
  have round0Capacity :
      trace.calls.relation.weights.components.val.length + 1 <
        Std.Usize.max := by
    rw [initialLength]
    omega
  obtain ⟨round0Schedule⟩ := acceptedRoundExposesTensorSchedule
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.calls.compact trace.additive1 0#usize (acceptedAlphaAt alphas 0)
    trace.calls.relation.weights trace.weights1
    trace.calls.relation.relation_value trace.claim1 rounds.round0
    round0Capacity
  have round0Length : trace.weights1.components.val.length = 6 := by
    rw [round0Schedule.outputLength, initialLength]
  have round1Capacity : trace.weights1.components.val.length + 1 <
      Std.Usize.max := by
    rw [round0Length]
    omega
  obtain ⟨round1Schedule⟩ := acceptedRoundExposesTensorSchedule
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.additive1 trace.additive2 1#usize (acceptedAlphaAt alphas 1)
    trace.weights1 trace.weights2 trace.claim1 trace.claim2 rounds.round1
    round1Capacity
  have round1Length : trace.weights2.components.val.length = 8 := by
    rw [round1Schedule.outputLength, round0Length]
  have round2Capacity : trace.weights2.components.val.length + 1 <
      Std.Usize.max := by
    rw [round1Length]
    omega
  obtain ⟨round2Schedule⟩ := acceptedRoundExposesTensorSchedule
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.additive2 trace.additive3 2#usize (acceptedAlphaAt alphas 2)
    trace.weights2 trace.weights3 trace.claim2 trace.claim3 rounds.round2
    round2Capacity
  have round2Length : trace.weights3.components.val.length = 10 := by
    rw [round2Schedule.outputLength, round1Length]
  have round3Capacity : trace.weights3.components.val.length + 1 <
      Std.Usize.max := by
    rw [round2Length]
    omega
  obtain ⟨round3Schedule⟩ := acceptedRoundExposesTensorSchedule
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.additive3 trace.additive4 3#usize (acceptedAlphaAt alphas 3)
    trace.weights3 trace.weights4 trace.claim3 trace.claim4 rounds.round3
    round3Capacity
  have round3Length : trace.weights4.components.val.length = 12 := by
    rw [round3Schedule.outputLength, round2Length]
  exact ⟨{
    rounds := rounds
    sourceRelation := sourceRelation
    prepareTrace := prepareTrace
    initialMapped := initialMapped
    initialExact := initialExact
    round0Schedule := round0Schedule
    round1Schedule := round1Schedule
    round2Schedule := round2Schedule
    round3Schedule := round3Schedule
    initialLength := initialLength
    round0Length := round0Length
    round1Length := round1Length
    round2Length := round2Length
    round3Length := round3Length }, rfl⟩

/-- Existence wrapper for clients which do not need to name the selected
four-round execution. -/
theorem acceptedFullTraceExposesAccumulatorSchedule
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    Nonempty (AcceptedFourRoundAccumulatorSchedule trace) := by
  obtain ⟨rounds⟩ := accepted_full_trace_exposes_four_round_executions trace
  obtain ⟨schedule, _⟩ :=
    acceptedFourRoundExecutionExposesAccumulatorSchedule trace rounds
  exact ⟨schedule⟩

#print axioms acceptedRoundExposesTensorSchedule
#print axioms acceptedFourRoundExecutionExposesAccumulatorSchedule
#print axioms acceptedFullTraceExposesAccumulatorSchedule

end AspisV5AcceptedAccumulatorSchedule
