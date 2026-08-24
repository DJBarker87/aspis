import V5AcceptedAccumulatorSchedule

/-!
# Every accepted relation component follows the extracted fold dispatcher

The exact list schedule is lifted here to a whole-accumulator invariant.  All
four prepared components and all eight appended tensors are in the released
constructor family, and every successful round fold maps every list cell
through the corresponding extracted component helper at the same index.
-/

namespace AspisV5AcceptedAccumulatorTraversal

open Aeneas Aeneas.Std Result
open AspisV5RelationAcceptanceSourceProof
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedAccumulatorSchedule
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedSupportedFold

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator

def AllReleased (weights : FullWeights) : Prop :=
  ∀ index, index < weights.components.val.length →
    ReleasedComponent
      (componentToLinked weights.components.val[index]!)

private theorem initialAllReleased
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
    (schedule : AcceptedFourRoundAccumulatorSchedule trace) :
    AllReleased trace.calls.relation.weights := by
  intro index bound
  have indexSmall : index < 4 := by simpa [schedule.initialLength] using bound
  have indexCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
    omega
  rw [schedule.initialMapped, schedule.initialExact]
  rcases indexCases with rfl | rfl | rfl | rfl <;>
    simp [AspisV5RelationCallerInitialComponents.prepareComponentToCaller,
      componentToLinked, ReleasedComponent,
      AspisV5RelationCallerInitialComponents.prepareVecToCaller]

private theorem appendTensorPreservesAllReleased
    (weights output : FullWeights) (scale : RawQM31)
    (factors : alloc.vec.Vec RawQM31)
    (released : AllReleased weights)
    (shape : output.components.val = weights.components.val ++
      [.Tensor scale factors]) :
    AllReleased output := by
  intro index bound
  rw [shape] at bound ⊢
  by_cases old : index < weights.components.val.length
  · rw [List.getElem!_append_left _ _ index old]
    exact released index old
  · have exactIndex : index = weights.components.val.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst index
    simp [componentToLinked, ReleasedComponent]

private theorem foldPreservesAllReleased
    (weights output : FullWeights) (alpha : RawQM31)
    (released : AllReleased weights)
    (success :
      aspis_core.sumcheck.WeightAccumulator.fold weights alpha = .ok output) :
    AllReleased output := by
  intro index outputBound
  have lengthExact := fullFoldSuccessPreservesComponentLength
    weights output alpha success
  have inputBound : index < weights.components.val.length := by
    omega
  obtain ⟨_, _, _, _, componentOut, _, _, _, _, _, _, outputCell,
      outputReleased⟩ :=
    fullFoldSuccessExposesLinkedComponent weights output alpha index inputBound
      (released index inputBound) success
  change ReleasedComponent
    (componentToLinked output.components.val[index]!)
  exact Eq.mpr (congrArg ReleasedComponent outputCell) outputReleased

/-- Every component in the accepted terminal main accumulator is the same
released component carried at the same index through the exact four fold
traversals.  Combined with the exact schedule theorem, this covers precisely
the original four cells and the eight production tensor appends. -/
theorem acceptedTerminalAccumulatorAllReleased
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
    AllReleased trace.weights4 := by
  obtain ⟨schedule⟩ := acceptedFullTraceExposesAccumulatorSchedule trace
  have initial := initialAllReleased trace schedule
  have round0AfterFirst := appendTensorPreservesAllReleased
    trace.calls.relation.weights schedule.rounds.round0.weights1
    schedule.rounds.round0.sample0.mix schedule.round0Schedule.firstFactors
    initial schedule.round0Schedule.firstShape
  have round0BeforeFold := appendTensorPreservesAllReleased
    schedule.rounds.round0.weights1 schedule.rounds.round0.weights2
    schedule.rounds.round0.sample1.mix schedule.round0Schedule.secondFactors
    round0AfterFirst (by
      rw [schedule.round0Schedule.secondShape,
        schedule.round0Schedule.firstShape]
      simp only [List.append_assoc]
      rfl)
  have afterRound0 := foldPreservesAllReleased
    schedule.rounds.round0.weights2 trace.weights1
    (acceptedAlphaAt alphas 0) round0BeforeFold
    schedule.round0Schedule.foldRun
  have round1AfterFirst := appendTensorPreservesAllReleased
    trace.weights1 schedule.rounds.round1.weights1
    schedule.rounds.round1.sample0.mix schedule.round1Schedule.firstFactors
    afterRound0 schedule.round1Schedule.firstShape
  have round1BeforeFold := appendTensorPreservesAllReleased
    schedule.rounds.round1.weights1 schedule.rounds.round1.weights2
    schedule.rounds.round1.sample1.mix schedule.round1Schedule.secondFactors
    round1AfterFirst (by
      rw [schedule.round1Schedule.secondShape,
        schedule.round1Schedule.firstShape]
      simp only [List.append_assoc]
      rfl)
  have afterRound1 := foldPreservesAllReleased
    schedule.rounds.round1.weights2 trace.weights2
    (acceptedAlphaAt alphas 1) round1BeforeFold
    schedule.round1Schedule.foldRun
  have round2AfterFirst := appendTensorPreservesAllReleased
    trace.weights2 schedule.rounds.round2.weights1
    schedule.rounds.round2.sample0.mix schedule.round2Schedule.firstFactors
    afterRound1 schedule.round2Schedule.firstShape
  have round2BeforeFold := appendTensorPreservesAllReleased
    schedule.rounds.round2.weights1 schedule.rounds.round2.weights2
    schedule.rounds.round2.sample1.mix schedule.round2Schedule.secondFactors
    round2AfterFirst (by
      rw [schedule.round2Schedule.secondShape,
        schedule.round2Schedule.firstShape]
      simp only [List.append_assoc]
      rfl)
  have afterRound2 := foldPreservesAllReleased
    schedule.rounds.round2.weights2 trace.weights3
    (acceptedAlphaAt alphas 2) round2BeforeFold
    schedule.round2Schedule.foldRun
  have round3AfterFirst := appendTensorPreservesAllReleased
    trace.weights3 schedule.rounds.round3.weights1
    schedule.rounds.round3.sample0.mix schedule.round3Schedule.firstFactors
    afterRound2 schedule.round3Schedule.firstShape
  have round3BeforeFold := appendTensorPreservesAllReleased
    schedule.rounds.round3.weights1 schedule.rounds.round3.weights2
    schedule.rounds.round3.sample1.mix schedule.round3Schedule.secondFactors
    round3AfterFirst (by
      rw [schedule.round3Schedule.secondShape,
        schedule.round3Schedule.firstShape]
      simp only [List.append_assoc]
      rfl)
  exact foldPreservesAllReleased schedule.rounds.round3.weights2 trace.weights4
    (acceptedAlphaAt alphas 3) round3BeforeFold
    schedule.round3Schedule.foldRun

#print axioms acceptedTerminalAccumulatorAllReleased

end AspisV5AcceptedAccumulatorTraversal
