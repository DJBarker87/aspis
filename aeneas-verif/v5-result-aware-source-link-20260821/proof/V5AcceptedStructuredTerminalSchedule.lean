import V5AcceptedStructuredWeightJourneys
import V5AcceptedCirclePointCanonical
import V5RelationPreparedPointCanonical
import V5RelationTerminalDotCanonical

/-!
# The eleven structured components in the accepted terminal accumulator

The released accumulator begins with three multilinear components and one
deferred inactive-table component.  Its four rounds append eight tensor
components.  This file follows the three multilinears and eight tensors to
their exact terminal four-entry meanings.  The inactive-table component is
kept separate because its first two folds are intentionally deferred.
-/

namespace AspisV5AcceptedStructuredTerminalSchedule

open Aeneas Aeneas.Std Result
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedAccumulatorCanonicalSchedule
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedStructuredWeightSemantics
open AspisV5AcceptedStructuredWeightJourneys
open AspisV5RelationAcceptanceSourceProof
open AspisV5RelationCallerInitialComponents
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedStructuredFold
open AspisV5RelationPrepareCanonicalProof
open AspisV5RelationPreparedPointCanonical
open AspisV5RelationPreparedPointVectors
open AspisV5RelationTerminalDotCanonical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev FullComponent :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator

private theorem callerOneCanonical :
    AspisV5RelationLinkedFieldProjection.CanonicalQM31
      V5RelationFullGenerated.aspis_core.field.QM31.ONE := by
  norm_num [AspisV5RelationLinkedFieldProjection.CanonicalQM31,
    AspisV5RelationLinkedFieldProjection.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationFullGenerated.aspis_core.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem prepareVecToCallerCanonical
    (values : alloc.vec.Vec
      V5RelationPrepareGenerated.aspis_core.field.QM31)
    (canonical : PrepareCanonicalList values.val) :
    CanonicalList (prepareVecToCaller values).val := by
  intro value member
  change value ∈ values.val.map prepareToCallerQM31 at member
  obtain ⟨source, sourceMember, sourceExact⟩ := List.mem_map.mp member
  subst value
  obtain ⟨index, bound, indexExact⟩ :=
    List.mem_iff_getElem.mp sourceMember
  have bangExact : values.val[index]! = values.val[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  have sourceCanonical : PrepareCanonicalQM31 source := by
    rw [← indexExact, ← bangExact]
    exact canonical index bound
  have mappedCanonical :=
    (prepareToCaller_canonical_iff source).2 sourceCanonical
  simpa [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisV5RelationLinkedFieldProjection.CanonicalQM31,
    AspisV5RelationLinkedFieldProjection.CanonicalCM31] using mappedCanonical

private theorem prepareToCallerCanonical
    (value : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (canonical : PrepareCanonicalQM31 value) :
    AspisV5RelationLinkedFieldProjection.CanonicalQM31
      (prepareToCallerQM31 value) := by
  have mappedCanonical :=
    (prepareToCaller_canonical_iff value).2 canonical
  simpa [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisV5RelationLinkedFieldProjection.CanonicalQM31,
    AspisV5RelationLinkedFieldProjection.CanonicalCM31] using mappedCanonical

/-- The terminal-dot ledger states canonicality by index, while the
structured-fold bridge consumes the equivalent membership formulation. -/
private theorem terminalCanonicalList_to_structured
    (values : List RawQM31)
    (canonical :
      AspisV5RelationLinkedTerminalDotSemantics.CanonicalList values) :
    AspisV5RelationLinkedStructuredFold.CanonicalList values := by
  intro value member
  obtain ⟨index, bound, valueEq⟩ := List.mem_iff_getElem.mp member
  have bangEq : values[index]! = values[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  rw [← valueEq, ← bangEq]
  exact canonical index bound

/-- Exact log lengths before and after every accepted fold. -/
theorem acceptedScheduleLogLengths
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
    trace.calls.relation.weights.log_len = 10#u32 ∧
      trace.weights1.log_len = 8#u32 ∧
      trace.weights2.log_len = 6#u32 ∧
      trace.weights3.log_len = 4#u32 ∧
      trace.weights4.log_len = 2#u32 := by
  have log0 :=
    AspisV5RelationPrepareLogLenProof.Prepare.prepareSuccess_implies_weights_log_len
      parsed kappa inactiveClaim preparedClaims trace.calls.relation
      trace.calls.ignoredAlphas trace.calls.denseScale
      trace.calls.prepareSuccess
  have log1 := full_fold_success_decrements_log_length
    schedule.rounds.round0.weights2 trace.weights1 (acceptedAlphaAt alphas 0)
    schedule.round0Schedule.foldRun
  have log2 := full_fold_success_decrements_log_length
    schedule.rounds.round1.weights2 trace.weights2 (acceptedAlphaAt alphas 1)
    schedule.round1Schedule.foldRun
  have log3 := full_fold_success_decrements_log_length
    schedule.rounds.round2.weights2 trace.weights3 (acceptedAlphaAt alphas 2)
    schedule.round2Schedule.foldRun
  have log4 := full_fold_success_decrements_log_length
    schedule.rounds.round3.weights2 trace.weights4 (acceptedAlphaAt alphas 3)
    schedule.round3Schedule.foldRun
  rw [schedule.rounds.round0.sample1WeightLog,
    schedule.rounds.round0.sample0WeightLog, log0] at log1
  rw [schedule.rounds.round1.sample1WeightLog,
    schedule.rounds.round1.sample0WeightLog, log1] at log2
  rw [schedule.rounds.round2.sample1WeightLog,
    schedule.rounds.round2.sample0WeightLog, log2] at log3
  rw [schedule.rounds.round3.sample1WeightLog,
    schedule.rounds.round3.sample0WeightLog, log3] at log4
  norm_num [Std.U32.wrapping_sub] at log1 log2 log3 log4
  exact ⟨log0, log1, log2, log3, log4⟩

/-- First prepared multilinear cell, viewed after the two round-zero tensor
appends and before the first fold. -/
def acceptedInitialMultilinear0
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace) :
    StructuredCellAt .multilinear schedule.rounds.round0.weights2 0 5 := by
  have points := preparedPointVectorsCanonical schedule.prepareTrace
  have lengths := preparedPointVectorsExact schedule.prepareTrace
  refine {
    scale := V5RelationFullGenerated.aspis_core.field.QM31.ONE
    values := prepareVecToCaller schedule.prepareTrace.pointVec0
    cell := ?_
    scaleCanonical := callerOneCanonical
    valuesCanonical := prepareVecToCallerCanonical
      schedule.prepareTrace.pointVec0 points.2.2.2.1
    valuesLength := ?_ }
  · rw [schedule.round0Schedule.secondShape, schedule.initialMapped,
      schedule.initialExact]
    simp [prepareComponentToCaller, componentToLinked,
      structuredLinkedComponent, prepareToCallerQM31,
      V5RelationPrepareGenerated.aspis_core.field.QM31.ONE,
      V5RelationFullGenerated.aspis_core.field.QM31.ONE]
  · simp [prepareVecToCaller, lengths.2.2.2.1]

/-- Second prepared multilinear cell before the first fold. -/
def acceptedInitialMultilinear1
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    StructuredCellAt .multilinear schedule.rounds.round0.weights2 1 5 := by
  have points := preparedPointVectorsCanonical schedule.prepareTrace
  have lengths := preparedPointVectorsExact schedule.prepareTrace
  refine {
    scale := kappa
    values := prepareVecToCaller schedule.prepareTrace.pointVec1
    cell := ?_
    scaleCanonical := hkappa
    valuesCanonical := prepareVecToCallerCanonical
      schedule.prepareTrace.pointVec1 points.2.2.2.2.1
    valuesLength := ?_ }
  · rw [schedule.round0Schedule.secondShape, schedule.initialMapped,
      schedule.initialExact]
    simp [prepareComponentToCaller, componentToLinked,
      structuredLinkedComponent, prepareToCaller_callerToPrepare]
  · simp [prepareVecToCaller, lengths.2.2.2.2.1]

/-- Third prepared multilinear cell before the first fold. -/
def acceptedInitialMultilinear2
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    StructuredCellAt .multilinear schedule.rounds.round0.weights2 2 5 := by
  have points := preparedPointVectorsCanonical schedule.prepareTrace
  have lengths := preparedPointVectorsExact schedule.prepareTrace
  have sourceKappaCanonical :
      PrepareCanonicalQM31 (callerToPrepareQM31 kappa) :=
    (callerToPrepare_canonical_iff kappa).2 (by
      simpa [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
        AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
        AspisV5RelationLinkedFieldProjection.CanonicalQM31,
        AspisV5RelationLinkedFieldProjection.CanonicalCM31] using hkappa)
  have kappa2Canonical := prepare_qm31_square_success_canonical
    (callerToPrepareQM31 kappa) schedule.prepareTrace.kappa2
    sourceKappaCanonical schedule.prepareTrace.kappa2Run
  refine {
    scale := prepareToCallerQM31 schedule.prepareTrace.kappa2
    values := prepareVecToCaller schedule.prepareTrace.pointVec2
    cell := ?_
    scaleCanonical := prepareToCallerCanonical schedule.prepareTrace.kappa2
      kappa2Canonical
    valuesCanonical := prepareVecToCallerCanonical
      schedule.prepareTrace.pointVec2 points.2.2.2.2.2
    valuesLength := ?_ }
  · rw [schedule.round0Schedule.secondShape, schedule.initialMapped,
      schedule.initialExact]
    simp [prepareComponentToCaller, componentToLinked,
      structuredLinkedComponent]
  · simp [prepareVecToCaller, lengths.2.2.2.2.2]

private def tensorCellOfExact
    (weights : FullWeights) (target rounds : Nat)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (cellExact : componentToLinked weights.components.val[target]! =
      .Tensor scale factors)
    (scaleCanonical :
      AspisV5RelationLinkedFieldProjection.CanonicalQM31 scale)
    (factorsCanonical : CanonicalList factors.val)
    (factorsLength : factors.val.length = 2 * rounds) :
    StructuredCellAt .tensor weights target rounds := {
  scale := scale
  values := factors
  cell := cellExact
  scaleCanonical := scaleCanonical
  valuesCanonical := factorsCanonical
  valuesLength := factorsLength }

/-- Terminal structured cells and their exact journeys from the three
prepared multilinears and eight accepted tensor appends. -/
structure AcceptedStructuredTerminalSchedule
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
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) : Type where
  initial0 : StructuredCellAt .multilinear trace.weights4 0 1
  initial1 : StructuredCellAt .multilinear trace.weights4 1 1
  initial2 : StructuredCellAt .multilinear trace.weights4 2 1
  round0First : StructuredCellAt .tensor trace.weights4 4 1
  round0Second : StructuredCellAt .tensor trace.weights4 5 1
  round1First : StructuredCellAt .tensor trace.weights4 6 1
  round1Second : StructuredCellAt .tensor trace.weights4 7 1
  round2First : StructuredCellAt .tensor trace.weights4 8 1
  round2Second : StructuredCellAt .tensor trace.weights4 9 1
  round3First : StructuredCellAt .tensor trace.weights4 10 1
  round3Second : StructuredCellAt .tensor trace.weights4 11 1
  initial0Exact :
    foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
        (toMaintainedExact (acceptedAlphaAt alphas 1))
        (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (acceptedInitialMultilinear0 schedule).meaning = initial0.meaning
  initial1Exact :
    foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
        (toMaintainedExact (acceptedAlphaAt alphas 1))
        (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (acceptedInitialMultilinear1 schedule
          hkappa).meaning = initial1.meaning
  initial2Exact :
    foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
        (toMaintainedExact (acceptedAlphaAt alphas 1))
        (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (acceptedInitialMultilinear2 schedule
          hkappa).meaning = initial2.meaning
  round0FirstExact :
    foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
        (toMaintainedExact (acceptedAlphaAt alphas 1))
        (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 5
          schedule.rounds.round0.sample0.mix
          schedule.round0Schedule.firstFactors.val) = round0First.meaning
  round0SecondExact :
    foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
        (toMaintainedExact (acceptedAlphaAt alphas 1))
        (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 5
          schedule.rounds.round0.sample1.mix
          schedule.round0Schedule.secondFactors.val) = round0Second.meaning
  round1FirstExact :
    foldThreeMeaning (toMaintainedExact (acceptedAlphaAt alphas 1))
        (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 4
          schedule.rounds.round1.sample0.mix
          schedule.round1Schedule.firstFactors.val) = round1First.meaning
  round1SecondExact :
    foldThreeMeaning (toMaintainedExact (acceptedAlphaAt alphas 1))
        (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 4
          schedule.rounds.round1.sample1.mix
          schedule.round1Schedule.secondFactors.val) = round1Second.meaning
  round2FirstExact :
    foldTwoMeaning (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 3
          schedule.rounds.round2.sample0.mix
          schedule.round2Schedule.firstFactors.val) = round2First.meaning
  round2SecondExact :
    foldTwoMeaning (toMaintainedExact (acceptedAlphaAt alphas 2))
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 3
          schedule.rounds.round2.sample1.mix
          schedule.round2Schedule.secondFactors.val) = round2Second.meaning
  round3FirstExact :
    foldOneMeaning (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 2
          schedule.rounds.round3.sample0.mix
          schedule.round3Schedule.firstFactors.val) = round3First.meaning
  round3SecondExact :
    foldOneMeaning (toMaintainedExact (acceptedAlphaAt alphas 3))
        (structuredComponentWeights .tensor 2
          schedule.rounds.round3.sample1.mix
          schedule.round3Schedule.secondFactors.val) = round3Second.meaning

/-- All eleven structured production components reach the terminal
accumulator with the exact maintained fold meaning. -/
theorem acceptedStructuredTerminalSchedule_exists
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
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa)
    (halphas : ∀ slot : Fin 4,
      AspisV5RelationLinkedFieldProjection.CanonicalQM31
        (acceptedAlphaAt alphas slot))
    (circleCanonical : CanonicalCirclePoints trace.circlePoints) :
    Nonempty (AcceptedStructuredTerminalSchedule trace schedule hkappa) := by
  have logs := acceptedScheduleLogLengths trace schedule
  have canonical0 := acceptedRoundTensorScheduleCanonical
    (trace := schedule.rounds.round0)
    (schedule := schedule.round0Schedule)
    (circleCanonical := fun _ => circleCanonical)
  have canonical1 := acceptedRoundTensorScheduleCanonical
    (trace := schedule.rounds.round1)
    (schedule := schedule.round1Schedule)
    (circleCanonical := fun impossible => by norm_num at impossible)
  have canonical2 := acceptedRoundTensorScheduleCanonical
    (trace := schedule.rounds.round2)
    (schedule := schedule.round2Schedule)
    (circleCanonical := fun impossible => by norm_num at impossible)
  have canonical3 := acceptedRoundTensorScheduleCanonical
    (trace := schedule.rounds.round3)
    (schedule := schedule.round3Schedule)
    (circleCanonical := fun impossible => by norm_num at impossible)

  have intermediate0Log : schedule.rounds.round0.weights1.log_len = 10#u32 :=
    schedule.rounds.round0.sample0WeightLog.trans logs.1
  have intermediate1Log : schedule.rounds.round1.weights1.log_len = 8#u32 :=
    schedule.rounds.round1.sample0WeightLog.trans logs.2.1
  have intermediate2Log : schedule.rounds.round2.weights1.log_len = 6#u32 :=
    schedule.rounds.round2.sample0WeightLog.trans logs.2.2.1
  have intermediate3Log : schedule.rounds.round3.weights1.log_len = 4#u32 :=
    schedule.rounds.round3.sample0WeightLog.trans logs.2.2.2.1

  have length00 : schedule.round0Schedule.firstFactors.val.length = 10 := by
    simpa [logs.1] using canonical0.firstFactorsLength
  have length01 : schedule.round0Schedule.secondFactors.val.length = 10 := by
    simpa [intermediate0Log] using canonical0.secondFactorsLength
  have length10 : schedule.round1Schedule.firstFactors.val.length = 8 := by
    simpa [logs.2.1] using canonical1.firstFactorsLength
  have length11 : schedule.round1Schedule.secondFactors.val.length = 8 := by
    simpa [intermediate1Log] using canonical1.secondFactorsLength
  have length20 : schedule.round2Schedule.firstFactors.val.length = 6 := by
    simpa [logs.2.2.1] using canonical2.firstFactorsLength
  have length21 : schedule.round2Schedule.secondFactors.val.length = 6 := by
    simpa [intermediate2Log] using canonical2.secondFactorsLength
  have length30 : schedule.round3Schedule.firstFactors.val.length = 4 := by
    simpa [logs.2.2.2.1] using canonical3.firstFactorsLength
  have length31 : schedule.round3Schedule.secondFactors.val.length = 4 := by
    simpa [intermediate3Log] using canonical3.secondFactorsLength

  have pre0Length :
      schedule.rounds.round0.weights2.components.val.length = 6 := by
    rw [schedule.round0Schedule.secondShape]
    simp [schedule.initialLength]
  have pre1Length :
      schedule.rounds.round1.weights2.components.val.length = 8 := by
    rw [schedule.round1Schedule.secondShape]
    simp [schedule.round0Length]
  have pre2Length :
      schedule.rounds.round2.weights2.components.val.length = 10 := by
    rw [schedule.round2Schedule.secondShape]
    simp [schedule.round1Length]
  have pre3Length :
      schedule.rounds.round3.weights2.components.val.length = 12 := by
    rw [schedule.round3Schedule.secondShape]
    simp [schedule.round2Length]

  let start00 : StructuredCellAt .tensor
      schedule.rounds.round0.weights2 4 5 := tensorCellOfExact _ _ _
    schedule.rounds.round0.sample0.mix schedule.round0Schedule.firstFactors
    (by
      rw [schedule.round0Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 4 (by
        rw [schedule.initialLength])]
      rw [schedule.initialLength]
      simp [componentToLinked])
    canonical0.firstMixCanonical
      (terminalCanonicalList_to_structured _ canonical0.firstFactorsCanonical) (by
      simpa using length00)
  let start01 : StructuredCellAt .tensor
      schedule.rounds.round0.weights2 5 5 := tensorCellOfExact _ _ _
    schedule.rounds.round0.sample1.mix schedule.round0Schedule.secondFactors
    (by
      rw [schedule.round0Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 5 (by
        rw [schedule.initialLength]
        norm_num)]
      rw [schedule.initialLength]
      simp [componentToLinked])
    canonical0.secondMixCanonical
      (terminalCanonicalList_to_structured _ canonical0.secondFactorsCanonical) (by
      simpa using length01)
  let start10 : StructuredCellAt .tensor
      schedule.rounds.round1.weights2 6 4 := tensorCellOfExact _ _ _
    schedule.rounds.round1.sample0.mix schedule.round1Schedule.firstFactors
    (by
      rw [schedule.round1Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 6 (by
        rw [schedule.round0Length])]
      rw [schedule.round0Length]
      simp [componentToLinked])
    canonical1.firstMixCanonical
      (terminalCanonicalList_to_structured _ canonical1.firstFactorsCanonical) (by
      simpa using length10)
  let start11 : StructuredCellAt .tensor
      schedule.rounds.round1.weights2 7 4 := tensorCellOfExact _ _ _
    schedule.rounds.round1.sample1.mix schedule.round1Schedule.secondFactors
    (by
      rw [schedule.round1Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 7 (by
        rw [schedule.round0Length]
        norm_num)]
      rw [schedule.round0Length]
      simp [componentToLinked])
    canonical1.secondMixCanonical
      (terminalCanonicalList_to_structured _ canonical1.secondFactorsCanonical) (by
      simpa using length11)
  let start20 : StructuredCellAt .tensor
      schedule.rounds.round2.weights2 8 3 := tensorCellOfExact _ _ _
    schedule.rounds.round2.sample0.mix schedule.round2Schedule.firstFactors
    (by
      rw [schedule.round2Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 8 (by
        rw [schedule.round1Length])]
      rw [schedule.round1Length]
      simp [componentToLinked])
    canonical2.firstMixCanonical
      (terminalCanonicalList_to_structured _ canonical2.firstFactorsCanonical) (by
      simpa using length20)
  let start21 : StructuredCellAt .tensor
      schedule.rounds.round2.weights2 9 3 := tensorCellOfExact _ _ _
    schedule.rounds.round2.sample1.mix schedule.round2Schedule.secondFactors
    (by
      rw [schedule.round2Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 9 (by
        rw [schedule.round1Length]
        norm_num)]
      rw [schedule.round1Length]
      simp [componentToLinked])
    canonical2.secondMixCanonical
      (terminalCanonicalList_to_structured _ canonical2.secondFactorsCanonical) (by
      simpa using length21)
  let start30 : StructuredCellAt .tensor
      schedule.rounds.round3.weights2 10 2 := tensorCellOfExact _ _ _
    schedule.rounds.round3.sample0.mix schedule.round3Schedule.firstFactors
    (by
      rw [schedule.round3Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 10 (by
        rw [schedule.round2Length])]
      rw [schedule.round2Length]
      simp [componentToLinked])
    canonical3.firstMixCanonical
      (terminalCanonicalList_to_structured _ canonical3.firstFactorsCanonical) (by
      simpa using length30)
  let start31 : StructuredCellAt .tensor
      schedule.rounds.round3.weights2 11 2 := tensorCellOfExact _ _ _
    schedule.rounds.round3.sample1.mix schedule.round3Schedule.secondFactors
    (by
      rw [schedule.round3Schedule.secondShape]
      rw [List.getElem!_append_right _ _ 11 (by
        rw [schedule.round2Length]
        norm_num)]
      rw [schedule.round2Length]
      simp [componentToLinked])
    canonical3.secondMixCanonical
      (terminalCanonicalList_to_structured _ canonical3.secondFactorsCanonical) (by
      simpa using length31)

  let suffix1 : List FullComponent :=
    [.Tensor schedule.rounds.round1.sample0.mix
        schedule.round1Schedule.firstFactors,
     .Tensor schedule.rounds.round1.sample1.mix
        schedule.round1Schedule.secondFactors]
  let suffix2 : List FullComponent :=
    [.Tensor schedule.rounds.round2.sample0.mix
        schedule.round2Schedule.firstFactors,
     .Tensor schedule.rounds.round2.sample1.mix
        schedule.round2Schedule.secondFactors]
  let suffix3 : List FullComponent :=
    [.Tensor schedule.rounds.round3.sample0.mix
        schedule.round3Schedule.firstFactors,
     .Tensor schedule.rounds.round3.sample1.mix
        schedule.round3Schedule.secondFactors]
  have shape1 : schedule.rounds.round1.weights2.components.val =
      trace.weights1.components.val ++ suffix1 := by
    simpa [suffix1] using schedule.round1Schedule.secondShape
  have shape2 : schedule.rounds.round2.weights2.components.val =
      trace.weights2.components.val ++ suffix2 := by
    simpa [suffix2] using schedule.round2Schedule.secondShape
  have shape3 : schedule.rounds.round3.weights2.components.val =
      trace.weights3.components.val ++ suffix3 := by
    simpa [suffix3] using schedule.round3Schedule.secondShape

  let alpha0 := acceptedAlphaAt alphas 0
  let alpha1 := acceptedAlphaAt alphas 1
  let alpha2 := acceptedAlphaAt alphas 2
  let alpha3 := acceptedAlphaAt alphas 3
  have ha0 : AspisV5RelationLinkedFieldProjection.CanonicalQM31 alpha0 :=
    halphas 0
  have ha1 : AspisV5RelationLinkedFieldProjection.CanonicalQM31 alpha1 :=
    halphas 1
  have ha2 : AspisV5RelationLinkedFieldProjection.CanonicalQM31 alpha2 :=
    halphas 2
  have ha3 : AspisV5RelationLinkedFieldProjection.CanonicalQM31 alpha3 :=
    halphas 3

  obtain ⟨terminal0, exact0⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldFour
      (acceptedInitialMultilinear0 schedule) (by rw [pre0Length]; decide)
      alpha0 alpha1 alpha2 alpha3 ha0 ha1 ha2 ha3
      schedule.round0Schedule.foldRun suffix1 shape1
      (by rw [schedule.round0Length]; decide)
      schedule.round1Schedule.foldRun suffix2 shape2
      (by rw [schedule.round1Length]; decide)
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal1, exact1⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldFour
      (acceptedInitialMultilinear1 schedule hkappa)
      (by rw [pre0Length]; decide)
      alpha0 alpha1 alpha2 alpha3 ha0 ha1 ha2 ha3
      schedule.round0Schedule.foldRun suffix1 shape1
      (by rw [schedule.round0Length]; decide)
      schedule.round1Schedule.foldRun suffix2 shape2
      (by rw [schedule.round1Length]; decide)
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal2, exact2⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldFour
      (acceptedInitialMultilinear2 schedule hkappa)
      (by rw [pre0Length]; decide)
      alpha0 alpha1 alpha2 alpha3 ha0 ha1 ha2 ha3
      schedule.round0Schedule.foldRun suffix1 shape1
      (by rw [schedule.round0Length]; decide)
      schedule.round1Schedule.foldRun suffix2 shape2
      (by rw [schedule.round1Length]; decide)
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal00, exact00⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldFour
      start00 (by rw [pre0Length]; decide)
      alpha0 alpha1 alpha2 alpha3 ha0 ha1 ha2 ha3
      schedule.round0Schedule.foldRun suffix1 shape1
      (by rw [schedule.round0Length]; decide)
      schedule.round1Schedule.foldRun suffix2 shape2
      (by rw [schedule.round1Length]; decide)
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal01, exact01⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldFour
      start01 (by rw [pre0Length]; decide)
      alpha0 alpha1 alpha2 alpha3 ha0 ha1 ha2 ha3
      schedule.round0Schedule.foldRun suffix1 shape1
      (by rw [schedule.round0Length]; decide)
      schedule.round1Schedule.foldRun suffix2 shape2
      (by rw [schedule.round1Length]; decide)
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal10, exact10⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldThree
      start10 (by rw [pre1Length]; decide) alpha1 alpha2 alpha3 ha1 ha2 ha3
      schedule.round1Schedule.foldRun suffix2 shape2
      (by rw [schedule.round1Length]; decide)
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal11, exact11⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldThree
      start11 (by rw [pre1Length]; decide) alpha1 alpha2 alpha3 ha1 ha2 ha3
      schedule.round1Schedule.foldRun suffix2 shape2
      (by rw [schedule.round1Length]; decide)
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal20, exact20⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldTwo
      start20 (by rw [pre2Length]; decide) alpha2 alpha3 ha2 ha3
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal21, exact21⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldTwo
      start21 (by rw [pre2Length]; decide) alpha2 alpha3 ha2 ha3
      schedule.round2Schedule.foldRun suffix3 shape3
      (by rw [schedule.round2Length]; decide)
      schedule.round3Schedule.foldRun
  obtain ⟨terminal30, exact30⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldOne
      start30 (by rw [pre3Length]; decide) alpha3 ha3
      schedule.round3Schedule.foldRun
  obtain ⟨terminal31, exact31⟩ :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.foldOne
      start31 (by rw [pre3Length]; decide) alpha3 ha3
      schedule.round3Schedule.foldRun
  exact ⟨{
    initial0 := terminal0
    initial1 := terminal1
    initial2 := terminal2
    round0First := terminal00
    round0Second := terminal01
    round1First := terminal10
    round1Second := terminal11
    round2First := terminal20
    round2Second := terminal21
    round3First := terminal30
    round3Second := terminal31
    initial0Exact := by simpa [alpha0, alpha1, alpha2, alpha3] using exact0
    initial1Exact := by simpa [alpha0, alpha1, alpha2, alpha3] using exact1
    initial2Exact := by simpa [alpha0, alpha1, alpha2, alpha3] using exact2
    round0FirstExact := by
      simpa [alpha0, alpha1, alpha2, alpha3, start00, tensorCellOfExact,
        StructuredCellAt.meaning]
        using exact00
    round0SecondExact := by
      simpa [alpha0, alpha1, alpha2, alpha3, start01, tensorCellOfExact,
        StructuredCellAt.meaning]
        using exact01
    round1FirstExact := by
      simpa [alpha1, alpha2, alpha3, start10, tensorCellOfExact,
        StructuredCellAt.meaning] using exact10
    round1SecondExact := by
      simpa [alpha1, alpha2, alpha3, start11, tensorCellOfExact,
        StructuredCellAt.meaning] using exact11
    round2FirstExact := by
      simpa [alpha2, alpha3, start20, tensorCellOfExact,
        StructuredCellAt.meaning] using exact20
    round2SecondExact := by
      simpa [alpha2, alpha3, start21, tensorCellOfExact,
        StructuredCellAt.meaning] using exact21
    round3FirstExact := by
      simpa [alpha3, start30, tensorCellOfExact,
        StructuredCellAt.meaning] using exact30
    round3SecondExact := by
      simpa [alpha3, start31, tensorCellOfExact,
        StructuredCellAt.meaning] using exact31 }⟩

#print axioms acceptedScheduleLogLengths
#print axioms acceptedInitialMultilinear0
#print axioms acceptedInitialMultilinear1
#print axioms acceptedInitialMultilinear2
#print axioms acceptedStructuredTerminalSchedule_exists

end AspisV5AcceptedStructuredTerminalSchedule
