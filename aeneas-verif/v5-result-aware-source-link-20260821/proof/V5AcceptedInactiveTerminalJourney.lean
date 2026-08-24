import V5AcceptedStructuredTerminalWeights
import V5AcceptedInactiveLowTraceTotal
import V5RelationLinkedGroupedRowsSemantics

/-!
# The accepted inactive component through the real four-fold driver

This follows component index three from the prepared released table through
the same four dispatcher calls used by an accepted relation execution.
-/

namespace AspisV5AcceptedInactiveTerminalJourney

open Aeneas Aeneas.Std Result
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedInactiveInitialSemantics
open AspisV5AcceptedInactiveLowTraceTotal
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedStructuredWeightSemantics
open AspisV5AcceptedStructuredTerminalSchedule
open AspisV5RelationAcceptanceSourceProof
open AspisV5RelationCallerInitialComponents
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedFoldArithmetic
open AspisV5RelationLinkedGroupedFold
open AspisV5RelationLinkedGroupedLowSemantics
open AspisV5RelationLinkedGroupedRows
open AspisV5RelationLinkedGroupedRowsStaged
open AspisV5RelationLinkedGroupedRowsSemantics
open AspisV5RelationLinkedPreparedSum
open AspisV5RelationLinkedSupportedFold

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev LinkedComponent :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent
abbrev LinkedPrepared :=
  V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩

private theorem vecExt {T : Type}
    (left right : alloc.vec.Vec T) (same : left.val = right.val) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Successful generic dispatch on a deferred grouped component exposes the
exact successful component-specific helper call and all four returned fields. -/
theorem groupedDeferredDispatchSuccessExposesHelper
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks : alloc.vec.Vec Std.U16)
    (firstAlpha : Option RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : LinkedPrepared)
    (componentOut : LinkedComponent)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha
            groupValues)
          currentLog alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
        ok (none, componentOut)) :
    ∃ rowGroupsOut groupMasksOut firstAlphaOut groupValuesOut,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          rowGroups groupMasks firstAlpha groupValues currentLog alpha alpha2
            alpha3 =
        ok (rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut) ∧
      componentOut = .Grouped64x16BinaryDeferred rowGroupsOut groupMasksOut
        firstAlphaOut groupValuesOut := by
  simp only [
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4]
    at success
  generalize helperRun :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks firstAlpha groupValues currentLog alpha alpha2
          alpha3 = helperResult at success
  cases helperResult with
  | fail error => simp at success
  | div => simp at success
  | ok value =>
      rcases value with ⟨rowGroupsOut, groupMasksOut, firstAlphaOut,
        groupValuesOut⟩
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, componentExact⟩
      exact ⟨rowGroupsOut, groupMasksOut, firstAlphaOut, groupValuesOut,
        rfl, componentExact.symm⟩

/-- Preparation really installs the fixed released row and mask vectors. -/
theorem acceptedPreparedInactiveVectorsExact
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
    schedule.prepareTrace.groupedRows = releasedRowGroups64 ∧
      schedule.prepareTrace.groupedMasks = releasedMasks := by
  have generatedRows :
      V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_ROW_GROUPS.val =
        releasedRowGroups64.val := by
    simp [V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_ROW_GROUPS,
      releasedRowGroups64, Array.make]
  have generatedMasks :
      V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_GROUP_MASKS.val =
        releasedMasks.val := by
    simp [V5RelationPrepareGenerated.v5_cu_probe.V5_ATOMIC_V3_INACTIVE_GROUP_MASKS,
      releasedMasks, Array.make]
  exact ⟨vecExt _ _ (schedule.prepareTrace.groupedRowsExact.trans generatedRows),
    vecExt _ _ (schedule.prepareTrace.groupedMasksExact.trans generatedMasks)⟩

/-- Before the first real fold, component index three is exactly the released
deferred inactive table and has no cached group values yet. -/
theorem acceptedInactiveInitialCellExact
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
    componentToLinked
        schedule.rounds.round0.weights2.components.val[3]! =
      .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks none
        (alloc.vec.Vec.new RawQM31) := by
  obtain ⟨rowsExact, masksExact⟩ :=
    acceptedPreparedInactiveVectorsExact schedule
  rw [schedule.round0Schedule.secondShape]
  rw [List.getElem!_append_left _ _ 3 (by
    rw [schedule.initialLength]
    decide)]
  rw [schedule.initialMapped, schedule.initialExact]
  simp [prepareComponentToCaller, componentToLinked, prepareVecToCaller,
    rowsExact, masksExact]

/-- Exact accepted state after the deferred component has consumed its first
two challenges and materialized the seven released group values. -/
structure AcceptedInactiveAfterTwoFolds
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) : Type where
  power : ReleasedBinaryPowerTrace (acceptedAlphaAt alphas 0)
    (acceptedAlphaAt alphas 1)
  values : ReleasedMaskValuesTrace
    (releasedBasis power.alpha0Cubed power.alpha0Squared
      (acceptedAlphaAt alphas 0) power.cross (acceptedAlphaAt alphas 1))
    power.total
  semantics : ReleasedLowValuesSemantics (acceptedAlphaAt alphas 0)
    (acceptedAlphaAt alphas 1) power values
  cell :
    componentToLinked trace.weights2.components.val[3]! =
      .Grouped64x16BinaryDeferred releasedRowGroups64
        (alloc.vec.Vec.new Std.U16) none
        (releasedLowSevenValues values.trace0.value values.trace1.value
          values.trace2.value values.trace3.value values.trace4.value
          values.trace5.value values.trace6.value)
  meaningExact :
    representedGroupedWeights releasedRowGroups64
        (releasedLowSevenValues values.trace0.value values.trace1.value
          values.trace2.value values.trace3.value values.trace4.value
          values.trace5.value values.trace6.value) =
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (toMaintainedExact (acceptedAlphaAt alphas 1))
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
          (toMaintainedExact (acceptedAlphaAt alphas 0))
          releasedInactiveInitialWeight)

/-- The first accepted fold stores alpha zero, and the second accepted fold
runs the exact seven-mask helper with alpha zero and alpha one. -/
theorem acceptedInactiveAfterTwoFolds_exists
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
    (halpha0 : CanonicalQM31 (acceptedAlphaAt alphas 0))
    (halpha1 : CanonicalQM31 (acceptedAlphaAt alphas 1)) :
    Nonempty (AcceptedInactiveAfterTwoFolds trace) := by
  have logs := acceptedScheduleLogLengths trace schedule
  have pre0Log : schedule.rounds.round0.weights2.log_len = 10#u32 := by
    rw [schedule.rounds.round0.sample1WeightLog,
      schedule.rounds.round0.sample0WeightLog, logs.1]
  have pre1Log : schedule.rounds.round1.weights2.log_len = 8#u32 := by
    rw [schedule.rounds.round1.sample1WeightLog,
      schedule.rounds.round1.sample0WeightLog, logs.2.1]

  have initialCell := acceptedInactiveInitialCellExact schedule
  have pre0Bound : 3 < schedule.rounds.round0.weights2.components.val.length := by
    rw [schedule.round0Schedule.secondShape]
    simp [schedule.initialLength]
  have initialReleased : ReleasedComponent
      (componentToLinked
        schedule.rounds.round0.weights2.components.val[3]!) := by
    rw [initialCell]
    trivial
  obtain ⟨_alpha20, _alpha30, _prepared0, _prepared20, component1, _folded0,
      _square0, _prepare0, _prepare20, _alpha30Run, dispatch0, outputCell0,
      _released1⟩ :=
    fullFoldSuccessExposesLinkedComponent schedule.rounds.round0.weights2
      trace.weights1 (acceptedAlphaAt alphas 0) 3 pre0Bound initialReleased
      schedule.round0Schedule.foldRun
  have dispatch0Exact :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks none
            (alloc.vec.Vec.new RawQM31))
          schedule.rounds.round0.weights2.log_len (acceptedAlphaAt alphas 0)
          _alpha20 _alpha30 _prepared0 _prepared20 = ok (none, component1) := by
    exact (congrArg
      (fun component =>
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component schedule.rounds.round0.weights2.log_len
            (acceptedAlphaAt alphas 0) _alpha20 _alpha30 _prepared0
            _prepared20)
      initialCell).symm.trans dispatch0
  obtain ⟨rows1, masks1, first1, values1, helper0, component1Exact⟩ :=
    groupedDeferredDispatchSuccessExposesHelper releasedRowGroups64
      releasedMasks none (alloc.vec.Vec.new RawQM31)
      schedule.rounds.round0.weights2.log_len (acceptedAlphaAt alphas 0)
      _alpha20 _alpha30 _prepared0 _prepared20 component1 dispatch0Exact
  rw [pre0Log] at helper0
  have expected0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          releasedRowGroups64 releasedMasks none (alloc.vec.Vec.new RawQM31)
          10#u32 (acceptedAlphaAt alphas 0) _alpha20 _alpha30 =
        ok (releasedRowGroups64, releasedMasks,
          some (acceptedAlphaAt alphas 0), alloc.vec.Vec.new RawQM31) := by
    rfl
  have same0 :
      (rows1, masks1, first1, values1) =
        (releasedRowGroups64, releasedMasks,
          some (acceptedAlphaAt alphas 0), alloc.vec.Vec.new RawQM31) :=
    Result.ok.inj (helper0.symm.trans expected0)
  cases same0
  have cell1 :
      componentToLinked trace.weights1.components.val[3]! =
        .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
          (some (acceptedAlphaAt alphas 0)) (alloc.vec.Vec.new RawQM31) :=
    outputCell0.trans component1Exact

  have pre1Cell :
      componentToLinked
          schedule.rounds.round1.weights2.components.val[3]! =
        .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
          (some (acceptedAlphaAt alphas 0)) (alloc.vec.Vec.new RawQM31) := by
    rw [schedule.round1Schedule.secondShape]
    rw [List.getElem!_append_left _ _ 3 (by
      rw [schedule.round0Length]
      decide)]
    exact cell1
  have pre1Bound : 3 < schedule.rounds.round1.weights2.components.val.length := by
    rw [schedule.round1Schedule.secondShape]
    simp [schedule.round0Length]
  have pre1Released : ReleasedComponent
      (componentToLinked
        schedule.rounds.round1.weights2.components.val[3]!) := by
    rw [pre1Cell]
    trivial
  obtain ⟨_alpha21, _alpha31, _prepared1, _prepared21, component2, _folded1,
      _square1, _prepare1, _prepare21, _alpha31Run, dispatch1, outputCell1,
      _released2⟩ :=
    fullFoldSuccessExposesLinkedComponent schedule.rounds.round1.weights2
      trace.weights2 (acceptedAlphaAt alphas 1) 3 pre1Bound pre1Released
      schedule.round1Schedule.foldRun
  have dispatch1Exact :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
            (some (acceptedAlphaAt alphas 0)) (alloc.vec.Vec.new RawQM31))
          schedule.rounds.round1.weights2.log_len (acceptedAlphaAt alphas 1)
          _alpha21 _alpha31 _prepared1 _prepared21 = ok (none, component2) := by
    exact (congrArg
      (fun component =>
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component schedule.rounds.round1.weights2.log_len
            (acceptedAlphaAt alphas 1) _alpha21 _alpha31 _prepared1
            _prepared21)
      pre1Cell).symm.trans dispatch1
  obtain ⟨rows2, masks2, first2, values2, helper1, component2Exact⟩ :=
    groupedDeferredDispatchSuccessExposesHelper releasedRowGroups64
      releasedMasks (some (acceptedAlphaAt alphas 0))
      (alloc.vec.Vec.new RawQM31) schedule.rounds.round1.weights2.log_len
      (acceptedAlphaAt alphas 1) _alpha21 _alpha31 _prepared1 _prepared21
      component2 dispatch1Exact
  rw [pre1Log] at helper1

  obtain ⟨power, values, semantics, lowRun, valuesExact⟩ :=
    releasedLowSourceTrace_exists (acceptedAlphaAt alphas 0)
      (acceptedAlphaAt alphas 1) halpha0 halpha1
  have clearRun : alloc.vec.Vec.clear Global releasedMasks =
      ok (alloc.vec.Vec.new Std.U16) := by
    rfl
  have expected1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          releasedRowGroups64 releasedMasks (some (acceptedAlphaAt alphas 0))
          (alloc.vec.Vec.new RawQM31) 8#u32 (acceptedAlphaAt alphas 1)
          _alpha21 _alpha31 =
        ok (releasedRowGroups64, alloc.vec.Vec.new Std.U16, none,
          releasedLowSevenValues values.trace0.value values.trace1.value
            values.trace2.value values.trace3.value values.trace4.value
            values.trace5.value values.trace6.value) := by
    unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
    change (do
      let groupValuesOut ←
        V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks
          (alloc.vec.Vec.deref releasedMasks) (acceptedAlphaAt alphas 0)
            (acceptedAlphaAt alphas 1)
      let cleared ← alloc.vec.Vec.clear Global releasedMasks
      ok (releasedRowGroups64, cleared, none, groupValuesOut)) = _
    rw [lowRun, clearRun]
    simp only [bind_tc_ok]
    exact congrArg
      (fun groupValues : alloc.vec.Vec RawQM31 =>
        ok (releasedRowGroups64, alloc.vec.Vec.new Std.U16, none,
          groupValues)) valuesExact
  have same1 :
      (rows2, masks2, first2, values2) =
        (releasedRowGroups64, alloc.vec.Vec.new Std.U16, none,
          releasedLowSevenValues values.trace0.value values.trace1.value
            values.trace2.value values.trace3.value values.trace4.value
            values.trace5.value values.trace6.value) :=
    Result.ok.inj (helper1.symm.trans expected1)
  cases same1
  refine ⟨{
    power := power
    values := values
    semantics := semantics
    cell := outputCell1.trans component2Exact
    meaningExact := ?_ }⟩
  exact releasedLowValues_represent_foldedInactiveInitialWeight
    (acceptedAlphaAt alphas 0) (acceptedAlphaAt alphas 1) power values
      semantics

/-- Exact terminal state of the inactive component after the two ordinary
grouped-row folds. -/
structure AcceptedInactiveTerminal
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) : Type where
  value0 : RawQM31
  value1 : RawQM31
  value2 : RawQM31
  value3 : RawQM31
  canonical : CanonicalFour value0 value1 value2 value3
  cell :
    componentToLinked trace.weights4.components.val[3]! =
      .Grouped64x16BinaryDeferred releasedRowGroups4
        (alloc.vec.Vec.new Std.U16) none
        (releasedFourValues value0 value1 value2 value3)
  meaningExact :
    representedGroupedWeights releasedRowGroups4
        (releasedFourValues value0 value1 value2 value3) =
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
        (toMaintainedExact (acceptedAlphaAt alphas 3))
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (toMaintainedExact (acceptedAlphaAt alphas 2))
          (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
            (toMaintainedExact (acceptedAlphaAt alphas 1))
            (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
              (toMaintainedExact (acceptedAlphaAt alphas 0))
              releasedInactiveInitialWeight)))

/-- All four accepted dispatcher calls carry component index three to the
exact four-value fold of the released inactive table. -/
theorem acceptedInactiveTerminal_exists
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
    (halphas : ∀ slot : Fin 4,
      CanonicalQM31 (acceptedAlphaAt alphas slot)) :
    Nonempty (AcceptedInactiveTerminal trace) := by
  obtain ⟨afterTwo⟩ := acceptedInactiveAfterTwoFolds_exists trace schedule
    (halphas 0) (halphas 1)
  have logs := acceptedScheduleLogLengths trace schedule
  have pre2Log : schedule.rounds.round2.weights2.log_len = 6#u32 := by
    rw [schedule.rounds.round2.sample1WeightLog,
      schedule.rounds.round2.sample0WeightLog, logs.2.2.1]
  have pre3Log : schedule.rounds.round3.weights2.log_len = 4#u32 := by
    rw [schedule.rounds.round3.sample1WeightLog,
      schedule.rounds.round3.sample0WeightLog, logs.2.2.2.1]

  have pre2Cell :
      componentToLinked
          schedule.rounds.round2.weights2.components.val[3]! =
        .Grouped64x16BinaryDeferred releasedRowGroups64
          (alloc.vec.Vec.new Std.U16) none
          (releasedSevenValues afterTwo.values.trace0.value
            afterTwo.values.trace1.value afterTwo.values.trace2.value
            afterTwo.values.trace3.value afterTwo.values.trace4.value
            afterTwo.values.trace5.value afterTwo.values.trace6.value) := by
    rw [schedule.round2Schedule.secondShape]
    rw [List.getElem!_append_left _ _ 3 (by
      rw [schedule.round1Length]
      decide)]
    simpa [releasedLowSevenValues, releasedSevenValues,
      releasedSevenValuesStaged] using afterTwo.cell
  have pre2Bound : 3 < schedule.rounds.round2.weights2.components.val.length := by
    rw [schedule.round2Schedule.secondShape]
    simp [schedule.round1Length]
  have pre2Released : ReleasedComponent
      (componentToLinked
        schedule.rounds.round2.weights2.components.val[3]!) := by
    rw [pre2Cell]
    trivial
  obtain ⟨alpha22, alpha32, prepared2, prepared22, component3, _folded2,
      square2, prepare2, prepare22, alpha32Run, dispatch2, outputCell2,
      _released3⟩ :=
    fullFoldSuccessExposesLinkedComponent schedule.rounds.round2.weights2
      trace.weights3 (acceptedAlphaAt alphas 2) 3 pre2Bound pre2Released
      schedule.round2Schedule.foldRun
  have dispatch2Exact :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Grouped64x16BinaryDeferred releasedRowGroups64
            (alloc.vec.Vec.new Std.U16) none
            (releasedSevenValues afterTwo.values.trace0.value
              afterTwo.values.trace1.value afterTwo.values.trace2.value
              afterTwo.values.trace3.value afterTwo.values.trace4.value
              afterTwo.values.trace5.value afterTwo.values.trace6.value))
          schedule.rounds.round2.weights2.log_len (acceptedAlphaAt alphas 2)
          alpha22 alpha32 prepared2 prepared22 = ok (none, component3) := by
    exact (congrArg
      (fun component =>
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component schedule.rounds.round2.weights2.log_len
            (acceptedAlphaAt alphas 2) alpha22 alpha32 prepared2 prepared22)
      pre2Cell).symm.trans dispatch2
  obtain ⟨rows3, masks3, first3, values3, helper2, component3Exact⟩ :=
    groupedDeferredDispatchSuccessExposesHelper releasedRowGroups64
      (alloc.vec.Vec.new Std.U16) none
      (releasedSevenValues afterTwo.values.trace0.value
        afterTwo.values.trace1.value afterTwo.values.trace2.value
        afterTwo.values.trace3.value afterTwo.values.trace4.value
        afterTwo.values.trace5.value afterTwo.values.trace6.value)
      schedule.rounds.round2.weights2.log_len (acceptedAlphaAt alphas 2)
      alpha22 alpha32 prepared2 prepared22 component3 dispatch2Exact
  rw [pre2Log] at helper2
  obtain ⟨halpha22, halpha32, _hprepared2, _hprepared22, alpha22Exact,
      alpha32Exact⟩ :=
    acceptedFoldPowerRunsExact (acceptedAlphaAt alphas 2) alpha22
      alpha32 prepared2 prepared22 (halphas 2) square2 prepare2 prepare22
      alpha32Run
  have lowCanonical : CanonicalSeven afterTwo.values.trace0.value
      afterTwo.values.trace1.value afterTwo.values.trace2.value
      afterTwo.values.trace3.value afterTwo.values.trace4.value
      afterTwo.values.trace5.value afterTwo.values.trace6.value :=
    ⟨afterTwo.semantics.canonical0, afterTwo.semantics.canonical1,
      afterTwo.semantics.canonical2, afterTwo.semantics.canonical3,
      afterTwo.semantics.canonical4, afterTwo.semantics.canonical5,
      afterTwo.semantics.canonical6⟩
  obtain ⟨mid0, mid1, mid2, mid3, mid4, mid5, mid6, grouped2Run,
      midCanonical, grouped2Exact⟩ :=
    released_first_grouped_rows_corresponds afterTwo.values.trace0.value
      afterTwo.values.trace1.value afterTwo.values.trace2.value
      afterTwo.values.trace3.value afterTwo.values.trace4.value
      afterTwo.values.trace5.value afterTwo.values.trace6.value
      (acceptedAlphaAt alphas 2) alpha22 alpha32 lowCanonical (halphas 2)
      halpha22 halpha32 alpha22Exact alpha32Exact
  have expected2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          releasedRowGroups64 (alloc.vec.Vec.new Std.U16) none
          (releasedSevenValues afterTwo.values.trace0.value
            afterTwo.values.trace1.value afterTwo.values.trace2.value
            afterTwo.values.trace3.value afterTwo.values.trace4.value
            afterTwo.values.trace5.value afterTwo.values.trace6.value)
          6#u32 (acceptedAlphaAt alphas 2) alpha22 alpha32 =
        ok (releasedRowGroups16, alloc.vec.Vec.new Std.U16, none,
          releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6) := by
    unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
    change (do
      let pair ←
        V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
          (alloc.vec.Vec.deref releasedRowGroups64)
          (alloc.vec.Vec.deref
            (releasedSevenValues afterTwo.values.trace0.value
              afterTwo.values.trace1.value afterTwo.values.trace2.value
              afterTwo.values.trace3.value afterTwo.values.trace4.value
              afterTwo.values.trace5.value afterTwo.values.trace6.value))
          (acceptedAlphaAt alphas 2) alpha22 alpha32
      ok (pair.1, alloc.vec.Vec.new Std.U16, none, pair.2)) = _
    rw [grouped2Run]
    rfl
  have same2 :
      (rows3, masks3, first3, values3) =
        (releasedRowGroups16, alloc.vec.Vec.new Std.U16, none,
          releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6) :=
    Result.ok.inj (helper2.symm.trans expected2)
  cases same2
  have cell3 :
      componentToLinked trace.weights3.components.val[3]! =
        .Grouped64x16BinaryDeferred releasedRowGroups16
          (alloc.vec.Vec.new Std.U16) none
          (releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6) :=
    outputCell2.trans component3Exact

  have pre3Cell :
      componentToLinked
          schedule.rounds.round3.weights2.components.val[3]! =
        .Grouped64x16BinaryDeferred releasedRowGroups16
          (alloc.vec.Vec.new Std.U16) none
          (releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6) := by
    rw [schedule.round3Schedule.secondShape]
    rw [List.getElem!_append_left _ _ 3 (by
      rw [schedule.round2Length]
      decide)]
    exact cell3
  have pre3Bound : 3 < schedule.rounds.round3.weights2.components.val.length := by
    rw [schedule.round3Schedule.secondShape]
    simp [schedule.round2Length]
  have pre3Released : ReleasedComponent
      (componentToLinked
        schedule.rounds.round3.weights2.components.val[3]!) := by
    rw [pre3Cell]
    trivial
  obtain ⟨alpha23, alpha33, prepared3, prepared23, component4, _folded3,
      square3, prepare3, prepare23, alpha33Run, dispatch3, outputCell3,
      _released4⟩ :=
    fullFoldSuccessExposesLinkedComponent schedule.rounds.round3.weights2
      trace.weights4 (acceptedAlphaAt alphas 3) 3 pre3Bound pre3Released
      schedule.round3Schedule.foldRun
  have dispatch3Exact :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Grouped64x16BinaryDeferred releasedRowGroups16
            (alloc.vec.Vec.new Std.U16) none
            (releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6))
          schedule.rounds.round3.weights2.log_len (acceptedAlphaAt alphas 3)
          alpha23 alpha33 prepared3 prepared23 = ok (none, component4) := by
    exact (congrArg
      (fun component =>
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component schedule.rounds.round3.weights2.log_len
            (acceptedAlphaAt alphas 3) alpha23 alpha33 prepared3 prepared23)
      pre3Cell).symm.trans dispatch3
  obtain ⟨rows4, masks4, first4, values4, helper3, component4Exact⟩ :=
    groupedDeferredDispatchSuccessExposesHelper releasedRowGroups16
      (alloc.vec.Vec.new Std.U16) none
      (releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6)
      schedule.rounds.round3.weights2.log_len (acceptedAlphaAt alphas 3)
      alpha23 alpha33 prepared3 prepared23 component4 dispatch3Exact
  rw [pre3Log] at helper3
  obtain ⟨halpha23, halpha33, _hprepared3, _hprepared23, alpha23Exact,
      alpha33Exact⟩ :=
    acceptedFoldPowerRunsExact (acceptedAlphaAt alphas 3) alpha23
      alpha33 prepared3 prepared23 (halphas 3) square3 prepare3 prepare23
      alpha33Run
  obtain ⟨final0, final1, final2, final3, grouped3Run, finalCanonical,
      grouped3Exact⟩ :=
    released_second_grouped_rows_corresponds mid0 mid1 mid2 mid3 mid4 mid5
      mid6 (acceptedAlphaAt alphas 3) alpha23 alpha33 midCanonical
      (halphas 3) halpha23 halpha33 alpha23Exact alpha33Exact
  have expected3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
          releasedRowGroups16 (alloc.vec.Vec.new Std.U16) none
          (releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6)
          4#u32 (acceptedAlphaAt alphas 3) alpha23 alpha33 =
        ok (releasedRowGroups4, alloc.vec.Vec.new Std.U16, none,
          releasedFourValues final0 final1 final2 final3) := by
    unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
    change (do
      let pair ←
        V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
          (alloc.vec.Vec.deref releasedRowGroups16)
          (alloc.vec.Vec.deref
            (releasedSevenValues mid0 mid1 mid2 mid3 mid4 mid5 mid6))
          (acceptedAlphaAt alphas 3) alpha23 alpha33
      ok (pair.1, alloc.vec.Vec.new Std.U16, none, pair.2)) = _
    rw [grouped3Run]
    rfl
  have same3 :
      (rows4, masks4, first4, values4) =
        (releasedRowGroups4, alloc.vec.Vec.new Std.U16, none,
          releasedFourValues final0 final1 final2 final3) :=
    Result.ok.inj (helper3.symm.trans expected3)
  cases same3
  refine ⟨{
    value0 := final0
    value1 := final1
    value2 := final2
    value3 := final3
    canonical := finalCanonical
    cell := outputCell3.trans component4Exact
    meaningExact := ?_ }⟩
  have afterTwoMeaningStaged :
      representedGroupedWeights releasedRowGroups64
          (releasedSevenValues afterTwo.values.trace0.value
            afterTwo.values.trace1.value afterTwo.values.trace2.value
            afterTwo.values.trace3.value afterTwo.values.trace4.value
            afterTwo.values.trace5.value afterTwo.values.trace6.value) =
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
          (toMaintainedExact (acceptedAlphaAt alphas 1))
          (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
            (toMaintainedExact (acceptedAlphaAt alphas 0))
            releasedInactiveInitialWeight) := by
    simpa [releasedLowSevenValues, releasedSevenValues,
      releasedSevenValuesStaged] using afterTwo.meaningExact
  rw [grouped3Exact, grouped2Exact, afterTwoMeaningStaged]

#print axioms groupedDeferredDispatchSuccessExposesHelper
#print axioms acceptedPreparedInactiveVectorsExact
#print axioms acceptedInactiveInitialCellExact
#print axioms acceptedInactiveAfterTwoFolds_exists
#print axioms acceptedInactiveTerminal_exists

end AspisV5AcceptedInactiveTerminalJourney
