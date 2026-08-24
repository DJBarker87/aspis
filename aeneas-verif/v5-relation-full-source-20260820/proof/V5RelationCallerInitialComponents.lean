import V5RelationPrepareCanonicalProof

/-!
# Exact initial relation components at the production caller boundary

The preparation extraction uses its own generated namespace.  This module
exposes the exact structural conversion performed by the public caller and
retains the source preparation trace that produced its four initial weight
components.
-/

namespace AspisV5RelationCallerInitialComponents

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationPrepareCanonicalProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev PrepareQM31 := V5RelationPrepareGenerated.aspis_core.field.QM31
abbrev CallerQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev PrepareComponent :=
  V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent
abbrev CallerComponent :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent

def prepareVecToCaller (values : alloc.vec.Vec PrepareQM31) :
    alloc.vec.Vec CallerQM31 :=
  ⟨values.val.map prepareToCallerQM31, by simpa using values.property⟩

def prepareArrayToCaller {count : Std.Usize}
    (values : Array PrepareQM31 count) : Array CallerQM31 count :=
  ⟨values.val.map prepareToCallerQM31, by simpa using values.property⟩

def prepareProductToCaller
    (values : alloc.vec.Vec (Array PrepareQM31 2#usize)) :
    alloc.vec.Vec (Array CallerQM31 2#usize) :=
  ⟨values.val.map prepareArrayToCaller, by simpa using values.property⟩

/-- Public spelling of the component conversion inside the generated caller
wrapper. -/
def prepareComponentToCaller : PrepareComponent → CallerComponent
  | .Geometric scale step =>
      .Geometric (prepareToCallerQM31 scale) (prepareToCallerQM31 step)
  | .Multilinear scale point =>
      .Multilinear (prepareToCallerQM31 scale) (prepareVecToCaller point)
  | .Tensor scale factors =>
      .Tensor (prepareToCallerQM31 scale) (prepareVecToCaller factors)
  | .Product scale factors =>
      .Product (prepareToCallerQM31 scale) (prepareProductToCaller factors)
  | .Dense values => .Dense (prepareVecToCaller values)
  | .Grouped64x16 rows weights logBlocks =>
      .Grouped64x16 rows (prepareVecToCaller weights) logBlocks
  | .Grouped64x16BinaryDeferred rows masks first weights =>
      .Grouped64x16BinaryDeferred rows masks
        (first.map prepareToCallerQM31) (prepareVecToCaller weights)
  | .Grouped128x16 rows weights logBlocks =>
      .Grouped128x16 rows (prepareVecToCaller weights) logBlocks

@[simp] theorem prepareToCaller_callerToPrepare (value : CallerQM31) :
    prepareToCallerQM31 (callerToPrepareQM31 value) = value := by
  rfl

/-- A successful public preparation is exactly the mapped successful source
preparation, retaining both its arithmetic trace and its exact four-component
list. -/
theorem callerPrepareSuccessExposesSourceComponents
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : CallerQM31)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationCallerGenerated.v5_cu_probe.PreparedRelation)
    (point : Array CallerQM31 10#usize)
    (denseScale : CallerQM31)
    (success :
      V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
          parsed
          V5RelationCallerGenerated.v5_cu_probe.RelationVariant.FourClaimsCompact
          kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    ∃ (sourceRelation :
        V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
        (trace :
          AspisV5RelationPrepareLogLenProof.Prepare.PrepareRelationArithmeticTrace
            (callerToPrepareQM31 kappa) (callerToPrepareQM31 inactiveClaim)
            (callerToPrepareClaims preparedClaims) sourceRelation),
      relation.weights.components.val =
        sourceRelation.weights.components.val.map prepareComponentToCaller ∧
      sourceRelation.weights.components.val =
        [V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Multilinear
            V5RelationPrepareGenerated.aspis_core.field.QM31.ONE trace.pointVec0,
         V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Multilinear
            (callerToPrepareQM31 kappa) trace.pointVec1,
         V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Multilinear
            trace.kappa2 trace.pointVec2,
         V5RelationPrepareGenerated.aspis_core.sumcheck.WeightComponent.Grouped64x16BinaryDeferred
            trace.groupedRows trace.groupedMasks none
            (alloc.vec.Vec.new PrepareQM31)] := by
  unfold
    V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
    at success
  generalize sourceRunEquation :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
        _ _ _ _ = sourceResult at success
  cases sourceResult with
  | fail error => simp [sourceRunEquation] at success
  | div => simp [sourceRunEquation] at success
  | ok sourceResult =>
    simp only [sourceRunEquation, bind_tc_ok] at success
    cases sourceResult with
    | Err error => simp at success
    | Ok sourceTriple =>
      rcases sourceTriple with ⟨sourceRelation, sourcePoint, sourceScale⟩
      change
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
            _ (callerToPrepareQM31 kappa) (callerToPrepareQM31 inactiveClaim)
            (callerToPrepareClaims preparedClaims) =
          .ok (.Ok (sourceRelation, sourcePoint, sourceScale))
        at sourceRunEquation
      have sourceFacts :=
        AspisV5RelationPrepareLogLenProof.Prepare.prepare_for_extraction_success_exposes_arithmetic
          _ (callerToPrepareQM31 kappa) (callerToPrepareQM31 inactiveClaim)
          (callerToPrepareClaims preparedClaims) sourceRelation sourcePoint
          sourceScale sourceRunEquation
      rcases sourceFacts with ⟨_, sourceTraceExists⟩
      rcases sourceTraceExists with ⟨sourceTrace⟩
      simp only at success
      have tripleEquality := core.result.Result.Ok.inj (Result.ok.inj success)
      have componentEquality := congrArg
        (fun triple => triple.1.weights.components.val) tripleEquality
      change
        sourceRelation.weights.components.val.map prepareComponentToCaller =
          relation.weights.components.val at componentEquality
      exact ⟨sourceRelation, sourceTrace, componentEquality.symm,
        sourceTrace.initialComponentsExact⟩

#print axioms callerPrepareSuccessExposesSourceComponents

end AspisV5RelationCallerInitialComponents
