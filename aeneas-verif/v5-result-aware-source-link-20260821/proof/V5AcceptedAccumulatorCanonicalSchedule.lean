import V5AcceptedTensorFactorCanonical

/-!
# Canonical tensor cells in the accepted accumulator schedule

This file connects the factor vectors constructed by the generated circle and
line wrappers to the exact eight tensor cells retained by the accepted
four-round schedule.
-/

namespace AspisV5AcceptedAccumulatorCanonicalSchedule

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationAcceptanceSourceProof
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedTensorFactorCanonical
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedTerminalDotSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
abbrev CirclePoint :=
  V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint

local instance : Inhabited CirclePoint :=
  ⟨{ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
     y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO }⟩

/-- Both coordinates of both circle points retained by the accepted relation
driver have canonical base-field representatives. -/
def CanonicalCirclePoints (points : Array CirclePoint 2#usize) : Prop :=
  ∀ index : Fin 2,
    CanonicalQM31 points.val[index.val]!.x ∧
      CanonicalQM31 points.val[index.val]!.y

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Std.Usize)
    (bound : index.val < count.val) :
    Array.index_usize values index = .ok values.val[index.val]! := by
  obtain ⟨value, run, valueExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using bound))
  have listBound : index.val < values.val.length := by
    simpa [Array.length_eq] using bound
  have bangExact : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueExact, bangExact] using run

private theorem indexedCirclePointCanonical
    (points : Array CirclePoint 2#usize)
    (canonical : CanonicalCirclePoints points)
    (sample : Std.Usize) (point : CirclePoint)
    (bound : sample.val < 2)
    (run : Array.index_usize points sample = .ok point) :
    CanonicalQM31 point.x ∧ CanonicalQM31 point.y := by
  have exactRun := arrayIndexRun points sample bound
  rw [exactRun] at run
  have pointExact : point = points.val[sample.val]! := Result.ok.inj run.symm
  subst point
  exact canonical ⟨sample.val, bound⟩

private theorem tensorFactorsUniqueFromShapes
    (weights output : FullWeights) (scale : RawQM31)
    (left right : alloc.vec.Vec RawQM31)
    (leftShape : output.components.val = weights.components.val ++
      [.Tensor scale left])
    (rightShape : output.components.val = weights.components.val ++
      [.Tensor scale right]) :
    left = right := by
  have appended :
      weights.components.val ++ [.Tensor scale left] =
        weights.components.val ++ [.Tensor scale right] :=
    leftShape.symm.trans rightShape
  have singletonExact := List.append_cancel_left appended
  simpa using singletonExact

/-- Canonicality and exact source lengths for the two tensor cells appended
by one accepted relation round. -/
structure CanonicalAcceptedRoundTensorSchedule {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array CirclePoint 2#usize)
    (additive nextAdditive : A)
    (round : Std.Usize) (alpha : RawQM31)
    (weights0 nextWeights : FullWeights)
    (claim0 nextClaim : RawQM31)
    (trace : AcceptedTwoSampleRoundExecution additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim)
    (schedule : AcceptedRoundTensorSchedule additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim
      trace) : Prop where
  firstMixCanonical : CanonicalQM31 trace.sample0.mix
  secondMixCanonical : CanonicalQM31 trace.sample1.mix
  firstFactorsCanonical : CanonicalList schedule.firstFactors.val
  secondFactorsCanonical : CanonicalList schedule.secondFactors.val
  firstFactorsLength : schedule.firstFactors.val.length =
    (UScalar.cast .Usize weights0.log_len).val
  secondFactorsLength : schedule.secondFactors.val.length =
    (UScalar.cast .Usize trace.weights1.log_len).val

/-- The decoder provenance of the accepted samples and circle points proves
that both tensor cells selected by this round are canonical. -/
theorem acceptedRoundTensorScheduleCanonical {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array CirclePoint 2#usize)
    (additive nextAdditive : A)
    (round : Std.Usize) (alpha : RawQM31)
    (weights0 nextWeights : FullWeights)
    (claim0 nextClaim : RawQM31)
    (trace : AcceptedTwoSampleRoundExecution additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim)
    (schedule : AcceptedRoundTensorSchedule additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim
      trace)
    (circleCanonical : round = 0#usize → CanonicalCirclePoints circlePoints) :
    CanonicalAcceptedRoundTensorSchedule additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim
      trace schedule := by
  have firstMixCanonical := accepted_decode_indexed_is_canonical bytes
    trace.sample0.mixOffset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
      0#usize) trace.sample0.mix trace.sample0.mixDecodeRun
  have secondMixCanonical := accepted_decode_indexed_is_canonical bytes
    trace.sample1.mixOffset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
      1#usize) trace.sample1.mix trace.sample1.mixDecodeRun
  have firstFactorsCanonical : CanonicalList schedule.firstFactors.val := by
    by_cases roundZero : round = 0#usize
    · obtain ⟨point, pointRun, appendRun⟩ :=
        trace.sample0WeightUpdate.circle roundZero
      have pointCanonical := indexedCirclePointCanonical circlePoints
        (circleCanonical roundZero) 0#usize point (by decide) pointRun
      obtain ⟨factors, commonRun, factorsCanonical⟩ :=
        addCircleTensorSuccessCanonicalFactors weights0 trace.weights1
          trace.sample0.mix point pointCanonical.1 pointCanonical.2 appendRun
      have actualShape :=
        (addTensorFactorsSuccessShapeExact weights0 trace.weights1
          trace.sample0.mix factors commonRun).2
      have factorsExact := tensorFactorsUniqueFromShapes weights0
        trace.weights1 trace.sample0.mix factors schedule.firstFactors
        actualShape schedule.firstShape
      simpa [factorsExact] using factorsCanonical
    · obtain ⟨lineOffset, lineValue, _, lineRun, appendRun⟩ :=
        trace.sample0WeightUpdate.line roundZero
      have lineCanonical := accepted_decode_indexed_is_canonical bytes
        lineOffset
        (Std.Usize.wrapping_add
          (Std.Usize.wrapping_mul
            (Std.Usize.wrapping_sub round 1#usize)
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
          0#usize) lineValue lineRun
      obtain ⟨factors, commonRun, factorsCanonical⟩ :=
        addLineTensorSuccessCanonicalFactors weights0 trace.weights1
          trace.sample0.mix lineValue lineCanonical appendRun
      have actualShape :=
        (addTensorFactorsSuccessShapeExact weights0 trace.weights1
          trace.sample0.mix factors commonRun).2
      have factorsExact := tensorFactorsUniqueFromShapes weights0
        trace.weights1 trace.sample0.mix factors schedule.firstFactors
        actualShape schedule.firstShape
      simpa [factorsExact] using factorsCanonical
  have secondFactorsCanonical : CanonicalList schedule.secondFactors.val := by
    by_cases roundZero : round = 0#usize
    · obtain ⟨point, pointRun, appendRun⟩ :=
        trace.sample1WeightUpdate.circle roundZero
      have pointCanonical := indexedCirclePointCanonical circlePoints
        (circleCanonical roundZero) 1#usize point (by decide) pointRun
      obtain ⟨factors, commonRun, factorsCanonical⟩ :=
        addCircleTensorSuccessCanonicalFactors trace.weights1 trace.weights2
          trace.sample1.mix point pointCanonical.1 pointCanonical.2 appendRun
      have actualShape :=
        (addTensorFactorsSuccessShapeExact trace.weights1 trace.weights2
          trace.sample1.mix factors commonRun).2
      have factorsExact := tensorFactorsUniqueFromShapes trace.weights1
        trace.weights2 trace.sample1.mix factors schedule.secondFactors
        actualShape (by
          rw [schedule.secondShape, schedule.firstShape]
          simp only [List.append_assoc]
          rfl)
      simpa [factorsExact] using factorsCanonical
    · obtain ⟨lineOffset, lineValue, _, lineRun, appendRun⟩ :=
        trace.sample1WeightUpdate.line roundZero
      have lineCanonical := accepted_decode_indexed_is_canonical bytes
        lineOffset
        (Std.Usize.wrapping_add
          (Std.Usize.wrapping_mul
            (Std.Usize.wrapping_sub round 1#usize)
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
          1#usize) lineValue lineRun
      obtain ⟨factors, commonRun, factorsCanonical⟩ :=
        addLineTensorSuccessCanonicalFactors trace.weights1 trace.weights2
          trace.sample1.mix lineValue lineCanonical appendRun
      have actualShape :=
        (addTensorFactorsSuccessShapeExact trace.weights1 trace.weights2
          trace.sample1.mix factors commonRun).2
      have factorsExact := tensorFactorsUniqueFromShapes trace.weights1
        trace.weights2 trace.sample1.mix factors schedule.secondFactors
        actualShape (by
          rw [schedule.secondShape, schedule.firstShape]
          simp only [List.append_assoc]
          rfl)
      simpa [factorsExact] using factorsCanonical
  exact {
    firstMixCanonical := firstMixCanonical
    secondMixCanonical := secondMixCanonical
    firstFactorsCanonical := firstFactorsCanonical
    secondFactorsCanonical := secondFactorsCanonical
    firstFactorsLength :=
      addTensorFactorsSuccessLength weights0 trace.weights1
        trace.sample0.mix schedule.firstFactors schedule.firstAppendRun
    secondFactorsLength :=
      addTensorFactorsSuccessLength trace.weights1 trace.weights2
        trace.sample1.mix schedule.secondFactors schedule.secondAppendRun }

#print axioms acceptedRoundTensorScheduleCanonical

end AspisV5AcceptedAccumulatorCanonicalSchedule
