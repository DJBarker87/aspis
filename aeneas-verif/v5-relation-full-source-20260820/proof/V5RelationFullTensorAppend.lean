import V5RelationFullLinkedAccumulatorBridge

/-!
# Exact tensor append operations in the complete relation extraction

Each accepted OOD sample appends one `Tensor` component before the round fold.
These theorems expose the exact appended component and prove that every older
component remains at the same index.
-/

namespace AspisV5RelationFullTensorAppend

open Aeneas Aeneas.Std Result ControlFlow

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev FullComponent :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator

deriving instance Inhabited for
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent

/-- The common append helper preserves the log length and appends exactly one
tensor component. -/
theorem addTensorFactorsSuccessShape
    (weights output : FullWeights) (scale : RawQM31)
    (factors : alloc.vec.Vec RawQM31)
    (capacity : weights.components.val.length < Std.Usize.max)
    (success :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
          weights scale factors = .ok (.Ok (), output)) :
    output.log_len = weights.log_len ∧
      output.components.val = weights.components.val ++
        [.Tensor scale factors] := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
    at success
  simp only [Aeneas.Std.lift, bind_tc_ok] at success
  by_cases wrongLength :
      alloc.vec.Vec.len factors != UScalar.cast .Usize weights.log_len
  · rw [if_pos wrongLength] at success
    simp at success
  · rw [if_neg wrongLength] at success
    let component : FullComponent := .Tensor scale factors
    obtain ⟨next, pushRun, nextValues⟩ := Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec weights.components component capacity)
    rw [pushRun] at success
    simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
    rcases success with ⟨_, rfl⟩
    exact ⟨rfl, by simpa [component] using nextValues⟩

/-- An accepted circle-tensor call reaches the common append helper with one
concrete generated factor vector. -/
theorem addCircleTensorSuccessExposesFactors
    (weights output : FullWeights) (scale : RawQM31)
    (point : V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)
    (capacity : weights.components.val.length < Std.Usize.max)
    (success :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
          weights scale point = .ok (.Ok (), output)) :
    ∃ factors,
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
          weights scale factors = .ok (.Ok (), output) ∧
      output.log_len = weights.log_len ∧
      output.components.val = weights.components.val ++
        [.Tensor scale factors] := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
    at success
  by_cases short : weights.log_len < 2#u32
  · rw [if_pos short] at success
    simp at success
  · rw [if_neg short] at success
    simp only [Aeneas.Std.lift, bind_tc_ok] at success
    generalize firstPush :
        alloc.vec.Vec.push
          (alloc.vec.Vec.with_capacity RawQM31
            (UScalar.cast .Usize weights.log_len)) point.y = firstResult
      at success
    cases firstResult with
    | fail error => simp at success
    | div => simp at success
    | ok first =>
      simp only [bind_tc_ok] at success
      generalize secondPush : alloc.vec.Vec.push first point.x = secondResult
        at success
      cases secondResult with
      | fail error => simp at success
      | div => simp at success
      | ok second =>
        simp only [bind_tc_ok] at success
        generalize factorLoop :
            V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor_loop
              { start := 2#u32, «end» := weights.log_len } second point.x =
            loopResult at success
        cases loopResult with
        | fail error => simp at success
        | div => simp at success
        | ok factors =>
          simp only [bind_tc_ok] at success
          have shape := addTensorFactorsSuccessShape weights output scale
            _ capacity success
          exact ⟨_, success, shape.1, shape.2⟩

/-- An accepted line-tensor call reaches the common append helper with one
concrete generated factor vector. -/
theorem addLineTensorSuccessExposesFactors
    (weights output : FullWeights) (scale x : RawQM31)
    (capacity : weights.components.val.length < Std.Usize.max)
    (success :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
          weights scale x = .ok (.Ok (), output)) :
    ∃ factors,
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
          weights scale factors = .ok (.Ok (), output) ∧
      output.log_len = weights.log_len ∧
      output.components.val = weights.components.val ++
        [.Tensor scale factors] := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
    at success
  simp only [Aeneas.Std.lift, bind_tc_ok] at success
  generalize factorLoop :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor_loop
        { start := 0#u32, «end» := weights.log_len } weights.log_len x
        (alloc.vec.Vec.with_capacity RawQM31
          (UScalar.cast .Usize weights.log_len)) = loopResult at success
  cases loopResult with
  | fail error => simp at success
  | div => simp at success
  | ok factors =>
    simp only [bind_tc_ok] at success
    have shape := addTensorFactorsSuccessShape weights output scale _
      capacity success
    exact ⟨_, success, shape.1, shape.2⟩

/-- Appending a tensor leaves every old cell unchanged. -/
theorem oldComponentPreserved
    (weights output : FullWeights) (scale : RawQM31)
    (factors : alloc.vec.Vec RawQM31)
    (shape : output.components.val = weights.components.val ++
      [.Tensor scale factors])
    (index : Nat) (bound : index < weights.components.val.length) :
    output.components.val[index]! = weights.components.val[index]! := by
  rw [shape]
  exact List.getElem!_append_left _ _ index bound

#print axioms addTensorFactorsSuccessShape
#print axioms addCircleTensorSuccessExposesFactors
#print axioms addLineTensorSuccessExposesFactors

end AspisV5RelationFullTensorAppend
