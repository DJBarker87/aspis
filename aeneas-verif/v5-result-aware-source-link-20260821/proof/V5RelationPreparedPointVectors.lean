import V5AcceptedAccumulatorSchedule

/-!
# Exact prepared relation point vectors

The preparation trace now retains the three successful point decoders and
the three exact array-to-vector calls that created the initial multilinear
components.  This module gives those vectors their direct list meaning.
-/

namespace AspisV5RelationPreparedPointVectors

open Aeneas Aeneas.Std Result
open AspisV5RelationPrepareLogLenProof.Prepare

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev PrepareQM31 := V5RelationPrepareGenerated.aspis_core.field.QM31

local instance : Inhabited PrepareQM31 :=
  ⟨V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO⟩

private theorem tenBelowUsizeMax : 10 < Std.Usize.max := by
  rw [Std.Usize.max, Std.Usize.numBits, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with bits | bits <;>
    rw [bits] <;> norm_num

private theorem arrayIndexRun
    (point : Array PrepareQM31 10#usize) (index : Std.Usize)
    (bound : index.val < 10) :
    Array.index_usize point index = .ok point.val[index.val]! := by
  have actualBound : index.val < point.val.length := by
    rw [point.property]
    exact bound
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec point index (by
      simpa [Array.length_eq, point.property] using bound))
  have bangExact : point.val[index.val]! = point.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp [actualBound]
  simpa [exact, bangExact] using run

/-- The generated helper copies the ten array cells in order, without
permuting or changing any field element. -/
theorem relationPointVecSuccessExact
    (point : Array PrepareQM31 10#usize)
    (output : alloc.vec.Vec PrepareQM31)
    (success :
      V5RelationPrepareGenerated.v5_cu_probe.relation_point_vec_for_extraction
          point = .ok output) :
    output.val = point.val := by
  unfold
    V5RelationPrepareGenerated.v5_cu_probe.relation_point_vec_for_extraction
    at success
  simp only [Aeneas.Std.lift, bind_tc_ok] at success
  let empty := alloc.vec.Vec.new PrepareQM31
  have emptyVal : empty.val = [] := by rfl
  have read0 : Array.index_usize point 0#usize = .ok point.val[0] := by
    simpa [point.property] using arrayIndexRun point 0#usize (by norm_num)
  have read1 : Array.index_usize point 1#usize = .ok point.val[1] := by
    simpa [point.property] using arrayIndexRun point 1#usize (by norm_num)
  have read2 : Array.index_usize point 2#usize = .ok point.val[2] := by
    simpa [point.property] using arrayIndexRun point 2#usize (by norm_num)
  have read3 : Array.index_usize point 3#usize = .ok point.val[3] := by
    simpa [point.property] using arrayIndexRun point 3#usize (by norm_num)
  have read4 : Array.index_usize point 4#usize = .ok point.val[4] := by
    simpa [point.property] using arrayIndexRun point 4#usize (by norm_num)
  have read5 : Array.index_usize point 5#usize = .ok point.val[5] := by
    simpa [point.property] using arrayIndexRun point 5#usize (by norm_num)
  have read6 : Array.index_usize point 6#usize = .ok point.val[6] := by
    simpa [point.property] using arrayIndexRun point 6#usize (by norm_num)
  have read7 : Array.index_usize point 7#usize = .ok point.val[7] := by
    simpa [point.property] using arrayIndexRun point 7#usize (by norm_num)
  have read8 : Array.index_usize point 8#usize = .ok point.val[8] := by
    simpa [point.property] using arrayIndexRun point 8#usize (by norm_num)
  have read9 : Array.index_usize point 9#usize = .ok point.val[9] := by
    simpa [point.property] using arrayIndexRun point 9#usize (by norm_num)
  obtain ⟨v1, push1, v1Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec empty point.val[0] (by
      simp only [empty, alloc.vec.Vec.new, List.length_nil]
      exact Nat.zero_lt_of_lt tenBelowUsizeMax))
  obtain ⟨v2, push2, v2Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v1 point.val[1] (by
      rw [v1Val, emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v3, push3, v3Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v2 point.val[2] (by
      rw [v2Val, v1Val, emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v4, push4, v4Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v3 point.val[3] (by
      rw [v3Val, v2Val, v1Val, emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v5, push5, v5Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v4 point.val[4] (by
      rw [v4Val, v3Val, v2Val, v1Val, emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v6, push6, v6Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v5 point.val[5] (by
      rw [v5Val, v4Val, v3Val, v2Val, v1Val, emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v7, push7, v7Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v6 point.val[6] (by
      rw [v6Val, v5Val, v4Val, v3Val, v2Val, v1Val, emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v8, push8, v8Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v7 point.val[7] (by
      rw [v7Val, v6Val, v5Val, v4Val, v3Val, v2Val, v1Val, emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v9, push9, v9Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v8 point.val[8] (by
      rw [v8Val, v7Val, v6Val, v5Val, v4Val, v3Val, v2Val, v1Val,
        emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  obtain ⟨v10, push10, v10Val⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v9 point.val[9] (by
      rw [v9Val, v8Val, v7Val, v6Val, v5Val, v4Val, v3Val, v2Val, v1Val,
        emptyVal]
      simp only [List.length_append, List.length_singleton, List.length_nil]
      exact lt_trans (by norm_num) tenBelowUsizeMax))
  change (do
    let q ← Array.index_usize point 0#usize
    let output1 ← alloc.vec.Vec.push empty q
    let q1 ← Array.index_usize point 1#usize
    let output2 ← alloc.vec.Vec.push output1 q1
    let q2 ← Array.index_usize point 2#usize
    let output3 ← alloc.vec.Vec.push output2 q2
    let q3 ← Array.index_usize point 3#usize
    let output4 ← alloc.vec.Vec.push output3 q3
    let q4 ← Array.index_usize point 4#usize
    let output5 ← alloc.vec.Vec.push output4 q4
    let q5 ← Array.index_usize point 5#usize
    let output6 ← alloc.vec.Vec.push output5 q5
    let q6 ← Array.index_usize point 6#usize
    let output7 ← alloc.vec.Vec.push output6 q6
    let q7 ← Array.index_usize point 7#usize
    let output8 ← alloc.vec.Vec.push output7 q7
    let q8 ← Array.index_usize point 8#usize
    let output9 ← alloc.vec.Vec.push output8 q8
    let q9 ← Array.index_usize point 9#usize
    alloc.vec.Vec.push output9 q9) = .ok output at success
  rw [read0] at success
  simp only [bind_tc_ok] at success
  rw [push1] at success
  simp only [bind_tc_ok] at success
  rw [read1] at success
  simp only [bind_tc_ok] at success
  rw [push2] at success
  simp only [bind_tc_ok] at success
  rw [read2] at success
  simp only [bind_tc_ok] at success
  rw [push3] at success
  simp only [bind_tc_ok] at success
  rw [read3] at success
  simp only [bind_tc_ok] at success
  rw [push4] at success
  simp only [bind_tc_ok] at success
  rw [read4] at success
  simp only [bind_tc_ok] at success
  rw [push5] at success
  simp only [bind_tc_ok] at success
  rw [read5] at success
  simp only [bind_tc_ok] at success
  rw [push6] at success
  simp only [bind_tc_ok] at success
  rw [read6] at success
  simp only [bind_tc_ok] at success
  rw [push7] at success
  simp only [bind_tc_ok] at success
  rw [read7] at success
  simp only [bind_tc_ok] at success
  rw [push8] at success
  simp only [bind_tc_ok] at success
  rw [read8] at success
  simp only [bind_tc_ok] at success
  rw [push9] at success
  simp only [bind_tc_ok] at success
  rw [read9] at success
  simp only [bind_tc_ok] at success
  rw [push10] at success
  have outputExact : output = v10 := (Result.ok.inj success).symm
  rw [outputExact, v10Val, v9Val, v8Val, v7Val, v6Val, v5Val, v4Val,
    v3Val, v2Val, v1Val, emptyVal]
  apply List.ext_get
  · simpa using point.property.symm
  · intro index leftBound rightBound
    have indexBound : index < 10 := by simpa using leftBound
    interval_cases index <;> rfl

/-- Consequently every retained prepared point vector has exactly ten
entries and agrees cell-for-cell with its decoded point array. -/
theorem preparedPointVectorsExact
    {kappa inactiveClaim : PrepareQM31}
    {preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation}
    (trace : PrepareRelationArithmeticTrace kappa inactiveClaim
      preparedClaims relation) :
    trace.pointVec0.val = trace.point0.val ∧
      trace.pointVec1.val = trace.point1.val ∧
      trace.pointVec2.val = trace.point2.val ∧
      trace.pointVec0.val.length = 10 ∧
      trace.pointVec1.val.length = 10 ∧
      trace.pointVec2.val.length = 10 := by
  have exact0 := relationPointVecSuccessExact trace.point0 trace.pointVec0
    trace.pointVec0Run
  have exact1 := relationPointVecSuccessExact trace.point1 trace.pointVec1
    trace.pointVec1Run
  have exact2 := relationPointVecSuccessExact trace.point2 trace.pointVec2
    trace.pointVec2Run
  refine ⟨exact0, exact1, exact2, ?_, ?_, ?_⟩
  · simpa [exact0] using trace.point0.property
  · simpa [exact1] using trace.point1.property
  · simpa [exact2] using trace.point2.property

#print axioms relationPointVecSuccessExact
#print axioms preparedPointVectorsExact

end AspisV5RelationPreparedPointVectors
