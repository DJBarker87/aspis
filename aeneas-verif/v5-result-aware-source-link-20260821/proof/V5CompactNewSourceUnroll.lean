import V5RelationCompactNewGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5CompactNewSourceUnroll

open V5RelationCompactNewGenerated

abbrev Raw := V5RelationCompactNewGenerated.aspis_core.field.QM31
abbrev Block := V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev State :=
  V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights

def unrolledNew (point : Array Raw 10#usize) (scale : Raw) : Result State := do
  let scale8 ← aspis_core.field.QM31.half scale
  let scale7 ← aspis_core.field.QM31.half scale8
  let scale6 ← aspis_core.field.QM31.half scale7
  let scale5 ← aspis_core.field.QM31.half scale6
  let scale4 ← aspis_core.field.QM31.half scale5
  let scale3 ← aspis_core.field.QM31.half scale4
  let scale2 ← aspis_core.field.QM31.half scale3
  let scale1 ← aspis_core.field.QM31.half scale2
  let scale0 ← aspis_core.field.QM31.half scale1
  let point0 ← Array.index_usize point 0#usize
  let square0 ← aspis_core.field.QM31.square point0
  let point1 ← Array.index_usize point 1#usize
  let square1 ← aspis_core.field.QM31.square point1
  let point2 ← Array.index_usize point 2#usize
  let square2 ← aspis_core.field.QM31.square point2
  let point3 ← Array.index_usize point 3#usize
  let square3 ← aspis_core.field.QM31.square point3
  let point4 ← Array.index_usize point 4#usize
  let square4 ← aspis_core.field.QM31.square point4
  let point5 ← Array.index_usize point 5#usize
  let square5 ← aspis_core.field.QM31.square point5
  let point6 ← Array.index_usize point 6#usize
  let square6 ← aspis_core.field.QM31.square point6
  let point7 ← Array.index_usize point 7#usize
  let square7 ← aspis_core.field.QM31.square point7
  let point8 ← Array.index_usize point 8#usize
  let square8 ← aspis_core.field.QM31.square point8
  let point9 ← Array.index_usize point 9#usize
  let square9 ← aspis_core.field.QM31.square point9
  let delta ← aspis_core.field.QM31.half scale0
  ok {
    blocks := Array.make 10#usize [
      { scale := scale0, power_lo := point0, power_hi := square0,
        selector := 0#u8 },
      { scale := scale1, power_lo := point1, power_hi := square1,
        selector := 1#u8 },
      { scale := scale2, power_lo := point2, power_hi := square2,
        selector := 2#u8 },
      { scale := scale3, power_lo := point3, power_hi := square3,
        selector := 3#u8 },
      { scale := scale4, power_lo := point4, power_hi := square4,
        selector := 4#u8 },
      { scale := scale5, power_lo := point5, power_hi := square5,
        selector := 5#u8 },
      { scale := scale6, power_lo := point6, power_hi := square6,
        selector := 6#u8 },
      { scale := scale7, power_lo := point7, power_hi := square7,
        selector := 28#u8 },
      { scale := scale8, power_lo := point8, power_hi := square8,
        selector := 29#u8 },
      { scale := scale, power_lo := point9, power_hi := square9,
        selector := 30#u8 }]
    delta_scale := delta
    folds := 0#u8 }

abbrev Iter :=
  core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)

def scaleStep (round : Std.Usize)
    (blockScales : Array Raw 10#usize) : Result (Array Raw 10#usize) := do
  let i ← lift (Std.Usize.wrapping_add round 1#usize)
  let q ← Array.index_usize blockScales i
  let q1 ← aspis_core.field.QM31.half q
  Array.update blockScales round q1

private theorem concrete_rev_next_9 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 9#usize }⟩ : Iter) =
      .ok (some 8#usize,
        (⟨{ start := 0#usize, «end» := 8#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_8 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 8#usize }⟩ : Iter) =
      .ok (some 7#usize,
        (⟨{ start := 0#usize, «end» := 7#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_7 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 7#usize }⟩ : Iter) =
      .ok (some 6#usize,
        (⟨{ start := 0#usize, «end» := 6#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_6 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 6#usize }⟩ : Iter) =
      .ok (some 5#usize,
        (⟨{ start := 0#usize, «end» := 5#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_5 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 5#usize }⟩ : Iter) =
      .ok (some 4#usize,
        (⟨{ start := 0#usize, «end» := 4#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_4 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 4#usize }⟩ : Iter) =
      .ok (some 3#usize,
        (⟨{ start := 0#usize, «end» := 3#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_3 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 3#usize }⟩ : Iter) =
      .ok (some 2#usize,
        (⟨{ start := 0#usize, «end» := 2#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_2 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 2#usize }⟩ : Iter) =
      .ok (some 1#usize,
        (⟨{ start := 0#usize, «end» := 1#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_1 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 1#usize }⟩ : Iter) =
      .ok (some 0#usize,
        (⟨{ start := 0#usize, «end» := 0#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem concrete_rev_next_0 :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (⟨{ start := 0#usize, «end» := 0#usize }⟩ : Iter) =
      .ok (none,
        (⟨{ start := 0#usize, «end» := 0#usize }⟩ : Iter)) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

private theorem generated_body_step_of_next
    (iter iterAfter : Iter) (round : Std.Usize)
    (blockScales : Array Raw 10#usize)
    (nextRun :
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize) iter =
        .ok (some round, iterAfter)) :
    v5_cu_probe.CompactBTerminalWeights.new_loop.body iter blockScales = (do
      let next ← scaleStep round blockScales
      ok (cont (iterAfter, next))) := by
  unfold v5_cu_probe.CompactBTerminalWeights.new_loop.body scaleStep
  rw [nextRun]
  simp only [bind_tc_ok, bind_assoc_eq]

private theorem generated_loop_step_of_next
    (iter iterAfter : Iter) (round : Std.Usize)
    (blockScales : Array Raw 10#usize)
    (nextRun :
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize) iter =
        .ok (some round, iterAfter)) :
    v5_cu_probe.CompactBTerminalWeights.new_loop iter blockScales = (do
      let next ← scaleStep round blockScales
      v5_cu_probe.CompactBTerminalWeights.new_loop iterAfter next) := by
  unfold v5_cu_probe.CompactBTerminalWeights.new_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [generated_body_step_of_next iter iterAfter round blockScales
    nextRun]
  generalize scaleStep round blockScales = stepResult
  cases stepResult <;> simp

private theorem generated_loop_done_of_next
    (iter iterAfter : Iter) (blockScales : Array Raw 10#usize)
    (nextRun :
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize) iter =
        .ok (none, iterAfter)) :
    v5_cu_probe.CompactBTerminalWeights.new_loop iter blockScales =
      .ok blockScales := by
  have bodyDone :
      v5_cu_probe.CompactBTerminalWeights.new_loop.body iter blockScales =
        .ok (done blockScales) := by
    unfold v5_cu_probe.CompactBTerminalWeights.new_loop.body
    rw [nextRun]
    simp only [bind_tc_ok]
  unfold v5_cu_probe.CompactBTerminalWeights.new_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [bodyDone, bind_tc_ok]

def unrolledScaleLoop (blockScales : Array Raw 10#usize) :
    Result (Array Raw 10#usize) := do
  let scales8 ← scaleStep 8#usize blockScales
  let scales7 ← scaleStep 7#usize scales8
  let scales6 ← scaleStep 6#usize scales7
  let scales5 ← scaleStep 5#usize scales6
  let scales4 ← scaleStep 4#usize scales5
  let scales3 ← scaleStep 3#usize scales4
  let scales2 ← scaleStep 2#usize scales3
  let scales1 ← scaleStep 1#usize scales2
  scaleStep 0#usize scales1

theorem generated_loop_eq_unrolledScaleLoop
    (blockScales : Array Raw 10#usize) :
    v5_cu_probe.CompactBTerminalWeights.new_loop
        (⟨{ start := 0#usize, «end» := 9#usize }⟩ : Iter) blockScales =
      unrolledScaleLoop blockScales := by
  unfold unrolledScaleLoop
  rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_9]
  generalize scaleStep 8#usize blockScales = result8
  cases result8 with
  | fail error => simp
  | div => simp
  | ok scales8 =>
      simp only [bind_tc_ok]
      rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_8]
      generalize scaleStep 7#usize scales8 = result7
      cases result7 with
      | fail error => simp
      | div => simp
      | ok scales7 =>
          simp only [bind_tc_ok]
          rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_7]
          generalize scaleStep 6#usize scales7 = result6
          cases result6 with
          | fail error => simp
          | div => simp
          | ok scales6 =>
              simp only [bind_tc_ok]
              rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_6]
              generalize scaleStep 5#usize scales6 = result5
              cases result5 with
              | fail error => simp
              | div => simp
              | ok scales5 =>
                  simp only [bind_tc_ok]
                  rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_5]
                  generalize scaleStep 4#usize scales5 = result4
                  cases result4 with
                  | fail error => simp
                  | div => simp
                  | ok scales4 =>
                      simp only [bind_tc_ok]
                      rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_4]
                      generalize scaleStep 3#usize scales4 = result3
                      cases result3 with
                      | fail error => simp
                      | div => simp
                      | ok scales3 =>
                          simp only [bind_tc_ok]
                          rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_3]
                          generalize scaleStep 2#usize scales3 = result2
                          cases result2 with
                          | fail error => simp
                          | div => simp
                          | ok scales2 =>
                              simp only [bind_tc_ok]
                              rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_2]
                              generalize scaleStep 1#usize scales2 = result1
                              cases result1 with
                              | fail error => simp
                              | div => simp
                              | ok scales1 =>
                                  simp only [bind_tc_ok]
                                  rw [generated_loop_step_of_next _ _ _ _ concrete_rev_next_1]
                                  generalize scaleStep 0#usize scales1 = result0
                                  cases result0 with
                                  | fail error => simp
                                  | div => simp
                                  | ok scales0 =>
                                      simp only [bind_tc_ok]
                                      exact generated_loop_done_of_next _ _ _
                                        concrete_rev_next_0

private theorem ten_wrapping_sub_one :
    Std.Usize.wrapping_sub 10#usize 1#usize = 9#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_sub_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem zero_wrapping_add_one :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem one_wrapping_add_one :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem two_wrapping_add_one :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem three_wrapping_add_one :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem four_wrapping_add_one :
    Std.Usize.wrapping_add 4#usize 1#usize = 5#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem five_wrapping_add_one :
    Std.Usize.wrapping_add 5#usize 1#usize = 6#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem six_wrapping_add_one :
    Std.Usize.wrapping_add 6#usize 1#usize = 7#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem seven_wrapping_add_one :
    Std.Usize.wrapping_add 7#usize 1#usize = 8#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

private theorem eight_wrapping_add_one :
    Std.Usize.wrapping_add 8#usize 1#usize = 9#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, Usize.ofNatCore_val_eq]
  cases h : System.Platform.numBits_eq <;>
    simp_all [UScalar.size, UScalarTy.numBits, Usize.size, Usize.numBits]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 12000 in
theorem new_eq_unrolled (point : Array Raw 10#usize) (scale : Raw) :
    v5_cu_probe.CompactBTerminalWeights.new point scale =
      unrolledNew point scale := by
  simp only [v5_cu_probe.CompactBTerminalWeights.new,
    v5_cu_probe.V5_CU_PROBE_B_STRUCTURED_BLOCKS,
    ten_wrapping_sub_one, Aeneas.Std.lift, bind_tc_ok,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default]
  simp only [generated_loop_eq_unrolledScaleLoop]
  unfold unrolledScaleLoop scaleStep
  rw [eight_wrapping_add_one, seven_wrapping_add_one,
    six_wrapping_add_one, five_wrapping_add_one,
    four_wrapping_add_one, three_wrapping_add_one,
    two_wrapping_add_one, one_wrapping_add_one,
    zero_wrapping_add_one]
  simp only [Aeneas.Std.lift, bind_tc_ok]
  simp (config := { maxSteps := 400000 })
    [v5_cu_probe.CompactBTerminalWeights.new.closure.Insts.CoreOpsFunctionFnMutTupleUsizeCompactBTerminalBlock.call_mut,
      core.array.from_fn, Array.update, Array.index_usize, Array.repeat,
      unrolledNew, Array.length_eq, Aeneas.Std.Array.make,
      v5_cu_probe.V5_CU_PROBE_B_BLOCK_SELECTORS]

#print axioms new_eq_unrolled

end AspisV5CompactNewSourceUnroll
