import V5RelationGeneratedSupportProof
import AspisFormal.V5RelationStressSourceBridge

/-!
# Complete generated V5 relation verifier

This file connects the exact Aeneas translation of the unchanged nested Rust
loops to the maintained relation model.  The first section removes the two
fixed mutable-array loops from the proof surface: four final coefficients and
seven round coefficients are read in increasing wire order and written back to
the corresponding array slots.
-/

namespace AspisV5RelationFullSourceProof

open Aeneas Aeneas.Std Result ControlFlow Error
open V5RelationFullGenerated

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31

private theorem usizeAddExact (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have hspec := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

deriving instance DecidableEq for
  V5RelationLinkedGenerated.aspis_core.field.CM31
deriving instance DecidableEq for
  V5RelationLinkedGenerated.aspis_core.field.QM31

theorem raw_qm31_eq_spec (left right : RawQM31) :
    V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
        left right = .ok (decide (left = right)) := by
  rcases left with ⟨⟨la0, la1⟩, ⟨lb0, lb1⟩⟩
  rcases right with ⟨⟨ra0, ra1⟩, ⟨rb0, rb1⟩⟩
  by_cases h0 : la0 = ra0 <;> by_cases h1 : la1 = ra1 <;>
    by_cases h2 : lb0 = rb0 <;> by_cases h3 : lb1 = rb1 <;>
    simp_all [
      V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      V5RelationFullGenerated.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      V5RelationFullGenerated.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]

theorem raw_qm31_ne_spec (left right : RawQM31) :
    core.cmp.PartialEq.ne.trait_default
        V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
        left right = .ok (decide (left ≠ right)) := by
  simp [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default, raw_qm31_eq_spec]

def fourValues (v0 v1 v2 v3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [v0, v1, v2, v3]

def sevenValues (v0 v1 v2 v3 v4 v5 v6 : RawQM31) :
    Array RawQM31 7#usize :=
  Array.make 7#usize [v0, v1, v2, v3, v4, v5, v6]

theorem generated_final_decoder_success_exact
    (bytes : Array Std.U8 928#usize) (offset : Std.Usize)
    (v0 v1 v2 v3 : RawQM31)
    (offsetExact :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_FINAL_OFFSET =
        .ok offset)
    (read0 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset 0#usize =
        .ok (.Ok v0))
    (read1 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset 1#usize =
        .ok (.Ok v1))
    (read2 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset 2#usize =
        .ok (.Ok v2))
    (read3 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset 3#usize =
        .ok (.Ok v3)) :
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final bytes =
      .ok (.Ok (fourValues v0 v1 v2 v3)) := by
  unfold V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final
  simp only [Aeneas.Std.lift, bind_tc_ok,
    core.slice.Slice.iter_mut, V5MutableEnumerateSupport.enumerate]
  unfold V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final_loop
  have firstInBounds :
      (0 : Nat) < (Array.repeat 4#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 0 < (Array.repeat 4#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExact <;> scalar_tac
  have secondInBounds :
      (1 : Nat) < (Array.repeat 4#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 1 < (Array.repeat 4#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have thirdInBounds :
      (2 : Nat) < (Array.repeat 4#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 2 < (Array.repeat 4#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have fourthInBounds :
      (3 : Nat) < (Array.repeat 4#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 3 < (Array.repeat 4#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have iteratorExhausted :
      ¬ (4 : Nat) < (Array.repeat 4#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change ¬ 4 < (Array.repeat 4#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have count1Next : 1#usize + 1#usize = ok 2#usize := by
    apply usizeAddExact <;> scalar_tac
  have count2Next : 2#usize + 1#usize = ok 3#usize := by
    apply usizeAddExact <;> scalar_tac
  have count3Next : 3#usize + 1#usize = ok 4#usize := by
    apply usizeAddExact <;> scalar_tac
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final_loop.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, firstInBounds, count0Next,
    core.result.Result.Insts.CoreOpsTry.branch, offsetExact, read0]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final_loop.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, secondInBounds, count1Next,
    core.result.Result.Insts.CoreOpsTry.branch, offsetExact, read1]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final_loop.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, thirdInBounds, count2Next,
    core.result.Result.Insts.CoreOpsTry.branch, offsetExact, read2]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final_loop.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, fourthInBounds, count3Next,
    core.result.Result.Insts.CoreOpsTry.branch, offsetExact, read3]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final_loop.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, iteratorExhausted,
    fourValues, Array.to_slice_mut,
    Array.to_slice, Array.from_slice]
  apply Subtype.ext
  simp [fourValues, Array.make, Slice.setAtNat, Array.repeat_val]

/-- A successful execution of the innermost production loop reads exactly
seven consecutive polynomial coefficients, reconstructs the exact array,
checks its boundary against the running claim, evaluates it, and hands both
weight states back after one fold. -/
theorem generated_polynomial_loop_success_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize)
    (additive nextAdditive : A)
    (round base offset : Std.Usize)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (v0 v1 v2 v3 v4 v5 v6 : RawQM31)
    (baseExact :
      Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS =
          base)
    (offsetExact :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET =
        .ok offset)
    (read0 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add base 0#usize) = .ok (.Ok v0))
    (read1 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add base 1#usize) = .ok (.Ok v1))
    (read2 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add base 2#usize) = .ok (.Ok v2))
    (read3 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add base 3#usize) = .ok (.Ok v3))
    (read4 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add base 4#usize) = .ok (.Ok v4))
    (read5 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add base 5#usize) = .ok (.Ok v5))
    (read6 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add base 6#usize) = .ok (.Ok v6))
    (boundaryExact :
      V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum
        (sevenValues v0 v1 v2 v3 v4 v5 v6) = .ok runningClaim)
    (evaluateExact :
      V5RelationFullGenerated.aspis_core.sumcheck.evaluate
        (sevenValues v0 v1 v2 v3 v4 v5 v6) alpha = .ok nextClaim)
    (weightFoldExact :
      aspis_core.sumcheck.WeightAccumulator.fold
        weights alpha = .ok nextWeights)
    (additiveFoldExact : additiveInst.fold additive alpha = .ok nextAdditive) :
    (do
      let polynomial := Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO
      let (s, toSliceBack) ← lift (Array.to_slice_mut polynomial)
      let (im, iterBack) ← core.slice.Slice.iter_mut s
      let (iter, enumerateBack) ← V5MutableEnumerateSupport.enumerate im
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
        additiveInst toSliceBack iterBack enumerateBack iter (fun e => e)
        weights runningClaim bytes additive round alpha pending) =
      .ok (nextWeights, nextClaim, nextAdditive, pending, 1#u32) := by
  simp only [Aeneas.Std.lift, bind_tc_ok, core.slice.Slice.iter_mut,
    V5MutableEnumerateSupport.enumerate]
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
  have inBounds0 :
      (0 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 0 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds1 :
      (1 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 1 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds2 :
      (2 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 2 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds3 :
      (3 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 3 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds4 :
      (4 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 4 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds5 :
      (5 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 5 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds6 :
      (6 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 6 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have exhausted :
      ¬ (7 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change ¬ 7 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExact <;> scalar_tac
  have count1Next : 1#usize + 1#usize = ok 2#usize := by
    apply usizeAddExact <;> scalar_tac
  have count2Next : 2#usize + 1#usize = ok 3#usize := by
    apply usizeAddExact <;> scalar_tac
  have count3Next : 3#usize + 1#usize = ok 4#usize := by
    apply usizeAddExact <;> scalar_tac
  have count4Next : 4#usize + 1#usize = ok 5#usize := by
    apply usizeAddExact <;> scalar_tac
  have count5Next : 5#usize + 1#usize = ok 6#usize := by
    apply usizeAddExact <;> scalar_tac
  have count6Next : 6#usize + 1#usize = ok 7#usize := by
    apply usizeAddExact <;> scalar_tac
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds0, count0Next,
    Aeneas.Std.lift, bind_tc_ok, baseExact, offsetExact, read0,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds1, count1Next,
    Aeneas.Std.lift, bind_tc_ok, baseExact, offsetExact, read1,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds2, count2Next,
    Aeneas.Std.lift, bind_tc_ok, baseExact, offsetExact, read2,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds3, count3Next,
    Aeneas.Std.lift, bind_tc_ok, baseExact, offsetExact, read3,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds4, count4Next,
    Aeneas.Std.lift, bind_tc_ok, baseExact, offsetExact, read4,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds5, count5Next,
    Aeneas.Std.lift, bind_tc_ok, baseExact, offsetExact, read5,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds6, count6Next,
    Aeneas.Std.lift, bind_tc_ok, baseExact, offsetExact, read6,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, exhausted,
    Array.to_slice_mut, Array.to_slice, Array.from_slice]
  simp only [Slice.setAtNat, Array.repeat_val, sevenValues, Array.make,
    List.set]
  have boundaryForAny
      (polynomial : Array RawQM31 7#usize)
      (valuesExact : polynomial.val = [v0, v1, v2, v3, v4, v5, v6]) :
      V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum polynomial =
        .ok runningClaim := by
    have polynomialExact :
        polynomial = sevenValues v0 v1 v2 v3 v4 v5 v6 := by
      apply Subtype.ext
      simpa [sevenValues, Array.make] using valuesExact
    simpa [polynomialExact] using boundaryExact
  have evaluateForAny
      (polynomial : Array RawQM31 7#usize)
      (valuesExact : polynomial.val = [v0, v1, v2, v3, v4, v5, v6]) :
      V5RelationFullGenerated.aspis_core.sumcheck.evaluate polynomial alpha =
        .ok nextClaim := by
    have polynomialExact :
        polynomial = sevenValues v0 v1 v2 v3 v4 v5 v6 := by
      apply Subtype.ext
      simpa [sevenValues, Array.make] using valuesExact
    simpa [polynomialExact] using evaluateExact
  rw [boundaryForAny _ rfl]
  simp only [bind_tc_ok]
  rw [raw_qm31_ne_spec]
  have neSelf : decide (runningClaim ≠ runningClaim) = false := by simp
  rw [neSelf]
  simp only [bind_tc_ok, Bool.false_eq_true, if_false]
  rw [evaluateForAny]
  · simp [weightFoldExact, additiveFoldExact]
  · rfl

def range2At (start : Std.Usize) : core.ops.range.Range Std.Usize :=
  { start, «end» := 2#usize }

theorem range2_next_some
    (start : Std.Usize) (startInBounds : start.val < 2) :
    ∃ next : Std.Usize,
      next.val = start.val + 1 ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          (range2At start) = .ok (some start, range2At next) := by
  have specification := core.iter.range.IteratorRange.next_Usize_some_spec
    (range2At start) (by simpa [range2At] using startInBounds)
  rcases Aeneas.Std.WP.spec_imp_exists specification with
    ⟨⟨option, nextRange⟩, nextExact, optionExact, nextStart, nextEnd⟩
  subst option
  let next : Std.Usize := nextRange.start
  have rangeExact : nextRange = range2At next := by
    cases nextRange
    simp only [range2At, core.ops.range.Range.mk.injEq]
    exact ⟨rfl, nextEnd⟩
  exact ⟨next, nextStart, by simpa [range2At, rangeExact] using nextExact⟩

theorem range2_next_none :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        (range2At 2#usize) = .ok (none, range2At 2#usize) := by
  have specification := core.iter.range.IteratorRange.next_Usize_none_spec
    (range2At 2#usize) (by simp [range2At])
  rcases Aeneas.Std.WP.spec_imp_exists specification with
    ⟨⟨option, nextRange⟩, nextExact, optionExact, rangeExact⟩
  simpa [optionExact, rangeExact] using nextExact

theorem range2_next_zero :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        (range2At 0#usize) = .ok (some 0#usize, range2At 1#usize) := by
  obtain ⟨next, nextValue, nextExact⟩ :=
    range2_next_some 0#usize (by decide)
  have nextIsOne : next = 1#usize := by
    apply UScalar.eq_of_val_eq
    simpa using nextValue
  simpa [nextIsOne] using nextExact

theorem range2_next_one :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        (range2At 1#usize) = .ok (some 1#usize, range2At 2#usize) := by
  obtain ⟨next, nextValue, nextExact⟩ :=
    range2_next_some 1#usize (by decide)
  have nextIsTwo : next = 2#usize := by
    apply UScalar.eq_of_val_eq
    simpa using nextValue
  simpa [nextIsTwo] using nextExact

theorem generated_round_zero_sample_step_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize) (additive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (alpha : RawQM31)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (range nextRange : core.ops.range.Range Std.Usize)
    (sample observation oodOffset mixOffset : Std.Usize)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim nextClaim value mix product : RawQM31)
    (point : V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)
    (nextExact :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
        .ok (some sample, nextRange))
    (observationExact :
      Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul 0#usize
          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
        sample = observation)
    (oodOffsetExact :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_OFFSET =
        .ok oodOffset)
    (mixOffsetExact :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_MIX_OFFSET =
        .ok mixOffset)
    (valueExact :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes oodOffset
        observation = .ok (.Ok value))
    (mixExact :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes mixOffset
        observation = .ok (.Ok mix))
    (pointExact : Array.index_usize circlePoints sample = .ok point)
    (tensorExact :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
        weights mix point = .ok (.Ok (), nextWeights))
    (productExact :
      V5RelationFullGenerated.aspis_core.field.QM31.mul mix value =
        .ok product)
    (claimExact :
      V5RelationFullGenerated.aspis_core.field.QM31.add runningClaim product =
        .ok nextClaim) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
        additiveInst bytes additive circlePoints 0#usize alpha pending range
        weights runningClaim =
      .ok (.cont (nextRange, nextWeights, nextClaim)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
  rw [nextExact]
  simp only [bind_tc_ok, Aeneas.Std.lift, observationExact,
    oodOffsetExact, valueExact,
    core.result.Result.Insts.CoreOpsTry.branch,
    mixOffsetExact, mixExact, pointExact, tensorExact,
    productExact, claimExact]
  rfl

theorem generated_later_round_sample_step_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize) (additive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round : Std.Usize)
    (alphaValue : RawQM31)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (range nextRange : core.ops.range.Range Std.Usize)
    (sample observation previousRound lineBase lineIndex : Std.Usize)
    (oodOffset mixOffset lineOffset : Std.Usize)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim nextClaim value mix lineValue product : RawQM31)
    (nextExact :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
        .ok (some sample, nextRange))
    (roundNonzero : round ≠ 0#usize)
    (observationExact :
      Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
        sample = observation)
    (previousRoundExact :
      Std.Usize.wrapping_sub round 1#usize = previousRound)
    (lineBaseExact :
      Std.Usize.wrapping_mul previousRound
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES =
          lineBase)
    (lineIndexExact :
      Std.Usize.wrapping_add lineBase sample = lineIndex)
    (oodOffsetExact :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_OFFSET =
        .ok oodOffset)
    (mixOffsetExact :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_MIX_OFFSET =
        .ok mixOffset)
    (lineOffsetExact :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_LINE_OFFSET =
        .ok lineOffset)
    (valueExact :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes oodOffset
        observation = .ok (.Ok value))
    (mixExact :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes mixOffset
        observation = .ok (.Ok mix))
    (lineExact :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes lineOffset
        lineIndex = .ok (.Ok lineValue))
    (tensorExact :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
        weights mix lineValue = .ok (.Ok (), nextWeights))
    (productExact :
      V5RelationFullGenerated.aspis_core.field.QM31.mul mix value =
        .ok product)
    (claimExact :
      V5RelationFullGenerated.aspis_core.field.QM31.add runningClaim product =
        .ok nextClaim) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
        additiveInst bytes additive circlePoints round alphaValue pending range
        weights runningClaim =
      .ok (.cont (nextRange, nextWeights, nextClaim)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
  rw [nextExact]
  simp only [bind_tc_ok, Aeneas.Std.lift, observationExact,
    oodOffsetExact, valueExact,
    core.result.Result.Insts.CoreOpsTry.branch,
    mixOffsetExact, mixExact, roundNonzero, if_false,
    previousRoundExact, lineBaseExact, lineIndexExact,
    lineOffsetExact, lineExact, tensorExact, productExact, claimExact]

theorem generated_sample_exhaustion_runs_polynomial
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round : Std.Usize) (alpha runningClaim nextClaim : RawQM31)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (polynomialExact :
      (do
        let polynomial := Array.repeat 7#usize
          V5RelationFullGenerated.aspis_core.field.QM31.ZERO
        let (s, toSliceBack) ← lift (Array.to_slice_mut polynomial)
        let (im, iterBack) ← core.slice.Slice.iter_mut s
        let (iter, enumerateBack) ← V5MutableEnumerateSupport.enumerate im
        V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
          additiveInst toSliceBack iterBack enumerateBack iter (fun e => e)
          weights runningClaim bytes additive round alpha pending) =
        .ok (nextWeights, nextClaim, nextAdditive, pending, 1#u32)) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
        additiveInst bytes additive circlePoints round alpha pending
        (range2At 2#usize) weights runningClaim =
      .ok (.done (nextWeights, nextClaim, nextAdditive, pending, 1#u32)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
  rw [range2_next_none]
  simp only [bind_tc_ok, Aeneas.Std.lift, core.slice.Slice.iter_mut,
    V5MutableEnumerateSupport.enumerate] at polynomialExact ⊢
  rw [polynomialExact]
  rfl

theorem generated_two_sample_loop_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round : Std.Usize) (alpha claim0 claim1 claim2 nextClaim : RawQM31)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (weights0 weights1 weights2 nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (sample0Exact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
          additiveInst bytes additive circlePoints round alpha pending
          (range2At 0#usize) weights0 claim0 =
        .ok (.cont (range2At 1#usize, weights1, claim1)))
    (sample1Exact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
          additiveInst bytes additive circlePoints round alpha pending
          (range2At 1#usize) weights1 claim1 =
        .ok (.cont (range2At 2#usize, weights2, claim2)))
    (exhaustionExact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
          additiveInst bytes additive circlePoints round alpha pending
          (range2At 2#usize) weights2 claim2 =
        .ok (.done
          (nextWeights, nextClaim, nextAdditive, pending, 1#u32))) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
        additiveInst (range2At 0#usize) weights0 claim0 bytes additive
        circlePoints round alpha pending =
      .ok (nextWeights, nextClaim, nextAdditive, pending, 1#u32) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [sample0Exact]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [sample1Exact]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [exhaustionExact]

theorem generated_active_round_body_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (iter nextIter : core.iter.adapters.enumerate.Enumerate
      (core.array.iter.IntoIter RawQM31 4#usize))
    (round : Std.Usize) (alpha : RawQM31)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim nextClaim : RawQM31)
    (additive nextAdditive : A)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (nextExact :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize) iter =
        .ok (some (round, alpha), nextIter))
    (roundExact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
          additiveInst (range2At 0#usize) weights runningClaim bytes additive
          circlePoints round alpha pending =
        .ok (nextWeights, nextClaim, nextAdditive, pending, 1#u32)) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
        additiveInst bytes circlePoints iter weights runningClaim additive
        pending =
      .ok (.cont
        (nextIter, nextWeights, nextClaim, nextAdditive, pending)) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
  rw [nextExact]
  simp only [bind_tc_ok]
  have initialRangeExact :
      ({ start := 0#usize,
         «end» :=
           V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES } :
        core.ops.range.Range Std.Usize) = range2At 0#usize := by
    unfold range2At
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES
    rfl
  rw [initialRangeExact]
  rw [roundExact]
  rfl

theorem generated_terminal_round_body_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (iter nextIter : core.iter.adapters.enumerate.Enumerate
      (core.array.iter.IntoIter RawQM31 4#usize))
    (weights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim mainDot additiveDot : RawQM31)
    (additive : A)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (finalCoefficients : Array RawQM31 4#usize)
    (nextExact :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize) iter = .ok (none, nextIter))
    (decoderExact :
      V5RelationFullGenerated.relation_stress.decode_v5_relation_stress_final
        bytes = .ok (.Ok finalCoefficients))
    (mainDotExact :
      aspis_core.sumcheck.WeightAccumulator.dot weights
        (Array.to_slice finalCoefficients) = .ok mainDot)
    (additiveDotExact :
      additiveInst.dot additive finalCoefficients = .ok additiveDot)
    (combinedExact :
      V5RelationFullGenerated.aspis_core.field.QM31.add mainDot additiveDot =
        .ok runningClaim) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
        additiveInst bytes circlePoints iter weights runningClaim additive
        pending =
      .ok (.done (some (.Ok
        { final_coefficients := finalCoefficients,
          terminal_claim := runningClaim }))) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
  rw [nextExact]
  simp only [bind_tc_ok, decoderExact,
    core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.lift, mainDotExact, additiveDotExact, combinedExact]
  have neSelf :
      core.cmp.PartialEq.ne.trait_default
          V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
          runningClaim runningClaim = .ok false := by
    simpa using raw_qm31_ne_spec runningClaim runningClaim
  rw [neSelf]
  rfl

theorem generated_four_round_loop_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (iter0 iter1 iter2 iter3 iter4 : core.iter.adapters.enumerate.Enumerate
      (core.array.iter.IntoIter RawQM31 4#usize))
    (weights0 weights1 weights2 weights3 weights4 :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 claim1 claim2 claim3 claim4 : RawQM31)
    (additive0 additive1 additive2 additive3 additive4 : A)
    (pending : Option (core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError))
    (output : core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError)
    (round0Exact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter0 weights0 claim0 additive0
          pending =
        .ok (.cont (iter1, weights1, claim1, additive1, pending)))
    (round1Exact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter1 weights1 claim1 additive1
          pending =
        .ok (.cont (iter2, weights2, claim2, additive2, pending)))
    (round2Exact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter2 weights2 claim2 additive2
          pending =
        .ok (.cont (iter3, weights3, claim3, additive3, pending)))
    (round3Exact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter3 weights3 claim3 additive3
          pending =
        .ok (.cont (iter4, weights4, claim4, additive4, pending)))
    (terminalExact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter4 weights4 claim4 additive4
          pending = .ok (.done (some output))) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
        additiveInst iter0 weights0 claim0 bytes additive0 circlePoints
        pending = .ok (some output) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [round0Exact]
  simp only
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [round1Exact]
  simp only
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [round2Exact]
  simp only
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [round3Exact]
  simp only
  rw [Aeneas.Std.loop.eq_def]
  simp only
  rw [terminalExact]

def alphaIteratorAt (alphas : Array RawQM31 4#usize)
    (index : Nat) (count : Std.Usize) :
    core.iter.adapters.enumerate.Enumerate
      (core.array.iter.IntoIter RawQM31 4#usize) :=
  { iter := { array := alphas, index := index }, count := count }

theorem alpha_iterator_setup_exact (alphas : Array RawQM31 4#usize) :
    (do
      let iterator ←
        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter alphas
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize) iterator) =
      .ok (alphaIteratorAt alphas 0 0#usize) := by
  simp [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    alphaIteratorAt]

theorem alpha_iterator_next_some_exact
    (alphas : Array RawQM31 4#usize)
    (index : Nat) (count nextCount : Std.Usize) (alpha : RawQM31)
    (inBounds : index < alphas.val.length)
    (alphaExact : alphas.val[index] = alpha)
    (countExact : count + 1#usize = ok nextCount) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize)
        (alphaIteratorAt alphas index count) =
      .ok (some (count, alpha),
        alphaIteratorAt alphas (index + 1) nextCount) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  have innerNext :=
    AspisV5RelationGeneratedSupportProof.fixed_array_next_some_exact
      ({ array := alphas, index := index } :
        core.array.iter.IntoIter RawQM31 4#usize) inBounds
  simp only [alphaIteratorAt]
  rw [innerNext]
  simp only [bind_tc_ok, alphaExact, countExact]

theorem alpha_iterator_next_none_exact
    (alphas : Array RawQM31 4#usize) (index : Nat) (count : Std.Usize)
    (exhausted : ¬ index < alphas.val.length) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize)
        (alphaIteratorAt alphas index count) =
      .ok (none, alphaIteratorAt alphas index count) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  have innerNext :=
    AspisV5RelationGeneratedSupportProof.fixed_array_next_none_exact
      ({ array := alphas, index := index } :
        core.array.iter.IntoIter RawQM31 4#usize) exhausted
  simp only [alphaIteratorAt]
  rw [innerNext]
  rfl

def twoCirclePoints (x0 y0 x1 y1 : RawQM31) : Array
    V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize :=
  Array.make 2#usize [
    { x := x0, y := y0 },
    { x := x1, y := y1 }]

theorem generated_complete_relation_success_exact
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (runningClaim : RawQM31)
    (alphas : Array RawQM31 4#usize)
    (bytes : Array Std.U8 928#usize) (additive : A)
    (x0 y0 x1 y1 x0Square y0Square x1Square y1Square : RawQM31)
    (output : core.result.Result
      V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
      V5RelationFullGenerated.relation_stress.V5RelationStressError)
    (readX0 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
        (Std.Usize.wrapping_mul 2#usize 0#usize) = .ok (.Ok x0))
    (readY0 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
        (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize 0#usize)
          1#usize) = .ok (.Ok y0))
    (readX1 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
        (Std.Usize.wrapping_mul 2#usize 1#usize) = .ok (.Ok x1))
    (readY1 :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
        (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize 1#usize)
          1#usize) = .ok (.Ok y1))
    (squareX0 :
      V5RelationFullGenerated.aspis_core.field.QM31.square x0 =
        .ok x0Square)
    (squareY0 :
      V5RelationFullGenerated.aspis_core.field.QM31.square y0 =
        .ok y0Square)
    (circle0 :
      V5RelationFullGenerated.aspis_core.field.QM31.add x0Square y0Square =
        .ok V5RelationFullGenerated.aspis_core.field.QM31.ONE)
    (squareX1 :
      V5RelationFullGenerated.aspis_core.field.QM31.square x1 =
        .ok x1Square)
    (squareY1 :
      V5RelationFullGenerated.aspis_core.field.QM31.square y1 =
        .ok y1Square)
    (circle1 :
      V5RelationFullGenerated.aspis_core.field.QM31.add x1Square y1Square =
        .ok V5RelationFullGenerated.aspis_core.field.QM31.ONE)
    (roundsExact :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
          additiveInst (alphaIteratorAt alphas 0 0#usize) weights
          runningClaim bytes additive (twoCirclePoints x0 y0 x1 y1) none =
        .ok (some output)) :
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive
        additiveInst weights runningClaim alphas bytes additive =
      .ok output := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive
  simp only [Aeneas.Std.lift, bind_tc_ok,
    core.slice.Slice.iter_mut, V5MutableEnumerateSupport.enumerate]
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0
  have firstInBounds :
      (0 : Nat) < (Array.repeat 2#usize
        ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
           y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
          V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).to_slice_mut.1.val.length := by
    change 0 < (Array.repeat 2#usize
      ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
         y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).val.length
    rw [Array.repeat_val]
    decide
  have secondInBounds :
      (1 : Nat) < (Array.repeat 2#usize
        ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
           y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
          V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).to_slice_mut.1.val.length := by
    change 1 < (Array.repeat 2#usize
      ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
         y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).val.length
    rw [Array.repeat_val]
    decide
  have exhausted :
      ¬ (2 : Nat) < (Array.repeat 2#usize
        ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
           y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
          V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).to_slice_mut.1.val.length := by
    change ¬ 2 < (Array.repeat 2#usize
      ({ x := V5RelationFullGenerated.aspis_core.field.QM31.ZERO,
         y := V5RelationFullGenerated.aspis_core.field.QM31.ZERO } :
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)).val.length
    rw [Array.repeat_val]
    decide
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExact <;> scalar_tac
  have count1Next : 1#usize + 1#usize = ok 2#usize := by
    apply usizeAddExact <;> scalar_tac
  have circle0Equal :
      core.cmp.PartialEq.ne.trait_default
          V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
          V5RelationFullGenerated.aspis_core.field.QM31.ONE
          V5RelationFullGenerated.aspis_core.field.QM31.ONE = .ok false := by
    simpa using raw_qm31_ne_spec
      V5RelationFullGenerated.aspis_core.field.QM31.ONE
      V5RelationFullGenerated.aspis_core.field.QM31.ONE
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, firstInBounds, count0Next,
    Aeneas.Std.lift, bind_tc_ok, readX0, readY0,
    core.result.Result.Insts.CoreOpsTry.branch,
    squareX0, squareY0, circle0, circle0Equal]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, secondInBounds, count1Next,
    Aeneas.Std.lift, bind_tc_ok, readX1, readY1,
    core.result.Result.Insts.CoreOpsTry.branch,
    squareX1, squareY1, circle1, circle0Equal]
  rw [Aeneas.Std.loop.eq_def]
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, exhausted,
    Array.to_slice_mut, Array.to_slice, Array.from_slice,
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    alphaIteratorAt]
  simp only [Slice.setAtNat, Array.repeat_val, List.set]
  have roundsForAny
      (points : Array
        V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
      (pointsExact : points.val =
        [{ x := x0, y := y0 }, { x := x1, y := y1 }]) :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0
          additiveInst (alphaIteratorAt alphas 0 0#usize) weights
          runningClaim bytes additive points none = .ok (some output) := by
    have exactArray : points = twoCirclePoints x0 y0 x1 y1 := by
      apply Subtype.ext
      simpa [twoCirclePoints, Array.make] using pointsExact
    simpa [exactArray] using roundsExact
  simp only [alphaIteratorAt] at roundsForAny
  rw [roundsForAny]
  · simp
  · rfl

#print axioms raw_qm31_eq_spec
#print axioms raw_qm31_ne_spec
#print axioms generated_final_decoder_success_exact
#print axioms generated_polynomial_loop_success_exact
#print axioms generated_round_zero_sample_step_exact
#print axioms generated_later_round_sample_step_exact
#print axioms generated_sample_exhaustion_runs_polynomial
#print axioms generated_two_sample_loop_exact
#print axioms generated_active_round_body_exact
#print axioms generated_terminal_round_body_exact
#print axioms generated_four_round_loop_exact
#print axioms alpha_iterator_setup_exact
#print axioms alpha_iterator_next_some_exact
#print axioms alpha_iterator_next_none_exact
#print axioms generated_complete_relation_success_exact

end AspisV5RelationFullSourceProof
