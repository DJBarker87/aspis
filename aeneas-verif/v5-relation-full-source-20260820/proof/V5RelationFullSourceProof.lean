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
  V5RelationFullGenerated.aspis_core.field.CM31
deriving instance DecidableEq for
  V5RelationFullGenerated.aspis_core.field.QM31

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

#print axioms raw_qm31_eq_spec
#print axioms raw_qm31_ne_spec
#print axioms generated_final_decoder_success_exact
#print axioms generated_polynomial_loop_success_exact

end AspisV5RelationFullSourceProof
