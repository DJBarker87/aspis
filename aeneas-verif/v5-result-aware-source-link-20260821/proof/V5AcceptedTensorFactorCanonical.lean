import V5AcceptedAccumulatorSchedule
import V5RelationLinkedTerminalDotSemantics
import Aeneas.Std.RangeIter

/-!
# Canonical tensor factors in the accepted relation schedule

The relation verifier constructs tensor factors by repeatedly applying the
translated circle `double_x` helper, then reversing the vector.  This file
proves directly from those generated functions that canonical input
coordinates yield a canonical factor vector.
-/

namespace AspisV5AcceptedTensorFactorCanonical

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedTerminalDotSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31

deriving instance Inhabited for
  V5RelationFullGenerated.aspis_core.field.QM31

def EveryCanonical (values : List RawQM31) : Prop :=
  ∀ value ∈ values, CanonicalQM31 value

theorem everyCanonical_append
    (values : List RawQM31) (value : RawQM31)
    (valuesCanonical : EveryCanonical values)
    (valueCanonical : CanonicalQM31 value) :
    EveryCanonical (values ++ [value]) := by
  intro present member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact valuesCanonical present member
  · exact valueCanonical

theorem everyCanonical_reverse
    (values : List RawQM31) (canonical : EveryCanonical values) :
    EveryCanonical values.reverse := by
  intro value member
  exact canonical value (by simpa using member)

theorem everyCanonical_toCanonicalList
    (values : List RawQM31) (canonical : EveryCanonical values) :
    CanonicalList values := by
  intro index bound
  apply canonical values[index]!
  have bangExact : values[index]! = values[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  rw [bangExact]
  exact List.get_mem values ⟨index, bound⟩

private theorem pushSuccessExact
    (values output : alloc.vec.Vec RawQM31) (value : RawQM31)
    (success : alloc.vec.Vec.push values value = .ok output) :
    output.val = values.val ++ [value] := by
  unfold alloc.vec.Vec.push at success
  dsimp only at success
  split at success
  · injection success with outputExact
    subst output
    simp [List.concat_eq_append]
  · simp at success

private theorem oneCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationFullGenerated.aspis_core.field.QM31.ONE,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- The generated circle doubling helper preserves canonical field
representatives. -/
theorem doubleXSuccessCanonical
    (x output : RawQM31) (xCanonical : CanonicalQM31 x)
    (success :
      aspis_core.circle.double_x x = .ok output) :
    CanonicalQM31 output := by
  change
    V5RelationLinkedGenerated.aspis_core.circle.double_x x = .ok output
    at success
  unfold V5RelationLinkedGenerated.aspis_core.circle.double_x at success
  generalize squareEquation :
      V5RelationLinkedGenerated.aspis_core.field.QM31.square x =
        squareResult at success
  cases squareResult with
  | fail error => simp at success
  | div => simp at success
  | ok square =>
      simp only [bind_tc_ok] at success
      have squareCanonical :=
        (generated_qm31_square_run_corresponds x square xCanonical
          squareEquation).1
      generalize doubleEquation :
          V5RelationLinkedGenerated.aspis_core.field.QM31.add square square =
            doubleResult at success
      cases doubleResult with
      | fail error => simp at success
      | div => simp at success
      | ok doubled =>
          simp only [bind_tc_ok] at success
          have doubledCanonical :=
            (generated_qm31_add_run_corresponds square square
              doubled squareCanonical squareCanonical doubleEquation).1
          exact
            (generated_qm31_sub_run_corresponds doubled
              V5RelationLinkedGenerated.aspis_core.field.QM31.ONE output
              doubledCanonical oneCanonical success).1

/-- The translated circle factor loop preserves canonicality of every
accumulated factor. -/
theorem circleFactorLoopSuccessCanonical
    (iter : core.ops.range.Range Std.U32)
    (factors output : alloc.vec.Vec RawQM31) (x : RawQM31)
    (factorsCanonical : EveryCanonical factors.val)
    (xCanonical : CanonicalQM31 x)
    (success :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor_loop
          iter factors x = .ok output) :
    EveryCanonical output.val := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor_loop
    at success
  rw [loop.eq_def] at success
  simp only at success
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor_loop.body
    at success
  by_cases active : iter.start.val < iter.end.val
  · have nextSpec :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
        ⦃ (option : Option Std.U32)
            (nextIter : core.ops.range.Range Std.U32) =>
          option = some iter.start ∧
            nextIter.start.val = iter.start.val + 1 ∧
            nextIter.end = iter.end ⦄ :=
      core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty := .U32) (by simp) (by intros; rfl) iter active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := Aeneas.Std.WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [nextRun] at success
    simp only [bind_tc_ok] at success
    generalize doubleEquation :
        aspis_core.circle.double_x x =
          doubleResult at success
    cases doubleResult with
    | fail error => simp at success
    | div => simp at success
    | ok doubled =>
        simp only [bind_tc_ok] at success
        have doubledCanonical := doubleXSuccessCanonical x doubled
          xCanonical doubleEquation
        generalize pushEquation : alloc.vec.Vec.push factors doubled =
          pushResult at success
        cases pushResult with
        | fail error => simp at success
        | div => simp at success
        | ok nextFactors =>
            simp only [bind_tc_ok] at success
            have nextValues := pushSuccessExact factors nextFactors doubled
              pushEquation
            have nextCanonical : EveryCanonical nextFactors.val := by
              rw [nextValues]
              exact everyCanonical_append factors.val doubled
                factorsCanonical doubledCanonical
            exact circleFactorLoopSuccessCanonical nextIter nextFactors output
              doubled nextCanonical doubledCanonical success
  · have nextSpec :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
        ⦃ (option : Option Std.U32)
            (nextIter : core.ops.range.Range Std.U32) =>
          option = none ∧ nextIter = iter ⦄ :=
      core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty := .U32) (by intros; rfl) iter (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      Aeneas.Std.WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at success
    simp only [bind_tc_ok, Result.ok.injEq] at success
    subst output
    exact factorsCanonical
termination_by iter.end.val - iter.start.val
decreasing_by
  rw [nextEnd, nextStart]
  omega

/-- The translated line factor loop likewise preserves canonicality. -/
theorem lineFactorLoopSuccessCanonical
    (iter : core.ops.range.Range Std.U32) (limit : Std.U32)
    (x : RawQM31) (factors output : alloc.vec.Vec RawQM31)
    (xCanonical : CanonicalQM31 x)
    (factorsCanonical : EveryCanonical factors.val)
    (success :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor_loop
          iter limit x factors = .ok output) :
    EveryCanonical output.val := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor_loop
    at success
  rw [loop.eq_def] at success
  simp only at success
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor_loop.body
    at success
  by_cases active : iter.start.val < iter.end.val
  · have nextSpec :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
        ⦃ (option : Option Std.U32)
            (nextIter : core.ops.range.Range Std.U32) =>
          option = some iter.start ∧
            nextIter.start.val = iter.start.val + 1 ∧
            nextIter.end = iter.end ⦄ :=
      core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty := .U32) (by simp) (by intros; rfl) iter active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := Aeneas.Std.WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [nextRun] at success
    simp only [bind_tc_ok] at success
    generalize pushEquation : alloc.vec.Vec.push factors x = pushResult
      at success
    cases pushResult with
    | fail error => simp at success
    | div => simp at success
    | ok nextFactors =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at success
        have nextValues := pushSuccessExact factors nextFactors x pushEquation
        have nextCanonical : EveryCanonical nextFactors.val := by
          rw [nextValues]
          exact everyCanonical_append factors.val x factorsCanonical xCanonical
        by_cases more : Std.U32.wrapping_add iter.start 1#u32 < limit
        · rw [if_pos more] at success
          generalize doubleEquation :
              aspis_core.circle.double_x x =
                doubleResult at success
          cases doubleResult with
          | fail error => simp at success
          | div => simp at success
          | ok doubled =>
              simp only [bind_tc_ok] at success
              have doubledCanonical := doubleXSuccessCanonical x doubled
                xCanonical doubleEquation
              exact lineFactorLoopSuccessCanonical nextIter limit doubled
                nextFactors output doubledCanonical nextCanonical success
        · rw [if_neg more] at success
          exact lineFactorLoopSuccessCanonical nextIter limit x nextFactors
            output xCanonical nextCanonical success
  · have nextSpec :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
        ⦃ (option : Option Std.U32)
            (nextIter : core.ops.range.Range Std.U32) =>
          option = none ∧ nextIter = iter ⦄ :=
      core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty := .U32) (by intros; rfl) iter (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      Aeneas.Std.WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at success
    simp only [bind_tc_ok, Result.ok.injEq] at success
    subst output
    exact factorsCanonical
termination_by iter.end.val - iter.start.val
decreasing_by all_goals
  rw [nextEnd, nextStart]
  omega

#print axioms doubleXSuccessCanonical
#print axioms circleFactorLoopSuccessCanonical
#print axioms lineFactorLoopSuccessCanonical

end AspisV5AcceptedTensorFactorCanonical
