import V5RelationBoundaryGenerated
import V5RelationEvaluateGenerated

/-!
# Extracted V5 relation-round arithmetic kernels

Pinned Aeneas cannot translate the enclosing relation verifier because that
Rust function returns from inside nested loops.  It does translate the two
arithmetic kernels called in every round.  This file proves their complete
generated control flow, for every seven-coefficient input:

* `boundary_sum` reads coefficients zero and four, adds them, and multiplies
  the result by the base-field value four;
* `evaluate` is exactly the six multiplication/addition steps of Horner
  evaluation, starting at coefficient six and ending at coefficient zero.

The theorems deliberately state the generated field calls themselves.  The
existing QM31 arithmetic proofs connect those calls to the exact field model;
this file does not add a second cryptographic or arithmetic assumption.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5RelationRoundKernelProof

namespace Boundary

open V5RelationBoundaryGenerated

abbrev RawQM31 := V5RelationBoundaryGenerated.aspis_core.field.QM31

/-- Exact straight-line body extracted from production `boundary_sum`. -/
def boundaryProgram (polynomial : Array RawQM31 7#usize) : Result RawQM31 := do
  let coefficient0 ← Array.index_usize polynomial 0#usize
  let coefficient4 ← Array.index_usize polynomial 4#usize
  let sum ←
    V5RelationBoundaryGenerated.aspis_core.field.QM31.add
      coefficient0 coefficient4
  V5RelationBoundaryGenerated.aspis_core.field.QM31.mul_m31 sum 4#u32

theorem extracted_boundary_sum_eq_program
    (polynomial : Array RawQM31 7#usize) :
    V5RelationBoundaryGenerated.extract_boundary_sum polynomial =
      boundaryProgram polynomial := by
  rfl

/-- Any successful extracted boundary computation witnesses every operation
in the exact source order. -/
theorem extracted_boundary_success_decomposition
    (polynomial : Array RawQM31 7#usize) (output : RawQM31)
    (success :
      V5RelationBoundaryGenerated.extract_boundary_sum polynomial = .ok output) :
    ∃ coefficient0 coefficient4 sum,
      Array.index_usize polynomial 0#usize = .ok coefficient0 ∧
      Array.index_usize polynomial 4#usize = .ok coefficient4 ∧
      V5RelationBoundaryGenerated.aspis_core.field.QM31.add
          coefficient0 coefficient4 = .ok sum ∧
      V5RelationBoundaryGenerated.aspis_core.field.QM31.mul_m31
          sum 4#u32 = .ok output := by
  rw [extracted_boundary_sum_eq_program] at success
  unfold boundaryProgram at success
  generalize h0 : Array.index_usize polynomial 0#usize = result0 at success
  cases result0 with
  | fail error => simp at success
  | div => simp at success
  | ok coefficient0 =>
    simp only [bind_tc_ok] at success
    generalize h4 : Array.index_usize polynomial 4#usize = result4 at success
    cases result4 with
    | fail error => simp at success
    | div => simp at success
    | ok coefficient4 =>
      simp only [bind_tc_ok] at success
      generalize hadd :
          V5RelationBoundaryGenerated.aspis_core.field.QM31.add
            coefficient0 coefficient4 = addResult at success
      cases addResult with
      | fail error => simp at success
      | div => simp at success
      | ok sum =>
        simp only [bind_tc_ok] at success
        exact ⟨coefficient0, coefficient4, sum, rfl, rfl, hadd, success⟩

end Boundary

namespace Evaluate

open V5RelationEvaluateGenerated

abbrev RawQM31 := V5RelationEvaluateGenerated.aspis_core.field.QM31

private theorem usize_wrapping_sub_one_exact
    (value result : Std.Usize)
    (hpositive : 1 ≤ value.val)
    (hresult : result.val = value.val - 1) :
    Std.Usize.wrapping_sub value 1#usize = result := by
  apply UScalar.eq_of_val_eq
  rw [Std.Usize.wrapping_sub_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := by rfl
  rw [hone, hresult]
  have hvalue := value.hSize
  have hrearrange :
      value.val + (UScalar.size .Usize - 1) =
        (value.val - 1) + UScalar.size .Usize := by
    omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem result_bind_congr {alpha beta : Type}
    (input : Result alpha) (left right : alpha → Result beta)
    (pointwise : ∀ value, left value = right value) :
    (do let value ← input; left value) =
      (do let value ← input; right value) := by
  cases input <;> simp [pointwise]

private theorem extracted_evaluate_loop_positive_step
    (polynomial : Array RawQM31 7#usize) (point accumulator : RawQM31)
    (degree nextDegree : Std.Usize)
    (positive : degree > 0#usize)
    (nextDegreeExact :
      Std.Usize.wrapping_sub degree 1#usize = nextDegree) :
    V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop
        polynomial point accumulator degree = (do
      let product ←
        V5RelationEvaluateGenerated.aspis_core.field.QM31.mul accumulator point
      let coefficient ← Array.index_usize polynomial nextDegree
      let nextAccumulator ←
        V5RelationEvaluateGenerated.aspis_core.field.QM31.add
          product coefficient
      V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop
        polynomial point nextAccumulator nextDegree) := by
  unfold V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [
    V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body,
    positive, if_pos, nextDegreeExact, Aeneas.Std.lift, bind_tc_ok]
  generalize hmul :
      V5RelationEvaluateGenerated.aspis_core.field.QM31.mul accumulator point =
        multiplyResult
  cases multiplyResult with
  | fail error => rfl
  | div => rfl
  | ok product =>
    generalize hindex :
        Array.index_usize polynomial nextDegree = indexResult
    cases indexResult with
    | fail error => rfl
    | div => rfl
    | ok coefficient =>
      generalize hadd :
          V5RelationEvaluateGenerated.aspis_core.field.QM31.add
            product coefficient = addResult
      cases addResult <;> simp [hadd]

private theorem extracted_evaluate_loop_zero
    (polynomial : Array RawQM31 7#usize) (point accumulator : RawQM31) :
    V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop
        polynomial point accumulator 0#usize = .ok accumulator := by
  unfold V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop
  rw [Aeneas.Std.loop.eq_def]
  simp [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]

/-- The literal seven-coefficient Horner program implemented by production
`evaluate`, written without a loop so its six ordered steps are visible. -/
def horner7Program
    (polynomial : Array RawQM31 7#usize) (point : RawQM31) : Result RawQM31 := do
  let coefficient6 ← Array.index_usize polynomial 6#usize
  let product5 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.mul coefficient6 point
  let coefficient5 ← Array.index_usize polynomial 5#usize
  let accumulator5 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.add product5 coefficient5
  let product4 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.mul accumulator5 point
  let coefficient4 ← Array.index_usize polynomial 4#usize
  let accumulator4 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.add product4 coefficient4
  let product3 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.mul accumulator4 point
  let coefficient3 ← Array.index_usize polynomial 3#usize
  let accumulator3 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.add product3 coefficient3
  let product2 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.mul accumulator3 point
  let coefficient2 ← Array.index_usize polynomial 2#usize
  let accumulator2 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.add product2 coefficient2
  let product1 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.mul accumulator2 point
  let coefficient1 ← Array.index_usize polynomial 1#usize
  let accumulator1 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.add product1 coefficient1
  let product0 ←
    V5RelationEvaluateGenerated.aspis_core.field.QM31.mul accumulator1 point
  let coefficient0 ← Array.index_usize polynomial 0#usize
  V5RelationEvaluateGenerated.aspis_core.field.QM31.add product0 coefficient0

/-- The complete extracted production evaluator equals the explicit six-step
Horner program for every polynomial and point. -/
theorem extracted_evaluate_eq_horner7_program
    (polynomial : Array RawQM31 7#usize) (point : RawQM31) :
    V5RelationEvaluateGenerated.extract_evaluate polynomial point =
      horner7Program polynomial point := by
  have sub7 : Std.Usize.wrapping_sub 7#usize 1#usize = 6#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub6 : Std.Usize.wrapping_sub 6#usize 1#usize = 5#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub5 : Std.Usize.wrapping_sub 5#usize 1#usize = 4#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub4 : Std.Usize.wrapping_sub 4#usize 1#usize = 3#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub3 : Std.Usize.wrapping_sub 3#usize 1#usize = 2#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub2 : Std.Usize.wrapping_sub 2#usize 1#usize = 1#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have sub1 : Std.Usize.wrapping_sub 1#usize 1#usize = 0#usize := by
    apply usize_wrapping_sub_one_exact <;> norm_num
  have gt6 : 6#usize > 0#usize := by scalar_tac
  have gt5 : 5#usize > 0#usize := by scalar_tac
  have gt4 : 4#usize > 0#usize := by scalar_tac
  have gt3 : 3#usize > 0#usize := by scalar_tac
  have gt2 : 2#usize > 0#usize := by scalar_tac
  have gt1 : 1#usize > 0#usize := by scalar_tac
  unfold V5RelationEvaluateGenerated.extract_evaluate
    V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate
    V5RelationEvaluateGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS
  simp only [sub7, Aeneas.Std.lift, bind_tc_ok]
  unfold horner7Program
  generalize h6 : Array.index_usize polynomial 6#usize = initialResult
  cases initialResult with
  | fail error => rfl
  | div => rfl
  | ok coefficient6 =>
    simp only [bind_tc_ok]
    rw [extracted_evaluate_loop_positive_step polynomial point coefficient6
      6#usize 5#usize gt6 sub6]
    apply result_bind_congr
    intro product5
    apply result_bind_congr
    intro coefficient5
    apply result_bind_congr
    intro accumulator5
    rw [extracted_evaluate_loop_positive_step polynomial point accumulator5
      5#usize 4#usize gt5 sub5]
    apply result_bind_congr
    intro product4
    apply result_bind_congr
    intro coefficient4
    apply result_bind_congr
    intro accumulator4
    rw [extracted_evaluate_loop_positive_step polynomial point accumulator4
      4#usize 3#usize gt4 sub4]
    apply result_bind_congr
    intro product3
    apply result_bind_congr
    intro coefficient3
    apply result_bind_congr
    intro accumulator3
    rw [extracted_evaluate_loop_positive_step polynomial point accumulator3
      3#usize 2#usize gt3 sub3]
    apply result_bind_congr
    intro product2
    apply result_bind_congr
    intro coefficient2
    apply result_bind_congr
    intro accumulator2
    rw [extracted_evaluate_loop_positive_step polynomial point accumulator2
      2#usize 1#usize gt2 sub2]
    apply result_bind_congr
    intro product1
    apply result_bind_congr
    intro coefficient1
    apply result_bind_congr
    intro accumulator1
    rw [extracted_evaluate_loop_positive_step polynomial point accumulator1
      1#usize 0#usize gt1 sub1]
    apply result_bind_congr
    intro product0
    apply result_bind_congr
    intro coefficient0
    generalize hlast :
        V5RelationEvaluateGenerated.aspis_core.field.QM31.add
          product0 coefficient0 = lastResult
    cases lastResult with
    | fail error => rfl
    | div => rfl
    | ok accumulator0 =>
      simp only [bind_tc_ok]
      exact extracted_evaluate_loop_zero polynomial point accumulator0

/-- Successful production evaluation is therefore successful execution of
the exact six multiply/add Horner steps, with no hidden loop case. -/
theorem extracted_evaluate_success_is_horner7_success
    (polynomial : Array RawQM31 7#usize) (point output : RawQM31)
    (success :
      V5RelationEvaluateGenerated.extract_evaluate polynomial point = .ok output) :
    horner7Program polynomial point = .ok output := by
  rw [extracted_evaluate_eq_horner7_program] at success
  exact success

end Evaluate

#print axioms Boundary.extracted_boundary_sum_eq_program
#print axioms Boundary.extracted_boundary_success_decomposition
#print axioms Evaluate.extracted_evaluate_eq_horner7_program
#print axioms Evaluate.extracted_evaluate_success_is_horner7_success

end AspisV5RelationRoundKernelProof
