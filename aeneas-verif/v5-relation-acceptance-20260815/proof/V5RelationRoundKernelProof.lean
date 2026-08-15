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
        exact ⟨coefficient0, coefficient4, sum, h0, h4, hadd, success⟩

end Boundary

namespace Evaluate

open V5RelationEvaluateGenerated

abbrev RawQM31 := V5RelationEvaluateGenerated.aspis_core.field.QM31

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
  unfold V5RelationEvaluateGenerated.extract_evaluate
    V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate
    V5RelationEvaluateGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS
  simp only [Aeneas.Std.lift, bind_tc_ok]
  unfold V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]
  rw [Aeneas.Std.loop.eq_def]
  simp only [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]
  rw [Aeneas.Std.loop.eq_def]
  simp only [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]
  rw [Aeneas.Std.loop.eq_def]
  simp only [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]
  rw [Aeneas.Std.loop.eq_def]
  simp only [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]
  rw [Aeneas.Std.loop.eq_def]
  simp only [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]
  rw [Aeneas.Std.loop.eq_def]
  simp only [V5RelationEvaluateGenerated.aspis_core.sumcheck.evaluate_loop.body]
  rfl

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
