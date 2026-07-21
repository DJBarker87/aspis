import ComponentBEvaluatorFieldBridge
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBRealEvaluatorProof

private abbrev OperationalPolynomial := Array QM31 28#usize

private def operationalCoefficientAt
    (polynomial : OperationalPolynomial) (i : Fin 28) : QM31 :=
  polynomial.val[i.val]

private abbrev Closure :=
  ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure

abbrev blockScalar
    (targetWidth : System.Platform.numBits = 64) (block : Nat) (hblock : block < 7) : Usize :=
  ⟨block, by
    simp [UScalar.max, Usize.max, Usize.numBits, targetWidth]
    omega⟩

/-- The generated block closure performs exactly the four concrete array
reads and then the extracted sum-products/add calls.  No field semantics are
used here. -/
theorem generated_block_call_runs
    (targetWidth : System.Platform.numBits = 64)
    (polynomial : OperationalPolynomial) (powers : Array QM31 3#usize)
    (block : Nat) (hblock : block < 7) (products out : QM31)
    (productsRun :
      ComponentBGenerated.aspis_core.field.qm31_sum_products3 powers
        (Array.make 3#usize [
          operationalCoefficientAt polynomial ⟨4 * block + 1, by omega⟩,
          operationalCoefficientAt polynomial ⟨4 * block + 2, by omega⟩,
          operationalCoefficientAt polynomial ⟨4 * block + 3, by omega⟩]) = .ok products)
    (addRun :
      ComponentBGenerated.aspis_core.field.QM31.add
        (operationalCoefficientAt polynomial ⟨4 * block, by omega⟩) products = .ok out) :
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
      ((polynomial, powers) : Closure) (blockScalar targetWidth block hblock) = .ok out := by
  have blockScalarVal : (blockScalar targetWidth block hblock).val = block := rfl
  interval_cases block <;>
    simp [operationalCoefficientAt] at productsRun addRun <;>
    simp only [
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call,
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure] <;>
    simp [targetWidth, blockScalarVal, operationalCoefficientAt, Array.index_usize, Aeneas.Std.lift,
      UScalar.wrapping_mul, UScalar.wrapping_add,
      Usize.size, Usize.numBits, productsRun, addRun] <;>
    simp_scalar [*]

#print axioms generated_block_call_runs

/-- Six concrete generated loop steps visit blocks 5,4,3,2,1,0 and then
terminate at block zero.  The hypotheses are only the actual called primitive
results; this lemma contains no polynomial or field-model assumption. -/
theorem generated_evaluator_loop_runs
    (targetWidth : System.Platform.numBits = 64)
    (powers : Array QM31 3#usize)
    (prepared : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier)
    (polynomial : OperationalPolynomial)
    (b6 b5 b4 b3 b2 b1 b0 m5 a5 m4 a4 m3 a3 m2 a2 m1 a1 m0 a0 : QM31)
    (b5Run :
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
        ((polynomial, powers) : Closure) (blockScalar targetWidth 5 (by omega)) = .ok b5)
    (b4Run :
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
        ((polynomial, powers) : Closure) (blockScalar targetWidth 4 (by omega)) = .ok b4)
    (b3Run :
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
        ((polynomial, powers) : Closure) (blockScalar targetWidth 3 (by omega)) = .ok b3)
    (b2Run :
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
        ((polynomial, powers) : Closure) (blockScalar targetWidth 2 (by omega)) = .ok b2)
    (b1Run :
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
        ((polynomial, powers) : Closure) (blockScalar targetWidth 1 (by omega)) = .ok b1)
    (b0Run :
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
        ((polynomial, powers) : Closure) (blockScalar targetWidth 0 (by omega)) = .ok b0)
    (m5Run : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul prepared b6 = .ok m5)
    (a5Run : ComponentBGenerated.aspis_core.field.QM31.add m5 b5 = .ok a5)
    (m4Run : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul prepared a5 = .ok m4)
    (a4Run : ComponentBGenerated.aspis_core.field.QM31.add m4 b4 = .ok a4)
    (m3Run : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul prepared a4 = .ok m3)
    (a3Run : ComponentBGenerated.aspis_core.field.QM31.add m3 b3 = .ok a3)
    (m2Run : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul prepared a3 = .ok m2)
    (a2Run : ComponentBGenerated.aspis_core.field.QM31.add m2 b2 = .ok a2)
    (m1Run : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul prepared a2 = .ok m1)
    (a1Run : ComponentBGenerated.aspis_core.field.QM31.add m1 b1 = .ok a1)
    (m0Run : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul prepared a1 = .ok m0)
    (a0Run : ComponentBGenerated.aspis_core.field.QM31.add m0 b0 = .ok a0) :
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop
      powers prepared polynomial b6 (blockScalar targetWidth 6 (by omega)) = .ok a0 := by
  have val6 : (blockScalar targetWidth 6 (by omega)).val = 6 := rfl
  have val5 : (blockScalar targetWidth 5 (by omega)).val = 5 := rfl
  have val4 : (blockScalar targetWidth 4 (by omega)).val = 4 := rfl
  have val3 : (blockScalar targetWidth 3 (by omega)).val = 3 := rfl
  have val2 : (blockScalar targetWidth 2 (by omega)).val = 2 := rfl
  have val1 : (blockScalar targetWidth 1 (by omega)).val = 1 := rfl
  have val0 : (blockScalar targetWidth 0 (by omega)).val = 0 := rfl
  have sub65 : Usize.wrapping_sub (blockScalar targetWidth 6 (by omega)) 1#usize =
      blockScalar targetWidth 5 (by omega) := by
    apply UScalar.eq_of_val_eq
    simp [val6, val5, Usize.size, Usize.numBits, targetWidth]
  have sub54 : Usize.wrapping_sub (blockScalar targetWidth 5 (by omega)) 1#usize =
      blockScalar targetWidth 4 (by omega) := by
    apply UScalar.eq_of_val_eq
    simp [val5, val4, Usize.size, Usize.numBits, targetWidth]
  have sub43 : Usize.wrapping_sub (blockScalar targetWidth 4 (by omega)) 1#usize =
      blockScalar targetWidth 3 (by omega) := by
    apply UScalar.eq_of_val_eq
    simp [val4, val3, Usize.size, Usize.numBits, targetWidth]
  have sub32 : Usize.wrapping_sub (blockScalar targetWidth 3 (by omega)) 1#usize =
      blockScalar targetWidth 2 (by omega) := by
    apply UScalar.eq_of_val_eq
    simp [val3, val2, Usize.size, Usize.numBits, targetWidth]
  have sub21 : Usize.wrapping_sub (blockScalar targetWidth 2 (by omega)) 1#usize =
      blockScalar targetWidth 1 (by omega) := by
    apply UScalar.eq_of_val_eq
    simp [val2, val1, Usize.size, Usize.numBits, targetWidth]
  have sub10 : Usize.wrapping_sub (blockScalar targetWidth 1 (by omega)) 1#usize =
      blockScalar targetWidth 0 (by omega) := by
    apply UScalar.eq_of_val_eq
    simp [val1, val0, Usize.size, Usize.numBits, targetWidth]
  unfold ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop
  rw [Aeneas.Std.loop.eq_def]
  simp [targetWidth, Aeneas.Std.lift, val6, sub65,
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop.body,
    m5Run, b5Run, a5Run]
  rw [Aeneas.Std.loop.eq_def]
  simp [targetWidth, Aeneas.Std.lift, val5, sub54,
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop.body,
    m4Run, b4Run, a4Run]
  rw [Aeneas.Std.loop.eq_def]
  simp [targetWidth, Aeneas.Std.lift, val4, sub43,
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop.body,
    m3Run, b3Run, a3Run]
  rw [Aeneas.Std.loop.eq_def]
  simp [targetWidth, Aeneas.Std.lift, val3, sub32,
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop.body,
    m2Run, b2Run, a2Run]
  rw [Aeneas.Std.loop.eq_def]
  simp [targetWidth, Aeneas.Std.lift, val2, sub21,
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop.body,
    m1Run, b1Run, a1Run]
  rw [Aeneas.Std.loop.eq_def]
  simp [targetWidth, Aeneas.Std.lift, val1, sub10,
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop.body,
    m0Run, b0Run, a0Run]
  rw [Aeneas.Std.loop.eq_def]
  simp [targetWidth, Aeneas.Std.lift, val0,
    ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop.body]

#print axioms generated_evaluator_loop_runs

end ComponentBRealEvaluatorProof
