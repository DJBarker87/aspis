import ComponentCRuntimeGenerated

/-!
# Source-authentic Component-C runtime evaluator boundary checks

These theorems execute the Aeneas definition generated from the real
`evaluate_component_c_runtime_private_view` Rust entrypoint.  They pin the two
shape checks that run before any relation or FRI arithmetic.  In particular,
the reported `actual` lengths are re-read from the supplied slices, exactly as
in Rust; they are not a handwritten model of the parser.
-/

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeEvaluatorProof

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeError :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeError

/-- The actual extracted top-level evaluator rejects every coefficient slice
whose length differs from the deployed 1,024-row message width, before reading
the codeword or executing field arithmetic. -/
theorem extracted_rejects_wrong_message_shape
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (hshape : Slice.len coefficients ≠ v5_mask.component_c.V5_C_ROWS) :
    v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
        schedule coefficients codeword expectedInactiveClaim =
      ok (core.result.Result.Err
        (v5_mask.component_c_runtime.V5ComponentCRuntimeError.MessageShape
          v5_mask.component_c.V5_C_ROWS (Slice.len coefficients))) := by
  simp [v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view,
    hshape]

/-- Once the coefficient shape is correct, the actual extracted evaluator
rejects every codeword whose length differs from the generated
`V5_CODEWORD_LEN`.  The expected codeword width is obtained by executing that
generated constant, rather than duplicated as a Lean literal. -/
theorem extracted_rejects_wrong_codeword_shape
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (expectedCodewordLength : Std.Usize)
    (hcoefficients :
      Slice.len coefficients = v5_mask.component_c.V5_C_ROWS)
    (hexpected : v5_mask.V5_CODEWORD_LEN = ok expectedCodewordLength)
    (hcodeword : Slice.len codeword ≠ expectedCodewordLength) :
    v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
        schedule coefficients codeword expectedInactiveClaim =
      ok (core.result.Result.Err
        (v5_mask.component_c_runtime.V5ComponentCRuntimeError.CodewordShape
          expectedCodewordLength (Slice.len codeword))) := by
  have hcodewordVal : codeword.val.length ≠ expectedCodewordLength.val := by
    intro hval
    apply hcodeword
    apply UScalar.eq_of_val_eq
    simpa using hval
  simp [v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view,
    hcoefficients, hexpected, hcodewordVal]

/-- The generated message-width constant is exactly 1,024. -/
theorem extracted_component_c_rows_eq :
    v5_mask.component_c.V5_C_ROWS = 1024#usize := by
  unfold v5_mask.component_c.V5_C_ROWS
  rfl

#print axioms extracted_rejects_wrong_message_shape
#print axioms extracted_rejects_wrong_codeword_shape
#print axioms extracted_component_c_rows_eq

end aspis_prover.ComponentCRuntimeEvaluatorProof
