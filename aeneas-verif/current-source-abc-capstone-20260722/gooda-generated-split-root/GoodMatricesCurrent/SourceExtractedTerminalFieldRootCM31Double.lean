import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Add
import GoodMatricesCurrent.SourceExtractedTerminalFieldAuthenticPowBridge

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem root_cm31_double_corresponds (value : RootCM31)
    (hvalue : CanonicalRootCM31 value) :
    ∃ output : RootCM31,
      AuthenticFieldPow.field.CM31.double
        { a := value.a, b := value.b } = .ok
          { a := output.a, b := output.b } ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact value + rootCM31ToExact value := by
  rcases root_m31_add_corresponds value.a value.a hvalue.1 hvalue.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases root_m31_add_corresponds value.b value.b hvalue.2 hvalue.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  have hcallA' : AuthenticFieldPow.field.M31.add value.a value.a = .ok oa := by
    rw [← root_m31_add_eq_authentic_pow]
    exact hcallA
  have hcallB' : AuthenticFieldPow.field.M31.add value.b value.b = .ok ob := by
    rw [← root_m31_add_eq_authentic_pow]
    exact hcallB
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AuthenticFieldPow.field.CM31.double,
      AuthenticFieldPow.field.CM31.add, hcallA', hcallB']
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

end GoodMatricesCurrent.SourceExtractedTerminalField
