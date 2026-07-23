import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Add
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Sub
import GoodMatricesCurrent.SourceExtractedTerminalFieldAuthenticPowBridge

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

open AspisV5ComponentCQM31TowerExact

theorem root_mul_by_r_corresponds (value : RootCM31)
    (hvalue : CanonicalRootCM31 value) :
    ∃ output : RootCM31,
      AuthenticFieldPow.field.mul_by_r
        { a := value.a, b := value.b } = .ok
          { a := output.a, b := output.b } ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = qm31R * rootCM31ToExact value := by
  rcases root_m31_add_corresponds value.a value.a hvalue.1 hvalue.1 with
    ⟨twoA, htwoA, htwoACan, htwoAExact⟩
  rcases root_m31_sub_corresponds twoA value.b htwoACan hvalue.2 with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases root_m31_add_corresponds value.b value.b hvalue.2 hvalue.2 with
    ⟨twoB, htwoB, htwoBCan, htwoBExact⟩
  rcases root_m31_add_corresponds value.a twoB hvalue.1 htwoBCan with
    ⟨imag, himag, himagCan, himagExact⟩
  have htwoA' : AuthenticFieldPow.field.M31.add value.a value.a = .ok twoA := by
    rw [← root_m31_add_eq_authentic_pow]
    exact htwoA
  have hreal' : AuthenticFieldPow.field.M31.sub twoA value.b = .ok real := by
    rw [← root_m31_sub_eq_authentic_pow]
    exact hreal
  have htwoB' : AuthenticFieldPow.field.M31.add value.b value.b = .ok twoB := by
    rw [← root_m31_add_eq_authentic_pow]
    exact htwoB
  have himag' : AuthenticFieldPow.field.M31.add value.a twoB = .ok imag := by
    rw [← root_m31_add_eq_authentic_pow]
    exact himag
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AuthenticFieldPow.field.mul_by_r,
      AuthenticFieldPow.field.M31.double,
      htwoA', hreal', htwoB', himag']
  · apply QuadraticAlgebra.ext
    · simp only [rootCM31ToExact, qm31R, QuadraticAlgebra.re_mul]
      rw [hrealExact, htwoAExact]
      ring
    · simp only [rootCM31ToExact, qm31R, QuadraticAlgebra.im_mul]
      rw [himagExact, htwoBExact]
      ring

end GoodMatricesCurrent.SourceExtractedTerminalField
