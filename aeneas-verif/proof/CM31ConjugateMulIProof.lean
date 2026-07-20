import AspisCoreCm31Helpers
import M31NegProof
import CM31ExactModel

/-!
# Extracted Rust CM31 conjugation and multiplication by i

Both source functions are multiplication-free coordinate transforms.  The only
arithmetic operation they call is the already bridged Rust M31 negation.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31ConjugateMulI

open AspisAeneasCM31Exact

abbrev HelperM31 := aspis_core_cm31_helpers.field.M31
abbrev HelperCM31 := aspis_core_cm31_helpers.field.CM31

def CanonicalCM31 (x : HelperCM31) : Prop :=
  AspisAeneasM31Neg.CanonicalRawM31 x.a.val ∧
  AspisAeneasM31Neg.CanonicalRawM31 x.b.val

def toExact (x : HelperCM31) : CM31Exact := ofRaw x.a.val x.b.val

theorem helper_m31_neg_eq (a : HelperM31) :
    aspis_core_cm31_helpers.field.M31.neg a =
      aspis_core.field.M31.neg a := by
  simp [aspis_core_cm31_helpers.field.M31.neg,
    aspis_core.field.M31.neg,
    aspis_core_cm31_helpers.field.P,
    aspis_core.field.P,
    Std.lift]

/-- Source-authentic conjugation preserves the real coordinate, negates the
imaginary coordinate, and maps to exact complex conjugation. -/
theorem extracted_cm31_conjugate_corresponds
    (x : HelperCM31) (hx : CanonicalCM31 x) :
    ∃ out : HelperCM31,
      aspis_core_cm31_helpers.field.CM31.conjugate x = ok out ∧
      out.a = x.a ∧
      out.b.val = AspisAeneasM31Neg.rawM31Neg x.b.val ∧
      CanonicalCM31 out ∧
      toExact out = conjugateExact (toExact x) := by
  rcases AspisAeneasM31Neg.extracted_m31_neg_corresponds
      x.b hx.2 with ⟨ob, hob, hrawb, hcanb, hexactb⟩
  have hhelper :
      aspis_core_cm31_helpers.field.M31.neg x.b = ok ob := by
    rw [helper_m31_neg_eq]
    exact hob
  refine ⟨⟨x.a, ob⟩, ?_, rfl, hrawb, ⟨hx.1, hcanb⟩, ?_⟩
  · simp [aspis_core_cm31_helpers.field.CM31.conjugate, hhelper]
  · ext
    · rfl
    · exact hexactb

/-- Source-authentic multiplication by `i` performs the exact coordinate
rotation `(-b, a)`. -/
theorem extracted_cm31_mul_i_corresponds
    (x : HelperCM31) (hx : CanonicalCM31 x) :
    ∃ out : HelperCM31,
      aspis_core_cm31_helpers.field.CM31.mul_i x = ok out ∧
      out.a.val = AspisAeneasM31Neg.rawM31Neg x.b.val ∧
      out.b = x.a ∧
      CanonicalCM31 out ∧
      toExact out = mulIExact (toExact x) := by
  rcases AspisAeneasM31Neg.extracted_m31_neg_corresponds
      x.b hx.2 with ⟨oa, hoa, hrawa, hcana, hexacta⟩
  have hhelper :
      aspis_core_cm31_helpers.field.M31.neg x.b = ok oa := by
    rw [helper_m31_neg_eq]
    exact hoa
  refine ⟨⟨oa, x.a⟩, ?_, hrawa, rfl, ⟨hcana, hx.1⟩, ?_⟩
  · simp [aspis_core_cm31_helpers.field.CM31.mul_i, hhelper]
  · ext
    · exact hexacta
    · rfl

theorem extracted_cm31_mul_i_eq_mul
    (x : HelperCM31) (hx : CanonicalCM31 x) :
    ∃ out : HelperCM31,
      aspis_core_cm31_helpers.field.CM31.mul_i x = ok out ∧
      toExact out = imaginaryUnit * toExact x := by
  rcases extracted_cm31_mul_i_corresponds x hx with
    ⟨out, hout, _hraw, _hcopy, _hcanonical, hexact⟩
  refine ⟨out, hout, ?_⟩
  rw [hexact, mulIExact_eq_mul]

#print axioms helper_m31_neg_eq
#print axioms extracted_cm31_conjugate_corresponds
#print axioms extracted_cm31_mul_i_corresponds
#print axioms extracted_cm31_mul_i_eq_mul

end AspisAeneasCM31ConjugateMulI
