import AspisCoreCm31Helpers
import M31AddProof
import CM31ExactModel

/-!
# Extracted Rust CM31 doubling correspondence

The helper extraction is deliberately placed in its own namespace so it can be
imported beside the independently generated M31 bridge without duplicate
declarations.  Both definitions still carry source spans into the same tracked
`field.rs` file.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31Double

open AspisAeneasCM31Exact

abbrev HelperM31 := aspis_core_cm31_helpers.field.M31
abbrev HelperCM31 := aspis_core_cm31_helpers.field.CM31

def CanonicalCM31 (x : HelperCM31) : Prop :=
  AspisAeneasM31Add.CanonicalRawM31 x.a.val ∧
  AspisAeneasM31Add.CanonicalRawM31 x.b.val

def toExact (x : HelperCM31) : CM31Exact := ofRaw x.a.val x.b.val

/-- The separately namespaced helper extraction contains the same actual M31
source body as the base addition extraction. -/
theorem helper_m31_add_eq (a b : HelperM31) :
    aspis_core_cm31_helpers.field.M31.add a b =
      aspis_core.field.M31.add a b := by
  simp [aspis_core_cm31_helpers.field.M31.add,
    aspis_core.field.M31.add,
    aspis_core_cm31_helpers.field.P,
    aspis_core.field.P,
    Std.lift]

/-- Source-authentic CM31 doubling is two coordinatewise M31 additions and
maps to exact addition by itself. -/
theorem extracted_cm31_double_corresponds
    (x : HelperCM31) (hx : CanonicalCM31 x) :
    ∃ out : HelperCM31,
      aspis_core_cm31_helpers.field.CM31.double x = ok out ∧
      out.a.val = AspisAeneasM31Add.rawM31Add x.a.val x.a.val ∧
      out.b.val = AspisAeneasM31Add.rawM31Add x.b.val x.b.val ∧
      CanonicalCM31 out ∧
      toExact out = toExact x + toExact x := by
  rcases AspisAeneasM31Add.extracted_m31_add_corresponds
      x.a x.a hx.1 hx.1 with ⟨oa, hoa, hrawa, hcana, hexacta⟩
  rcases AspisAeneasM31Add.extracted_m31_add_corresponds
      x.b x.b hx.2 hx.2 with ⟨ob, hob, hrawb, hcanb, hexactb⟩
  have hhelpera :
      aspis_core_cm31_helpers.field.M31.add x.a x.a = ok oa := by
    rw [helper_m31_add_eq]
    exact hoa
  have hhelperb :
      aspis_core_cm31_helpers.field.M31.add x.b x.b = ok ob := by
    rw [helper_m31_add_eq]
    exact hob
  refine ⟨⟨oa, ob⟩, ?_, hrawa, hrawb, ⟨hcana, hcanb⟩, ?_⟩
  · simp [aspis_core_cm31_helpers.field.CM31.double,
      aspis_core_cm31_helpers.field.CM31.add, hhelpera, hhelperb]
  · ext
    · exact hexacta
    · exact hexactb

#print axioms helper_m31_add_eq
#print axioms extracted_cm31_double_corresponds

end AspisAeneasCM31Double
