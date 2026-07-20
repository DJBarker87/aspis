import M31SubProof
import CM31ExactModel

/-!
# Extracted Rust CM31 subtraction correspondence

The capstone composes the actual Aeneas definition generated from
`crates/aspis-core/src/field.rs` with the proved M31 subtraction bridge.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31Sub

open aspis_core
open AspisAeneasCM31Exact

def CanonicalCM31 (x : field.CM31) : Prop :=
  AspisAeneasM31Sub.CanonicalRawM31 x.a.val ∧
  AspisAeneasM31Sub.CanonicalRawM31 x.b.val

def toExact (x : field.CM31) : CM31Exact := ofRaw x.a.val x.b.val

@[simp] theorem toExact_re (x : field.CM31) :
    (toExact x).re = (x.a.val : M31Exact) := rfl

@[simp] theorem toExact_im (x : field.CM31) :
    (toExact x).im = (x.b.val : M31Exact) := rfl

/-- Source-authentic CM31 subtraction is coordinatewise exact. -/
theorem extracted_cm31_sub_corresponds
    (x y : field.CM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : field.CM31,
      field.CM31.sub x y = ok out ∧
      out.a.val = AspisAeneasM31Sub.rawM31Sub x.a.val y.a.val ∧
      out.b.val = AspisAeneasM31Sub.rawM31Sub x.b.val y.b.val ∧
      CanonicalCM31 out ∧
      toExact out = toExact x - toExact y := by
  rcases AspisAeneasM31Sub.extracted_m31_sub_corresponds
      x.a y.a hx.1 hy.1 with ⟨oa, hoa, hrawa, hcana, hexacta⟩
  rcases AspisAeneasM31Sub.extracted_m31_sub_corresponds
      x.b y.b hx.2 hy.2 with ⟨ob, hob, hrawb, hcanb, hexactb⟩
  refine ⟨⟨oa, ob⟩, ?_, hrawa, hrawb, ⟨hcana, hcanb⟩, ?_⟩
  · simp [field.CM31.sub, hoa, hob]
  · ext
    · exact hexacta
    · exact hexactb

#print axioms extracted_cm31_sub_corresponds

end AspisAeneasCM31Sub
