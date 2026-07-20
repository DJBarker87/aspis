import M31AddProof
import CM31ExactModel

/-!
# Extracted Rust CM31 addition correspondence

The capstone composes the actual Aeneas definition generated from
`crates/aspis-core/src/field.rs` with the proved M31 addition bridge.  No CM31
operation is restated as a model function.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31Add

open aspis_core
open AspisAeneasCM31Exact

/-- Both Rust coordinates are canonical M31 words. -/
def CanonicalCM31 (x : field.CM31) : Prop :=
  AspisAeneasM31Add.CanonicalRawM31 x.a.val ∧
  AspisAeneasM31Add.CanonicalRawM31 x.b.val

/-- Literal coordinate embedding of the generated Rust CM31 structure. -/
def toExact (x : field.CM31) : CM31Exact := ofRaw x.a.val x.b.val

@[simp] theorem toExact_re (x : field.CM31) :
    (toExact x).re = (x.a.val : M31Exact) := rfl

@[simp] theorem toExact_im (x : field.CM31) :
    (toExact x).im = (x.b.val : M31Exact) := rfl

/-- Source-authentic CM31 addition is successful, applies the exact raw M31
graph independently to both coordinates, preserves canonicality, and maps to
addition in the exact quadratic algebra. -/
theorem extracted_cm31_add_corresponds
    (x y : field.CM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : field.CM31,
      field.CM31.add x y = ok out ∧
      out.a.val = AspisAeneasM31Add.rawM31Add x.a.val y.a.val ∧
      out.b.val = AspisAeneasM31Add.rawM31Add x.b.val y.b.val ∧
      CanonicalCM31 out ∧
      toExact out = toExact x + toExact y := by
  rcases AspisAeneasM31Add.extracted_m31_add_corresponds
      x.a y.a hx.1 hy.1 with ⟨oa, hoa, hrawa, hcana, hexacta⟩
  rcases AspisAeneasM31Add.extracted_m31_add_corresponds
      x.b y.b hx.2 hy.2 with ⟨ob, hob, hrawb, hcanb, hexactb⟩
  refine ⟨⟨oa, ob⟩, ?_, hrawa, hrawb, ⟨hcana, hcanb⟩, ?_⟩
  · simp [field.CM31.add, hoa, hob]
  · ext
    · exact hexacta
    · exact hexactb

#print axioms extracted_cm31_add_corresponds

end AspisAeneasCM31Add
