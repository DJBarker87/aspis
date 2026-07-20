import M31NegProof
import CM31ExactModel

/-!
# Extracted Rust CM31 negation correspondence

The capstone composes the actual Aeneas definition generated from
`crates/aspis-core/src/field.rs` with the proved M31 negation bridge.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31Neg

open aspis_core
open AspisAeneasCM31Exact

def CanonicalCM31 (x : field.CM31) : Prop :=
  AspisAeneasM31Neg.CanonicalRawM31 x.a.val ∧
  AspisAeneasM31Neg.CanonicalRawM31 x.b.val

def toExact (x : field.CM31) : CM31Exact := ofRaw x.a.val x.b.val

@[simp] theorem toExact_re (x : field.CM31) :
    (toExact x).re = (x.a.val : M31Exact) := rfl

@[simp] theorem toExact_im (x : field.CM31) :
    (toExact x).im = (x.b.val : M31Exact) := rfl

/-- Source-authentic CM31 negation is coordinatewise exact. -/
theorem extracted_cm31_neg_corresponds
    (x : field.CM31) (hx : CanonicalCM31 x) :
    ∃ out : field.CM31,
      field.CM31.neg x = ok out ∧
      out.a.val = AspisAeneasM31Neg.rawM31Neg x.a.val ∧
      out.b.val = AspisAeneasM31Neg.rawM31Neg x.b.val ∧
      CanonicalCM31 out ∧
      toExact out = -toExact x := by
  rcases AspisAeneasM31Neg.extracted_m31_neg_corresponds
      x.a hx.1 with ⟨oa, hoa, hrawa, hcana, hexacta⟩
  rcases AspisAeneasM31Neg.extracted_m31_neg_corresponds
      x.b hx.2 with ⟨ob, hob, hrawb, hcanb, hexactb⟩
  refine ⟨⟨oa, ob⟩, ?_, hrawa, hrawb, ⟨hcana, hcanb⟩, ?_⟩
  · simp [field.CM31.neg, hoa, hob]
  · ext
    · exact hexacta
    · exact hexactb

#print axioms extracted_cm31_neg_corresponds

end AspisAeneasCM31Neg
