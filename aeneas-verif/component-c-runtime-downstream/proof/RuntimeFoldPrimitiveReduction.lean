import ComponentCRuntimeGenerated
import AspisFormal.V5ComponentCConcreteFoldLinearity

/-!
# Component-C extracted fold reduced to field primitives

The deployed arity-four line fold is source-authentic Rust extracted by
Charon/Aeneas.  This file proves that its complete operation graph is the
maintained `lineFoldValue`, conditional only on the five field primitives the
graph actually calls.  This is a strict narrowing of a whole-evaluator
correspondence premise: array order, butterfly order, the `alpha^2` outer
challenge, and every intermediate dependency are fixed by the generated
definition below.
-/

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeFoldPrimitiveReduction

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity

abbrev RawM31 := aspis_core.field.M31
abbrev RawQM31 := aspis_core.field.QM31

/-- Exact semantic interface for the five generated primitives used by the
prepared line fold.  Canonicality is explicit because the production M31
representation is canonical, rather than an arbitrary 32-bit word. -/
structure RuntimeFoldPrimitiveLaws (K : Type*) [Field K] where
  canonicalM31 : RawM31 → Prop
  canonicalQM31 : RawQM31 → Prop
  m31View : RawM31 → K
  qm31View : RawQM31 → K
  add : ∀ x y,
    canonicalQM31 x → canonicalQM31 y →
      ∃ out, aspis_core.field.QM31.add x y = ok out ∧
        canonicalQM31 out ∧ qm31View out = qm31View x + qm31View y
  sub : ∀ x y,
    canonicalQM31 x → canonicalQM31 y →
      ∃ out, aspis_core.field.QM31.sub x y = ok out ∧
        canonicalQM31 out ∧ qm31View out = qm31View x - qm31View y
  mul : ∀ x y,
    canonicalQM31 x → canonicalQM31 y →
      ∃ out, aspis_core.field.QM31.mul x y = ok out ∧
        canonicalQM31 out ∧ qm31View out = qm31View x * qm31View y
  half : ∀ x,
    canonicalQM31 x →
      ∃ out, aspis_core.field.QM31.half x = ok out ∧
        canonicalQM31 out ∧ qm31View out = qm31View x / 2
  mulM31 : ∀ x r,
    canonicalQM31 x → canonicalM31 r →
      ∃ out, aspis_core.field.QM31.mul_m31 x r = ok out ∧
        canonicalQM31 out ∧ qm31View out = qm31View x * m31View r

/-- The circle-to-line fold needs one additional base-field operation: the
negation of the second fibre's `inv_2y`. -/
structure RuntimeCirclePrimitiveLaws (K : Type*) [Field K]
    extends RuntimeFoldPrimitiveLaws K where
  negM31 : ∀ r,
    canonicalM31 r →
      ∃ out, aspis_core.field.M31.neg r = ok out ∧
        canonicalM31 out ∧ m31View out = -m31View r

/-- Explicit four-slot function used to state the maintained fold without
relying on elaborator-specific vector-notation reduction. -/
def orderedFour {K : Type*} (a b c d : K) (i : Fin 4) : K :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

@[simp] theorem orderedFour_zero {K : Type*} (a b c d : K) :
    orderedFour a b c d 0 = a := by simp [orderedFour]

@[simp] theorem orderedFour_one {K : Type*} (a b c d : K) :
    orderedFour a b c d 1 = b := by simp [orderedFour]

@[simp] theorem orderedFour_two {K : Type*} (a b c d : K) :
    orderedFour a b c d 2 = c := by simp [orderedFour]

@[simp] theorem orderedFour_three {K : Type*} (a b c d : K) :
    orderedFour a b c d 3 = d := by simp [orderedFour]

variable {K : Type*} [Field K]

/-- The source-authentic prepared line fold is exactly the maintained nested
arity-four fold.  The four input slots and three inverse slots are literal
generated arrays, so this theorem also binds their deployed ordering. -/
theorem extracted_prepared_line_fold_eq_maintained
    (laws : RuntimeFoldPrimitiveLaws K)
    (v0 v1 v2 v3 alpha alphaSquared : RawQM31)
    (inv0 inv1 inv2 : RawM31)
    (hv0 : laws.canonicalQM31 v0)
    (hv1 : laws.canonicalQM31 v1)
    (hv2 : laws.canonicalQM31 v2)
    (hv3 : laws.canonicalQM31 v3)
    (halpha : laws.canonicalQM31 alpha)
    (halphaSquared : laws.canonicalQM31 alphaSquared)
    (hinv0 : laws.canonicalM31 inv0)
    (hinv1 : laws.canonicalM31 inv1)
    (hinv2 : laws.canonicalM31 inv2)
    (halphaSquaredView :
      laws.qm31View alphaSquared = laws.qm31View alpha ^ 2) :
    ∃ out,
      aspis_core.circle_fri.normalized_line_arity4_prepared_with_square
          (Array.make 4#usize [v0, v1, v2, v3]) alpha alphaSquared
          (Array.make 3#usize [inv0, inv1, inv2]) = ok out ∧
      laws.canonicalQM31 out ∧
      laws.qm31View out =
        lineFoldValue (laws.qm31View alpha)
          (laws.m31View inv0) (laws.m31View inv1) (laws.m31View inv2)
          (orderedFour (laws.qm31View v0) (laws.qm31View v1)
            (laws.qm31View v2) (laws.qm31View v3)) := by
  rcases laws.add v0 v1 hv0 hv1 with
    ⟨sum0, hsum0, hsum0Canonical, hsum0View⟩
  rcases laws.half sum0 hsum0Canonical with
    ⟨mean0, hmean0, hmean0Canonical, hmean0View⟩
  rcases laws.sub v0 v1 hv0 hv1 with
    ⟨diff0, hdiff0, hdiff0Canonical, hdiff0View⟩
  rcases laws.mulM31 diff0 inv0 hdiff0Canonical hinv0 with
    ⟨scaled0, hscaled0, hscaled0Canonical, hscaled0View⟩
  rcases laws.mul alpha scaled0 halpha hscaled0Canonical with
    ⟨term0, hterm0, hterm0Canonical, hterm0View⟩
  rcases laws.add mean0 term0 hmean0Canonical hterm0Canonical with
    ⟨first, hfirst, hfirstCanonical, hfirstView⟩

  rcases laws.add v2 v3 hv2 hv3 with
    ⟨sum1, hsum1, hsum1Canonical, hsum1View⟩
  rcases laws.half sum1 hsum1Canonical with
    ⟨mean1, hmean1, hmean1Canonical, hmean1View⟩
  rcases laws.sub v2 v3 hv2 hv3 with
    ⟨diff1, hdiff1, hdiff1Canonical, hdiff1View⟩
  rcases laws.mulM31 diff1 inv1 hdiff1Canonical hinv1 with
    ⟨scaled1, hscaled1, hscaled1Canonical, hscaled1View⟩
  rcases laws.mul alpha scaled1 halpha hscaled1Canonical with
    ⟨term1, hterm1, hterm1Canonical, hterm1View⟩
  rcases laws.add mean1 term1 hmean1Canonical hterm1Canonical with
    ⟨second, hsecond, hsecondCanonical, hsecondView⟩

  rcases laws.add first second hfirstCanonical hsecondCanonical with
    ⟨outerSum, houterSum, houterSumCanonical, houterSumView⟩
  rcases laws.half outerSum houterSumCanonical with
    ⟨outerMean, houterMean, houterMeanCanonical, houterMeanView⟩
  rcases laws.sub first second hfirstCanonical hsecondCanonical with
    ⟨outerDiff, houterDiff, houterDiffCanonical, houterDiffView⟩
  rcases laws.mulM31 outerDiff inv2 houterDiffCanonical hinv2 with
    ⟨outerScaled, houterScaled, houterScaledCanonical, houterScaledView⟩
  rcases laws.mul alphaSquared outerScaled
      halphaSquared houterScaledCanonical with
    ⟨outerTerm, houterTerm, houterTermCanonical, houterTermView⟩
  rcases laws.add outerMean outerTerm
      houterMeanCanonical houterTermCanonical with
    ⟨out, hout, houtCanonical, houtView⟩

  have hV0 :
      (Array.make 4#usize [v0, v1, v2, v3]).index_usize 0#usize = ok v0 := by
    rfl
  have hV1 :
      (Array.make 4#usize [v0, v1, v2, v3]).index_usize 1#usize = ok v1 := by
    rfl
  have hV2 :
      (Array.make 4#usize [v0, v1, v2, v3]).index_usize 2#usize = ok v2 := by
    rfl
  have hV3 :
      (Array.make 4#usize [v0, v1, v2, v3]).index_usize 3#usize = ok v3 := by
    rfl
  have hI0 :
      (Array.make 3#usize [inv0, inv1, inv2]).index_usize 0#usize = ok inv0 := by
    rfl
  have hI1 :
      (Array.make 3#usize [inv0, inv1, inv2]).index_usize 1#usize = ok inv1 := by
    rfl
  have hI2 :
      (Array.make 3#usize [inv0, inv1, inv2]).index_usize 2#usize = ok inv2 := by
    rfl

  refine ⟨out, ?_, houtCanonical, ?_⟩
  · simp [aspis_core.circle_fri.normalized_line_arity4_prepared_with_square,
      aspis_core.circle_fri.normalized_line_arity4_prepared_with_square.closure.Insts.CoreOpsFunctionFnTupleQM31QM31QM31M31QM31.call,
      hV0, hV1, hV2, hV3, hI0, hI1, hI2,
      hsum0, hmean0, hdiff0, hscaled0, hterm0, hfirst,
      hsum1, hmean1, hdiff1, hscaled1, hterm1, hsecond,
      houterSum, houterMean, houterDiff, houterScaled, houterTerm, hout]
  · rw [houtView, houterMeanView, houterSumView,
      houterTermView, houterScaledView, houterDiffView,
      hfirstView, hsecondView,
      hmean0View, hsum0View, hterm0View, hscaled0View, hdiff0View,
      hmean1View, hsum1View, hterm1View, hscaled1View, hdiff1View,
      halphaSquaredView]
    simp only [lineFoldValue, pairFoldValue, orderedFour_zero,
      orderedFour_one, orderedFour_two, orderedFour_three]

/-- The source-authentic circle-to-line fold is the maintained circle fold.
This theorem fixes the deployed sign convention: the second pair uses
`-inv_2y`, while the outer butterfly uses `inv_2x`. -/
theorem extracted_prepared_circle_fold_eq_maintained
    (laws : RuntimeCirclePrimitiveLaws K)
    (v0 v1 v2 v3 alpha alphaSquared : RawQM31)
    (inv2x inv2y : RawM31)
    (hv0 : laws.canonicalQM31 v0)
    (hv1 : laws.canonicalQM31 v1)
    (hv2 : laws.canonicalQM31 v2)
    (hv3 : laws.canonicalQM31 v3)
    (halpha : laws.canonicalQM31 alpha)
    (halphaSquared : laws.canonicalQM31 alphaSquared)
    (hinv2x : laws.canonicalM31 inv2x)
    (hinv2y : laws.canonicalM31 inv2y)
    (halphaSquaredView :
      laws.qm31View alphaSquared = laws.qm31View alpha ^ 2) :
    ∃ out,
      aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_with_square
          (Array.make 4#usize [v0, v1, v2, v3]) alpha alphaSquared
          inv2x inv2y = ok out ∧
      laws.canonicalQM31 out ∧
      laws.qm31View out =
        circleFoldValue (laws.qm31View alpha)
          (laws.m31View inv2x) (laws.m31View inv2y)
          (orderedFour (laws.qm31View v0) (laws.qm31View v1)
            (laws.qm31View v2) (laws.qm31View v3)) := by
  rcases laws.negM31 inv2y hinv2y with
    ⟨negInv2y, hnegInv2y, hnegInv2yCanonical, hnegInv2yView⟩
  rcases extracted_prepared_line_fold_eq_maintained
      laws.toRuntimeFoldPrimitiveLaws
      v0 v1 v2 v3 alpha alphaSquared inv2y negInv2y inv2x
      hv0 hv1 hv2 hv3 halpha halphaSquared
      hinv2y hnegInv2yCanonical hinv2x halphaSquaredView with
    ⟨out, hline, houtCanonical, houtView⟩
  refine ⟨out, ?_, houtCanonical, ?_⟩
  · simpa [aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_with_square,
      aspis_core.circle_fri.normalized_line_arity4_prepared_with_square,
      aspis_core.circle_fri.normalized_line_arity4_prepared_with_square.closure.Insts.CoreOpsFunctionFnTupleQM31QM31QM31M31QM31.call,
      Array.index_usize, Array.make, hnegInv2y] using hline
  · simpa [circleFoldValue, hnegInv2yView] using houtView

#print axioms orderedFour_zero
#print axioms orderedFour_one
#print axioms orderedFour_two
#print axioms orderedFour_three
#print axioms extracted_prepared_line_fold_eq_maintained
#print axioms extracted_prepared_circle_fold_eq_maintained

end aspis_prover.ComponentCRuntimeFoldPrimitiveReduction
