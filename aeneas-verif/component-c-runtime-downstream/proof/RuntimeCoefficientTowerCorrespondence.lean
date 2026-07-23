import RuntimeCoefficientFoldCorrespondence

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeCoefficientTowerCorrespondence

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeCoefficientFoldCorrespondence
open AspisV5ComponentCConcreteFoldLinearity

abbrev RawQM31 := aspis_core.field.QM31
abbrev ExtensionField := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

def runtimeCoefficientView (values : Slice RawQM31) (n : Nat) :
    Fin n → ExtensionField :=
  fun row => runtimeQM31View values.val[row.val]!

/-- One public generated coefficient fold is the maintained natural-basis
fold layer, with no residual arithmetic premise. -/
theorem generated_coefficient_round_equals_maintained
    (values : Slice RawQM31) (alpha : RawQM31) (n : Nat)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 256)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (halpha : runtimeCanonicalQM31 alpha) :
    ∃ out,
      circle_candidate.fold_adjacent_natural_arity4 values alpha = ok out ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ fibre : Fin n,
        runtimeQM31View out.val[fibre.val]! =
          coefficientFoldLayer n (runtimeQM31View alpha)
            (runtimeCoefficientView values (4 * n)) fibre := by
  obtain ⟨out, hrun, hlength, hcanonical, hexact⟩ :=
    extracted_fold_adjacent_natural_arity4_exact values alpha n
      hvaluesLength hn hvaluesCanonical halpha
  refine ⟨out, hrun, hlength, hcanonical, ?_⟩
  intro fibre
  rw [hexact fibre.val fibre.isLt, coefficientFoldLayer_apply]
  unfold coefficientFoldAt exactSliceEntry runtimeCoefficientView
  rfl

/-- The four actual generated coefficient folds compose to the exact maintained
`1024 → 256 → 64 → 16 → 4` final-coefficient map. -/
theorem generated_four_round_coefficient_tower
    (values0 : Slice RawQM31)
    (alpha0 alpha1 alpha2 alpha3 : RawQM31)
    (hvalues0Length : values0.val.length = 1024)
    (hvalues0Canonical : RuntimeCanonicalList values0.val)
    (halpha0 : runtimeCanonicalQM31 alpha0)
    (halpha1 : runtimeCanonicalQM31 alpha1)
    (halpha2 : runtimeCanonicalQM31 alpha2)
    (halpha3 : runtimeCanonicalQM31 alpha3) :
    ∃ values1 values2 values3 values4,
      circle_candidate.fold_adjacent_natural_arity4 values0 alpha0 =
        ok values1 ∧
      circle_candidate.fold_adjacent_natural_arity4
          (alloc.vec.Vec.deref values1) alpha1 = ok values2 ∧
      circle_candidate.fold_adjacent_natural_arity4
          (alloc.vec.Vec.deref values2) alpha2 = ok values3 ∧
      circle_candidate.fold_adjacent_natural_arity4
          (alloc.vec.Vec.deref values3) alpha3 = ok values4 ∧
      values1.val.length = 256 ∧
      values2.val.length = 64 ∧
      values3.val.length = 16 ∧
      values4.val.length = 4 ∧
      RuntimeCanonicalList values1.val ∧
      RuntimeCanonicalList values2.val ∧
      RuntimeCanonicalList values3.val ∧
      RuntimeCanonicalList values4.val ∧
      (∀ coefficient : Fin 256,
        runtimeQM31View values1.val[coefficient.val]! =
          coefficientFoldLayer 256 (runtimeQM31View alpha0)
            (runtimeCoefficientView values0 1024) coefficient) ∧
      (∀ coefficient : Fin 64,
        runtimeQM31View values2.val[coefficient.val]! =
          coefficientFoldLayer 64 (runtimeQM31View alpha1)
            (coefficientFoldLayer 256 (runtimeQM31View alpha0)
              (runtimeCoefficientView values0 1024)) coefficient) ∧
      (∀ coefficient : Fin 16,
        runtimeQM31View values3.val[coefficient.val]! =
          coefficientFoldLayer 16 (runtimeQM31View alpha2)
            (coefficientFoldLayer 64 (runtimeQM31View alpha1)
              (coefficientFoldLayer 256 (runtimeQM31View alpha0)
                (runtimeCoefficientView values0 1024))) coefficient) ∧
      ∀ coefficient : Fin 4,
        runtimeQM31View values4.val[coefficient.val]! =
          coefficientFoldLayer 4 (runtimeQM31View alpha3)
            (coefficientFoldLayer 16 (runtimeQM31View alpha2)
              (coefficientFoldLayer 64 (runtimeQM31View alpha1)
                (coefficientFoldLayer 256 (runtimeQM31View alpha0)
                  (runtimeCoefficientView values0 1024)))) coefficient := by
  obtain ⟨values1, run1, length1, canonical1, exact1⟩ :=
    generated_coefficient_round_equals_maintained values0 alpha0 256
      (by omega) (by norm_num) hvalues0Canonical halpha0
  have inputLength1 :
      (alloc.vec.Vec.deref values1).val.length = 4 * 64 := by
    change values1.val.length = 4 * 64
    omega
  obtain ⟨values2, run2, length2, canonical2, exact2⟩ :=
    generated_coefficient_round_equals_maintained
      (alloc.vec.Vec.deref values1) alpha1 64 inputLength1
      (by norm_num) canonical1 halpha1
  have inputLength2 :
      (alloc.vec.Vec.deref values2).val.length = 4 * 16 := by
    change values2.val.length = 4 * 16
    omega
  obtain ⟨values3, run3, length3, canonical3, exact3⟩ :=
    generated_coefficient_round_equals_maintained
      (alloc.vec.Vec.deref values2) alpha2 16 inputLength2
      (by norm_num) canonical2 halpha2
  have inputLength3 :
      (alloc.vec.Vec.deref values3).val.length = 4 * 4 := by
    change values3.val.length = 4 * 4
    omega
  obtain ⟨values4, run4, length4, canonical4, exact4⟩ :=
    generated_coefficient_round_equals_maintained
      (alloc.vec.Vec.deref values3) alpha3 4 inputLength3
      (by norm_num) canonical3 halpha3
  have view1 : runtimeCoefficientView (alloc.vec.Vec.deref values1) 256 =
      coefficientFoldLayer 256 (runtimeQM31View alpha0)
        (runtimeCoefficientView values0 1024) := by
    funext fibre
    exact exact1 fibre
  have view2 : runtimeCoefficientView (alloc.vec.Vec.deref values2) 64 =
      coefficientFoldLayer 64 (runtimeQM31View alpha1)
        (coefficientFoldLayer 256 (runtimeQM31View alpha0)
          (runtimeCoefficientView values0 1024)) := by
    funext fibre
    change runtimeQM31View values2.val[fibre.val]! = _
    rw [exact2 fibre, view1]
  have view3 : runtimeCoefficientView (alloc.vec.Vec.deref values3) 16 =
      coefficientFoldLayer 16 (runtimeQM31View alpha2)
        (coefficientFoldLayer 64 (runtimeQM31View alpha1)
          (coefficientFoldLayer 256 (runtimeQM31View alpha0)
            (runtimeCoefficientView values0 1024))) := by
    funext fibre
    change runtimeQM31View values3.val[fibre.val]! = _
    rw [exact3 fibre, view2]
  refine ⟨values1, values2, values3, values4,
    run1, run2, run3, run4,
    length1, length2, length3, length4,
    canonical1, canonical2, canonical3, canonical4,
    exact1, ?_, ?_, ?_⟩
  · intro coefficient
    exact congrFun view2 coefficient
  · intro coefficient
    exact congrFun view3 coefficient
  intro coefficient
  rw [exact4 coefficient, view3]

#print axioms generated_coefficient_round_equals_maintained
#print axioms generated_four_round_coefficient_tower

end aspis_prover.ComponentCRuntimeCoefficientTowerCorrespondence
