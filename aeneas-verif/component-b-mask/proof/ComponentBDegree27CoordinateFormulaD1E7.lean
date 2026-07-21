import ComponentBMaintainedTerminalBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBMaintainedTerminalBridge

noncomputable section

private def degreeNatTerm (polynomial : Polynomial) (x : ExactQM31) :
    Nat → ExactQM31
  | 0 => exactConstant polynomial
  | coefficient + 1 =>
      if h : coefficient < 27 then
        exactTail polynomial ⟨coefficient, h⟩ * x ^ (coefficient + 1)
      else
        0

private def prefixThroughSix (polynomial : Polynomial)
    (x : ExactQM31) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨0, by omega⟩) +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨1, by omega⟩) * x +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨2, by omega⟩) * x^2 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨3, by omega⟩) * x^3 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨4, by omega⟩) * x^4 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨5, by omega⟩) * x^5 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨6, by omega⟩) * x^6

private def chunkSevenToThirteen (polynomial : Polynomial)
    (x : ExactQM31) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨7, by omega⟩) * x^7 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨8, by omega⟩) * x^8 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨9, by omega⟩) * x^9 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨10, by omega⟩) * x^10 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨11, by omega⟩) * x^11 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨12, by omega⟩) * x^12 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨13, by omega⟩) * x^13

private def prefixThroughThirteen (polynomial : Polynomial)
    (x : ExactQM31) : ExactQM31 :=
  prefixThroughSix polynomial x +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨7, by omega⟩) * x^7 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨8, by omega⟩) * x^8 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨9, by omega⟩) * x^9 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨10, by omega⟩) * x^10 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨11, by omega⟩) * x^11 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨12, by omega⟩) * x^12 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨13, by omega⟩) * x^13

private def chunkFourteenToTwenty (polynomial : Polynomial)
    (x : ExactQM31) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨14, by omega⟩) * x^14 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨15, by omega⟩) * x^15 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨16, by omega⟩) * x^16 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨17, by omega⟩) * x^17 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨18, by omega⟩) * x^18 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨19, by omega⟩) * x^19 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨20, by omega⟩) * x^20

private def prefixThroughTwenty (polynomial : Polynomial)
    (x : ExactQM31) : ExactQM31 :=
  prefixThroughThirteen polynomial x +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨14, by omega⟩) * x^14 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨15, by omega⟩) * x^15 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨16, by omega⟩) * x^16 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨17, by omega⟩) * x^17 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨18, by omega⟩) * x^18 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨19, by omega⟩) * x^19 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨20, by omega⟩) * x^20

private def chunkTwentyOneToTwentySeven (polynomial : Polynomial)
    (x : ExactQM31) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨21, by omega⟩) * x^21 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨22, by omega⟩) * x^22 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨23, by omega⟩) * x^23 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨24, by omega⟩) * x^24 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨25, by omega⟩) * x^25 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨26, by omega⟩) * x^26 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨27, by omega⟩) * x^27

private def prefixThroughTwentySeven (polynomial : Polynomial)
    (x : ExactQM31) : ExactQM31 :=
  prefixThroughTwenty polynomial x +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨21, by omega⟩) * x^21 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨22, by omega⟩) * x^22 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨23, by omega⟩) * x^23 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨24, by omega⟩) * x^24 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨25, by omega⟩) * x^25 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨26, by omega⟩) * x^26 +
  ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨27, by omega⟩) * x^27

private theorem prefixThroughSix_expansion (polynomial : Polynomial)
    (x : ExactQM31) :
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨0, by omega⟩) +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨1, by omega⟩) * x +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨2, by omega⟩) * x^2 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨3, by omega⟩) * x^3 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨4, by omega⟩) * x^4 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨5, by omega⟩) * x^5 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨6, by omega⟩) * x^6 =
      prefixThroughSix polynomial x := by
  rfl

private theorem prefixThroughThirteen_expansion (polynomial : Polynomial)
    (x : ExactQM31) :
    prefixThroughSix polynomial x +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨7, by omega⟩) * x^7 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨8, by omega⟩) * x^8 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨9, by omega⟩) * x^9 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨10, by omega⟩) * x^10 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨11, by omega⟩) * x^11 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨12, by omega⟩) * x^12 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨13, by omega⟩) * x^13 =
      prefixThroughThirteen polynomial x := by
  rfl

private theorem prefixThroughTwenty_expansion (polynomial : Polynomial)
    (x : ExactQM31) :
    prefixThroughThirteen polynomial x +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨14, by omega⟩) * x^14 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨15, by omega⟩) * x^15 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨16, by omega⟩) * x^16 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨17, by omega⟩) * x^17 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨18, by omega⟩) * x^18 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨19, by omega⟩) * x^19 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨20, by omega⟩) * x^20 =
      prefixThroughTwenty polynomial x := by
  rfl

private theorem prefixThroughTwentySeven_expansion (polynomial : Polynomial)
    (x : ExactQM31) :
    prefixThroughTwenty polynomial x +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨21, by omega⟩) * x^21 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨22, by omega⟩) * x^22 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨23, by omega⟩) * x^23 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨24, by omega⟩) * x^24 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨25, by omega⟩) * x^25 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨26, by omega⟩) * x^26 +
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨27, by omega⟩) * x^27 =
      prefixThroughTwentySeven polynomial x := by
  rfl

private theorem sumRangeSeven (f : Nat → ExactQM31) :
    (∑ i ∈ Finset.range 7, f i) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  norm_num [Finset.sum_range_succ]

private theorem prefixThroughSix_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    prefixThroughSix polynomial x =
      ∑ i ∈ Finset.range 7, degreeNatTerm polynomial x i := by
  rw [sumRangeSeven]
  norm_num [prefixThroughSix, degreeNatTerm, exactConstant, exactTail]

private theorem chunkSevenToThirteen_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    chunkSevenToThirteen polynomial x =
      ∑ i ∈ Finset.range 7, degreeNatTerm polynomial x (7 + i) := by
  rw [sumRangeSeven]
  norm_num [chunkSevenToThirteen, degreeNatTerm, exactTail]

private theorem chunkFourteenToTwenty_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    chunkFourteenToTwenty polynomial x =
      ∑ i ∈ Finset.range 7, degreeNatTerm polynomial x (14 + i) := by
  rw [sumRangeSeven]
  norm_num [chunkFourteenToTwenty, degreeNatTerm, exactTail]

private theorem chunkTwentyOneToTwentySeven_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    chunkTwentyOneToTwentySeven polynomial x =
      ∑ i ∈ Finset.range 7, degreeNatTerm polynomial x (21 + i) := by
  rw [sumRangeSeven]
  norm_num [chunkTwentyOneToTwentySeven, degreeNatTerm, exactTail]

private theorem prefixThroughThirteen_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    prefixThroughThirteen polynomial x =
      ∑ i ∈ Finset.range 14, degreeNatTerm polynomial x i := by
  calc
    prefixThroughThirteen polynomial x =
        prefixThroughSix polynomial x + chunkSevenToThirteen polynomial x := by
          unfold prefixThroughThirteen chunkSevenToThirteen
          abel
    _ = (∑ i ∈ Finset.range 7, degreeNatTerm polynomial x i) +
        ∑ i ∈ Finset.range 7, degreeNatTerm polynomial x (7 + i) := by
          rw [prefixThroughSix_eq_sum, chunkSevenToThirteen_eq_sum]
    _ = ∑ i ∈ Finset.range 14, degreeNatTerm polynomial x i := by
          simpa using
            (Finset.sum_range_add (degreeNatTerm polynomial x) 7 7).symm

private theorem prefixThroughTwenty_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    prefixThroughTwenty polynomial x =
      ∑ i ∈ Finset.range 21, degreeNatTerm polynomial x i := by
  calc
    prefixThroughTwenty polynomial x =
        prefixThroughThirteen polynomial x + chunkFourteenToTwenty polynomial x := by
          unfold prefixThroughTwenty chunkFourteenToTwenty
          abel
    _ = (∑ i ∈ Finset.range 14, degreeNatTerm polynomial x i) +
        ∑ i ∈ Finset.range 7, degreeNatTerm polynomial x (14 + i) := by
          rw [prefixThroughThirteen_eq_sum, chunkFourteenToTwenty_eq_sum]
    _ = ∑ i ∈ Finset.range 21, degreeNatTerm polynomial x i := by
          simpa using
            (Finset.sum_range_add (degreeNatTerm polynomial x) 14 7).symm

private theorem prefixThroughTwentySeven_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    prefixThroughTwentySeven polynomial x =
      ∑ i ∈ Finset.range 28, degreeNatTerm polynomial x i := by
  calc
    prefixThroughTwentySeven polynomial x =
        prefixThroughTwenty polynomial x +
          chunkTwentyOneToTwentySeven polynomial x := by
            unfold prefixThroughTwentySeven chunkTwentyOneToTwentySeven
            abel
    _ = (∑ i ∈ Finset.range 21, degreeNatTerm polynomial x i) +
        ∑ i ∈ Finset.range 7, degreeNatTerm polynomial x (21 + i) := by
          rw [prefixThroughTwenty_eq_sum, chunkTwentyOneToTwentySeven_eq_sum]
    _ = ∑ i ∈ Finset.range 28, degreeNatTerm polynomial x i := by
          simpa using
            (Finset.sum_range_add (degreeNatTerm polynomial x) 21 7).symm

private theorem exactDegree27Evaluation_eq_sum (polynomial : Polynomial)
    (x : ExactQM31) :
    ComponentBRealEvaluatorProof.exactDegree27Evaluation polynomial x =
      ∑ coefficient ∈ Finset.range 28, degreeNatTerm polynomial x coefficient := by
  unfold ComponentBRealEvaluatorProof.exactDegree27Evaluation
  rw [prefixThroughSix_expansion]
  rw [prefixThroughThirteen_expansion]
  rw [prefixThroughTwenty_expansion]
  rw [prefixThroughTwentySeven_expansion]
  exact prefixThroughTwentySeven_eq_sum polynomial x

private theorem sumRangeTwentyEight_eq_headTail (polynomial : Polynomial)
    (x : ExactQM31) :
    (∑ coefficient ∈ Finset.range 28,
        degreeNatTerm polynomial x coefficient) =
      exactConstant polynomial +
        ∑ coefficient : Fin 27,
          exactTail polynomial coefficient * x ^ (coefficient.val + 1) := by
  calc
    (∑ coefficient ∈ Finset.range 28,
        degreeNatTerm polynomial x coefficient) =
        (∑ coefficient ∈ Finset.range 1,
          degreeNatTerm polynomial x coefficient) +
        ∑ coefficient ∈ Finset.range 27,
          degreeNatTerm polynomial x (1 + coefficient) := by
            simpa using (Finset.sum_range_add
              (degreeNatTerm polynomial x) 1 27)
    _ = exactConstant polynomial +
        ∑ coefficient ∈ Finset.range 27,
          degreeNatTerm polynomial x (1 + coefficient) := by
            simp [degreeNatTerm]
    _ = exactConstant polynomial +
        ∑ coefficient : Fin 27,
          exactTail polynomial coefficient * x ^ (coefficient.val + 1) := by
            congr 1

/-- The explicit generated degree-27 evaluator is the maintained constant
followed by the increasing 27-coordinate tail. The proof crosses the 28
coordinates in four seven-term chunks, then reindexes the range as one head
plus 27 tail coordinates. No elaboration step compares both expanded sides. -/
theorem degree27CoordinateFormula_d1e7 : Degree27CoordinateFormula := by
  constructor
  intro polynomial x
  rw [exactDegree27Evaluation_eq_sum, sumRangeTwentyEight_eq_headTail]
  congr 1

#print axioms degree27CoordinateFormula_d1e7

end

end ComponentBMaintainedTerminalBridge
