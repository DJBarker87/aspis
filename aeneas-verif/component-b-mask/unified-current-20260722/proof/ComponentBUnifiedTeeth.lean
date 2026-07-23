import ComponentBUnifiedTransportFree

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBUnifiedTeeth

/-! These are negative executable seams, not substitutes for the universal
source correspondence.  Each uses an explicit nonzero model. -/

def coordinateBlock (tag : ℚ) : List ℚ :=
  tag :: List.replicate 26 0

def twoRoundCommitment (first second : ℚ) : List ℚ :=
  3 :: coordinateBlock first ++ coordinateBlock second

/-- Tooth 1: swapping adjacent nonzero round blocks changes the exact flattened
commitment-coordinate order. -/
theorem adjacent_round_block_swap_changes_coordinates :
    twoRoundCommitment 1 2 ≠ twoRoundCommitment 2 1 := by
  intro equality
  have atFirstRound := congrArg (fun values : List ℚ ↦ values[1]?) equality
  norm_num [twoRoundCommitment, coordinateBlock] at atFirstRound

def degree27Model (coefficient : Fin 28) : ℚ :=
  if coefficient.val = 0 then 1
  else if coefficient.val = 27 then 2
  else 0

def degree27Evaluation (coefficients : Fin 28 → ℚ) (x : ℚ) : ℚ :=
  ∑ coefficient : Fin 28,
    coefficients coefficient * x ^ coefficient.val

/-- Tooth 2: reversing all 28 coefficients of one nonzero round is observable
away from the Boolean endpoints. -/
theorem reverse_full_round_changes_degree27_evaluation :
    degree27Evaluation degree27Model 2 ≠
      degree27Evaluation (fun coefficient ↦ degree27Model coefficient.rev) 2 := by
  norm_num [degree27Evaluation, degree27Model, Fin.sum_univ_succ]

def zeroBoundaryModel (coefficient : Fin 28) : ℚ :=
  if coefficient.val = 0 then -1
  else if coefficient.val = 1 then 2
  else 0

def alteredConstantModel (coefficient : Fin 28) : ℚ :=
  if coefficient.val = 0 then 0 else zeroBoundaryModel coefficient

def booleanBoundary (coefficients : Fin 28 → ℚ) : ℚ :=
  2 * coefficients ⟨0, by omega⟩ +
    ∑ coefficient : Fin 27, coefficients ⟨coefficient.val + 1, by omega⟩

/-- Tooth 3: the nonzero zero-boundary model has derived `c0 = -1`; changing
only that correction to zero destroys the Boolean boundary equation. -/
theorem altering_nonzero_zero_boundary_c0_breaks_boundary :
    booleanBoundary zeroBoundaryModel = 0 ∧
      booleanBoundary alteredConstantModel ≠ 0 := by
  constructor <;>
    norm_num [booleanBoundary, zeroBoundaryModel, alteredConstantModel,
      Fin.sum_univ_succ]

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev ExactQM31 := ComponentBRealEvaluatorProof.ExactQM31

def canonicalAdapterModel : QM31 :=
  ⟨⟨1#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩

def swappedLimbAdapter (value : QM31) : ExactQM31 :=
  ⟨⟨(value.c0.b.val : ComponentBRealEvaluatorProof.ExactM31),
      (value.c0.a.val : ComponentBRealEvaluatorProof.ExactM31)⟩,
    ⟨(value.c1.a.val : ComponentBRealEvaluatorProof.ExactM31),
      (value.c1.b.val : ComponentBRealEvaluatorProof.ExactM31)⟩⟩

/-- Tooth 4: swapping the two base-field limbs in the exact adapter changes a
canonical nonzero generated value. -/
theorem altered_exact_adapter_changes_canonical_nonzero_value :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 canonicalAdapterModel ∧
      canonicalAdapterModel ≠ ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact canonicalAdapterModel ≠
        swappedLimbAdapter canonicalAdapterModel := by
  constructor
  · norm_num [canonicalAdapterModel,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus]
  constructor
  · norm_num [canonicalAdapterModel,
      ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero]
  · intro equality
    have realReal := congrArg
      (fun value : ExactQM31 ↦ value.re.re) equality
    norm_num [canonicalAdapterModel, swappedLimbAdapter,
      ComponentBRealEvaluatorProof.generatedQm31ToExact,
      ComponentBRealEvaluatorProof.generatedCm31ToExact] at realReal

#print axioms adjacent_round_block_swap_changes_coordinates
#print axioms reverse_full_round_changes_degree27_evaluation
#print axioms altering_nonzero_zero_boundary_c0_breaks_boundary
#print axioms altered_exact_adapter_changes_canonical_nonzero_value

end ComponentBUnifiedTeeth
