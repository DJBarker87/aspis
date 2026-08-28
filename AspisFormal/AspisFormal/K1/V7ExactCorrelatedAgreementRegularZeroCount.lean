import AspisFormal.K1.V7ExactCorrelatedAgreementRegularRing
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Weighted resultant zero count for the exact V7 regular branch

This module reconstructs BCIKS Lemma A.1.  The determinant lemma below keeps
row potentials instead of applying a uniform worst-case degree to every
Sylvester entry.  That distinction is what yields the exact `d_H * weight`
bound used by the released challenge caps.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementRegularZeroCount

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementSmooth

noncomputable section

/-- Determinant degree bound with row potentials.  Each selected determinant
term uses every row exactly once, so the row costs cancel globally against
the column budgets. -/
theorem matrix_det_natDegree_le_of_potentials
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι (Polynomial K))
    (rowPotential columnBudget : ι → Nat) (totalBudget : Nat)
    (entries : ∀ row column,
      matrix row column ≠ 0 →
        (matrix row column).natDegree + rowPotential row ≤
          columnBudget column)
    (budgets : ∑ column, columnBudget column ≤
      totalBudget + ∑ row, rowPotential row) :
    matrix.det.natDegree ≤ totalBudget := by
  classical
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro permutation
  by_cases productZero :
      ∏ column : ι, matrix (permutation column) column = 0
  · simp [productZero]
  have entryNeZero : ∀ column : ι,
      matrix (permutation column) column ≠ 0 := by
    intro column entryZero
    apply productZero
    exact Finset.prod_eq_zero (Finset.mem_univ column) entryZero
  calc
    (Equiv.Perm.sign permutation •
        ∏ column : ι, matrix (permutation column) column).natDegree ≤
        (∏ column : ι, matrix (permutation column) column).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with sign | sign
      · rw [sign, one_smul]
      · rw [sign, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ column : ι,
        (matrix (permutation column) column).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ totalBudget := by
      have entrySum :
          ∑ column : ι,
              ((matrix (permutation column) column).natDegree +
                rowPotential (permutation column)) ≤
            ∑ column : ι, columnBudget column := by
        exact Finset.sum_le_sum fun column _ =>
          entries (permutation column) column (entryNeZero column)
      have permutedPotential :
          ∑ column : ι, rowPotential (permutation column) =
            ∑ row : ι, rowPotential row := by
        exact Equiv.sum_comp permutation rowPotential
      rw [Finset.sum_add_distrib, permutedPotential] at entrySum
      have combined := entrySum.trans budgets
      omega

/-- Exact weighted Sylvester bound.  The first block contains `m` shifted
copies of the monicized equation and the second contains `d` shifted copies
of the regular representative.  The shifts cancel against the row
permutation, leaving exactly `d * representativeWeight`. -/
theorem resultant_natDegree_le_mul_weight
    {K : Type*} [Field K]
    (representative modulus : Polynomial (Polynomial K))
    (m d tWeight representativeWeight : Nat)
    (representativeCoefficients : ∀ coefficient,
      representative.coeff coefficient ≠ 0 →
        (representative.coeff coefficient).natDegree +
          coefficient * tWeight ≤ representativeWeight)
    (modulusCoefficients : ∀ coefficient,
      modulus.coeff coefficient ≠ 0 →
        (modulus.coeff coefficient).natDegree +
          coefficient * tWeight ≤ d * tWeight) :
    (Polynomial.resultant representative modulus m d).natDegree ≤
      d * representativeWeight := by
  classical
  let rowPotential : Fin (m + d) → Nat := fun row => row.1 * tWeight
  let columnBudget : Fin (m + d) → Nat := fun column =>
    column.addCases
      (fun shift : Fin m => d * tWeight + shift.1 * tWeight)
      (fun shift : Fin d => representativeWeight + shift.1 * tWeight)
  unfold Polynomial.resultant
  apply matrix_det_natDegree_le_of_potentials
    (Polynomial.sylvester representative modulus m d)
    rowPotential columnBudget (d * representativeWeight)
  · intro row column entryNeZero
    induction column using Fin.addCases with
    | left column =>
        have entryDescription :
            column.1 ≤ row.1 ∧ row.1 ≤ column.1 + d ∧
              modulus.coeff (row.1 - column.1) ≠ 0 := by
          simpa [Polynomial.sylvester] using entryNeZero
        have bounded := modulusCoefficients
          (row.1 - column.1) entryDescription.2.2
        have rowWeight :
            row.1 * tWeight =
              (row.1 - column.1) * tWeight + column.1 * tWeight := by
          rw [← Nat.add_mul, Nat.sub_add_cancel entryDescription.1]
        have indexCancel :
            row.1 - column.1 + column.1 - column.1 =
              row.1 - column.1 := by omega
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left,
          Set.mem_Icc, entryDescription.1, entryDescription.2.1, and_self,
          ↓reduceIte, rowPotential, columnBudget]
        rw [rowWeight]
        simpa [Nat.add_assoc, indexCancel] using Nat.add_le_add_right bounded
          (column.1 * tWeight)
    | right column =>
        have entryDescription :
            column.1 ≤ row.1 ∧ row.1 ≤ column.1 + m ∧
              representative.coeff (row.1 - column.1) ≠ 0 := by
          simpa [Polynomial.sylvester] using entryNeZero
        have bounded := representativeCoefficients
          (row.1 - column.1) entryDescription.2.2
        have rowWeight :
            row.1 * tWeight =
              (row.1 - column.1) * tWeight + column.1 * tWeight := by
          rw [← Nat.add_mul, Nat.sub_add_cancel entryDescription.1]
        have indexCancel :
            row.1 - column.1 + column.1 - column.1 =
              row.1 - column.1 := by omega
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right,
          Set.mem_Icc, entryDescription.1, entryDescription.2.1, and_self,
          ↓reduceIte, rowPotential, columnBudget]
        rw [rowWeight]
        simpa [Nat.add_assoc, indexCancel] using Nat.add_le_add_right bounded
          (column.1 * tWeight)
  · dsimp [columnBudget, rowPotential]
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd,
      Fin.val_natAdd, Finset.sum_add_distrib]
    simp_rw [Nat.add_mul]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [Nat.cast_id]
    have productCommute :
        m * (d * tWeight) = d * (m * tWeight) := by ac_rfl
    exact le_of_eq (by
      rw [productCommute]
      omega)

/-! ## The fixed branch has one nonzero controlling resultant -/

/-- A nonzero element of the integral quotient has a nonzero resultant of
its canonical representative with the monicized branch equation.  The proof
passes to `K(Z)`, rescales `T` back to the fixed irreducible `Y`-branch, and
uses the strict canonical degree bound.  Thus it counts one fixed global
branch; it does not choose a new factor after each specialization. -/
theorem canonicalRegularRepresentative_resultant_ne_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))]
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (element : IntegralLocalBranch factor) (elementNeZero : element ≠ 0) :
    Polynomial.resultant
        (canonicalRegularRepresentative factor factorNeZero element)
        (integralLocalFactor factor) ≠ 0 := by
  let representative :=
    canonicalRegularRepresentative factor factorNeZero element
  let rationalMap : Polynomial K →+* ChallengeRationalField K :=
    algebraMap (Polynomial K) (ChallengeRationalField K)
  let mappedRepresentative := representative.map rationalMap
  let mappedFactor := localFactorOverRational factor
  have representativeNeZero : representative ≠ 0 := by
    intro representativeZero
    apply elementNeZero
    rw [← mk_canonicalRegularRepresentative factor factorNeZero element]
    simp [representative, representativeZero]
  have rationalMapInjective : Function.Injective rationalMap :=
    IsFractionRing.injective (Polynomial K) (ChallengeRationalField K)
  have mappedRepresentativeNeZero : mappedRepresentative ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff rationalMapInjective).mpr
      representativeNeZero
  have mappedFactorIrreducible : Irreducible mappedFactor := Fact.out
  have mappedFactorNeZero : mappedFactor ≠ 0 :=
    mappedFactorIrreducible.ne_zero
  have mappedLeadingCoefficientNeZero : mappedFactor.leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp mappedFactorNeZero
  let unscaledRepresentative := mappedRepresentative.scaleRoots
    mappedFactor.leadingCoeff⁻¹
  have unscaledRepresentativeNeZero : unscaledRepresentative ≠ 0 :=
    Polynomial.scaleRoots_ne_zero mappedRepresentativeNeZero _
  have representativeDegreeLt :
      representative.natDegree < factor.natDegree :=
    canonicalRegularRepresentative_natDegree_lt factor factorNeZero
      factorPositive element
  have unscaledDegreeLt :
      unscaledRepresentative.natDegree < mappedFactor.natDegree := by
    rw [Polynomial.natDegree_scaleRoots,
      Polynomial.natDegree_map_eq_of_injective rationalMapInjective,
      localFactorOverRational_natDegree]
    exact representativeDegreeLt
  have mappedFactorNotDvd : ¬ mappedFactor ∣ unscaledRepresentative :=
    Polynomial.not_dvd_of_natDegree_lt unscaledRepresentativeNeZero
      unscaledDegreeLt
  have coprime : IsCoprime unscaledRepresentative mappedFactor :=
    ((mappedFactorIrreducible.coprime_iff_not_dvd.mpr
      mappedFactorNotDvd).symm)
  have unscaledResultantNeZero :
      Polynomial.resultant unscaledRepresentative mappedFactor ≠ 0 := by
    intro resultantZero
    exact (Polynomial.resultant_eq_zero_iff.mp resultantZero).2 coprime
  have scaleBack :
      unscaledRepresentative.scaleRoots mappedFactor.leadingCoeff =
        mappedRepresentative := by
    change (mappedRepresentative.scaleRoots mappedFactor.leadingCoeff⁻¹).scaleRoots
        mappedFactor.leadingCoeff = mappedRepresentative
    rw [← Polynomial.scaleRoots_mul]
    simp [mappedLeadingCoefficientNeZero]
  have mappedNormalizedResultantNeZero :
      Polynomial.resultant mappedRepresentative
          mappedFactor.integralNormalization ≠ 0 := by
    rw [← scaleBack]
    rw [Polynomial.resultant_integralNormalization unscaledRepresentative
      mappedFactor (by
        rw [localFactorOverRational_natDegree]
        omega)]
    exact mul_ne_zero
      (pow_ne_zero _ mappedLeadingCoefficientNeZero)
      unscaledResultantNeZero
  intro resultantZero
  have mappedResultantZero := congrArg rationalMap resultantZero
  rw [← Polynomial.resultant_map_map] at mappedResultantZero
  have mappedNormalization :
      (integralLocalFactor factor).map rationalMap =
        mappedFactor.integralNormalization := by
    exact (Polynomial.integralNormalization_map rationalMap factor (by
      intro mappedZero
      apply factorNeZero
      apply Polynomial.leadingCoeff_eq_zero.mp
      apply rationalMapInjective
      simpa using mappedZero)).symm
  have representativeDegreeMap : mappedRepresentative.natDegree =
      representative.natDegree :=
    Polynomial.natDegree_map_eq_of_injective rationalMapInjective _
  have normalizationDegreeMap :
      ((integralLocalFactor factor).map rationalMap).natDegree =
        (integralLocalFactor factor).natDegree :=
    Polynomial.natDegree_map_eq_of_injective rationalMapInjective _
  simp only [map_zero] at mappedResultantZero
  change Polynomial.resultant mappedRepresentative
      ((integralLocalFactor factor).map rationalMap)
      representative.natDegree (integralLocalFactor factor).natDegree = 0 at mappedResultantZero
  rw [← representativeDegreeMap, ← normalizationDegreeMap] at mappedResultantZero
  apply mappedNormalizedResultantNeZero
  rw [← mappedNormalization]
  exact mappedResultantZero

/-- Every root-pair specialization that kills a regular element makes its
single controlling resultant vanish at that challenge.  Both specialized
polynomials are kept at their pre-specialization degree bounds, so collisions
or degree drops at `z` do not enter the argument. -/
theorem eval_canonicalRegularRepresentative_resultant_eq_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (element : IntegralLocalBranch factor) (z t : K)
    (rootPair : (integralLocalFactor factor).eval₂
      (Polynomial.evalRingHom z) t = 0)
    (specializationZero :
      integralBranchSpecialization factor z t rootPair element = 0) :
    (Polynomial.resultant
        (canonicalRegularRepresentative factor factorNeZero element)
        (integralLocalFactor factor)).eval z = 0 := by
  let representative :=
    canonicalRegularRepresentative factor factorNeZero element
  let modulus := integralLocalFactor factor
  let evaluation := Polynomial.evalRingHom z
  have representativeRoot : (representative.map evaluation).IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    rw [← integralBranchSpecialization_eq_eval_canonical factor
      factorNeZero z t rootPair element]
    exact specializationZero
  have modulusRoot : (modulus.map evaluation).IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact rootPair
  have swappedResultantZero : Polynomial.resultant
      (modulus.map evaluation) (representative.map evaluation)
      factor.natDegree representative.natDegree = 0 :=
    resultant_eq_zero_of_common_root_of_natDegree_le _ _ _ _ t
      factorPositive
      (by
        rw [← integralLocalFactor_natDegree factor]
        exact Polynomial.natDegree_map_le)
      Polynomial.natDegree_map_le modulusRoot representativeRoot
  have specializedResultantZero : Polynomial.resultant
      (representative.map evaluation) (modulus.map evaluation)
      representative.natDegree factor.natDegree = 0 := by
    rw [Polynomial.resultant_comm]
    rw [swappedResultantZero, mul_zero]
  change evaluation (Polynomial.resultant representative modulus
      representative.natDegree modulus.natDegree) = 0
  rw [← Polynomial.resultant_map_map]
  rw [integralLocalFactor_natDegree]
  exact specializedResultantZero

/-- The controlling resultant has the exact BCIKS degree ceiling
`d_H * weight(element)`.  This is the non-uniform Sylvester estimate above,
instantiated with the canonical representative and the literal monicization
coefficient bounds. -/
theorem canonicalRegularRepresentative_resultant_natDegree_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (element : IntegralLocalBranch factor) :
    (Polynomial.resultant
        (canonicalRegularRepresentative factor factorNeZero element)
        (integralLocalFactor factor)).natDegree ≤
      factor.natDegree *
        integralBranchIteratedWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) element := by
  let generatorWeight := totalBound + ell - ell * factor.natDegree
  let representative :=
    canonicalRegularRepresentative factor factorNeZero element
  have representativeCoefficients : ∀ coefficient,
      representative.coeff coefficient ≠ 0 →
        (representative.coeff coefficient).natDegree +
            coefficient * generatorWeight ≤
          integralBranchIteratedWeight factor factorNeZero
            generatorWeight element := by
    intro coefficient coefficientNeZero
    exact coeff_weight_le_iteratedBivariateWeight generatorWeight
      representative coefficient
      (Polynomial.mem_support_iff.mpr coefficientNeZero)
  have modulusCoefficients : ∀ coefficient,
      (integralLocalFactor factor).coeff coefficient ≠ 0 →
        ((integralLocalFactor factor).coeff coefficient).natDegree +
            coefficient * generatorWeight ≤
          factor.natDegree * generatorWeight := by
    intro coefficient coefficientNeZero
    exact integralLocalFactor_coefficientWeight_le factor factorNeZero ell
      totalBound coefficientBound coefficient
      (Polynomial.mem_support_iff.mpr coefficientNeZero)
  rw [integralLocalFactor_natDegree]
  exact resultant_natDegree_le_mul_weight representative
    (integralLocalFactor factor) representative.natDegree factor.natDegree
    generatorWeight
    (integralBranchIteratedWeight factor factorNeZero generatorWeight element)
    representativeCoefficients modulusCoefficients

/-- Exact regular-function zero count on challenge-dependent root pairs.  The
root value `t(z)` may be selected independently for every challenge, but all
zeros are charged to the one resultant attached to the already-fixed
irreducible branch and regular element. -/
theorem card_rootPair_specializations_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))]
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (element : IntegralLocalBranch factor) (elementNeZero : element ≠ 0)
    (challenges : Finset K) (rootValue : K → K)
    (rootPair : ∀ z ∈ challenges,
      (integralLocalFactor factor).eval₂ (Polynomial.evalRingHom z)
        (rootValue z) = 0)
    (specializationZero : ∀ z (zMem : z ∈ challenges),
      integralBranchSpecialization factor z (rootValue z)
          (rootPair z zMem) element = 0) :
    challenges.card ≤ factor.natDegree *
      integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) element := by
  classical
  let controllingResultant := Polynomial.resultant
    (canonicalRegularRepresentative factor factorNeZero element)
    (integralLocalFactor factor)
  have controllingResultantNeZero : controllingResultant ≠ 0 :=
    canonicalRegularRepresentative_resultant_ne_zero factor factorNeZero
      factorPositive element elementNeZero
  calc
    challenges.card ≤ controllingResultant.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z zMem
      rw [Polynomial.mem_roots controllingResultantNeZero,
        Polynomial.IsRoot]
      apply eval_canonicalRegularRepresentative_resultant_eq_zero factor
        factorNeZero factorPositive element z (rootValue z)
        (rootPair z (by simpa using zMem))
      exact specializationZero z (by simpa using zMem)
    _ ≤ factor.natDegree *
        integralBranchIteratedWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) element :=
      canonicalRegularRepresentative_resultant_natDegree_le factor
        factorNeZero ell totalBound coefficientBound element

/-- BCIKS Lemma A.1 in the exact quotient formulation used below: more than
`d_H * weight` challenge-dependent root-pair zeros force the regular element
itself to vanish. -/
theorem integralBranch_eq_zero_of_mul_weight_lt_card
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))]
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (element : IntegralLocalBranch factor)
    (challenges : Finset K) (rootValue : K → K)
    (rootPair : ∀ z ∈ challenges,
      (integralLocalFactor factor).eval₂ (Polynomial.evalRingHom z)
        (rootValue z) = 0)
    (specializationZero : ∀ z (zMem : z ∈ challenges),
      integralBranchSpecialization factor z (rootValue z)
          (rootPair z zMem) element = 0)
    (tooManyZeros : factor.natDegree *
        integralBranchIteratedWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) element <
      challenges.card) :
    element = 0 := by
  by_contra elementNeZero
  have bounded := card_rootPair_specializations_le factor factorNeZero
    factorPositive ell totalBound coefficientBound element elementNeZero
    challenges rootValue rootPair specializationZero
  omega

/-- The integral branch embeds faithfully into the selected algebraic
function field.  The proof uses the same one fixed resultant as the zero
count: a nonzero quotient element cannot acquire the selected branch root
as a common root with the monicized local equation after passage to
`K(Z)`. -/
theorem integralBranchToFunctionField_injective
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))]
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree) :
    Function.Injective (integralBranchToFunctionField factor) := by
  intro left right mappedEquality
  apply sub_eq_zero.mp
  let element := left - right
  have mappedZero : integralBranchToFunctionField factor element = 0 := by
    change integralBranchToFunctionField factor (left - right) = 0
    rw [map_sub, mappedEquality, sub_self]
  by_contra elementNeZero
  let representative :=
    canonicalRegularRepresentative factor factorNeZero element
  let modulus := integralLocalFactor factor
  let coefficientMap := regularCoefficientMap factor
  let branchRoot := integralBranchGenerator factor
  have representativeRoot :
      (representative.map coefficientMap).IsRoot branchRoot := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    have mappedZero' := mappedZero
    rw [← mk_canonicalRegularRepresentative factor factorNeZero element]
      at mappedZero'
    unfold integralBranchToFunctionField at mappedZero'
    rw [AdjoinRoot.lift_mk] at mappedZero'
    exact mappedZero'
  have modulusRoot : (modulus.map coefficientMap).IsRoot branchRoot := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact integralBranchGenerator_isRoot factor
  have mappedSwappedResultantZero :
      Polynomial.resultant (modulus.map coefficientMap)
          (representative.map coefficientMap)
          modulus.natDegree representative.natDegree = 0 := by
    apply resultant_eq_zero_of_common_root_of_natDegree_le
      (modulus.map coefficientMap) (representative.map coefficientMap)
      modulus.natDegree representative.natDegree branchRoot
    · rw [show modulus.natDegree = factor.natDegree by
          exact integralLocalFactor_natDegree factor]
      exact factorPositive
    · exact Polynomial.natDegree_map_le
    · exact Polynomial.natDegree_map_le
    · exact modulusRoot
    · exact representativeRoot
  have mappedResultantZero :
      Polynomial.resultant (representative.map coefficientMap)
          (modulus.map coefficientMap)
          representative.natDegree modulus.natDegree = 0 := by
    rw [Polynomial.resultant_comm]
    rw [mappedSwappedResultantZero, mul_zero]
  have originalResultantZero :
      Polynomial.resultant representative modulus
          representative.natDegree modulus.natDegree = 0 := by
    apply (regularCoefficientMap_injective factor)
    rw [map_zero, ← Polynomial.resultant_map_map]
    exact mappedResultantZero
  exact (canonicalRegularRepresentative_resultant_ne_zero factor factorNeZero
    factorPositive element elementNeZero) originalResultantZero

#print axioms matrix_det_natDegree_le_of_potentials
#print axioms resultant_natDegree_le_mul_weight
#print axioms canonicalRegularRepresentative_resultant_ne_zero
#print axioms eval_canonicalRegularRepresentative_resultant_eq_zero
#print axioms canonicalRegularRepresentative_resultant_natDegree_le
#print axioms card_rootPair_specializations_le
#print axioms integralBranch_eq_zero_of_mul_weight_lt_card
#print axioms integralBranchToFunctionField_injective

end

end AspisK1.V7ExactCorrelatedAgreementRegularZeroCount
