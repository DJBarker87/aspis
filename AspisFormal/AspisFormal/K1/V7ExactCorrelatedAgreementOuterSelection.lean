import AspisFormal.K1.V7ExactCorrelatedAgreementConcreteBranch
import AspisFormal.K1.V7ExactCorrelatedAgreementWeightedPigeonhole

/-!
# Exact outer irreducible-branch selection for V7 correlated agreement

This file performs the quantifier-sensitive outer count.  Every challenge may
select a different candidate.  The candidate is first assigned to one fixed
global prime factor and then, away from explicit finite-characteristic
specialization exceptions, to one fixed local prime factor.  A weighted
pigeonhole argument selects one literal pair `(R,H)` with enough incidences
for the fixed-branch theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisK1.V7ExactCorrelatedAgreementOuterSelection

open Polynomial
open AspisK1.V7ExactCorrelatedAgreement
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementWeightedPigeonhole
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Reordering with `Z` outermost and then evaluating at the constant `z`
is exactly the released challenge specialization. -/
theorem trivariateZOuter_eval_eq_specializeChallenge
    {K : Type*} [Field K] (polynomial : TrivariatePolynomial K) (z : K) :
    (trivariateZOuterEquiv K polynomial).eval (C (C z)) =
      specializeChallenge z polynomial := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp [map_add, leftInduction, rightInduction]
  | monomial yExponent coefficient =>
      induction coefficient using Polynomial.induction_on' with
      | add left right leftInduction rightInduction =>
          simp [map_add, leftInduction, rightInduction]
      | monomial zExponent xCoefficient =>
          induction xCoefficient using Polynomial.induction_on' with
          | add left right leftInduction rightInduction =>
              simp [map_add, leftInduction, rightInduction]
          | monomial xExponent value =>
              rw [trivariateZOuterEquiv_monomial]
              simp [specializeChallenge, eval_monomial]
              rw [← Polynomial.C_pow, Polynomial.monomial_mul_C]

/-- Challenges at which the entire symbolic interpolant specializes to zero.
These are the content exceptions noted explicitly in BCH+25 footnote 5. -/
noncomputable def zeroSpecializationChallengeSet
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (polynomial : TrivariatePolynomial K) : Finset K :=
  Finset.univ.filter fun z => specializeChallenge z polynomial = 0

@[simp] theorem mem_zeroSpecializationChallengeSet_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (polynomial : TrivariatePolynomial K) (z : K) :
    z ∈ zeroSpecializationChallengeSet polynomial ↔
      specializeChallenge z polynomial = 0 := by
  simp [zeroSpecializationChallengeSet]

/-- The content exceptions are bounded by the literal outer `Z` degree.
The proof injects constants into the root multiset over the domain
`K[X,Y]`; it does not appeal to compiled evaluation. -/
theorem zeroSpecializationChallengeSet_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (polynomial : TrivariatePolynomial K) (polynomialNeZero : polynomial ≠ 0) :
    (zeroSpecializationChallengeSet polynomial).card ≤
      (trivariateZOuterEquiv K polynomial).natDegree := by
  classical
  let reordered := trivariateZOuterEquiv K polynomial
  have reorderedNeZero : reordered ≠ 0 := by
    intro reorderedZero
    apply polynomialNeZero
    apply (trivariateZOuterEquiv K).injective
    simpa [reordered] using reorderedZero
  let constants : Finset (BivariatePolynomial K) :=
    (zeroSpecializationChallengeSet polynomial).image fun z => C (C z)
  have constantsCard : constants.card =
      (zeroSpecializationChallengeSet polynomial).card := by
    apply Finset.card_image_of_injective
    intro left right equality
    exact Polynomial.C_injective (Polynomial.C_injective equality)
  have constantsRoots : constants.val ⊆ reordered.roots := by
    intro constant constantMem
    rw [Polynomial.mem_roots reorderedNeZero]
    have constantMem' : constant ∈ constants := constantMem
    rw [Finset.mem_image] at constantMem'
    obtain ⟨z, zMem, rfl⟩ := constantMem'
    rw [Polynomial.IsRoot,
      trivariateZOuter_eval_eq_specializeChallenge]
    exact (mem_zeroSpecializationChallengeSet_iff polynomial z).mp zMem
  rw [← constantsCard]
  simpa [reordered] using
    Polynomial.card_le_degree_of_subset_roots constantsRoots

/-- A nonzero separability certificate at `X=x` also certifies that the
specialized parent itself is nonzero. -/
theorem specializeEvaluationPoint_ne_zero_of_certificate
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x : K)
    (factorPositive : 0 < factor.natDegree)
    (certificateAtPoint :
      (Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x) ≠ 0) :
    specializeEvaluationPoint x factor ≠ 0 := by
  intro parentZero
  apply certificateAtPoint
  rw [← specialized_resultant_eq_certificate_eval_x]
  have derivativeZero : specializeEvaluationPoint x factor.derivative = 0 := by
    change factor.derivative.map (evaluateInnerVariable x) = 0
    have differentiated := congrArg Polynomial.derivative parentZero
    simpa [specializeEvaluationPoint, Polynomial.derivative_map] using
      differentiated
  rw [parentZero, derivativeZero]
  simp [Nat.ne_of_gt factorPositive]

/-- Removing duplicates from a multiset cannot increase a natural-valued
sum.  Prime factorizations retain multiplicity, so this lemma lets the finite
branch selector use `toFinset` while charging against the stronger multiset
degree identities. -/
theorem sum_toFinset_le_multiset_sum
    {α : Type*} [DecidableEq α] (values : Multiset α) (weight : α → Nat) :
    ∑ value ∈ values.toFinset, weight value ≤ (values.map weight).sum := by
  induction values using Multiset.induction_on with
  | empty => simp
  | @cons value values induction =>
      by_cases valueMem : value ∈ values
      · simp [valueMem]
        exact induction.trans (Nat.le_add_left _ _)
      · simp [valueMem, induction]

/-- Pure nested-branch cardinal accounting.  The total number of global/local
pairs is bounded by the sum of the global `Y` degrees, not its square. -/
theorem sigma_card_le_of_local_card_le
    {Global Local : Type*} [DecidableEq Global]
    (globals : Finset Global) (locals : Global → Finset Local)
    (globalDegree : Global → Nat) (yRows : Nat)
    (localCard : ∀ global ∈ globals,
      (locals global).card ≤ globalDegree global)
    (globalDegreeSum : ∑ global ∈ globals, globalDegree global ≤ yRows) :
    (globals.sigma locals).card ≤ yRows := by
  rw [Finset.card_sigma]
  exact (Finset.sum_le_sum localCard).trans globalDegreeSum

/-- Weighted nested-branch accounting in the exact shape needed after the
support-incidence conversion. -/
theorem sigma_scaledBudget_sum_le
    {Global Local : Type*} [DecidableEq Global]
    (globals : Finset Global) (locals : Global → Finset Local)
    (globalDegree parentWeight : Global → Nat)
    (localDegree : Local → Nat)
    (branchBudget : Global → Local → Nat)
    (maximumDegree yRows zWeight : Nat)
    (localDegreeSum : ∀ global ∈ globals,
      ∑ branchLocal ∈ locals global, localDegree branchLocal ≤
        globalDegree global)
    (globalDegreeLe : ∀ global ∈ globals,
      globalDegree global ≤ yRows)
    (globalDegreeSum : ∑ global ∈ globals, globalDegree global ≤ yRows)
    (parentWeightSum : ∑ global ∈ globals, parentWeight global ≤ zWeight)
    (branchBound : ∀ global ∈ globals,
      ∀ branchLocal ∈ locals global,
      29 * branchBudget global branchLocal ≤
        58 * (maximumDegree + 1) * globalDegree global *
          localDegree branchLocal * parentWeight global) :
    ∑ branch ∈ globals.sigma locals,
        29 * branchBudget branch.1 branch.2 ≤
      58 * (maximumDegree + 1) * yRows ^ 2 * zWeight := by
  rw [← Finset.sum_sigma' globals locals
    (fun global branchLocal => 29 * branchBudget global branchLocal)]
  calc
    ∑ global ∈ globals, ∑ branchLocal ∈ locals global,
        29 * branchBudget global branchLocal ≤
      ∑ global ∈ globals, ∑ branchLocal ∈ locals global,
        58 * (maximumDegree + 1) * globalDegree global *
          localDegree branchLocal * parentWeight global := by
            exact Finset.sum_le_sum fun global globalMem =>
              Finset.sum_le_sum fun branchLocal branchLocalMem =>
                branchBound global globalMem branchLocal branchLocalMem
    _ = ∑ global ∈ globals,
        (58 * (maximumDegree + 1) * globalDegree global *
          parentWeight global) *
            (∑ branchLocal ∈ locals global,
              localDegree branchLocal) := by
      apply Finset.sum_congr rfl
      intro global _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro branchLocal _
      ring
    _ ≤ ∑ global ∈ globals,
        (58 * (maximumDegree + 1) * globalDegree global *
          parentWeight global) * globalDegree global := by
      exact Finset.sum_le_sum fun global globalMem =>
        Nat.mul_le_mul_left _ (localDegreeSum global globalMem)
    _ ≤ ∑ global ∈ globals,
        (58 * (maximumDegree + 1) * yRows ^ 2) *
          parentWeight global := by
      apply Finset.sum_le_sum
      intro global globalMem
      have degreeLe := globalDegreeLe global globalMem
      calc
        (58 * (maximumDegree + 1) * globalDegree global *
            parentWeight global) * globalDegree global =
          (58 * (maximumDegree + 1) * parentWeight global) *
            (globalDegree global * globalDegree global) := by ring
        _ ≤ (58 * (maximumDegree + 1) * parentWeight global) *
            (yRows * yRows) := Nat.mul_le_mul_left _
              (Nat.mul_le_mul degreeLe degreeLe)
        _ = (58 * (maximumDegree + 1) * yRows ^ 2) *
            parentWeight global := by ring
    _ = (58 * (maximumDegree + 1) * yRows ^ 2) *
        (∑ global ∈ globals, parentWeight global) := by
      rw [Finset.mul_sum]
    _ ≤ (58 * (maximumDegree + 1) * yRows ^ 2) * zWeight :=
      Nat.mul_le_mul_left _ parentWeightSum
    _ = 58 * (maximumDegree + 1) * yRows ^ 2 * zWeight := by ring

/-! ## One fixed global/local branch from challenge-dependent roots -/

set_option maxRecDepth 262144 in
set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
/-- Exact weighted outer selection.  The output is one literal member of the
global prime factorization and one literal member of its smooth local prime
factorization.  Every selected challenge has the ordinary global root, the
certified simple specialization, the local root, and the explicit pole-free
condition required by the finite-characteristic Hensel theorem. -/
theorem exists_weighted_fixed_branch
    (polynomial : TrivariatePolynomial QM31Exact)
    (polynomialNeZero : polynomial ≠ 0)
    (candidate : QM31Exact → QM31Exact[X])
    (challenges : Finset QM31Exact)
    (maximumDegree curveDegree yRows zWeight concurrencyReserve : Nat)
    (yRowsLe : yRows ≤ 113)
    (zWeightPositive : 0 < zWeight)
    (polynomialYDegree : polynomial.natDegree < yRows)
    (polynomialXDegree :
      (trivariateXOuterEquiv QM31Exact polynomial).natDegree < 114688)
    (polynomialZDegree :
      (trivariateZOuterEquiv QM31Exact polynomial).natDegree < zWeight)
    (polynomialYZWeight :
      trivariateYZWeight curveDegree polynomial < zWeight)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidateHom z (candidate z) polynomial = 0)
    (many :
      zWeight + 224 * yRows * zWeight +
          58 * (maximumDegree + 1) * yRows ^ 2 * zWeight +
            concurrencyReserve * yRows < challenges.card) :
    ∃ (globalFactor : TrivariatePolynomial QM31Exact)
        (x₀ : QM31Exact)
        (localFactor : BivariatePolynomial QM31Exact)
        (selected : Finset QM31Exact),
      globalFactor ∈ curvePrimeFactors polynomial ∧
      0 < globalFactor.natDegree ∧
      (Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0 ∧
      localFactor ∈ bivariatePrimeFactors
        (specializeEvaluationPoint x₀ globalFactor) ∧
      0 < localFactor.natDegree ∧
      29 * fixedBranchEvaluationBudget maximumDegree curveDegree
          globalFactor.natDegree localFactor.natDegree
            (localBivariateWeight curveDegree localFactor)
              (trivariateYZWeight curveDegree globalFactor) +
          concurrencyReserve < selected.card ∧
      selected ⊆ challenges ∧
      ∀ z ∈ selected,
        challengeCandidateHom z (candidate z) globalFactor = 0 ∧
        SimpleSpecializedRoot globalFactor x₀ z (candidate z) ∧
        localChallengeCandidateHom z ((candidate z).eval x₀)
          localFactor = 0 ∧
        z ∉ localPoleChallengeSet localFactor := by
  classical
  let globals : Finset (TrivariatePolynomial QM31Exact) :=
    (positiveYPrimeFactors polynomial).toFinset
  have globalSpec : ∀ globalFactor ∈ globals,
      globalFactor ∈ curvePrimeFactors polynomial ∧
        0 < globalFactor.natDegree := by
    intro globalFactor globalMem
    exact (mem_positiveYPrimeFactors polynomial globalFactor).mp <| by
      simpa only [globals, Multiset.mem_toFinset] using globalMem
  have polynomialYDegreeSmall : polynomial.natDegree < 113 :=
    polynomialYDegree.trans_le yRowsLe
  have smoothExists : ∀ globalFactor ∈ globals,
      ∃ x₀ : QM31Exact,
        (Polynomial.Bivariate.swap
          (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0 := by
    intro globalFactor globalMem
    exact exists_exactV7_uniformSmoothEvaluationPoint polynomial globalFactor
      polynomialNeZero (globalSpec globalFactor globalMem).1
      (globalSpec globalFactor globalMem).2 polynomialYDegreeSmall
      polynomialXDegree
  let smoothPoint : TrivariatePolynomial QM31Exact → QM31Exact :=
    fun globalFactor => if globalMem : globalFactor ∈ globals then
      Classical.choose (smoothExists globalFactor globalMem) else 0
  have smoothPointSpec : ∀ globalFactor ∈ globals,
      (Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval
          (C (smoothPoint globalFactor)) ≠ 0 := by
    intro globalFactor globalMem
    simp only [smoothPoint, dif_pos globalMem]
    exact Classical.choose_spec (smoothExists globalFactor globalMem)
  let locals : TrivariatePolynomial QM31Exact →
      Finset (BivariatePolynomial QM31Exact) := fun globalFactor =>
    (positiveYBivariatePrimeFactors
      (specializeEvaluationPoint (smoothPoint globalFactor)
        globalFactor)).toFinset
  have parentNeZero : ∀ globalFactor ∈ globals,
      specializeEvaluationPoint (smoothPoint globalFactor) globalFactor ≠ 0 := by
    intro globalFactor globalMem
    exact specializeEvaluationPoint_ne_zero_of_certificate globalFactor
      (smoothPoint globalFactor) (globalSpec globalFactor globalMem).2
      (smoothPointSpec globalFactor globalMem)
  have localSpec : ∀ globalFactor ∈ globals,
      ∀ localFactor ∈ locals globalFactor,
        localFactor ∈ bivariatePrimeFactors
            (specializeEvaluationPoint (smoothPoint globalFactor)
              globalFactor) ∧
          0 < localFactor.natDegree := by
    intro globalFactor globalMem localFactor localMem
    exact (mem_positiveYBivariatePrimeFactors
      (specializeEvaluationPoint (smoothPoint globalFactor) globalFactor)
        localFactor).mp <| by
          simpa only [locals, Multiset.mem_toFinset] using localMem
  let branches := globals.sigma locals
  have globalDegreeSum :
      ∑ globalFactor ∈ globals, globalFactor.natDegree ≤
        polynomial.natDegree := by
    exact (sum_toFinset_le_multiset_sum
      (positiveYPrimeFactors polynomial) Polynomial.natDegree).trans
        (sum_positiveYPrimeFactors_natDegree_le polynomial polynomialNeZero)
  have globalDegreeSumRows :
      ∑ globalFactor ∈ globals, globalFactor.natDegree ≤ yRows :=
    globalDegreeSum.trans (Nat.le_of_lt polynomialYDegree)
  have globalDegreeLe : ∀ globalFactor ∈ globals,
      globalFactor.natDegree ≤ yRows := by
    intro globalFactor globalMem
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      globalMem).trans globalDegreeSumRows
  have parentWeightSum :
      ∑ globalFactor ∈ globals,
          trivariateYZWeight curveDegree globalFactor ≤
        trivariateYZWeight curveDegree polynomial := by
    exact (sum_toFinset_le_multiset_sum
      (positiveYPrimeFactors polynomial)
        (trivariateYZWeight curveDegree)).trans
      (sum_positiveGlobalFactorYZWeights_le curveDegree polynomial
        polynomialNeZero)
  have parentWeightSumBound :
      ∑ globalFactor ∈ globals,
          trivariateYZWeight curveDegree globalFactor ≤ zWeight :=
    parentWeightSum.trans (Nat.le_of_lt polynomialYZWeight)
  have parentWeightLe : ∀ globalFactor ∈ globals,
      trivariateYZWeight curveDegree globalFactor ≤ zWeight := by
    intro globalFactor globalMem
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      globalMem).trans parentWeightSumBound
  have localDegreeSum : ∀ globalFactor ∈ globals,
      ∑ localFactor ∈ locals globalFactor, localFactor.natDegree ≤
        globalFactor.natDegree := by
    intro globalFactor globalMem
    let parent := specializeEvaluationPoint (smoothPoint globalFactor)
      globalFactor
    calc
      ∑ localFactor ∈ locals globalFactor, localFactor.natDegree ≤
          ((positiveYBivariatePrimeFactors parent).map
            Polynomial.natDegree).sum :=
        sum_toFinset_le_multiset_sum
          (positiveYBivariatePrimeFactors parent) Polynomial.natDegree
      _ ≤ parent.natDegree :=
        sum_positiveYBivariatePrimeFactors_natDegree_le parent
          (parentNeZero globalFactor globalMem)
      _ ≤ globalFactor.natDegree := Polynomial.natDegree_map_le
  have localCard : ∀ globalFactor ∈ globals,
      (locals globalFactor).card ≤ globalFactor.natDegree := by
    intro globalFactor globalMem
    calc
      (locals globalFactor).card =
          ∑ _localFactor ∈ locals globalFactor, 1 := by simp
      _ ≤ ∑ localFactor ∈ locals globalFactor,
            localFactor.natDegree := by
        apply Finset.sum_le_sum
        intro localFactor localMem
        have localPositive :=
          (localSpec globalFactor globalMem localFactor localMem).2
        omega
      _ ≤ globalFactor.natDegree :=
        localDegreeSum globalFactor globalMem
  have globalsCard : globals.card ≤ yRows := by
    calc
      globals.card ≤ (positiveYPrimeFactors polynomial).card :=
        Multiset.toFinset_card_le _
      _ ≤ polynomial.natDegree :=
        positiveYPrimeFactors_card_le_natDegree polynomial polynomialNeZero
      _ ≤ yRows := Nat.le_of_lt polynomialYDegree
  have branchesCard : branches.card ≤ yRows := by
    exact sigma_card_le_of_local_card_le globals locals
      Polynomial.natDegree yRows localCard globalDegreeSumRows
  have localWeightLeParent : ∀ globalFactor ∈ globals,
      ∀ localFactor ∈ locals globalFactor,
        localBivariateWeight curveDegree localFactor ≤
          trivariateYZWeight curveDegree globalFactor := by
    intro globalFactor globalMem localFactor localMem
    let parent := specializeEvaluationPoint (smoothPoint globalFactor)
      globalFactor
    have localWeightMem : localBivariateWeight curveDegree localFactor ∈
        (positiveYBivariatePrimeFactors parent).map
          (localBivariateWeight curveDegree) :=
      Multiset.mem_map_of_mem _ <| by
        exact (mem_positiveYBivariatePrimeFactors parent localFactor).mpr
          (localSpec globalFactor globalMem localFactor localMem)
    calc
      localBivariateWeight curveDegree localFactor ≤
          ((positiveYBivariatePrimeFactors parent).map
            (localBivariateWeight curveDegree)).sum :=
        Multiset.le_sum_of_mem localWeightMem
      _ ≤ localBivariateWeight curveDegree parent :=
        sum_positiveLocalFactorWeights_le curveDegree parent
          (parentNeZero globalFactor globalMem)
      _ ≤ trivariateYZWeight curveDegree globalFactor :=
        localBivariateWeight_specializeEvaluationPoint_le curveDegree
          globalFactor (smoothPoint globalFactor)
  have curveLeLocalWeight : ∀ globalFactor ∈ globals,
      ∀ localFactor ∈ locals globalFactor,
        curveDegree ≤ localBivariateWeight curveDegree localFactor := by
    intro globalFactor globalMem localFactor localMem
    have localPositive := (localSpec globalFactor globalMem localFactor
      localMem).2
    have leadingMem : localFactor.natDegree ∈ localFactor.support :=
      Polynomial.natDegree_mem_support_of_nonzero <| by
        exact (bivariatePrimeFactors_prime _
          (parentNeZero globalFactor globalMem) localFactor
            (localSpec globalFactor globalMem localFactor localMem).1).ne_zero
    have weighted := coeff_weight_le_localBivariateWeight curveDegree
      localFactor localFactor.natDegree leadingMem
    calc
      curveDegree = curveDegree * 1 := by simp
      _ ≤ curveDegree * localFactor.natDegree :=
        Nat.mul_le_mul_left curveDegree
          (Nat.succ_le_iff.mpr localPositive)
      _ ≤ (localFactor.coeff localFactor.natDegree).natDegree +
          localFactor.natDegree * curveDegree := by
        rw [Nat.mul_comm curveDegree localFactor.natDegree]
        exact Nat.le_add_left _ _
      _ ≤ localBivariateWeight curveDegree localFactor := by
        simpa [Nat.mul_comm] using weighted
  let branchBudget : (Σ _ : TrivariatePolynomial QM31Exact,
      BivariatePolynomial QM31Exact) → Nat := fun branch =>
    fixedBranchEvaluationBudget maximumDegree curveDegree
      branch.1.natDegree branch.2.natDegree
        (localBivariateWeight curveDegree branch.2)
          (trivariateYZWeight curveDegree branch.1)
  have branchBudgetSum :
      ∑ branch ∈ branches, 29 * branchBudget branch ≤
        58 * (maximumDegree + 1) * yRows ^ 2 * zWeight := by
    apply sigma_scaledBudget_sum_le globals locals Polynomial.natDegree
      (trivariateYZWeight curveDegree) Polynomial.natDegree
      (fun globalFactor localFactor => fixedBranchEvaluationBudget
        maximumDegree curveDegree globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight curveDegree localFactor)
            (trivariateYZWeight curveDegree globalFactor))
      maximumDegree yRows zWeight localDegreeSum globalDegreeLe
      globalDegreeSumRows parentWeightSumBound
    intro globalFactor globalMem localFactor localMem
    have unscaled := fixedBranchEvaluationBudget_le_two maximumDegree
      curveDegree globalFactor.natDegree localFactor.natDegree
      (localBivariateWeight curveDegree localFactor)
      (trivariateYZWeight curveDegree globalFactor)
      (globalSpec globalFactor globalMem).2
      (localSpec globalFactor globalMem localFactor localMem).2
      (curveLeLocalWeight globalFactor globalMem localFactor localMem)
      (localWeightLeParent globalFactor globalMem localFactor localMem)
    exact (Nat.mul_le_mul_left 29 unscaled).trans_eq (by ring)
  let nonsimpleExceptions : Finset QM31Exact :=
    globals.biUnion fun globalFactor =>
      nonsimpleChallengeSet globalFactor (smoothPoint globalFactor)
  have nonsimpleExceptionsCard : nonsimpleExceptions.card ≤
      223 * yRows * zWeight := by
    calc
      nonsimpleExceptions.card ≤ ∑ globalFactor ∈ globals,
          (nonsimpleChallengeSet globalFactor
            (smoothPoint globalFactor)).card := Finset.card_biUnion_le
      _ ≤ ∑ _globalFactor ∈ globals, 223 * (zWeight - 1) := by
        apply Finset.sum_le_sum
        intro globalFactor globalMem
        exact exactV7_nonsimpleChallengeSet_card_le polynomial globalFactor
          (smoothPoint globalFactor) zWeight zWeightPositive polynomialNeZero
          (globalSpec globalFactor globalMem).1 polynomialYDegreeSmall
          polynomialZDegree
      _ = globals.card * (223 * (zWeight - 1)) := by simp
      _ ≤ yRows * (223 * zWeight) := by
        exact Nat.mul_le_mul globalsCard
          (Nat.mul_le_mul_left 223 (Nat.sub_le _ _))
      _ = 223 * yRows * zWeight := by ring
  let poleExceptions : Finset QM31Exact :=
    branches.biUnion fun branch => localPoleChallengeSet branch.2
  have poleExceptionsCard : poleExceptions.card ≤ yRows * zWeight := by
    calc
      poleExceptions.card ≤ ∑ branch ∈ branches,
          (localPoleChallengeSet branch.2).card := Finset.card_biUnion_le
      _ ≤ ∑ _branch ∈ branches, zWeight := by
        apply Finset.sum_le_sum
        intro branch branchMem
        rw [Finset.mem_sigma] at branchMem
        have branchNeZero : branch.2 ≠ 0 :=
          (bivariatePrimeFactors_prime _
            (parentNeZero branch.1 branchMem.1) branch.2
              (localSpec branch.1 branchMem.1 branch.2 branchMem.2).1).ne_zero
        have weighted := coeff_weight_le_localBivariateWeight curveDegree
          branch.2 branch.2.natDegree
            (Polynomial.natDegree_mem_support_of_nonzero branchNeZero)
        calc
          (localPoleChallengeSet branch.2).card ≤
              branch.2.leadingCoeff.natDegree :=
            localPoleChallengeSet_card_le branch.2
          _ ≤ (branch.2.coeff branch.2.natDegree).natDegree +
              branch.2.natDegree * curveDegree := by
            rw [Polynomial.leadingCoeff]
            exact Nat.le_add_right _ _
          _ ≤ localBivariateWeight curveDegree branch.2 := weighted
          _ ≤ trivariateYZWeight curveDegree branch.1 :=
            localWeightLeParent branch.1 branchMem.1 branch.2 branchMem.2
          _ ≤ zWeight := parentWeightLe branch.1 branchMem.1
      _ = branches.card * zWeight := by simp
      _ ≤ yRows * zWeight := Nat.mul_le_mul_right _ branchesCard
  let exceptions := zeroSpecializationChallengeSet polynomial ∪
    nonsimpleExceptions ∪ poleExceptions
  have zeroExceptionsCard :
      (zeroSpecializationChallengeSet polynomial).card ≤ zWeight :=
    (zeroSpecializationChallengeSet_card_le polynomial polynomialNeZero).trans
      (Nat.le_of_lt polynomialZDegree)
  have exceptionsCard : exceptions.card ≤
      zWeight + 224 * yRows * zWeight := by
    calc
      exceptions.card ≤
          (zeroSpecializationChallengeSet polynomial).card +
            nonsimpleExceptions.card + poleExceptions.card := by
        exact (Finset.card_union_le _ _).trans <|
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ zWeight + 223 * yRows * zWeight + yRows * zWeight := by omega
      _ = zWeight + 224 * yRows * zWeight := by ring
  have pairExists : ∀ z ∈ challenges \ exceptions,
      ∃ branch ∈ branches,
        challengeCandidateHom z (candidate z) branch.1 = 0 ∧
        SimpleSpecializedRoot branch.1 (smoothPoint branch.1) z
          (candidate z) ∧
        localChallengeCandidateHom z
          ((candidate z).eval (smoothPoint branch.1)) branch.2 = 0 ∧
        z ∉ localPoleChallengeSet branch.2 := by
    intro z zMem
    have zChallenge : z ∈ challenges := (Finset.mem_sdiff.mp zMem).1
    have zNotExceptions : z ∉ exceptions := (Finset.mem_sdiff.mp zMem).2
    have zNotZero : z ∉ zeroSpecializationChallengeSet polynomial := by
      intro zZero
      exact zNotExceptions <| by
        simp [exceptions, zZero]
    obtain ⟨globalFactor, globalMem, globalPositive, globalRoot⟩ :=
      exists_positiveDegree_primeFactor_root polynomial polynomialNeZero z
        (candidate z) (by
          intro specializedZero
          apply zNotZero
          simp [zeroSpecializationChallengeSet, specializedZero])
        (candidateRoot z zChallenge)
    have globalIn : globalFactor ∈ globals := by
      simpa only [globals, Multiset.mem_toFinset,
        mem_positiveYPrimeFactors] using And.intro globalMem globalPositive
    have zNotNonsimple : z ∉ nonsimpleChallengeSet globalFactor
        (smoothPoint globalFactor) := by
      intro zBad
      apply zNotExceptions
      simp only [exceptions, Finset.mem_union]
      exact Or.inl <| Or.inr <| by
        exact (Finset.mem_biUnion.mpr ⟨globalFactor, globalIn, zBad⟩)
    have simpleRoot := simpleSpecializedRoot_of_not_mem_nonsimpleChallengeSet
      globalFactor (smoothPoint globalFactor) z (candidate z) globalPositive
      (smoothPointSpec globalFactor globalIn) zNotNonsimple globalRoot
    obtain ⟨localFactor, localMem, localPositive, localRoot⟩ :=
      exists_localPrimeFactor_for_simpleSpecializedRoot globalFactor
        (smoothPoint globalFactor) z (candidate z)
        (parentNeZero globalFactor globalIn) simpleRoot
    have localIn : localFactor ∈ locals globalFactor := by
      simpa only [locals, Multiset.mem_toFinset,
        mem_positiveYBivariatePrimeFactors] using
          And.intro localMem localPositive
    have branchIn : (⟨globalFactor, localFactor⟩ :
        Σ _ : TrivariatePolynomial QM31Exact,
          BivariatePolynomial QM31Exact) ∈ branches := by
      exact Finset.mem_sigma.mpr ⟨globalIn, localIn⟩
    have notPole : z ∉ localPoleChallengeSet localFactor := by
      intro zPole
      apply zNotExceptions
      simp only [exceptions, Finset.mem_union]
      exact Or.inr <| by
        exact Finset.mem_biUnion.mpr ⟨_, branchIn, zPole⟩
    exact ⟨⟨globalFactor, localFactor⟩, branchIn, globalRoot,
      simpleRoot, localRoot, notPole⟩
  let selectedBranch : QM31Exact →
      (Σ _ : TrivariatePolynomial QM31Exact,
        BivariatePolynomial QM31Exact) := fun z =>
    if zMem : z ∈ challenges \ exceptions then
      Classical.choose (pairExists z zMem) else ⟨0, 0⟩
  have selectedBranchSpec : ∀ z ∈ challenges \ exceptions,
      selectedBranch z ∈ branches ∧
        challengeCandidateHom z (candidate z) (selectedBranch z).1 = 0 ∧
        SimpleSpecializedRoot (selectedBranch z).1
          (smoothPoint (selectedBranch z).1) z (candidate z) ∧
        localChallengeCandidateHom z
          ((candidate z).eval (smoothPoint (selectedBranch z).1))
            (selectedBranch z).2 = 0 ∧
        z ∉ localPoleChallengeSet (selectedBranch z).2 := by
    intro z zMem
    simp only [selectedBranch, dif_pos zMem]
    exact Classical.choose_spec (pairExists z zMem)
  have budgetTotal : exceptions.card +
      ∑ branch ∈ branches, (29 * branchBudget branch + concurrencyReserve) <
        challenges.card := by
    have branchConcurrency :
        ∑ _branch ∈ branches, concurrencyReserve =
          branches.card * concurrencyReserve := by simp
    rw [Finset.sum_add_distrib, branchConcurrency]
    have concurrencyBound : branches.card * concurrencyReserve ≤
        concurrencyReserve * yRows := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right concurrencyReserve
        branchesCard
    have totalLe := Nat.add_le_add exceptionsCard
      (Nat.add_le_add branchBudgetSum concurrencyBound)
    omega
  obtain ⟨branch, branchMem, branchFrequent⟩ :=
    exists_fixed_branch_exceeding_budget_of_exception_add_sum_lt challenges
      exceptions branches selectedBranch
      (fun branch => 29 * branchBudget branch + concurrencyReserve)
      (fun z zMem => (selectedBranchSpec z zMem).1) budgetTotal
  let selected := (challenges \ exceptions).filter fun z =>
    selectedBranch z = branch
  have selectedSubset : selected ⊆ challenges := by
    intro z zMem
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp zMem).1).1
  have selectedSpec : ∀ z ∈ selected,
      challengeCandidateHom z (candidate z) branch.1 = 0 ∧
      SimpleSpecializedRoot branch.1 (smoothPoint branch.1) z
        (candidate z) ∧
      localChallengeCandidateHom z
        ((candidate z).eval (smoothPoint branch.1)) branch.2 = 0 ∧
      z ∉ localPoleChallengeSet branch.2 := by
    intro z zMem
    have filtered := Finset.mem_filter.mp zMem
    have spec := (selectedBranchSpec z filtered.1).2
    simpa only [filtered.2] using spec
  have branchParts := Finset.mem_sigma.mp branchMem
  refine ⟨branch.1, smoothPoint branch.1, branch.2, selected,
    (globalSpec branch.1 branchParts.1).1,
    (globalSpec branch.1 branchParts.1).2,
    smoothPointSpec branch.1 branchParts.1,
    (localSpec branch.1 branchParts.1 branch.2 branchParts.2).1,
    (localSpec branch.1 branchParts.1 branch.2 branchParts.2).2,
    ?_, selectedSubset, selectedSpec⟩
  simpa only [selected, branchBudget] using branchFrequent

#print axioms zeroSpecializationChallengeSet_card_le
#print axioms sum_toFinset_le_multiset_sum
#print axioms sigma_card_le_of_local_card_le
#print axioms sigma_scaledBudget_sum_le
#print axioms exists_weighted_fixed_branch

end

end AspisK1.V7ExactCorrelatedAgreementOuterSelection
