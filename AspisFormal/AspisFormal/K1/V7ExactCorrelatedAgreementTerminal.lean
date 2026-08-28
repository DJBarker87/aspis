import AspisFormal.K1.V7ExactCorrelatedAgreementOuterSelection

/-!
# Terminal exact V7 correlated-agreement instances

This file instantiates the weighted irreducible-branch selector, the explicit
finite-characteristic Hensel lift, and the released-message fixed-branch
wrappers for the two deployed V7 codes.
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisK1.V7ExactCorrelatedAgreementTerminal

open Polynomial
open AspisK1.V7ExactCorrelatedAgreement
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementConcreteBranch
open AspisK1.V7ExactCorrelatedAgreementOuterSelection
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
open AspisV6PublishedTheoremInterfaces
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Opaque generic elimination of good-challenge membership.  Keeping the
encoder abstract prevents elaboration from unfolding either concrete V7
encoder merely to project the validity conjunct. -/
theorem validResponse_of_mem_goodChallenges
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) (z : K)
    (member : z ∈ goodChallenges encoder agreementThreshold lanes strategy) :
    ValidResponse encoder agreementThreshold lanes strategy z :=
  (mem_goodChallenges_iff encoder agreementThreshold lanes strategy z).mp
    member

theorem all_goodChallenges_valid
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) :
    ∀ z ∈ goodChallenges encoder agreementThreshold lanes strategy,
      ValidResponse encoder agreementThreshold lanes strategy z := by
  intro z member
  exact validResponse_of_mem_goodChallenges encoder agreementThreshold lanes
    strategy z member

structure GoodChallengePackage
    (K Domain Message : Type*)
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) where
  challenges : Finset K
  challenges_eq : challenges =
    goodChallenges encoder agreementThreshold lanes strategy
  valid : ∀ z ∈ challenges,
    ValidResponse encoder agreementThreshold lanes strategy z

noncomputable def packageGoodChallenges
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) :
    GoodChallengePackage K Domain Message encoder agreementThreshold lanes
      strategy where
  challenges := goodChallenges encoder agreementThreshold lanes strategy
  challenges_eq := rfl
  valid := all_goodChallenges_valid encoder agreementThreshold lanes strategy


set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
set_option linter.constructorNameAsVariable false in
/-- The exact released final V7 `256 → 2^18` encoder satisfies the complete
degree-three curve-decodability predicate at the unchanged release cap. -/
theorem exactV7FinalDegreeThreeCurveDecodable :
    DegreeThreeCurveDecodable exactFinalEncoder 9557 foldChallengeCap := by
  classical
  let encoder :
      AspisV6OneFoldCandidateExtraction.FinalCoefficients QM31Exact →
        Fin 262144 → QM31Exact := exactFinalEncoder
  change DegreeThreeCurveDecodable encoder 9557 foldChallengeCap
  intro lanes strategy manyGood
  obtain ⟨coefficients, coefficientsNeZero, kernel⟩ :=
    exists_exactFinalCurveInterpolation lanes
  let polynomial := curveTrivariatePolynomial coefficients
  have polynomialNeZero : polynomial ≠ 0 :=
    curveTrivariatePolynomial_ne_zero coefficients coefficientsNeZero
  let candidate : QM31Exact → QM31Exact[X] := fun z =>
    exactFinalGRSConversion.messagePolynomial (strategy.candidate z)
  obtain ⟨challenges, challengesEq, validOn⟩ :=
    packageGoodChallenges encoder 9557 lanes strategy
  have candidateRoot : ∀ z ∈ challenges,
      challengeCandidateHom z (candidate z) polynomial = 0 := by
    intro z zMem
    have valid : ValidResponse encoder 9557 lanes strategy z := by
      exact validOn z zMem
    have validExact : ValidResponse exactFinalEncoder 9557 lanes strategy z := by
      simpa only [encoder] using valid
    have root := exactFinalValidCandidate_substitute_eq_zero lanes strategy
      coefficients kernel z validExact
    change substituteCandidate (candidate z)
      (specializeChallenge z polynomial) = 0
    rw [show specializeChallenge z polynomial =
        weightedBivariatePolynomial
          (specializeCurveCoefficients
            (by norm_num [finalCurveXBound, finalCurveYRows])
              coefficients z) by
      exact specializeChallenge_curveTrivariatePolynomial
        (by norm_num [finalCurveXBound, finalCurveYRows]) coefficients z]
    simpa [challengeCandidateHom, candidate] using root
  have outerMany :
      finalCurveZBound + 224 * finalCurveYRows * finalCurveZBound +
          58 * (255 + 1) * finalCurveYRows ^ 2 * finalCurveZBound +
            (3 * 262144 + 1) * finalCurveYRows <
              challenges.card := by
    apply lt_trans (b := foldChallengeCap)
    · norm_num [finalCurveZBound, finalCurveYRows, foldChallengeCap]
    · rw [challengesEq]
      exact manyGood
  obtain ⟨globalFactor, x₀, localFactor, selected, globalMem,
      globalPositive, certificateAtPoint, localMem, localPositive,
      selectedLarge, selectedSubset, selectedSpec⟩ :=
    exists_weighted_fixed_branch polynomial polynomialNeZero candidate
      challenges 255 3 finalCurveYRows finalCurveZBound
      (3 * 262144 + 1)
      (by norm_num [finalCurveYRows])
      (by norm_num [finalCurveZBound])
      (curveTrivariatePolynomial_natDegree_lt
        (by norm_num [finalCurveYRows]) coefficients)
      ((curveTrivariatePolynomial_xNatDegree_lt
        (by norm_num [finalCurveXBound]) coefficients).trans_le <| by
          norm_num [finalCurveXBound])
      (curveTrivariatePolynomial_zNatDegree_lt
        (by norm_num [finalCurveZBound]) coefficients)
      (trivariateYZWeight_curveTrivariatePolynomial_lt
        (by norm_num [finalCurveZBound]) coefficients)
      candidateRoot outerMany
  have parentNeZero : specializeEvaluationPoint x₀ globalFactor ≠ 0 :=
    specializeEvaluationPoint_ne_zero_of_certificate globalFactor x₀
      globalPositive certificateAtPoint
  letI : Fact (Irreducible (localFactorOverRational localFactor)) :=
    ⟨localFactorOverRational_irreducible
      (specializeEvaluationPoint x₀ globalFactor) localFactor parentNeZero
        localMem localPositive⟩
  have localNeZero : localFactor ≠ 0 :=
    (bivariatePrimeFactors_prime _ parentNeZero localFactor localMem).ne_zero
  obtain ⟨root, rootEquation, rootConstant⟩ :=
    exists_exactV7_fixedBranch_powerSeriesRoot globalFactor x₀
      certificateAtPoint localFactor localMem localPositive
  have etaNeZero := exactV7_regularizedHenselDerivative_ne_zero globalFactor
    x₀ certificateAtPoint localFactor localMem localPositive
  have selectedValid : ∀ z ∈ selected,
      ValidResponse exactFinalEncoder 9557 lanes strategy z := by
    intro z zMem
    have valid : ValidResponse encoder 9557 lanes strategy z :=
      validOn z (selectedSubset zMem)
    simpa only [encoder] using valid
  have localRoot : ∀ z ∈ selected,
      localFactor.eval₂ (Polynomial.evalRingHom z)
        ((candidate z).eval x₀) = 0 := by
    intro z zMem
    rw [Polynomial.eval₂_eq_eval_map]
    exact (selectedSpec z zMem).2.2.1
  have components := exists_exactFinal_components_of_fixed_branch lanes
    strategy globalFactor globalPositive x₀ localFactor localNeZero
    localPositive root rootEquation rootConstant etaNeZero selected
    selectedValid localRoot
    (fun z zMem => (selectedSpec z zMem).1)
    (fun z zMem => (selectedSpec z zMem).2.1)
    (fun z zMem => (selectedSpec z zMem).2.2.2)
    selectedLarge
  obtain ⟨componentMessages, onCurve⟩ := components
  refine ⟨componentMessages, selected, ?_, ?_, ?_⟩
  · intro z zMem
    rw [← challengesEq]
    exact selectedSubset zMem
  · rw [Fintype.card_fin]
    omega
  · simpa only [encoder] using onCurve

/-- V7-specific discharge of the historical published one-fold interface. -/
theorem exactV7FinalPublishedOneFoldCurveDecodability :
    PublishedOneFoldCurveDecodability exactFinalLinear := by
  change DegreeThreeCurveDecodable exactFinalEncoder 9557 foldChallengeCap
  exact exactV7FinalDegreeThreeCurveDecodable

#print axioms exactV7FinalDegreeThreeCurveDecodable
#print axioms exactV7FinalPublishedOneFoldCurveDecodability


end

end AspisK1.V7ExactCorrelatedAgreementTerminal
