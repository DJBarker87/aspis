import AspisFormal.K1.V7ExactCorrelatedAgreementInitialBranch

/-!
# Exact initial V7 fixed-branch selection

This module serializes the weighted pigeonhole/frequency output before the
selected branch is passed to the finite-characteristic Hensel lift.  Keeping
those two large proof terms in separate declarations bounds kernel memory.
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
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementOuterSelection
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7Tag73ExactGRSConversion
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV6Width29CorrelatedAgreement
open AspisV5ComponentCQM31TowerExact

noncomputable section

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
-- The fixed-branch selector expands exact width-29 weighted-degree budgets;
-- isolating it here lets Lean serialize that proof before the Hensel lift.
theorem exists_exactV7Initial_weighted_fixed_branch
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (coefficients :
      CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound → QM31Exact)
    (coefficientsNeZero : coefficients ≠ 0)
    (kernel : curveInterpolationMap exactInitialGRSConversion.points
      (exactInitialNormalizedLanes lanes) coefficients = 0)
    (challenges : Finset QM31Exact)
    (validOn : ∀ gamma ∈ challenges,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (outerMany :
      initialCurveZBound + 224 * initialCurveYRows * initialCurveZBound +
          58 * (1024 + 1) * initialCurveYRows ^ 2 * initialCurveZBound +
            (28 * 1048576 + 1) * initialCurveYRows < challenges.card) :
    ∃ (globalFactor : TrivariatePolynomial QM31Exact)
        (x₀ : QM31Exact)
        (localFactor : BivariatePolynomial QM31Exact)
        (selected : Finset QM31Exact),
      globalFactor ∈ curvePrimeFactors
          (curveTrivariatePolynomial coefficients) ∧
      0 < globalFactor.natDegree ∧
      (Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0 ∧
      localFactor ∈ bivariatePrimeFactors
        (specializeEvaluationPoint x₀ globalFactor) ∧
      0 < localFactor.natDegree ∧
      29 * fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 28 localFactor)
          (trivariateYZWeight 28 globalFactor) +
        (28 * 1048576 + 1) < selected.card ∧
      selected ⊆ challenges ∧
      ∀ gamma ∈ selected,
        challengeCandidateHom gamma
            (exactInitialGRSConversion.messagePolynomial
              (strategy.candidate gamma)) globalFactor = 0 ∧
        SimpleSpecializedRoot globalFactor x₀ gamma
            (exactInitialGRSConversion.messagePolynomial
              (strategy.candidate gamma)) ∧
        localChallengeCandidateHom gamma
            ((exactInitialGRSConversion.messagePolynomial
              (strategy.candidate gamma)).eval x₀) localFactor = 0 ∧
        gamma ∉ localPoleChallengeSet localFactor := by
  classical
  have polynomialNeZero : curveTrivariatePolynomial coefficients ≠ 0 :=
    curveTrivariatePolynomial_ne_zero coefficients coefficientsNeZero
  have candidateRoot : ∀ gamma ∈ challenges,
      challengeCandidateHom gamma
        (exactInitialGRSConversion.messagePolynomial
          (strategy.candidate gamma))
        (curveTrivariatePolynomial coefficients) = 0 := by
    intro gamma gammaMem
    exact exactInitial_challengeCandidateHom_eq_zero lanes strategy coefficients
      kernel gamma (validOn gamma gammaMem)
  exact exists_weighted_fixed_branch
    (curveTrivariatePolynomial coefficients) polynomialNeZero
    (fun gamma => exactInitialGRSConversion.messagePolynomial
      (strategy.candidate gamma)) challenges 1024 28 initialCurveYRows
    initialCurveZBound (28 * 1048576 + 1)
    (by norm_num [initialCurveYRows])
    (by norm_num [initialCurveZBound])
    (curveTrivariatePolynomial_natDegree_lt
      (by norm_num [initialCurveYRows]) coefficients)
    ((curveTrivariatePolynomial_xNatDegree_lt
      (by norm_num [initialCurveXBound]) coefficients).trans_le <| by
        norm_num [initialCurveXBound])
    (curveTrivariatePolynomial_zNatDegree_lt
      (by norm_num [initialCurveZBound]) coefficients)
    (trivariateYZWeight_curveTrivariatePolynomial_lt
      (by norm_num [initialCurveZBound]) coefficients)
    candidateRoot outerMany

end

end AspisK1.V7ExactCorrelatedAgreementTerminal
