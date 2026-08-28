import AspisFormal.K1.V7ExactCorrelatedAgreementTerminal

/-!
# Exact initial V7 specialization root
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisK1.V7ExactCorrelatedAgreementTerminal

open Polynomial
open AspisK1.V7Tag73ExactMultiplicityThreeGS
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

structure Width29GoodChallengePackage
    (K Domain Message : Type*)
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message) where
  challenges : Finset K
  challenges_eq : challenges =
    width29GoodChallenges encoder agreementThreshold lanes strategy
  valid : ∀ gamma ∈ challenges,
    gamma ≠ 0 ∧ Width29ValidResponse encoder agreementThreshold lanes strategy gamma

noncomputable def packageWidth29GoodChallenges
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message) :
    Width29GoodChallengePackage K Domain Message encoder agreementThreshold
      lanes strategy where
  challenges := width29GoodChallenges encoder agreementThreshold lanes strategy
  challenges_eq := rfl
  valid := by
    intro gamma member
    exact (mem_width29GoodChallenges_iff encoder agreementThreshold lanes
      strategy gamma).mp member

/-- Symbolic bridge between the interpolation module's specialized
bivariate polynomial and the factor module's trivariate candidate-root map. -/
theorem challengeCandidateHom_curveTrivariatePolynomial_eq_zero
    {K : Type*} [Field K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (z : K) (candidate : K[X])
    (root : interpolationSubstitute
      (specializeCurveCoefficients lastRow coefficients z) candidate = 0) :
    challengeCandidateHom z candidate
      (curveTrivariatePolynomial coefficients) = 0 := by
  change substituteCandidate candidate
      (specializeChallenge z (curveTrivariatePolynomial coefficients)) = 0
  rw [specializeChallenge_curveTrivariatePolynomial lastRow coefficients z]
  rw [substituteCandidate_weightedBivariatePolynomial]
  exact root


set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
-- The exact `Fin 1024`/width-29 dependent indices make normalization of the
-- specialized initial interpolant substantially more expensive than the
-- generic symbolic bridge above.
/-- Convert the exact initial interpolation-specialization statement to the
branch selector's trivariate root convention.  This declaration is kept
opaque so its large dependent interpolation indices are checked once. -/
theorem exactInitial_challengeCandidateHom_eq_zero
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (coefficients :
      CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound → QM31Exact)
    (kernel : curveInterpolationMap exactInitialGRSConversion.points
      (exactInitialNormalizedLanes lanes) coefficients = 0)
    (gamma : QM31Exact)
    (valid : Width29ValidResponse exactInitialEncoder 38229 lanes strategy
      gamma) :
    challengeCandidateHom gamma
      (exactInitialGRSConversion.messagePolynomial
        (strategy.candidate gamma))
      (curveTrivariatePolynomial coefficients) = 0 := by
  have root := exactInitialValidCandidate_substitute_eq_zero lanes strategy
    coefficients kernel gamma valid
  exact challengeCandidateHom_curveTrivariatePolynomial_eq_zero
    (by norm_num [initialCurveXBound, initialCurveYRows]) coefficients gamma
      (exactInitialGRSConversion.messagePolynomial (strategy.candidate gamma))
        root

end

end AspisK1.V7ExactCorrelatedAgreementTerminal
