import AspisFormal.K1.V7ExactCorrelatedAgreementInitialRoot

/-!
# Exact initial V7 branch-to-message lift
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
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
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

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 1000000 in
/-- Close one selected initial branch through finite-characteristic Hensel
lifting and the exact released-message image theorem. -/
theorem exists_exactV7Initial_components_of_branchSelection
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (globalFactor : TrivariatePolynomial QM31Exact)
    (x₀ : QM31Exact) (localFactor : BivariatePolynomial QM31Exact)
    (selected : Finset QM31Exact)
    (globalPositive : 0 < globalFactor.natDegree)
    (certificateAtPoint : (Polynomial.Bivariate.swap
      (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0)
    (localMem : localFactor ∈ bivariatePrimeFactors
      (specializeEvaluationPoint x₀ globalFactor))
    (localPositive : 0 < localFactor.natDegree)
    (selectedLarge :
      29 * fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 28 localFactor)
          (trivariateYZWeight 28 globalFactor) +
        (28 * 1048576 + 1) < selected.card)
    (selectedValid : ∀ gamma ∈ selected,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (selectedSpec : ∀ gamma ∈ selected,
      challengeCandidateHom gamma
          (exactInitialGRSConversion.messagePolynomial
            (strategy.candidate gamma)) globalFactor = 0 ∧
      SimpleSpecializedRoot globalFactor x₀ gamma
          (exactInitialGRSConversion.messagePolynomial
            (strategy.candidate gamma)) ∧
      localChallengeCandidateHom gamma
          ((exactInitialGRSConversion.messagePolynomial
            (strategy.candidate gamma)).eval x₀) localFactor = 0 ∧
      gamma ∉ localPoleChallengeSet localFactor) :
    ∃ components : Fin 29 → InitialMessage QM31Exact,
      ∀ gamma ∈ selected,
        Width29CandidateOnCurve exactInitialEncoder strategy components
          gamma := by
  classical
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
  have localRoot : ∀ gamma ∈ selected,
      localFactor.eval₂ (Polynomial.evalRingHom gamma)
        ((exactInitialGRSConversion.messagePolynomial
          (strategy.candidate gamma)).eval x₀) = 0 := by
    intro gamma gammaMem
    rw [Polynomial.eval₂_eq_eval_map]
    exact (selectedSpec gamma gammaMem).2.2.1
  exact exists_exactInitial_components_of_fixed_branch lanes strategy
    globalFactor globalPositive x₀ localFactor localNeZero localPositive root
    rootEquation rootConstant etaNeZero selected selectedValid localRoot
    (fun gamma gammaMem => (selectedSpec gamma gammaMem).1)
    (fun gamma gammaMem => (selectedSpec gamma gammaMem).2.1)
    (fun gamma gammaMem => (selectedSpec gamma gammaMem).2.2.2)
    selectedLarge

end

end AspisK1.V7ExactCorrelatedAgreementTerminal
