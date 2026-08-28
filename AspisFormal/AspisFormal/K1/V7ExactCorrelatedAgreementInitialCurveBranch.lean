import AspisFormal.K1.V7ExactCorrelatedAgreementInitialSelection

/-!
# Exact initial V7 selected branch to released curve

The explicit branch-to-message lift is serialized separately from elimination
of the outer branch-selection existential to bound kernel memory.
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisK1.V7ExactCorrelatedAgreementTerminal

open Polynomial
open AspisK1.V7ExactCorrelatedAgreement
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7Tag73ExactGRSConversion
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV6Width29CorrelatedAgreement
open AspisV5ComponentCQM31TowerExact

noncomputable section

private theorem exists_strengthen
    {A : Type*} {P : A → Prop} {Q : Prop}
    (existsWitness : ∃ value, P value) (property : Q) :
    ∃ value, Q ∧ P value := by
  obtain ⟨value, witness⟩ := existsWitness
  exact ⟨value, property, witness⟩

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
-- This theorem checks the exact finite-characteristic Hensel/message-image
-- bridge once for the width-29 dependent candidate family.
theorem exists_exactV7Initial_components_of_selected_branch
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (challenges : Finset QM31Exact)
    (validOn : ∀ gamma ∈ challenges,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (globalFactor : TrivariatePolynomial QM31Exact)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
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
    (selectedSubset : selected ⊆ challenges)
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
      28 * Fintype.card (Fin 1048576) < selected.card ∧
      ∀ gamma ∈ selected,
        Width29CandidateOnCurve exactInitialEncoder strategy components
          gamma := by
  have selectedValid : ∀ gamma ∈ selected,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma := by
    intro gamma gammaMem
    exact validOn gamma (selectedSubset gammaMem)
  have selectedCard :
      28 * Fintype.card (Fin 1048576) < selected.card := by
    rw [Fintype.card_fin]
    omega
  exact exists_strengthen
    (exists_exactV7Initial_components_of_branchSelection lanes strategy
      globalFactor x₀ localFactor selected globalPositive certificateAtPoint
      localMem localPositive selectedLarge selectedValid selectedSpec)
    selectedCard

end

end AspisK1.V7ExactCorrelatedAgreementTerminal
