import AspisFormal.K1.V7ExactCorrelatedAgreementAmbientCurve
import AspisFormal.K1.V7ExactCorrelatedAgreementFactorBudgets

/-!
# One fixed irreducible branch yields one ambient codeword curve

This module combines the exact support-incidence double count, regular
resultant zero count, and Lagrange interpolation.  The candidate polynomial
is still allowed to depend arbitrarily on every challenge.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementFixedBranchCurve

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisK1.V7ExactCorrelatedAgreementHenselSpecialization
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementIncidence
open AspisK1.V7ExactCorrelatedAgreementBranchEvaluation
open AspisK1.V7ExactCorrelatedAgreementAmbientCurve
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact fixed-branch form of BCH+25/BCIKS Section 5.2.7.  More support
incidences than the literal regular-function budget produce one base-field
ambient curve containing every challenge-dependent candidate assigned to the
fixed branch. -/
theorem exists_ambient_curve_of_fixed_branch
    {Domain : Type*} [Fintype Domain] [DecidableEq Domain]
    (points : Domain → QM31Exact) (pointsInjective : Function.Injective points)
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (maximumDegree curveDegree agreementThreshold localBound parentBound : Nat)
    (curveDegreeLeParent : curveDegree ≤ parentBound)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + curveDegree * exponent ≤
        localBound)
    (globalCoefficientBound : ∀ exponent ∈ globalFactor.support,
      (globalFactor.coeff exponent).natDegree + curveDegree * exponent ≤
        parentBound)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (etaNeZero : regularizedHenselDerivative globalFactor x₀ localFactor ≠ 0)
    (challenges : Finset QM31Exact)
    (candidate : QM31Exact → QM31Exact[X])
    (support : QM31Exact → Finset Domain)
    (received : Domain → QM31Exact[X])
    (supportLarge : ∀ z ∈ challenges,
      agreementThreshold < (support z).card)
    (agreement : ∀ z ∈ challenges, ∀ coordinate ∈ support z,
      (candidate z).eval (points coordinate) = (received coordinate).eval z)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ maximumDegree)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ curveDegree)
    (localRoot : ∀ z ∈ challenges,
      localFactor.eval₂ (Polynomial.evalRingHom z)
        ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidateHom z (candidate z) globalFactor = 0)
    (simple : ∀ z ∈ challenges,
      SimpleSpecializedRoot globalFactor x₀ z (candidate z))
    (notPole : ∀ z ∈ challenges,
      z ∉ localPoleChallengeSet localFactor)
    (incidenceLarge :
      maximumDegree * challenges.card + Fintype.card Domain *
          fixedBranchEvaluationBudget maximumDegree curveDegree
            globalFactor.natDegree localFactor.natDegree localBound
              parentBound <
        challenges.card * (agreementThreshold + 1)) :
    ∃ ambient : Domain → QM31Exact[X],
      (∀ coordinate, (ambient coordinate).natDegree ≤ curveDegree) ∧
      ∀ z ∈ challenges, ∀ coordinate,
        (candidate z).eval (points coordinate) =
          (ambient coordinate).eval z := by
  classical
  let branchBudget := fixedBranchEvaluationBudget maximumDegree curveDegree
    globalFactor.natDegree localFactor.natDegree localBound parentBound
  have manyHeavy : maximumDegree <
      (heavyCoordinates challenges support branchBudget).card := by
    apply maximumDegree_lt_card_heavyCoordinates challenges support
      agreementThreshold maximumDegree branchBudget supportLarge
    simpa only [branchBudget] using incidenceLarge
  obtain ⟨nodes, nodesSubset, nodesCard⟩ :=
    Finset.exists_subset_card_eq
      (s := heavyCoordinates challenges support branchBudget)
      (n := maximumDegree + 1) (by omega)
  have pointsInjectiveOn : Set.InjOn points nodes := pointsInjective.injOn
  have nodeDiscrepancyZero : ∀ node ∈ nodes,
      clearedFiniteBranchDiscrepancy globalFactor globalFactorPositive x₀
        localFactor root rootEquation rootConstant (maximumDegree + 1)
          (points node)
          (received node) = 0 := by
    intro node nodeMem
    let fiber := supportFiber challenges support node
    have nodeHeavy := nodesSubset nodeMem
    have fiberLarge : branchBudget < fiber.card := by
      exact (Finset.mem_filter.mp nodeHeavy).2
    have fiberResult := finiteBranchValue_eq_received_of_many_agreements
      globalFactor globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive curveDegree localBound parentBound
      curveDegreeLeParent localCoefficientBound globalCoefficientBound
      root rootEquation rootConstant etaNeZero (maximumDegree + 1) fiber candidate
      (fun z zMem => localRoot z (Finset.mem_filter.mp zMem).1)
      (fun z zMem => candidateRoot z (Finset.mem_filter.mp zMem).1)
      (fun z zMem => simple z (Finset.mem_filter.mp zMem).1)
      (fun z zMem => notPole z (Finset.mem_filter.mp zMem).1)
      (fun z zMem => (candidateDegree z
        (Finset.mem_filter.mp zMem).1).trans_lt (Nat.lt_succ_self _))
      (points node) (received node)
      (receivedDegree node)
      (fun z zMem => agreement z (Finset.mem_filter.mp zMem).1 node
        (Finset.mem_filter.mp zMem).2)
      (by
        simpa only [fiber, branchBudget, fixedBranchEvaluationBudget,
          Nat.add_sub_cancel] using fiberLarge)
    exact fiberResult.1
  let ambient := lagrangeAmbientCurve nodes points received
  refine ⟨ambient, ?_, ?_⟩
  · intro coordinate
    exact lagrangeAmbientCurve_natDegree_le nodes points received curveDegree
      receivedDegree coordinate
  · intro z zMem coordinate
    apply candidate_eval_eq_lagrangeAmbientCurve_eval nodes points
      pointsInjectiveOn maximumDegree nodesCard received z (candidate z)
      (candidateDegree z zMem)
    · intro node nodeMem
      exact candidate_eval_eq_received_of_discrepancy_eq_zero globalFactor
        globalFactorPositive x₀ localFactor localFactorNeZero
        localFactorPositive root rootEquation rootConstant z (candidate z)
        (localRoot z zMem) (candidateRoot z zMem) (simple z zMem)
        (notPole z zMem) (maximumDegree + 1)
        ((candidateDegree z zMem).trans_lt (Nat.lt_succ_self _))
        (points node) (received node) (nodeDiscrepancyZero node nodeMem)

#print axioms exists_ambient_curve_of_fixed_branch

end

end AspisK1.V7ExactCorrelatedAgreementFixedBranchCurve
