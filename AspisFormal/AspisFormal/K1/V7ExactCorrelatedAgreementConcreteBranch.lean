import AspisFormal.K1.V7ExactCorrelatedAgreementFixedBranchCurve
import AspisFormal.K1.V7ExactCorrelatedAgreementReleasedLift
import AspisFormal.K1.V7ExactCorrelatedAgreementFactorBudgets

/-!
# Exact V7 wrappers for one selected irreducible branch

These wrappers connect the algebraic fixed-branch theorem to the literal V7
GRS points, received scalar-power curves, and released message types.  The
remaining outer theorem must supply the fixed global/local factors by the
weighted pigeonhole argument.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementConcreteBranch

open Polynomial
open AspisK1.V7ExactCorrelatedAgreement
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementFixedBranchCurve
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementReleasedLift
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7Tag73ExactMultiplicityThreeGS
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
open AspisV5ComponentCQM31TowerExact

noncomputable section

set_option maxRecDepth 262144 in
set_option maxHeartbeats 2000000 in
/-- Final V7 fixed-branch extraction, already returning four literal
`Fin 256 → QM31Exact` messages. -/
theorem exists_exactFinal_components_of_fixed_branch
    (lanes : Fin 4 → FinalWord QM31Exact)
    (strategy : ProximateStrategy QM31Exact (Fin 262144)
      (FinalMessage QM31Exact))
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (etaNeZero : regularizedHenselDerivative globalFactor x₀ localFactor ≠ 0)
    (selected : Finset QM31Exact)
    (selectedValid : ∀ z ∈ selected,
      ValidResponse exactFinalEncoder 9557 lanes strategy z)
    (localRoot : ∀ z ∈ selected,
      localFactor.eval₂ (Polynomial.evalRingHom z)
        ((exactFinalGRSConversion.messagePolynomial
          (strategy.candidate z)).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ selected,
      challengeCandidateHom z
        (exactFinalGRSConversion.messagePolynomial (strategy.candidate z))
          globalFactor = 0)
    (simple : ∀ z ∈ selected,
      SimpleSpecializedRoot globalFactor x₀ z
        (exactFinalGRSConversion.messagePolynomial (strategy.candidate z)))
    (notPole : ∀ z ∈ selected,
      z ∉ localPoleChallengeSet localFactor)
    (selectedLarge :
      29 * fixedBranchEvaluationBudget 255 3 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 3 localFactor)
          (trivariateYZWeight 3 globalFactor) +
        (3 * 262144 + 1) < selected.card) :
    ∃ components : Fin 4 → FinalMessage QM31Exact,
      ∀ z ∈ selected,
        CandidateOnCurve exactFinalEncoder strategy components z := by
  classical
  have globalFactorNeZero : globalFactor ≠ 0 := by
    exact fun globalZero => by simpa [globalZero] using globalFactorPositive
  have curveLeParent : 3 ≤ trivariateYZWeight 3 globalFactor := by
    have leadingMem : globalFactor.natDegree ∈ globalFactor.support :=
      Polynomial.natDegree_mem_support_of_nonzero globalFactorNeZero
    have bounded := coeff_weight_le_localBivariateWeight 3 globalFactor
      globalFactor.natDegree leadingMem
    change (globalFactor.coeff globalFactor.natDegree).natDegree +
        globalFactor.natDegree * 3 ≤ trivariateYZWeight 3 globalFactor at bounded
    omega
  have localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + 3 * exponent ≤
        localBivariateWeight 3 localFactor := by
    intro exponent exponentMem
    have bounded := coeff_weight_le_localBivariateWeight 3 localFactor
      exponent exponentMem
    simpa [Nat.mul_comm] using bounded
  have globalCoefficientBound : ∀ exponent ∈ globalFactor.support,
      (globalFactor.coeff exponent).natDegree + 3 * exponent ≤
        trivariateYZWeight 3 globalFactor := by
    intro exponent exponentMem
    have bounded := coeff_weight_le_localBivariateWeight 3 globalFactor
      exponent exponentMem
    simpa [trivariateYZWeight, Nat.mul_comm] using bounded
  let candidate : QM31Exact → QM31Exact[X] := fun z =>
    exactFinalGRSConversion.messagePolynomial (strategy.candidate z)
  let received : Fin 262144 → QM31Exact[X] :=
    receivedCurvePolynomial lanes
  have localRoot' : ∀ z ∈ selected,
      localFactor.eval₂ (Polynomial.evalRingHom z)
        ((candidate z).eval x₀) = 0 := by
    exact localRoot
  have candidateRoot' : ∀ z ∈ selected,
      challengeCandidateHom z (candidate z) globalFactor = 0 := by
    exact candidateRoot
  have simple' : ∀ z ∈ selected,
      SimpleSpecializedRoot globalFactor x₀ z (candidate z) := by
    exact simple
  have supportLarge : ∀ z ∈ selected,
      9557 < (strategy.support z).card := by
    intro z zMem
    exact (selectedValid z zMem).1
  have agreement : ∀ z ∈ selected, ∀ coordinate ∈ strategy.support z,
      (candidate z).eval (exactFinalGRSConversion.points coordinate) =
        (received coordinate).eval z := by
    intro z zMem coordinate coordinateMem
    have valid := selectedValid z zMem
    have encoded := congrFun
      (exactFinalEncoder_eq_grs (strategy.candidate z)) coordinate
    calc
      (candidate z).eval (exactFinalGRSConversion.points coordinate) =
          exactFinalEncoder (strategy.candidate z) coordinate := by
        simpa [candidate, ExactGRSConversion.grsEncoder,
          generalizedReedSolomonEncode, exactFinalGRSConversion] using
            encoded.symm
      _ = curveValue lanes z coordinate := (valid.2 coordinate coordinateMem).symm
      _ = (received coordinate).eval z := by
        simpa [received] using (exactFinalLanes_curve lanes z coordinate).symm
  have candidateDegree : ∀ z ∈ selected,
      (candidate z).natDegree ≤ 255 := by
    intro z _
    exact exactFinalGRSConversion.messagePolynomial_degree_le
      (strategy.candidate z)
  have receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ 3 := by
    intro coordinate
    exact receivedCurvePolynomial_natDegree_le lanes coordinate
  have incidence := exactFinal_incidence_of_branchSelection
    (fixedBranchEvaluationBudget 255 3 globalFactor.natDegree
      localFactor.natDegree (localBivariateWeight 3 localFactor)
      (trivariateYZWeight 3 globalFactor)) selected.card selectedLarge
  have incidence' :
      255 * selected.card + Fintype.card (Fin 262144) *
          fixedBranchEvaluationBudget 255 3 globalFactor.natDegree
            localFactor.natDegree (localBivariateWeight 3 localFactor)
              (trivariateYZWeight 3 globalFactor) <
        selected.card * (9557 + 1) := by
    rw [Fintype.card_fin]
    exact incidence
  have ambientExists : ∃ ambient : Fin 262144 → QM31Exact[X],
      (∀ coordinate, (ambient coordinate).natDegree ≤ 3) ∧
      ∀ z ∈ selected, ∀ coordinate,
        (candidate z).eval (exactFinalGRSConversion.points coordinate) =
          (ambient coordinate).eval z := by
    apply exists_ambient_curve_of_fixed_branch (Domain := Fin 262144)
      exactFinalGRSConversion.points
      exactFinalGRSConversion.points_injective globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive 255 3 9557 (localBivariateWeight 3 localFactor)
      (trivariateYZWeight 3 globalFactor) curveLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant etaNeZero selected candidate strategy.support received
    · exact supportLarge
    · exact agreement
    · exact candidateDegree
    · exact receivedDegree
    · exact localRoot'
    · exact candidateRoot'
    · exact simple'
    · exact notPole
    · exact incidence'
  obtain ⟨ambient, ambientDegree, candidateAmbient⟩ := ambientExists
  apply exists_exactFinal_components_of_ambient_curve strategy selected ambient
  · have concurrency :=
      exactFinal_concurrency_of_branchSelection _ _ selectedLarge
    omega
  · exact ambientDegree
  · intro z zMem coordinate
    have encoded := congrFun
      (exactFinalEncoder_eq_grs (strategy.candidate z)) coordinate
    calc
      exactFinalEncoder (strategy.candidate z) coordinate =
          (candidate z).eval (exactFinalGRSConversion.points coordinate) := by
        simpa [candidate, ExactGRSConversion.grsEncoder,
          generalizedReedSolomonEncode, exactFinalGRSConversion] using encoded
      _ = (ambient coordinate).eval z := candidateAmbient z zMem coordinate

#print axioms exists_exactFinal_components_of_fixed_branch

set_option maxRecDepth 262144 in
set_option maxHeartbeats 2000000 in
/-- Initial V7 fixed-branch extraction.  The proof performs the exact
nonzero column-multiplier normalization used by the released circle-to-GRS
conversion, then returns 29 literal released messages. -/
theorem exists_exactInitial_components_of_fixed_branch
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (etaNeZero : regularizedHenselDerivative globalFactor x₀ localFactor ≠ 0)
    (selected : Finset QM31Exact)
    (selectedValid : ∀ gamma ∈ selected,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (localRoot : ∀ gamma ∈ selected,
      localFactor.eval₂ (Polynomial.evalRingHom gamma)
        ((exactInitialGRSConversion.messagePolynomial
          (strategy.candidate gamma)).eval x₀) = 0)
    (candidateRoot : ∀ gamma ∈ selected,
      challengeCandidateHom gamma
        (exactInitialGRSConversion.messagePolynomial
          (strategy.candidate gamma)) globalFactor = 0)
    (simple : ∀ gamma ∈ selected,
      SimpleSpecializedRoot globalFactor x₀ gamma
        (exactInitialGRSConversion.messagePolynomial
          (strategy.candidate gamma)))
    (notPole : ∀ gamma ∈ selected,
      gamma ∉ localPoleChallengeSet localFactor)
    (selectedLarge :
      29 * fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 28 localFactor)
          (trivariateYZWeight 28 globalFactor) +
        (28 * 1048576 + 1) < selected.card) :
    ∃ components : Fin 29 → InitialMessage QM31Exact,
      ∀ gamma ∈ selected,
        Width29CandidateOnCurve exactInitialEncoder strategy components gamma := by
  classical
  have globalFactorNeZero : globalFactor ≠ 0 := by
    exact fun globalZero => by simpa [globalZero] using globalFactorPositive
  have curveLeParent : 28 ≤ trivariateYZWeight 28 globalFactor := by
    have leadingMem : globalFactor.natDegree ∈ globalFactor.support :=
      Polynomial.natDegree_mem_support_of_nonzero globalFactorNeZero
    have bounded := coeff_weight_le_localBivariateWeight 28 globalFactor
      globalFactor.natDegree leadingMem
    change (globalFactor.coeff globalFactor.natDegree).natDegree +
        globalFactor.natDegree * 28 ≤
          trivariateYZWeight 28 globalFactor at bounded
    omega
  have localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + 28 * exponent ≤
        localBivariateWeight 28 localFactor := by
    intro exponent exponentMem
    have bounded := coeff_weight_le_localBivariateWeight 28 localFactor
      exponent exponentMem
    simpa [Nat.mul_comm] using bounded
  have globalCoefficientBound : ∀ exponent ∈ globalFactor.support,
      (globalFactor.coeff exponent).natDegree + 28 * exponent ≤
        trivariateYZWeight 28 globalFactor := by
    intro exponent exponentMem
    have bounded := coeff_weight_le_localBivariateWeight 28 globalFactor
      exponent exponentMem
    simpa [trivariateYZWeight, Nat.mul_comm] using bounded
  let candidate : QM31Exact → QM31Exact[X] := fun gamma =>
    exactInitialGRSConversion.messagePolynomial (strategy.candidate gamma)
  let received : Fin 1048576 → QM31Exact[X] :=
    receivedCurvePolynomial (exactInitialNormalizedLanes lanes)
  have localRoot' : ∀ gamma ∈ selected,
      localFactor.eval₂ (Polynomial.evalRingHom gamma)
        ((candidate gamma).eval x₀) = 0 := by exact localRoot
  have candidateRoot' : ∀ gamma ∈ selected,
      challengeCandidateHom gamma (candidate gamma) globalFactor = 0 := by
    exact candidateRoot
  have simple' : ∀ gamma ∈ selected,
      SimpleSpecializedRoot globalFactor x₀ gamma (candidate gamma) := by
    exact simple
  have supportLarge : ∀ gamma ∈ selected,
      38229 < (strategy.support gamma).card := by
    intro gamma gammaMem
    exact (selectedValid gamma gammaMem).1
  have agreement : ∀ gamma ∈ selected,
      ∀ coordinate ∈ strategy.support gamma,
      (candidate gamma).eval
          (exactInitialGRSConversion.points coordinate) =
        (received coordinate).eval gamma := by
    intro gamma gammaMem coordinate coordinateMem
    have valid := selectedValid gamma gammaMem
    have response := valid.2 coordinate coordinateMem
    have encoded := exactInitialEncoder_coordinate_grs
      (strategy.candidate gamma) coordinate
    have multiplierNeZero :=
      exactInitialGRSConversion.multipliers_ne_zero coordinate
    calc
      (candidate gamma).eval
          (exactInitialGRSConversion.points coordinate) =
          (exactInitialGRSConversion.multipliers coordinate)⁻¹ *
            exactInitialEncoder (strategy.candidate gamma) coordinate := by
        rw [encoded]
        unfold generalizedReedSolomonEncode
        field_simp
        simp only [candidate, exactInitialGRSConversion]
        ring
      _ = (exactInitialGRSConversion.multipliers coordinate)⁻¹ *
            width29CurveValue lanes gamma coordinate := by rw [← response]
      _ = (received coordinate).eval gamma := by
        simpa [received, exactInitialNormalizedReceived] using
          (exactInitialNormalizedLanes_curve lanes gamma coordinate).symm
  have candidateDegree : ∀ gamma ∈ selected,
      (candidate gamma).natDegree ≤ 1024 := by
    intro gamma _
    exact exactInitialGRSConversion.messagePolynomial_degree_le
      (strategy.candidate gamma)
  have receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ 28 := by
    intro coordinate
    exact receivedCurvePolynomial_natDegree_le
      (exactInitialNormalizedLanes lanes) coordinate
  have incidence := exactInitial_incidence_of_branchSelection
    (fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
      localFactor.natDegree (localBivariateWeight 28 localFactor)
      (trivariateYZWeight 28 globalFactor)) selected.card selectedLarge
  have incidence' :
      1024 * selected.card + Fintype.card (Fin 1048576) *
          fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
            localFactor.natDegree (localBivariateWeight 28 localFactor)
              (trivariateYZWeight 28 globalFactor) <
        selected.card * (38229 + 1) := by
    rw [Fintype.card_fin]
    exact incidence
  have ambientExists : ∃ ambient : Fin 1048576 → QM31Exact[X],
      (∀ coordinate, (ambient coordinate).natDegree ≤ 28) ∧
      ∀ gamma ∈ selected, ∀ coordinate,
        (candidate gamma).eval
            (exactInitialGRSConversion.points coordinate) =
          (ambient coordinate).eval gamma := by
    apply exists_ambient_curve_of_fixed_branch (Domain := Fin 1048576)
      exactInitialGRSConversion.points
      exactInitialGRSConversion.points_injective globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive 1024 28 38229
      (localBivariateWeight 28 localFactor)
      (trivariateYZWeight 28 globalFactor) curveLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant etaNeZero selected candidate strategy.support received
    · exact supportLarge
    · exact agreement
    · exact candidateDegree
    · exact receivedDegree
    · exact localRoot'
    · exact candidateRoot'
    · exact simple'
    · exact notPole
    · exact incidence'
  obtain ⟨ambient, ambientDegree, candidateAmbient⟩ := ambientExists
  let releasedAmbient : Fin 1048576 → QM31Exact[X] := fun coordinate =>
    C (exactInitialGRSConversion.multipliers coordinate) * ambient coordinate
  apply exists_exactInitial_components_of_ambient_curve strategy selected
    releasedAmbient
  · have concurrency :=
      exactInitial_concurrency_of_branchSelection _ _ selectedLarge
    omega
  · intro coordinate
    exact (Polynomial.natDegree_C_mul_le
      (exactInitialGRSConversion.multipliers coordinate)
      (ambient coordinate)).trans (ambientDegree coordinate)
  · intro gamma gammaMem coordinate
    rw [exactInitialEncoder_coordinate_grs]
    unfold generalizedReedSolomonEncode releasedAmbient
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      ← candidateAmbient gamma gammaMem coordinate]
    rfl

#print axioms exists_exactInitial_components_of_fixed_branch

end

end AspisK1.V7ExactCorrelatedAgreementConcreteBranch
