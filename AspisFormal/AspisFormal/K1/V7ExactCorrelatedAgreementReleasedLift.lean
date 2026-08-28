import AspisFormal.K1.V7ExactCorrelatedAgreement
import Mathlib.LinearAlgebra.Lagrange

/-!
# Returning an ambient curve to exact released messages

The algebraic correlated-agreement argument first produces a scalar-power
curve of ambient codewords.  This file proves the final bridge that the curve
can be represented by component messages of the exact released message type,
provided more than its degree many selected specializations are already
released codewords.  It does not assume that the ambient GRS space equals the
released image.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementReleasedLift

open scoped BigOperators
open Polynomial
open AspisK1.V7ExactCorrelatedAgreement
open AspisV5FriConcreteEncoderApplicability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6Width29CorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement

noncomputable section

/-- Coefficient messages obtained by coordinatewise Lagrange interpolation
of actual selected messages. -/
noncomputable def releasedInterpolationComponents
    {K : Type*} [Field K]
    {messageCoordinates curveDegree : Nat}
    (nodes : Finset K) (candidate : K → Fin messageCoordinates → K) :
    Fin (curveDegree + 1) → Fin messageCoordinates → K := by
  classical
  exact fun coefficient coordinate =>
    (Lagrange.interpolate nodes id (fun z => candidate z coordinate)).coeff
      coefficient.1

/-- The interpolated component messages reproduce every selected actual
message at the interpolation nodes. -/
theorem releasedInterpolationComponents_curve_eq_candidate
    {K : Type*} [Field K]
    {messageCoordinates curveDegree : Nat}
    (nodes : Finset K) (candidate : K → Fin messageCoordinates → K)
    (nodesCard : nodes.card = curveDegree + 1)
    (z : K) (zMem : z ∈ nodes) :
    (∑ coefficient : Fin (curveDegree + 1),
        z ^ coefficient.1 •
          releasedInterpolationComponents nodes candidate coefficient) =
      candidate z := by
  classical
  funext coordinate
  let interpolant :=
    Lagrange.interpolate nodes id (fun value => candidate value coordinate)
  have nodesInjective : Set.InjOn (id : K → K) nodes :=
    Function.injective_id.injOn
  have interpolantDegreeSmall : interpolant.natDegree < curveDegree + 1 := by
    by_cases interpolantZero : interpolant = 0
    · simp [interpolantZero]
    · apply (Polynomial.natDegree_lt_iff_degree_lt interpolantZero).mpr
      change (Lagrange.interpolate nodes id
        (fun value => candidate value coordinate)).degree <
          ((curveDegree + 1 : Nat) : WithBot Nat)
      simpa only [nodesCard] using
        (Lagrange.degree_interpolate_lt
          (fun value => candidate value coordinate) nodesInjective)
  have interpolantAtNode : interpolant.eval z = candidate z coordinate := by
    exact Lagrange.eval_interpolate_at_node
      (fun value => candidate value coordinate) nodesInjective zMem
  have coefficientExpansion :=
    Polynomial.eval_eq_sum_range' interpolantDegreeSmall z
  rw [interpolantAtNode] at coefficientExpansion
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul,
    releasedInterpolationComponents]
  change (∑ coefficient : Fin (curveDegree + 1),
    z ^ coefficient.1 * interpolant.coeff coefficient.1) = candidate z coordinate
  rw [Fin.sum_univ_eq_sum_range
    (fun coefficient : Nat =>
      z ^ coefficient * interpolant.coeff coefficient) (curveDegree + 1)]
  calc
    (∑ coefficient ∈ Finset.range (curveDegree + 1),
        z ^ coefficient * interpolant.coeff coefficient) =
        ∑ coefficient ∈ Finset.range (curveDegree + 1),
          interpolant.coeff coefficient * z ^ coefficient := by
      apply Finset.sum_congr rfl
      intro coefficient _
      ring
    _ = candidate z coordinate := coefficientExpansion.symm

/-- A scalar-power polynomial built from `curveDegree+1` values. -/
def scalarPowerPolynomial
    {K : Type*} [Field K] {curveDegree : Nat}
    (values : Fin (curveDegree + 1) → K) : K[X] :=
  ∑ coefficient, Polynomial.monomial coefficient.1 (values coefficient)

@[simp] theorem scalarPowerPolynomial_eval
    {K : Type*} [Field K] {curveDegree : Nat}
    (values : Fin (curveDegree + 1) → K) (z : K) :
    (scalarPowerPolynomial values).eval z =
      ∑ coefficient, z ^ coefficient.1 * values coefficient := by
  classical
  simp [scalarPowerPolynomial, Polynomial.eval_finsetSum, eval_monomial,
    mul_comm]

theorem scalarPowerPolynomial_natDegree_le
    {K : Type*} [Field K] {curveDegree : Nat}
    (values : Fin (curveDegree + 1) → K) :
    (scalarPowerPolynomial values).natDegree ≤ curveDegree := by
  classical
  unfold scalarPowerPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro coefficient _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- Generic released-image recovery.  The ambient curve may have been found
inside a larger GRS space.  Because `curveDegree+1` of its selected values are
actual messages and the exact encoder is linear, coordinatewise Lagrange
interpolation produces actual component messages whose released codeword
curve equals every selected ambient specialization. -/
theorem exists_released_components_of_ambient_curve
    {K : Type*} [Field K]
    {messageCoordinates curveDegree : Nat}
    {Domain : Type*} [Fintype Domain]
    (encoder : (Fin messageCoordinates → K) →ₗ[K] (Domain → K))
    (candidate : K → Fin messageCoordinates → K)
    (selected : Finset K) (ambient : Domain → K[X])
    (selectedLarge : curveDegree < selected.card)
    (ambientDegree : ∀ coordinate,
      (ambient coordinate).natDegree ≤ curveDegree)
    (candidateOnAmbient : ∀ z ∈ selected, ∀ coordinate,
      encoder (candidate z) coordinate = (ambient coordinate).eval z) :
    ∃ components : Fin (curveDegree + 1) → Fin messageCoordinates → K,
      ∀ z ∈ selected,
        encoder (candidate z) =
          encoder (∑ coefficient : Fin (curveDegree + 1),
            z ^ coefficient.1 • components coefficient) := by
  classical
  obtain ⟨nodes, nodesSubset, nodesCard⟩ :=
    Finset.exists_subset_card_eq (s := selected) (n := curveDegree + 1)
      (by omega)
  let components : Fin (curveDegree + 1) → Fin messageCoordinates → K :=
    releasedInterpolationComponents nodes candidate
  refine ⟨components, ?_⟩
  intro z zMem
  funext coordinate
  let generated := scalarPowerPolynomial
    (fun coefficient => encoder (components coefficient) coordinate)
  have nodesInjective : Set.InjOn (id : K → K) nodes :=
    Function.injective_id.injOn
  have generatedDegree : generated.degree < (nodes.card : WithBot Nat) := by
    calc
      generated.degree ≤ (generated.natDegree : WithBot Nat) :=
        Polynomial.degree_le_natDegree
      _ ≤ (curveDegree : WithBot Nat) := by
        exact_mod_cast scalarPowerPolynomial_natDegree_le
          (fun coefficient => encoder (components coefficient) coordinate)
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self curveDegree
  have ambientDegree' : (ambient coordinate).degree <
      (nodes.card : WithBot Nat) := by
    calc
      (ambient coordinate).degree ≤
          ((ambient coordinate).natDegree : WithBot Nat) :=
        Polynomial.degree_le_natDegree
      _ ≤ (curveDegree : WithBot Nat) := by
        exact_mod_cast ambientDegree coordinate
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self curveDegree
  have equalPolynomials : generated = ambient coordinate := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq nodes nodesInjective
      generatedDegree ambientDegree'
    intro node nodeMem
    have messageAtNode :
        (∑ coefficient : Fin (curveDegree + 1),
            node ^ coefficient.1 • components coefficient) = candidate node :=
      releasedInterpolationComponents_curve_eq_candidate nodes candidate
        nodesCard node nodeMem
    calc
      generated.eval node =
          ∑ coefficient : Fin (curveDegree + 1),
            node ^ coefficient.1 *
              encoder (components coefficient) coordinate := by
        exact scalarPowerPolynomial_eval _ _
      _ = encoder
          (∑ coefficient : Fin (curveDegree + 1),
            node ^ coefficient.1 • components coefficient) coordinate := by
        rw [map_sum]
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = encoder (candidate node) coordinate := by rw [messageAtNode]
      _ = (ambient coordinate).eval node :=
        candidateOnAmbient node (nodesSubset nodeMem) coordinate
  have candidateValue := candidateOnAmbient z zMem coordinate
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← scalarPowerPolynomial_eval]
  change encoder (candidate z) coordinate = generated.eval z
  rw [equalPolynomials, ← candidateValue]

/-- Exact initial-code wrapper: an ambient degree-28 word curve containing a
large selected family is converted to 29 actual `Fin 1024 → QM31Exact`
messages and the precise `Width29CandidateOnCurve` conclusion. -/
theorem exists_exactInitial_components_of_ambient_curve
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (selected : Finset QM31Exact)
    (ambient : Fin 1048576 → Polynomial QM31Exact)
    (selectedLarge : 28 < selected.card)
    (ambientDegree : ∀ coordinate, (ambient coordinate).natDegree ≤ 28)
    (candidateOnAmbient : ∀ gamma ∈ selected, ∀ coordinate,
      exactInitialEncoder (strategy.candidate gamma) coordinate =
        (ambient coordinate).eval gamma) :
    ∃ components : Fin 29 → InitialMessage QM31Exact,
      ∀ gamma ∈ selected,
        Width29CandidateOnCurve exactInitialEncoder strategy components gamma := by
  obtain ⟨components, componentsOnCurve⟩ :=
    exists_released_components_of_ambient_curve
      (curveDegree := 28) exactInitialLinear strategy.candidate selected ambient
      selectedLarge ambientDegree candidateOnAmbient
  refine ⟨components, ?_⟩
  intro gamma gammaMem
  unfold Width29CandidateOnCurve
  rw [← exactInitialEncoder_messageCurve]
  have curveEquality := componentsOnCurve gamma gammaMem
  change exactInitialEncoder (strategy.candidate gamma) =
    exactInitialEncoder
      (∑ coefficient : Fin 29,
        gamma ^ coefficient.1 • components coefficient) at curveEquality
  simpa only [exactInitialMessageCurve] using curveEquality

/-- Exact final-code wrapper producing four actual released final messages. -/
theorem exists_exactFinal_components_of_ambient_curve
    (strategy : ProximateStrategy QM31Exact (Fin 262144)
      (FinalMessage QM31Exact))
    (selected : Finset QM31Exact)
    (ambient : Fin 262144 → Polynomial QM31Exact)
    (selectedLarge : 3 < selected.card)
    (ambientDegree : ∀ coordinate, (ambient coordinate).natDegree ≤ 3)
    (candidateOnAmbient : ∀ z ∈ selected, ∀ coordinate,
      exactFinalEncoder (strategy.candidate z) coordinate =
        (ambient coordinate).eval z) :
    ∃ components : Fin 4 → FinalMessage QM31Exact,
      ∀ z ∈ selected,
        CandidateOnCurve exactFinalEncoder strategy components z := by
  obtain ⟨components, componentsOnCurve⟩ :=
    exists_released_components_of_ambient_curve
      (curveDegree := 3) exactFinalLinear strategy.candidate selected ambient
      selectedLarge ambientDegree candidateOnAmbient
  refine ⟨components, ?_⟩
  intro z zMem
  unfold CandidateOnCurve
  rw [← exactFinalEncoder_messageCurve]
  have curveEquality := componentsOnCurve z zMem
  change exactFinalEncoder (strategy.candidate z) =
    exactFinalEncoder
      (∑ coefficient : Fin 4,
        z ^ coefficient.1 • components coefficient) at curveEquality
  simpa only [exactFinalMessageCurve] using curveEquality

#print axioms releasedInterpolationComponents_curve_eq_candidate
#print axioms exists_released_components_of_ambient_curve
#print axioms exists_exactInitial_components_of_ambient_curve
#print axioms exists_exactFinal_components_of_ambient_curve

end

end AspisK1.V7ExactCorrelatedAgreementReleasedLift
