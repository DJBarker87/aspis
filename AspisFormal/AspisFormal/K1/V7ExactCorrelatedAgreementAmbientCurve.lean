import AspisFormal.K1.V7ExactCorrelatedAgreementBranchEvaluation
import Mathlib.LinearAlgebra.Lagrange

/-!
# Ambient base-field curve from heavy evaluation coordinates

After the fixed regular branch agrees with the received challenge polynomial
at more than the message degree many evaluation points, ordinary Lagrange
interpolation in the evaluation variable produces one polynomial-in-challenge
ambient word curve containing every selected candidate.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementAmbientCurve

open scoped BigOperators
open Polynomial

noncomputable section

/-- Evaluate the Lagrange interpolation in the codeword variable while
retaining the received values as polynomials in the challenge variable. -/
def lagrangeAmbientCurve
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (received : Domain → K[X]) (coordinate : Domain) : K[X] :=
  ∑ node ∈ nodes,
    C ((Lagrange.basis nodes points node).eval (points coordinate)) *
      received node

/-- The challenge degree of the ambient word curve is no larger than the
degree of the received scalar-power curve. -/
theorem lagrangeAmbientCurve_natDegree_le
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (received : Domain → K[X]) (curveDegree : Nat)
    (receivedDegree : ∀ coordinate,
      (received coordinate).natDegree ≤ curveDegree)
    (coordinate : Domain) :
    (lagrangeAmbientCurve nodes points received coordinate).natDegree ≤
      curveDegree := by
  classical
  unfold lagrangeAmbientCurve
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro node nodeMem
  exact (Polynomial.natDegree_C_mul_le
    ((Lagrange.basis nodes points node).eval (points coordinate))
    (received node)).trans (receivedDegree node)

/-- At a selected interpolation node the ambient polynomial is the literal
received challenge polynomial. -/
theorem lagrangeAmbientCurve_at_node
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjective : Set.InjOn points nodes)
    (received : Domain → K[X]) (node : Domain) (nodeMem : node ∈ nodes) :
    lagrangeAmbientCurve nodes points received node = received node := by
  classical
  unfold lagrangeAmbientCurve
  rw [← Finset.add_sum_erase _ _ nodeMem]
  rw [Lagrange.eval_basis_self pointsInjective nodeMem, C_1, one_mul]
  simp only [add_eq_left]
  apply Finset.sum_eq_zero
  intro other otherMem
  have otherNe : other ≠ node := (Finset.mem_erase.mp otherMem).1
  rw [Lagrange.eval_basis_of_ne otherNe nodeMem, C_0, zero_mul]

/-- A degree-bounded candidate matching the received curve on all Lagrange
nodes is exactly the corresponding specialization of the ambient word curve
at every domain coordinate. -/
theorem candidate_eval_eq_lagrangeAmbientCurve_eval
    {K Domain : Type*} [Field K] [DecidableEq Domain]
    (nodes : Finset Domain) (points : Domain → K)
    (pointsInjective : Set.InjOn points nodes)
    (maximumDegree : Nat) (nodesCard : nodes.card = maximumDegree + 1)
    (received : Domain → K[X]) (z : K) (candidate : K[X])
    (candidateDegree : candidate.natDegree ≤ maximumDegree)
    (matchesNodes : ∀ node ∈ nodes,
      candidate.eval (points node) = (received node).eval z)
    (coordinate : Domain) :
    candidate.eval (points coordinate) =
      (lagrangeAmbientCurve nodes points received coordinate).eval z := by
  classical
  have candidateDegreeLt : candidate.degree < (nodes.card : WithBot Nat) := by
    calc
      candidate.degree ≤ (candidate.natDegree : WithBot Nat) :=
        Polynomial.degree_le_natDegree
      _ ≤ (maximumDegree : WithBot Nat) := by exact_mod_cast candidateDegree
      _ < (nodes.card : WithBot Nat) := by
        rw [nodesCard]
        exact_mod_cast Nat.lt_succ_self maximumDegree
  have candidateInterpolation : candidate =
    Lagrange.interpolate nodes points
        (fun node => (received node).eval z) :=
    Lagrange.eq_interpolate_of_eval_eq
      (fun node => (received node).eval z) pointsInjective candidateDegreeLt
      matchesNodes
  rw [candidateInterpolation, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum]
  unfold lagrangeAmbientCurve
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro node nodeMem
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

#print axioms lagrangeAmbientCurve_natDegree_le
#print axioms lagrangeAmbientCurve_at_node
#print axioms candidate_eval_eq_lagrangeAmbientCurve_eval

end

end AspisK1.V7ExactCorrelatedAgreementAmbientCurve
