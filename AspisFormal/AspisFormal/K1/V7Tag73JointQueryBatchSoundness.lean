import AspisFormal.V6QueryBatchSoundness
import AspisFormal.Pool.V7RelationCandidateBinding

/-!
# Joint Tag-73 round-zero/query-batch soundness

Tag-73 injects the authenticated sixteen-query claim immediately after the
first relation challenge.  Reusing the V6 powers `1, rho, ..., rho^15` is not
enough to bind that injection jointly to the already-carried relation scalar:
an ordinal-zero query error can cancel an arbitrary prior scalar error for
every `rho`.

The Tag-73 repair is to multiply the complete V6 batch by the same nonzero
challenge, giving powers `rho, rho^2, ..., rho^16`.  The complete discrepancy
is then a degree-at-most-sixteen polynomial whose constant coefficient is the
pre-query relation discrepancy.  If either that scalar is nonzero or the two
query vectors differ, this joint polynomial is nonzero.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73JointQueryBatchSoundness

open Polynomial
open AspisPool.V7RelationCandidateBinding
open AspisV6QueryBatchSoundness

variable {K : Type*} [Field K]

/-- The Tag-73 query residual with powers `rho^(i+1)`. -/
def shiftedQueryBatchResidual
    (expected authenticated : QueryVector K) (rho : K) : K :=
  rho * queryBatchResidual expected authenticated rho

/-- Scalar discrepancy immediately before the query injection, minus the
shifted expected/authenticated residual installed by that injection. -/
def jointQueryBatchDiscrepancy
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K) (rho : K) : K :=
  preQueryDiscrepancy - shiftedQueryBatchResidual expected authenticated rho

/-- Polynomial whose evaluation is the complete Tag-73 discrepancy after
query injection. -/
noncomputable def jointQueryBatchPolynomial
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K) : K[X] :=
  C preQueryDiscrepancy - X * queryBatchPolynomial expected authenticated

@[simp]
theorem eval_jointQueryBatchPolynomial
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K) (rho : K) :
    (jointQueryBatchPolynomial preQueryDiscrepancy expected authenticated).eval
        rho =
      jointQueryBatchDiscrepancy preQueryDiscrepancy expected authenticated
        rho := by
  simp [jointQueryBatchPolynomial, jointQueryBatchDiscrepancy,
    shiftedQueryBatchResidual, eval_queryBatchPolynomial]

/-- Unlike the legacy start-at-one batch, differing query vectors make the
joint polynomial nonzero for every prior scalar discrepancy. -/
theorem jointQueryBatchPolynomial_ne_zero_of_vectors_ne
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K)
    (different : expected ≠ authenticated) :
    jointQueryBatchPolynomial preQueryDiscrepancy expected authenticated ≠
      0 := by
  intro zero
  have equalPolynomials : C preQueryDiscrepancy =
      X * queryBatchPolynomial expected authenticated :=
    sub_eq_zero.mp zero
  have preZero : preQueryDiscrepancy = 0 := by
    have coefficientZero := congrArg
      (fun polynomial : K[X] => polynomial.coeff 0) equalPolynomials
    simpa using coefficientZero
  have productZero : X * queryBatchPolynomial expected authenticated = 0 := by
    rw [← equalPolynomials, preZero]
    simp
  exact (mul_ne_zero X_ne_zero
    (queryBatchPolynomial_ne_zero_of_vectors_ne expected authenticated
      different)) productZero

/-- A nonzero prior scalar also makes the joint polynomial nonzero, even when
all sixteen query values agree. -/
theorem jointQueryBatchPolynomial_ne_zero_of_preQuery_ne
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K)
    (preNonzero : preQueryDiscrepancy ≠ 0) :
    jointQueryBatchPolynomial preQueryDiscrepancy expected authenticated ≠
      0 := by
  intro zero
  have equalPolynomials : C preQueryDiscrepancy =
      X * queryBatchPolynomial expected authenticated :=
    sub_eq_zero.mp zero
  apply preNonzero
  have coefficientZero := congrArg
    (fun polynomial : K[X] => polynomial.coeff 0) equalPolynomials
  simpa using coefficientZero

/-- The complete repaired discrepancy polynomial has degree at most sixteen. -/
theorem jointQueryBatchPolynomial_natDegree_le_sixteen
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K) :
    (jointQueryBatchPolynomial preQueryDiscrepancy expected authenticated).natDegree
      ≤ 16 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (by simp)
        (queryBatchPolynomial_natDegree_le expected authenticated))

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- Nonzero challenges at which the repaired combined discrepancy vanishes. -/
def jointQueryBatchNonzeroCollisionSet
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K) : Finset K :=
  (Finset.univ.erase 0).filter fun rho =>
    jointQueryBatchDiscrepancy preQueryDiscrepancy expected authenticated rho =
      0

/-- Direct constructor for the repaired nonzero collision set.  Keeping this
generic prevents concrete protocol types from re-elaborating the finite-field
filter and erase machinery. -/
theorem mem_jointQueryBatchNonzeroCollisionSet_of_nonzero_of_zero
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K) (rho : K)
    (rhoNonzero : rho ≠ 0)
    (zero : jointQueryBatchDiscrepancy preQueryDiscrepancy expected
      authenticated rho = 0) :
    rho ∈ jointQueryBatchNonzeroCollisionSet preQueryDiscrepancy expected
      authenticated := by
  simp only [jointQueryBatchNonzeroCollisionSet, Finset.mem_filter,
    Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨rhoNonzero, zero⟩

/-- Generic repaired handoff from query injection to the later relation
rounds.  If the joint discrepancy is not a `rho` root, terminal acceptance
forces a repair in one of rounds one through three. -/
theorem joint_collision_or_later_alphaRepair
    (execution : CandidateExecution K)
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K) (rho : K)
    (rhoNonzero : rho ≠ 0)
    (different : expected ≠ authenticated)
    (beforeOneExact : execution.discrepancyTrace.before 1 =
      jointQueryBatchDiscrepancy preQueryDiscrepancy expected authenticated rho)
    (terminal : execution.RelationTerminalAccepts) :
    (expected ≠ authenticated ∧
        rho ∈ jointQueryBatchNonzeroCollisionSet preQueryDiscrepancy expected
          authenticated) ∨
      ∃ round : Fin 4, 0 < round.val ∧
        execution.discrepancyTrace.AlphaRepair round := by
  by_cases afterQueryZero : execution.discrepancyTrace.before 1 = 0
  · exact Or.inl ⟨different,
      mem_jointQueryBatchNonzeroCollisionSet_of_nonzero_of_zero _ _ _ _
        rhoNonzero (by rw [← beforeOneExact]; exact afterQueryZero)⟩
  · exact Or.inr
      (execution.later_alphaRepair_of_before_one_ne_terminal afterQueryZero
        terminal)

/-- If the query vectors differ, at most sixteen nonzero challenges can hide
the combined prior/query discrepancy. -/
theorem jointQueryBatch_nonzero_collision_card_le_sixteen_of_vectors_ne
    (preQueryDiscrepancy : K)
    (expected authenticated : QueryVector K)
    (different : expected ≠ authenticated) :
    (jointQueryBatchNonzeroCollisionSet preQueryDiscrepancy expected
      authenticated).card ≤ 16 := by
  let polynomial :=
    jointQueryBatchPolynomial preQueryDiscrepancy expected authenticated
  have polynomialNonzero : polynomial ≠ 0 :=
    jointQueryBatchPolynomial_ne_zero_of_vectors_ne preQueryDiscrepancy
      expected authenticated different
  have subsetRoots :
      (jointQueryBatchNonzeroCollisionSet preQueryDiscrepancy expected
        authenticated).val ⊆ polynomial.roots := by
    intro rho member
    have residualZero :
        jointQueryBatchDiscrepancy preQueryDiscrepancy expected authenticated
          rho = 0 := (Finset.mem_filter.mp member).2
    rw [Polynomial.mem_roots polynomialNonzero]
    simpa [Polynomial.IsRoot, polynomial] using residualZero
  exact (Polynomial.card_le_degree_of_subset_roots subsetRoots).trans
    (jointQueryBatchPolynomial_natDegree_le_sixteen preQueryDiscrepancy
      expected authenticated)

/-! ## Explicit failure of the legacy start-at-one composition -/

/-- A vector differing only at ordinal zero. -/
def ordinalZeroOffsetVector (delta : K) : QueryVector K :=
  fun ordinal => if ordinal = 0 then delta else 0

omit [Fintype K] [DecidableEq K] in
@[simp]
theorem queryBatchResidual_ordinalZeroOffset
    (delta rho : K) :
    queryBatchResidual (ordinalZeroOffsetVector delta)
        (0 : QueryVector K) rho = delta := by
  simp [queryBatchResidual, ordinalZeroOffsetVector]

omit [Fintype K] [DecidableEq K] in
/-- Concrete algebraic counterexample for the old composition: a nonzero
ordinal-zero error exactly cancels the same pre-query discrepancy for every
challenge.  This is why the Tag-73 repair cannot retain powers starting at
one. -/
theorem legacy_start_at_one_allows_universal_constant_cancellation
    (delta rho : K) :
    delta - queryBatchResidual (ordinalZeroOffsetVector delta)
      (0 : QueryVector K) rho = 0 := by
  simp

end FiniteField

#print axioms eval_jointQueryBatchPolynomial
#print axioms jointQueryBatchPolynomial_ne_zero_of_vectors_ne
#print axioms jointQueryBatchPolynomial_ne_zero_of_preQuery_ne
#print axioms jointQueryBatchPolynomial_natDegree_le_sixteen
#print axioms mem_jointQueryBatchNonzeroCollisionSet_of_nonzero_of_zero
#print axioms joint_collision_or_later_alphaRepair
#print axioms jointQueryBatch_nonzero_collision_card_le_sixteen_of_vectors_ne
#print axioms legacy_start_at_one_allows_universal_constant_cancellation

end AspisK1.V7Tag73JointQueryBatchSoundness
