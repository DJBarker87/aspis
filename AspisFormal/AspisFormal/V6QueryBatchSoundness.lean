import AspisFormal.V5FriConcreteEncoderApplicability

/-!
# Exact soundness of the V6 sixteen-query batch

The V6 verifier compares sixteen evaluations of the disclosed degree-less-than-
256 polynomial with sixteen values authenticated by the folded commitment.  It
samples one nonzero field element `rho` after those two vectors are fixed and
checks their scalar-power batch

`sum_i rho^i * (expected_i - authenticated_i)`.

This file proves the complete elementary algebra for that check.  If the two
fixed vectors differ, the residual is a nonzero polynomial of degree at most
fifteen.  Consequently it vanishes for at most fifteen field elements.  The
exact uniform bounds are `15 / |K|` for a full-field sampler and
`15 / (|K| - 1)` for the nonzero sampler used by the source.

The last result is deliberately conditional on an explicit statement that the
successful source challenge is uniform over the nonzero field elements.  No
deterministic transcript theorem can itself prove that cryptographic sampling
claim.
-/

set_option autoImplicit false

namespace AspisV6QueryBatchSoundness

open Polynomial
open AspisV5FriConcreteEncoderApplicability
open AspisSoundnessLedger

variable {K : Type*} [Field K]

abbrev QueryVector (K : Type*) := Fin 16 -> K

/-- The coefficient at query ordinal `i`: disclosed evaluation minus the
value authenticated by the folded commitment. -/
def queryResidualVector
    (expected authenticated : QueryVector K) : QueryVector K :=
  fun i => expected i - authenticated i

/-- The exact source-order V6 check
`sum_i rho^i * (expected_i - authenticated_i)`. -/
def queryBatchResidual
    (expected authenticated : QueryVector K) (rho : K) : K :=
  ∑ i : Fin 16, rho ^ i.val * (expected i - authenticated i)

/-- The ordinary degree-at-most-fifteen polynomial underlying the source
batch. -/
noncomputable def queryBatchPolynomial
    (expected authenticated : QueryVector K) : K[X] :=
  monomialPolynomial (queryResidualVector expected authenticated)

@[simp]
theorem queryResidualVector_apply
    (expected authenticated : QueryVector K) (i : Fin 16) :
    queryResidualVector expected authenticated i =
      expected i - authenticated i := by
  rfl

theorem queryResidualVector_eq_zero_iff
    (expected authenticated : QueryVector K) :
    queryResidualVector expected authenticated = 0 ↔
      expected = authenticated := by
  constructor
  · intro hzero
    funext i
    have hi := congrFun hzero i
    simpa [queryResidualVector] using sub_eq_zero.mp hi
  · intro heq
    subst authenticated
    funext i
    simp [queryResidualVector]

theorem queryResidualVector_ne_zero_iff
    (expected authenticated : QueryVector K) :
    queryResidualVector expected authenticated ≠ 0 ↔
      expected ≠ authenticated := by
  rw [ne_eq, ne_eq, queryResidualVector_eq_zero_iff]

@[simp]
theorem queryBatchPolynomial_coeff
    (expected authenticated : QueryVector K) (i : Fin 16) :
    (queryBatchPolynomial expected authenticated).coeff i =
      expected i - authenticated i := by
  simp [queryBatchPolynomial, queryResidualVector]

@[simp]
theorem eval_queryBatchPolynomial
    (expected authenticated : QueryVector K) (rho : K) :
    (queryBatchPolynomial expected authenticated).eval rho =
      queryBatchResidual expected authenticated rho := by
  simp [queryBatchPolynomial, monomialPolynomial, queryBatchResidual,
    queryResidualVector, Polynomial.eval_finsetSum, mul_comm]

/-- Different expected and authenticated query vectors give a genuinely
nonzero residual polynomial. -/
theorem queryBatchPolynomial_ne_zero_of_vectors_ne
    (expected authenticated : QueryVector K)
    (hdifferent : expected ≠ authenticated) :
    queryBatchPolynomial expected authenticated ≠ 0 := by
  intro hzero
  apply hdifferent
  apply (queryResidualVector_eq_zero_iff expected authenticated).mp
  apply monomialPolynomial_injective
  simpa [queryBatchPolynomial, monomialPolynomial] using hzero

/-- A differing vector exposes at least one nonzero polynomial coefficient;
this is the coefficient-level form of the preceding theorem. -/
theorem exists_nonzero_queryBatchPolynomial_coeff_of_vectors_ne
    (expected authenticated : QueryVector K)
    (hdifferent : expected ≠ authenticated) :
    ∃ i : Fin 16,
      (queryBatchPolynomial expected authenticated).coeff i ≠ 0 := by
  by_contra hnone
  apply hdifferent
  funext i
  apply sub_eq_zero.mp
  rw [← queryBatchPolynomial_coeff]
  by_contra hcoefficient
  exact hnone ⟨i, hcoefficient⟩

/-- The residual polynomial has degree at most fifteen, including all
degenerate lower-degree cases. -/
theorem queryBatchPolynomial_natDegree_le
    (expected authenticated : QueryVector K) :
    (queryBatchPolynomial expected authenticated).natDegree <= 15 := by
  simpa [queryBatchPolynomial] using
    (monomialPolynomial_natDegree_le (K := K) (n := 16) (by decide)
      (queryResidualVector expected authenticated))

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- All full-field challenges for which the sixteen-query batch vanishes. -/
def queryBatchCollisionSet
    (expected authenticated : QueryVector K) : Finset K :=
  Finset.univ.filter fun rho =>
    queryBatchResidual expected authenticated rho = 0

/-- For different fixed vectors, the collision set is exactly the root set of
the residual polynomial. -/
theorem queryBatchCollisionSet_eq_roots
    (expected authenticated : QueryVector K)
    (hdifferent : expected ≠ authenticated) :
    queryBatchCollisionSet expected authenticated =
      (queryBatchPolynomial expected authenticated).roots.toFinset := by
  classical
  ext rho
  have hpolynomial := queryBatchPolynomial_ne_zero_of_vectors_ne
    expected authenticated hdifferent
  simp [queryBatchCollisionSet, Polynomial.mem_roots hpolynomial,
    Polynomial.IsRoot, eval_queryBatchPolynomial]

/-- A false sixteen-query vector equality can pass for at most fifteen values
of `rho`. -/
theorem queryBatch_collision_card_le_fifteen
    (expected authenticated : QueryVector K)
    (hdifferent : expected ≠ authenticated) :
    (queryBatchCollisionSet expected authenticated).card <= 15 := by
  let polynomial := queryBatchPolynomial expected authenticated
  have hpolynomial : polynomial ≠ 0 :=
    queryBatchPolynomial_ne_zero_of_vectors_ne
      expected authenticated hdifferent
  have hsubset :
      (queryBatchCollisionSet expected authenticated).val ⊆
        polynomial.roots := by
    intro rho hrho
    have hresidual : queryBatchResidual expected authenticated rho = 0 :=
      (Finset.mem_filter.mp hrho).2
    rw [Polynomial.mem_roots hpolynomial]
    simpa [Polynomial.IsRoot, polynomial] using hresidual
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    (queryBatchPolynomial_natDegree_le expected authenticated)

/-- Exact rational collision mass for a challenge uniform over the complete
field. -/
def uniformFullFieldCollisionProbability
    (expected authenticated : QueryVector K) : Rat :=
  (queryBatchCollisionSet expected authenticated).card /
    (Fintype.card K : Rat)

/-- A full-field uniform `rho` hides a false sixteen-query equality with
probability at most `15 / |K|`. -/
theorem uniformFullFieldCollisionProbability_le
    (expected authenticated : QueryVector K)
    (hdifferent : expected ≠ authenticated) :
    uniformFullFieldCollisionProbability expected authenticated <=
      (15 : Rat) / (Fintype.card K : Rat) := by
  have hcardNat : 0 < Fintype.card K :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : Rat) < (Fintype.card K : Rat) := by
    exact_mod_cast hcardNat
  rw [uniformFullFieldCollisionProbability,
    div_le_div_iff_of_pos_right hcard]
  exact_mod_cast queryBatch_collision_card_le_fifteen
    expected authenticated hdifferent

/-- Collision challenges after restricting the sample space to nonzero field
elements, exactly as the V6 source does. -/
def queryBatchNonzeroCollisionSet
    (expected authenticated : QueryVector K) : Finset K :=
  (Finset.univ.erase 0).filter fun rho =>
    queryBatchResidual expected authenticated rho = 0

theorem queryBatchNonzeroCollisionSet_subset
    (expected authenticated : QueryVector K) :
    queryBatchNonzeroCollisionSet expected authenticated ⊆
      queryBatchCollisionSet expected authenticated := by
  intro rho hrho
  simp only [queryBatchNonzeroCollisionSet, Finset.mem_filter,
    Finset.mem_erase] at hrho
  simp [queryBatchCollisionSet, hrho.2]

/-- Removing zero cannot increase the fifteen-root ceiling. -/
theorem queryBatch_nonzero_collision_card_le_fifteen
    (expected authenticated : QueryVector K)
    (hdifferent : expected ≠ authenticated) :
    (queryBatchNonzeroCollisionSet expected authenticated).card <= 15 := by
  exact (Finset.card_le_card
    (queryBatchNonzeroCollisionSet_subset expected authenticated)).trans
    (queryBatch_collision_card_le_fifteen
      expected authenticated hdifferent)

/-- Exact rational collision mass for a challenge uniform over `K` without
zero.  The denominator is deliberately `|K| - 1`, not `|K|`. -/
def uniformNonzeroCollisionProbability
    (expected authenticated : QueryVector K) : Rat :=
  (queryBatchNonzeroCollisionSet expected authenticated).card /
    ((Fintype.card K - 1 : Nat) : Rat)

/-- The exact nonzero-uniform bound for the sampler used by the V6 code. -/
theorem uniformNonzeroCollisionProbability_le
    (expected authenticated : QueryVector K)
    (hdifferent : expected ≠ authenticated) :
    uniformNonzeroCollisionProbability expected authenticated <=
      (15 : Rat) / ((Fintype.card K - 1 : Nat) : Rat) := by
  have hdenNat : 0 < Fintype.card K - 1 := Nat.sub_pos_iff_lt.mpr
    (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance)
  have hden : (0 : Rat) < ((Fintype.card K - 1 : Nat) : Rat) := by
    exact_mod_cast hdenNat
  rw [uniformNonzeroCollisionProbability,
    div_le_div_iff_of_pos_right hden]
  exact_mod_cast queryBatch_nonzero_collision_card_le_fifteen
    expected authenticated hdifferent

/-! ## Explicit source-uniformity boundary -/

/-- The successful source draw is uniform over nonzero field elements.  This
is the cryptographic sampling premise; bounded rejection only proves that a
successful value is nonzero. -/
def SourceQueryBatchRhoIsUniformNonzero (mass : K -> Rat) : Prop :=
  (mass 0 = 0) /\
    ∀ rho, rho ≠ 0 ->
      mass rho = 1 / ((Fintype.card K - 1 : Nat) : Rat)

/-- Total source mass of the nonzero challenges that hide the discrepancy. -/
def sourceQueryBatchCollisionMass
    (mass : K -> Rat)
    (expected authenticated : QueryVector K) : Rat :=
  ∑ rho ∈ queryBatchNonzeroCollisionSet expected authenticated,
    mass rho

/-- Under the explicit source-uniformity premise, source collision mass is
exactly the finite count divided by `|K| - 1`. -/
theorem sourceQueryBatchCollisionMass_eq_uniformNonzeroProbability
    (mass : K -> Rat)
    (expected authenticated : QueryVector K)
    (huniform : SourceQueryBatchRhoIsUniformNonzero mass) :
    sourceQueryBatchCollisionMass mass expected authenticated =
      uniformNonzeroCollisionProbability expected authenticated := by
  classical
  unfold sourceQueryBatchCollisionMass uniformNonzeroCollisionProbability
  calc
    (∑ rho ∈ queryBatchNonzeroCollisionSet expected authenticated,
        mass rho) =
        ∑ rho ∈ queryBatchNonzeroCollisionSet expected authenticated,
          1 / ((Fintype.card K - 1 : Nat) : Rat) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      apply huniform.2
      have hrho' : rho ≠ 0 /\
          queryBatchResidual expected authenticated rho = 0 := by
        simpa [queryBatchNonzeroCollisionSet] using hrho
      exact hrho'.1
    _ = (queryBatchNonzeroCollisionSet expected authenticated).card /
        ((Fintype.card K - 1 : Nat) : Rat) := by
      simp [div_eq_mul_inv]

/-- Final implementation-facing statement: if the successful `rho` is uniform over
`K*`, a false set of sixteen query equalities passes with probability at most
`15 / (|K| - 1)`. -/
theorem sourceQueryBatchCollisionMass_le
    (mass : K -> Rat)
    (expected authenticated : QueryVector K)
    (huniform : SourceQueryBatchRhoIsUniformNonzero mass)
    (hdifferent : expected ≠ authenticated) :
    sourceQueryBatchCollisionMass mass expected authenticated <=
      (15 : Rat) / ((Fintype.card K - 1 : Nat) : Rat) := by
  rw [sourceQueryBatchCollisionMass_eq_uniformNonzeroProbability
    mass expected authenticated huniform]
  exact uniformNonzeroCollisionProbability_le
    expected authenticated hdifferent

end FiniteField

/-- At the deployed QM31 cardinality the exact nonzero-sampler term is below
`2^-120`.  This is the rounded value suitable for the V6 security ledger. -/
theorem deployed_nonzero_query_batch_term_le_two_pow_neg_120 :
    (15 : Real) / (FIELD - 1) ≤ (1 : Real) / 2 ^ 120 := by
  norm_num [FIELD]

#print axioms queryResidualVector_eq_zero_iff
#print axioms eval_queryBatchPolynomial
#print axioms queryBatchPolynomial_ne_zero_of_vectors_ne
#print axioms exists_nonzero_queryBatchPolynomial_coeff_of_vectors_ne
#print axioms queryBatchPolynomial_natDegree_le
#print axioms queryBatchCollisionSet_eq_roots
#print axioms queryBatch_collision_card_le_fifteen
#print axioms uniformFullFieldCollisionProbability_le
#print axioms queryBatch_nonzero_collision_card_le_fifteen
#print axioms uniformNonzeroCollisionProbability_le
#print axioms sourceQueryBatchCollisionMass_eq_uniformNonzeroProbability
#print axioms sourceQueryBatchCollisionMass_le
#print axioms deployed_nonzero_query_batch_term_le_two_pow_neg_120

end AspisV6QueryBatchSoundness
