import AspisFormal.V5RelationSumcheckSoundness
import AspisFormal.V5ComponentCRelationRowLinearity

/-!
# The algebraic bridge from one FRI candidate to the Tag-67 relation check

A FRI list decoder is expected to return coefficient vectors.  The Tag-67
relation check does not read such a vector directly: it reads two claimed OOD
values and seven claimed polynomial coefficients in each round.  This file
proves the missing algebra in between for any one supplied coefficient vector.

For one arity-four round, let `values` be the current candidate coefficients
and let `weights` be the verifier's current linear functional.  Two OOD
functionals are mixed into those weights.  Lean proves that:

* the boundary of the resulting degree-six polynomial is the mixed dot
  product before the fold; and
* evaluating that polynomial at `alpha` is the dot product after folding the
  candidate and the weights in the exact dual orders used by Rust.

Consequently the scalar discrepancy equations used by
`V5RelationSumcheckSoundness` are not an extra cryptographic assumption once a
coefficient candidate and the corresponding weight vectors have been
obtained.  The same theorem can be applied at sizes `1024`, `256`, `64`, and
`16` for the four deployed rounds.

The final section proves the exact union bound for a supplied finite family of
candidate strategies: at most `L` candidates cost at most
`32 * L / |K|`.  This validates that piece of the conservative arithmetic.

What remains open is the important part: accepted Merkle/FRI openings have not
yet been proved to produce such a family of at most `240` coefficient
candidates, nor has false Tag-67 acceptance been proved to select one member
of it.  This file also says nothing about hash binding, Fiat--Shamir, Rust
extraction, or the Solana runtime.
-/

namespace AspisV5FriRelationCandidateBridge

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity
open AspisV5RelationSumcheckSoundness

variable {K : Type*} [Field K]

/-! ## One exact arity-four fibre -/

/-- The dual weight fold used by `WeightAccumulator::fold` on a dense fibre.
The order is `[1, alpha^3, alpha^2, alpha] / 4`, dual to the candidate's
natural coefficient fold `[1, alpha, alpha^2, alpha^3]`. -/
def dualWeightFoldValue (alpha : K) (weights : Fin 4 → K) : K :=
  (weights 0 + alpha ^ 3 * weights 1 + alpha ^ 2 * weights 2 +
    alpha * weights 3) / 4

/-- The degree-six polynomial made by one deployed convolution has boundary
equal to the original four-term dot product. -/
theorem relationBoundary_accumulateChunkLinear
    (weights values : Fin 4 → K) (hfour : (4 : K) ≠ 0) :
    relationBoundary (accumulateChunkLinear weights values) =
      ∑ i, values i * weights i := by
  rw [relationBoundary_eq_componentC_boundary, boundaryLinear_apply,
    accumulateChunkLinear_apply]
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_four]
  change 4 * (values 0 * weights 0 / 4 +
      (values 1 * weights 1 + values 2 * weights 2 +
        values 3 * weights 3) / 4) =
    values 0 * weights 0 + values 1 * weights 1 +
      values 2 * weights 2 + values 3 * weights 3
  field_simp [hfour]
  ring

/-- Evaluating the same degree-six convolution is exactly the dot product of
the natural candidate fold and the dual weight fold. -/
theorem relationPolynomial_accumulateChunkLinear_eval
    (alpha : K) (weights values : Fin 4 → K) :
    (relationPolynomial (accumulateChunkLinear weights values)).eval alpha =
      coefficientFoldValue alpha values * dualWeightFoldValue alpha weights := by
  rw [eval_relationPolynomial, accumulateChunkLinear_apply]
  rw [Fin.sum_univ_seven]
  simp [coefficientFoldValue, dualWeightFoldValue]
  change
    values 0 * weights 0 / 4 +
      ((values 0 * weights 3 + values 1 * weights 0) / 4) * alpha +
      ((values 0 * weights 2 + values 1 * weights 3 +
        values 2 * weights 0) / 4) * alpha ^ 2 +
      ((values 0 * weights 1 + values 1 * weights 2 +
        values 2 * weights 3 + values 3 * weights 0) / 4) * alpha ^ 3 +
      ((values 1 * weights 1 + values 2 * weights 2 +
        values 3 * weights 3) / 4) * alpha ^ 4 +
      ((values 2 * weights 1 + values 3 * weights 2) / 4) * alpha ^ 5 +
      (values 3 * weights 1 / 4) * alpha ^ 6 =
    coefficientFoldValue alpha values * dualWeightFoldValue alpha weights
  unfold coefficientFoldValue dualWeightFoldValue
  ring

/-! ## A whole round with any number of fibres -/

/-- Apply the exact dual weight fold independently to every consecutive
four-element fibre. -/
def dualWeightFoldLayer (n : Nat) (alpha : K)
    (weights : Fin (4 * n) → K) : Fin n → K :=
  fun fibre => dualWeightFoldValue alpha
    (fun slot => weights (childIndex fibre slot))

/-- Pairing a fibre number with one of its four slots is exactly the flat
index used by the Rust loops. -/
def fibreSlotEquiv (n : Nat) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))

@[simp] theorem fibreSlotEquiv_apply (n : Nat) (fibre : Fin n) (slot : Fin 4) :
    fibreSlotEquiv n (fibre, slot) = childIndex fibre slot := by
  apply Fin.ext
  simp [fibreSlotEquiv, childIndex]
  omega

/-- The boundary of the complete round polynomial is the current candidate
dot product.  This is the honest counterpart of the verifier's boundary
check. -/
theorem relationBoundary_polynomialForExtension
    (n : Nat) (weights values : Fin (4 * n) → K)
    (hfour : (4 : K) ≠ 0) :
    relationBoundary (polynomialForExtension n weights values) =
      ∑ i, values i * weights i := by
  calc
    relationBoundary (polynomialForExtension n weights values) =
        ∑ fibre : Fin n,
          relationBoundary
            (accumulateChunkLinear
              (fun slot => weights (childIndex fibre slot))
              (fun slot => values (childIndex fibre slot))) := by
      rw [relationBoundary_eq_componentC_boundary,
        polynomialForExtension_apply, map_sum]
      rfl
    _ = ∑ fibre : Fin n, ∑ slot : Fin 4,
          values (childIndex fibre slot) * weights (childIndex fibre slot) := by
      apply Finset.sum_congr rfl
      intro fibre _
      exact relationBoundary_accumulateChunkLinear
        (fun slot => weights (childIndex fibre slot))
        (fun slot => values (childIndex fibre slot)) hfour
    _ = ∑ i, values i * weights i := by
      calc
        (∑ fibre : Fin n, ∑ slot : Fin 4,
            values (childIndex fibre slot) * weights (childIndex fibre slot)) =
            ∑ pair : Fin n × Fin 4,
              values (fibreSlotEquiv n pair) *
                weights (fibreSlotEquiv n pair) := by
          simpa using (Fintype.sum_prod_type (fun pair : Fin n × Fin 4 =>
            values (fibreSlotEquiv n pair) *
              weights (fibreSlotEquiv n pair))).symm
        _ = ∑ i, values i * weights i :=
          (fibreSlotEquiv n).sum_comp (fun i => values i * weights i)

/-- Evaluating the complete round polynomial is the dot product after the
candidate's natural fold and the verifier weight's dual fold. -/
theorem relationPolynomial_polynomialForExtension_eval
    (n : Nat) (alpha : K) (weights values : Fin (4 * n) → K) :
    (relationPolynomial (polynomialForExtension n weights values)).eval alpha =
      ∑ fibre,
        coefficientFoldLayer n alpha values fibre *
          dualWeightFoldLayer n alpha weights fibre := by
  rw [eval_relationPolynomial]
  rw [polynomialForExtension_apply]
  simp only [Finset.sum_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro fibre _
  rw [← eval_relationPolynomial]
  rw [relationPolynomial_accumulateChunkLinear_eval]
  rfl

/-! ## Two OOD mixes and the scalar discrepancy equations -/

/-- Weights after the two OOD functionals have been mixed in, in deployed
order.  The second functional may already depend on the first mix. -/
def mixedWeights {n : Nat}
    (incoming firstOod : Fin (4 * n) → K)
    (secondOod : K → Fin (4 * n) → K)
    (firstMix secondMix : K) : Fin (4 * n) → K :=
  fun i => incoming i + firstMix * firstOod i +
    secondMix * secondOod firstMix i

/-- Honest evaluation of one supplied linear functional on the candidate. -/
def candidateClaim {n : Nat}
    (weights values : Fin n → K) : K :=
  ∑ i, values i * weights i

/-- Mixing two claimed OOD values changes the verifier-minus-candidate
discrepancy exactly by the two claimed-minus-honest value errors. -/
theorem mixed_claim_discrepancy
    {n : Nat}
    (values incoming firstOod : Fin (4 * n) → K)
    (secondOod : K → Fin (4 * n) → K)
    (claimedIncoming claimedFirst : K) (claimedSecond : K → K)
    (firstMix secondMix : K) :
    (claimedIncoming - candidateClaim incoming values) +
        firstMix * (claimedFirst - candidateClaim firstOod values) +
        secondMix *
          (claimedSecond firstMix - candidateClaim (secondOod firstMix) values) =
      (claimedIncoming + firstMix * claimedFirst +
          secondMix * claimedSecond firstMix) -
        candidateClaim
          (mixedWeights incoming firstOod secondOod firstMix secondMix) values := by
  simp only [candidateClaim, mixedWeights, mul_add, Finset.sum_add_distrib]
  have hfirst :
      (∑ x, values x * (firstMix * firstOod x)) =
        firstMix * ∑ x, values x * firstOod x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsecond :
      (∑ x, values x * (secondMix * secondOod firstMix x)) =
        secondMix * ∑ x, values x * secondOod firstMix x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfirst, hsecond]
  ring

/-- The post-mix scalar discrepancy is exactly the claimed incoming boundary
minus the boundary of the candidate's honest degree-six polynomial. -/
theorem mixed_discrepancy_eq_boundary_difference
    {n : Nat}
    (values incoming firstOod : Fin (4 * n) → K)
    (secondOod : K → Fin (4 * n) → K)
    (claimedIncoming claimedFirst : K) (claimedSecond : K → K)
    (firstMix secondMix : K) (hfour : (4 : K) ≠ 0) :
    (claimedIncoming - candidateClaim incoming values) +
        firstMix * (claimedFirst - candidateClaim firstOod values) +
        secondMix *
          (claimedSecond firstMix - candidateClaim (secondOod firstMix) values) =
      (claimedIncoming + firstMix * claimedFirst +
          secondMix * claimedSecond firstMix) -
        relationBoundary
          (polynomialForExtension n
            (mixedWeights incoming firstOod secondOod firstMix secondMix)
            values) := by
  rw [mixed_claim_discrepancy]
  rw [relationBoundary_polynomialForExtension _ _ _ hfour]
  rfl

/-- After alpha, the verifier-minus-candidate discrepancy is exactly the
difference between the claimed polynomial evaluation and the candidate's
folded dot product. -/
theorem evaluation_discrepancy_eq_folded_difference
    {n : Nat} (alpha : K)
    (values weights : Fin (4 * n) → K)
    (claimed : RelationCoefficients K) :
    (relationPolynomial claimed).eval alpha -
        ∑ fibre,
          coefficientFoldLayer n alpha values fibre *
            dualWeightFoldLayer n alpha weights fibre =
      (relationPolynomial claimed).eval alpha -
        (relationPolynomial
          (polynomialForExtension n weights values)).eval alpha := by
  rw [relationPolynomial_polynomialForExtension_eval]

/-! ## A bounded list of candidate strategies -/

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- Union of the twelve-challenge repair events for a supplied finite family
of candidate strategies. -/
noncomputable def boundedCandidateRepairEvent
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (data : Candidate → AdaptiveFixedCandidateFourRounds K) :
    Finset (TwelveRelationChallenges K) := by
  classical
  exact Finset.univ.biUnion fun candidate =>
    adaptiveFixedCandidateRepairEvent (data candidate)

/-- At most `L` candidate strategies occupy at most
`L * 32 * |K|^11` twelve-challenge tuples. -/
theorem boundedCandidateRepairEvent_card_le
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (data : Candidate → AdaptiveFixedCandidateFourRounds K) :
    (boundedCandidateRepairEvent data).card ≤
      Fintype.card Candidate * (32 * Fintype.card K ^ 11) := by
  classical
  unfold boundedCandidateRepairEvent
  calc
    (Finset.univ.biUnion fun candidate =>
        adaptiveFixedCandidateRepairEvent (data candidate)).card ≤
        ∑ candidate : Candidate,
          (adaptiveFixedCandidateRepairEvent (data candidate)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _candidate : Candidate, 32 * Fintype.card K ^ 11 := by
      exact Finset.sum_le_sum fun candidate _ =>
        adaptiveFixedCandidateRepairEvent_card_le (data candidate)
    _ = Fintype.card Candidate * (32 * Fintype.card K ^ 11) := by simp

/-- Exact uniform mass of the supplied candidate-family union. -/
noncomputable def uniformBoundedCandidateRepairProbability
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (data : Candidate → AdaptiveFixedCandidateFourRounds K) : ℚ :=
  (boundedCandidateRepairEvent data).card /
    Fintype.card (TwelveRelationChallenges K)

/-- A supplied family of `L` candidate strategies has uniform repair mass at
most `32 * L / |K|`.  This theorem does not prove that FRI supplies the family
or that accepted Tag-67 proofs lie in its union. -/
theorem uniformBoundedCandidateRepairProbability_le
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (data : Candidate → AdaptiveFixedCandidateFourRounds K) :
    uniformBoundedCandidateRepairProbability data ≤
      (32 * Fintype.card Candidate : ℚ) / Fintype.card K := by
  classical
  let fieldCard := Fintype.card K
  have hcardNat : 0 < fieldCard := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : ℚ) < fieldCard := by exact_mod_cast hcardNat
  have hfull : Fintype.card (TwelveRelationChallenges K) = fieldCard ^ 12 := by
    simp [TwelveRelationChallenges, RelationRoundChallenges, fieldCard]
    ring
  have hevent := boundedCandidateRepairEvent_card_le data
  unfold uniformBoundedCandidateRepairProbability
  rw [hfull]
  change ((boundedCandidateRepairEvent data).card : ℚ) /
      (fieldCard : ℚ) ^ 12 ≤
    (32 * Fintype.card Candidate : ℚ) / (fieldCard : ℚ)
  rw [div_le_iff₀ (pow_pos hcard 12)]
  have heventQ : ((boundedCandidateRepairEvent data).card : ℚ) ≤
      Fintype.card Candidate * (32 * (fieldCard : ℚ) ^ 11) := by
    exact_mod_cast hevent
  calc
    ((boundedCandidateRepairEvent data).card : ℚ) ≤
        Fintype.card Candidate * (32 * (fieldCard : ℚ) ^ 11) := heventQ
    _ = ((32 * Fintype.card Candidate : ℚ) / (fieldCard : ℚ)) *
        (fieldCard : ℚ) ^ 12 := by field_simp

end FiniteField

#print axioms relationBoundary_accumulateChunkLinear
#print axioms relationPolynomial_accumulateChunkLinear_eval
#print axioms relationBoundary_polynomialForExtension
#print axioms relationPolynomial_polynomialForExtension_eval
#print axioms mixed_claim_discrepancy
#print axioms mixed_discrepancy_eq_boundary_difference
#print axioms evaluation_discrepancy_eq_folded_difference
#print axioms boundedCandidateRepairEvent_card_le
#print axioms uniformBoundedCandidateRepairProbability_le

end AspisV5FriRelationCandidateBridge
