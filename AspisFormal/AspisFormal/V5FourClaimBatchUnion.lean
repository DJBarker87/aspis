import AspisFormal.V5FunctionalBatching
import AspisFormal.V5RawFinalSecurityAccounting
import AspisFormal.V5Tag67CandidateTraceExtraction

/-!
# Four-claim batching across the fixed candidate list

`V5FunctionalBatching` proves that one fixed nonzero vector of four claim
errors can vanish for at most three values of the batching challenge.  This
file applies that result to the complete initial FRI candidate list.

The candidate list and every four-error vector must be fixed before the
batching challenge is sampled.  Under that condition, a list of at most 240
candidates has at most `3 * 240 = 720` bad challenge values.  For the released
QM31 field, the resulting ideal-uniform probability is below `2^-114`.

This is a mathematical ideal-challenge result.  Showing that the production
transcript samples the challenge after fixing the same candidate records is a
separate Rust/transcript connection.
-/

namespace AspisV5FourClaimBatchUnion

open AspisSoundnessLedger
open AspisV5FunctionalBatching
open AspisV5RawFinalSecurityAccounting
open AspisV5Tag67CandidateTraceExtraction

variable {K Candidate : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Candidate] [DecidableEq Candidate]

/-- Every challenge that hides the nonzero four-claim discrepancy of at least
one fixed candidate.  Candidates with an all-zero discrepancy contribute no
bad challenge values. -/
def candidateBatchCollisionSet
    (discrepancy : Candidate → Fin 4 → K) : Finset K :=
  Finset.univ.biUnion fun candidate =>
    if discrepancy candidate = 0 then ∅
    else collisionSet (discrepancy candidate)

theorem mem_candidateBatchCollisionSet_iff
    (discrepancy : Candidate → Fin 4 → K) (kappa : K) :
    kappa ∈ candidateBatchCollisionSet discrepancy ↔
      ∃ candidate,
        discrepancy candidate ≠ 0 ∧
          batchedDiscrepancy (discrepancy candidate) kappa = 0 := by
  classical
  simp only [candidateBatchCollisionSet, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨candidate, hmember⟩
    by_cases hzero : discrepancy candidate = 0
    · simp [hzero] at hmember
    · exact ⟨candidate, hzero, by simpa [hzero, collisionSet] using hmember⟩
  · rintro ⟨candidate, hnonzero, hbatch⟩
    exact ⟨candidate, by simpa [hnonzero, collisionSet] using hbatch⟩

/-- A fixed candidate family contributes at most three bad challenges per
candidate. -/
theorem candidateBatchCollisionSet_card_le
    (discrepancy : Candidate → Fin 4 → K) :
    (candidateBatchCollisionSet discrepancy).card ≤
      3 * Fintype.card Candidate := by
  classical
  have hroot : ∀ candidate ∈ (Finset.univ : Finset Candidate),
      (if discrepancy candidate = 0 then ∅
        else collisionSet (discrepancy candidate)).card ≤ 3 := by
    intro candidate _
    by_cases hzero : discrepancy candidate = 0
    · simp [hzero]
    · simpa [hzero] using
        (collision_card_le_three (discrepancy candidate) hzero)
  calc
    (candidateBatchCollisionSet discrepancy).card ≤
        (Finset.univ : Finset Candidate).card * 3 :=
      Finset.card_biUnion_le_card_mul _ _ 3 hroot
    _ = 3 * Fintype.card Candidate := by simp [Nat.mul_comm]

/-- Exact rational mass under a uniform batching challenge. -/
def uniformCandidateBatchCollisionProbability
    (discrepancy : Candidate → Fin 4 → K) : Rat :=
  (candidateBatchCollisionSet discrepancy).card / Fintype.card K

theorem uniformCandidateBatchCollisionProbability_le
    (discrepancy : Candidate → Fin 4 → K) :
    uniformCandidateBatchCollisionProbability discrepancy ≤
      (3 * Fintype.card Candidate : Rat) / Fintype.card K := by
  have hfieldNat : 0 < Fintype.card K :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hfield : (0 : Rat) < Fintype.card K := by
    exact_mod_cast hfieldNat
  rw [uniformCandidateBatchCollisionProbability,
    div_le_div_iff_of_pos_right hfield]
  exact_mod_cast candidateBatchCollisionSet_card_le discrepancy

theorem uniformCandidateBatchCollisionProbability_le_720
    (discrepancy : Candidate → Fin 4 → K)
    (hcandidates : Fintype.card Candidate ≤ 240) :
    uniformCandidateBatchCollisionProbability discrepancy ≤
      (720 : Rat) / Fintype.card K := by
  calc
    uniformCandidateBatchCollisionProbability discrepancy ≤
        (3 * Fintype.card Candidate : Rat) / Fintype.card K :=
      uniformCandidateBatchCollisionProbability_le discrepancy
    _ ≤ (720 : Rat) / Fintype.card K := by
      have hfield : (0 : Rat) ≤ Fintype.card K := by positivity
      apply div_le_div_of_nonneg_right _ hfield
      exact_mod_cast Nat.mul_le_mul_left 3 hcandidates

/-! ## The exact candidate-record event -/

/-- Candidate records may be written as a function of the future challenge so
that the causality condition can be stated and checked explicitly. -/
def CandidateRecordsFixedBeforeKappa
    (records : K → Candidate → CandidateSemanticRecord K) : Prop :=
  ∀ kappa₁ kappa₂ candidate,
    (records kappa₁ candidate).fourClaimDiscrepancy =
      (records kappa₂ candidate).fourClaimDiscrepancy

/-- Every candidate record must carry the challenge at which it is being
evaluated. -/
def CandidateRecordsCarryKappa
    (records : K → Candidate → CandidateSemanticRecord K) : Prop :=
  ∀ kappa candidate, (records kappa candidate).kappa = kappa

noncomputable def recordBatchCollisionSet
    (records : K → Candidate → CandidateSemanticRecord K) : Finset K := by
  classical
  exact Finset.univ.filter fun kappa =>
    ∃ candidate, FourClaimBatchCollision (records kappa candidate)

theorem recordBatchCollisionSet_eq_candidateBatchCollisionSet
    (records : K → Candidate → CandidateSemanticRecord K)
    (hfixed : CandidateRecordsFixedBeforeKappa records)
    (hcarries : CandidateRecordsCarryKappa records)
    (referenceKappa : K) :
    recordBatchCollisionSet records =
      candidateBatchCollisionSet
        (fun candidate =>
          (records referenceKappa candidate).fourClaimDiscrepancy) := by
  classical
  ext kappa
  simp only [recordBatchCollisionSet, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_candidateBatchCollisionSet_iff,
    FourClaimBatchCollision]
  constructor
  · rintro ⟨candidate, hnonzero, hbatch⟩
    refine ⟨candidate, ?_, ?_⟩
    · simpa only [← hfixed kappa referenceKappa candidate] using hnonzero
    · simpa only [hfixed kappa referenceKappa candidate,
        hcarries kappa candidate] using hbatch
  · rintro ⟨candidate, hnonzero, hbatch⟩
    refine ⟨candidate, ?_, ?_⟩
    · simpa only [hfixed kappa referenceKappa candidate] using hnonzero
    · rw [hfixed kappa referenceKappa candidate, hcarries kappa candidate]
      exact hbatch

theorem recordBatchCollisionSet_card_le_720
    (records : K → Candidate → CandidateSemanticRecord K)
    (hfixed : CandidateRecordsFixedBeforeKappa records)
    (hcarries : CandidateRecordsCarryKappa records)
    (hcandidates : Fintype.card Candidate ≤ 240)
    (referenceKappa : K) :
    (recordBatchCollisionSet records).card ≤ 720 := by
  rw [recordBatchCollisionSet_eq_candidateBatchCollisionSet records hfixed
    hcarries referenceKappa]
  exact (candidateBatchCollisionSet_card_le
    (fun candidate =>
      (records referenceKappa candidate).fourClaimDiscrepancy)).trans (by
        omega)

/-- For the released field cardinality, `720 / |QM31|` is below `2^-114`. -/
theorem qm31_candidate_batch_collision_le_two_pow_neg_114 :
    (720 : Real) / FIELD ≤ (1 : Real) / 2 ^ 114 := by
  unfold FIELD
  norm_num

/-- The ideal-uniform contribution of four-claim batching across all 240
candidates. -/
noncomputable def rawFourClaimBatchCollisionBound : Real :=
  (720 : Real) / FIELD

theorem rawFourClaimBatchCollisionBound_le_two_pow_neg_114 :
    rawFourClaimBatchCollisionBound ≤ (1 : Real) / 2 ^ 114 := by
  exact qm31_candidate_batch_collision_le_two_pow_neg_114

/-- Adding the complete 240-candidate batching term does not change the
conservative 75-bit raw ideal bound. -/
theorem raw_core_plus_four_claim_batch_le_two_pow_neg_75 :
    rawCoreSubtotal + rawFourClaimBatchCollisionBound ≤
      (1 : Real) / 2 ^ 75 := by
  have hquery := raw_q18_bound_le_two_pow_neg_79
  have hfri0 := raw_fri_round_zero_le_three_mul_two_pow_neg_77
  have hfri1 : rawFriFibreBound 1 ≤ (1 : Real) / 2 ^ 78 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (1 : Fin 4))
  have hfri2 : rawFriFibreBound 2 ≤ (1 : Real) / 2 ^ 82 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (2 : Fin 4))
  have hfri3 : rawFriFibreBound 3 ≤ (1 : Real) / 2 ^ 88 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (3 : Fin 4))
  have hrelation := raw_relation_repair_bound_le_two_pow_neg_111
  have hbatch := rawFourClaimBatchCollisionBound_le_two_pow_neg_114
  norm_num [rawCoreSubtotal] at hquery hfri0 hfri1 hfri2 hfri3 hrelation hbatch ⊢
  linarith

/-! ## Audit -/

#print axioms mem_candidateBatchCollisionSet_iff
#print axioms candidateBatchCollisionSet_card_le
#print axioms uniformCandidateBatchCollisionProbability_le_720
#print axioms recordBatchCollisionSet_eq_candidateBatchCollisionSet
#print axioms recordBatchCollisionSet_card_le_720
#print axioms qm31_candidate_batch_collision_le_two_pow_neg_114
#print axioms raw_core_plus_four_claim_batch_le_two_pow_neg_75

end AspisV5FourClaimBatchUnion
