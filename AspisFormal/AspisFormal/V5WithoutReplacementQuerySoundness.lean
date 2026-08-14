import Mathlib
import AspisFormal.SoundnessLedger

/-!
# Exact probability of the V5 query sampler's ideal experiment

The V5 verifier requests eighteen distinct query fibres.  This file proves the
finite combinatorial part of that query-phase calculation: if the schedule is
uniform over ordered injections `Fin q ↪ Fin n`, then the probability that all
queries land in a fixed bad set is the ratio of two descending factorials.

At the deployed values, any bad set of at most `6082` fibres therefore has
miss probability at most

`(6082/131072) * (6081/131071) * ... * (6065/131055)`.

The file also checks the existing numeric ratio after division by `2^32` and
provides a conditional theorem for an overall failure probability once a
separate argument establishes that final-work factor.  It does not derive the
work factor from a probability experiment.

This theorem does not identify SHA-256 output with a uniform injection, prove
the Rust rejection sampler has that law, or prove that FRI failure produces a
fixed bad set of size at most `6082`.  Those remain the random-oracle,
implementation-correspondence, and FRI/list-decoding obligations.
-/

namespace AspisV5WithoutReplacementQuerySoundness

/-- An ordered `q`-query schedule without replacement from `n` positions. -/
abbrev QuerySchedule (q n : Nat) := Fin q ↪ Fin n

/-- Every selected query lies in the fixed bad set. -/
def AllQueriesIn {q n : Nat} (bad : Finset (Fin n))
    (schedule : QuerySchedule q n) : Prop :=
  ∀ query, schedule query ∈ bad

/-- The same event represented as an embedding whose codomain is the bad-set
subtype.  This representation has a direct finite-cardinality formula. -/
abbrev MissSchedule {q n : Nat} (bad : Finset (Fin n)) :=
  Fin q ↪ {position : Fin n // position ∈ bad}

/-- Probability in the ideal experiment that samples uniformly from all
ordered injections.  Writing the probability as a finite cardinality ratio
keeps the experiment exact and avoids any independence assumption between the
without-replacement coordinates. -/
noncomputable def idealMissProbability {q n : Nat}
    (bad : Finset (Fin n)) : ℝ := by
  classical
  exact Fintype.card (MissSchedule (q := q) bad) /
    Fintype.card (QuerySchedule q n)

/-- Schedules whose image lies in `bad` are exactly embeddings into the
subtype represented by `bad`. -/
noncomputable def allQueriesInEquiv {q n : Nat} (bad : Finset (Fin n)) :
    {schedule : QuerySchedule q n // AllQueriesIn bad schedule} ≃
      MissSchedule (q := q) bad := by
  classical
  exact Equiv.codRestrict (Fin q) (bad : Set (Fin n))

noncomputable instance allQueriesInFintype {q n : Nat}
    (bad : Finset (Fin n)) :
    Fintype {schedule : QuerySchedule q n // AllQueriesIn bad schedule} := by
  classical
  exact Fintype.ofFinite _

/-- `idealMissProbability` is the cardinality ratio of the event stated using
the original query schedules.  This connects the subtype used for counting
back to `AllQueriesIn`, rather than merely relying on the two descriptions in
prose. -/
theorem ideal_miss_probability_eq_event_card_ratio
    {q n : Nat} (bad : Finset (Fin n)) :
    idealMissProbability (q := q) bad =
      (Fintype.card
        {schedule : QuerySchedule q n // AllQueriesIn bad schedule} : ℝ) /
        Fintype.card (QuerySchedule q n) := by
  classical
  unfold idealMissProbability
  rw [Fintype.card_congr (allQueriesInEquiv (q := q) bad)]

theorem card_miss_schedule {q n : Nat} (bad : Finset (Fin n)) :
    Fintype.card (MissSchedule (q := q) bad) =
      bad.card.descFactorial q := by
  classical
  calc
    Fintype.card (MissSchedule (q := q) bad) =
        (Fintype.card {position : Fin n // position ∈ bad}).descFactorial
          (Fintype.card (Fin q)) := Fintype.card_embedding_eq
    _ = bad.card.descFactorial q := by simp

/-- Exact hypergeometric probability for the ideal ordered sampler. -/
theorem ideal_miss_probability_eq_descFactorial_ratio
    {q n : Nat} (bad : Finset (Fin n)) :
    idealMissProbability (q := q) bad =
      (bad.card.descFactorial q : ℝ) / n.descFactorial q := by
  classical
  unfold idealMissProbability
  rw [card_miss_schedule, Fintype.card_embedding_eq]
  simp

/-- Enlarging the bad set cardinality can only increase the ideal miss
probability, provided the population admits a `q`-query schedule. -/
theorem ideal_miss_probability_mono_card
    {q n cap : Nat} (bad : Finset (Fin n))
    (hcard : bad.card ≤ cap) (hq : q ≤ n) :
    idealMissProbability (q := q) bad ≤
      (cap.descFactorial q : ℝ) / n.descFactorial q := by
  rw [ideal_miss_probability_eq_descFactorial_ratio]
  have hdenNat : 0 < n.descFactorial q :=
    Nat.descFactorial_pos.mpr hq
  have hnumNat : bad.card.descFactorial q ≤ cap.descFactorial q :=
    Nat.descFactorial_le q hcard
  exact div_le_div_of_nonneg_right (by exact_mod_cast hnumNat)
    (by exact_mod_cast hdenNat.le)

/-- The exact deployed cardinality ratio is the eighteen-factor expression
used by `SoundnessLedger.raw_query_miss`. -/
theorem deployed_descFactorial_ratio_eq_product :
    ((((6082 : Nat).descFactorial 18 : Nat) : ℝ) /
        (((131072 : Nat).descFactorial 18 : Nat) : ℝ)) =
      ((6082 : ℝ) / 131072) * (6081 / 131071) * (6080 / 131070) *
        (6079 / 131069) * (6078 / 131068) * (6077 / 131067) *
        (6076 / 131066) * (6075 / 131065) * (6074 / 131064) *
        (6073 / 131063) * (6072 / 131062) * (6071 / 131061) *
        (6070 / 131060) * (6069 / 131059) * (6068 / 131058) *
        (6067 / 131057) * (6066 / 131056) * (6065 / 131055) := by
  norm_num [Nat.descFactorial]

/-- Numeric consequence for the ideal q18 miss ratio divided by `2^32`.

This theorem does not model a work event or prove that its probability is
independent of the query event.  The next theorem exposes that application as
an explicit premise. -/
theorem deployed_q18_ideal_miss_ratio_div_2pow32_le
    (bad : Finset (Fin 131072)) (hcard : bad.card ≤ 6082) :
    idealMissProbability (q := 18) bad / 2 ^ 32 ≤ (1 : ℝ) / 2 ^ 111 := by
  have hmiss := ideal_miss_probability_mono_card (q := 18) (cap := 6082)
    bad hcard (by norm_num)
  rw [deployed_descFactorial_ratio_eq_product] at hmiss
  calc
    idealMissProbability (q := 18) bad / 2 ^ 32 ≤
        (((6082 : ℝ) / 131072) * (6081 / 131071) * (6080 / 131070) *
          (6079 / 131069) * (6078 / 131068) * (6077 / 131067) *
          (6076 / 131066) * (6075 / 131065) * (6074 / 131064) *
          (6073 / 131063) * (6072 / 131062) * (6071 / 131061) *
          (6070 / 131060) * (6069 / 131059) * (6068 / 131058) *
          (6067 / 131057) * (6066 / 131056) * (6065 / 131055)) / 2 ^ 32 :=
      div_le_div_of_nonneg_right hmiss (by positivity)
    _ ≤ (1 : ℝ) / 2 ^ 111 := AspisSoundnessLedger.raw_query_miss

/-- If a separate grinding/random-oracle argument bounds the joint failure
probability by the ideal q18 miss ratio divided by `2^32`, then the joint
failure probability is at most `2^-111`.  The premise is deliberately visible:
this finite counting file does not prove it. -/
theorem deployed_q18_overall_failure_le
    (bad : Finset (Fin 131072)) (hcard : bad.card ≤ 6082)
    (overallFailureProbability : ℝ)
    (workReduction : overallFailureProbability ≤
      idealMissProbability (q := 18) bad / 2 ^ 32) :
    overallFailureProbability ≤ (1 : ℝ) / 2 ^ 111 :=
  workReduction.trans
    (deployed_q18_ideal_miss_ratio_div_2pow32_le bad hcard)

/-! ## With-replacement comparison for a future protocol revision -/

/-- Eighteen independent with-replacement draws would still meet the same
integer `2^-111` query-plus-work target at the deployed cardinalities.  This is
finite arithmetic only; changing V5 would change its transcript and released
proof format. -/
theorem deployed_q18_with_replacement_ratio_div_2pow32_le :
    ((6082 : ℝ) / 131072) ^ 18 / 2 ^ 32 ≤ (1 : ℝ) / 2 ^ 111 := by
  norm_num

/-! ## Axiom audit -/

#print axioms allQueriesInEquiv
#print axioms ideal_miss_probability_eq_event_card_ratio
#print axioms card_miss_schedule
#print axioms ideal_miss_probability_eq_descFactorial_ratio
#print axioms ideal_miss_probability_mono_card
#print axioms deployed_descFactorial_ratio_eq_product
#print axioms deployed_q18_ideal_miss_ratio_div_2pow32_le
#print axioms deployed_q18_overall_failure_le
#print axioms deployed_q18_with_replacement_ratio_div_2pow32_le

end AspisV5WithoutReplacementQuerySoundness
