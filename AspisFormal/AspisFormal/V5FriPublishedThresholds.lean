import AspisFormal.V5FriListCap

/-!
# Exact V5 side conditions for the published curve-decoding theorem

S-two Theorem 25 applies only in its stated Johnson interval.  This file
checks that interval for each of the four *output* Reed--Solomon codes used by
the V5 radix-four folds, including the final `4 -> 2048` code that is not one
of the committed-layer list calculations in `V5FriListCap`.

It also defines the exact real challenge and concurrency thresholds from the
published formula with curve degree `M = 3`.  These are mathematical
numerators, before division by the challenge-field size and the recorded work
factor.
-/

namespace AspisV5FriPublishedThresholds

open AspisV5FriListCap

/-- Distance complements `(k-1)/N` of the four output RS codes. -/
noncomputable def round0Rate : Real := 255 / 131072
noncomputable def round1Rate : Real := 63 / 32768
noncomputable def round2Rate : Real := 15 / 8192
noncomputable def round3Rate : Real := 3 / 2048

/-- Common required agreement fraction. -/
noncomputable def requiredAgreement : Real :=
  (21 / 20) * Real.sqrt (1 / 512)

noncomputable def proximity (rate : Real) : Real := 1 - requiredAgreement
noncomputable def distance (rate : Real) : Real := 1 - rate

private theorem sqrt_base_sq :
    Real.sqrt (1 / 512 : Real) ^ 2 = 1 / 512 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_base_pos : 0 < Real.sqrt (1 / 512 : Real) :=
  Real.sqrt_pos.2 (by norm_num)

private theorem rate0_sqrt_sq : Real.sqrt round0Rate ^ 2 = round0Rate :=
  Real.sq_sqrt (by norm_num [round0Rate])

private theorem rate1_sqrt_sq : Real.sqrt round1Rate ^ 2 = round1Rate :=
  Real.sq_sqrt (by norm_num [round1Rate])

private theorem rate2_sqrt_sq : Real.sqrt round2Rate ^ 2 = round2Rate :=
  Real.sq_sqrt (by norm_num [round2Rate])

private theorem rate3_sqrt_sq : Real.sqrt round3Rate ^ 2 = round3Rate :=
  Real.sq_sqrt (by norm_num [round3Rate])

private theorem rate0_sqrt_pos : 0 < Real.sqrt round0Rate :=
  Real.sqrt_pos.2 (by norm_num [round0Rate])

private theorem rate1_sqrt_pos : 0 < Real.sqrt round1Rate :=
  Real.sqrt_pos.2 (by norm_num [round1Rate])

private theorem rate2_sqrt_pos : 0 < Real.sqrt round2Rate :=
  Real.sqrt_pos.2 (by norm_num [round2Rate])

private theorem rate3_sqrt_pos : 0 < Real.sqrt round3Rate :=
  Real.sqrt_pos.2 (by norm_num [round3Rate])

theorem sqrt_rate_lt_requiredAgreement :
    Real.sqrt round0Rate < requiredAgreement ∧
      Real.sqrt round1Rate < requiredAgreement ∧
      Real.sqrt round2Rate < requiredAgreement ∧
      Real.sqrt round3Rate < requiredAgreement := by
  have hb := sqrt_base_sq
  have hbp := sqrt_base_pos
  have h0 := rate0_sqrt_sq
  have h0p := rate0_sqrt_pos
  have h1 := rate1_sqrt_sq
  have h1p := rate1_sqrt_pos
  have h2 := rate2_sqrt_sq
  have h2p := rate2_sqrt_pos
  have h3 := rate3_sqrt_sq
  have h3p := rate3_sqrt_pos
  unfold requiredAgreement round0Rate round1Rate round2Rate round3Rate at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem requiredAgreement_le_half_one_add_rate :
    requiredAgreement ≤ (1 + round0Rate) / 2 ∧
      requiredAgreement ≤ (1 + round1Rate) / 2 ∧
      requiredAgreement ≤ (1 + round2Rate) / 2 ∧
      requiredAgreement ≤ (1 + round3Rate) / 2 := by
  have hb := sqrt_base_sq
  have hbp := sqrt_base_pos
  unfold requiredAgreement round0Rate round1Rate round2Rate round3Rate at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Every output code is in the exact Johnson interval required by S-two
Theorem 25: `delta/2 <= theta < 1 - sqrt(1-delta)`. -/
theorem all_rounds_in_published_johnson_interval :
    distance round0Rate / 2 ≤ proximity round0Rate ∧
      proximity round0Rate < 1 - Real.sqrt round0Rate ∧
    distance round1Rate / 2 ≤ proximity round1Rate ∧
      proximity round1Rate < 1 - Real.sqrt round1Rate ∧
    distance round2Rate / 2 ≤ proximity round2Rate ∧
      proximity round2Rate < 1 - Real.sqrt round2Rate ∧
    distance round3Rate / 2 ≤ proximity round3Rate ∧
      proximity round3Rate < 1 - Real.sqrt round3Rate := by
  rcases sqrt_rate_lt_requiredAgreement with ⟨hs0, hs1, hs2, hs3⟩
  rcases requiredAgreement_le_half_one_add_rate with ⟨ha0, ha1, ha2, ha3⟩
  unfold distance proximity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem listCapAgreement_eq :
    AspisV5FriListCap.agreement = requiredAgreement := by
  simp [AspisV5FriListCap.agreement, AspisV5FriListCap.circleRate,
    requiredAgreement]

/-- The final output code's multiplicity ratio is at most three, so the
published formula's explicit lower bound selects `m = 3`. -/
theorem final_multiplicity_ratio_le_three :
    AspisV5FriListCap.multiplicityRatio round3Rate ≤ 3 := by
  have hden : 0 < 2 *
      (AspisV5FriListCap.agreement - Real.sqrt round3Rate) := by
    have hs := sqrt_rate_lt_requiredAgreement.2.2.2
    rw [listCapAgreement_eq]
    exact (show
      0 < 2 * (requiredAgreement - Real.sqrt round3Rate) by linarith)
  rw [show AspisV5FriListCap.multiplicityRatio round3Rate =
      Real.sqrt round3Rate /
        (2 * (AspisV5FriListCap.agreement - Real.sqrt round3Rate)) by rfl]
  rw [div_le_iff₀ hden]
  have hb := sqrt_base_sq
  have hbp := sqrt_base_pos
  have h3 := rate3_sqrt_sq
  have h3p := rate3_sqrt_pos
  rw [listCapAgreement_eq] at hden ⊢
  unfold requiredAgreement round3Rate at *
  nlinarith

theorem final_multiplicity :
    AspisV5FriListCap.multiplicity round3Rate = 3 := by
  have hratioNonneg :
      0 ≤ AspisV5FriListCap.multiplicityRatio round3Rate := by
    unfold AspisV5FriListCap.multiplicityRatio
    have hnum : 0 ≤ Real.sqrt round3Rate := Real.sqrt_nonneg _
    have hden : 0 < 2 *
        (AspisV5FriListCap.agreement - Real.sqrt round3Rate) := by
      have hs := sqrt_rate_lt_requiredAgreement.2.2.2
      rw [listCapAgreement_eq]
      exact (show
        0 < 2 * (requiredAgreement - Real.sqrt round3Rate) by linarith)
    positivity
  have hceil :
      ⌈AspisV5FriListCap.multiplicityRatio round3Rate⌉₊ ≤ 3 := by
    exact (Nat.ceil_le).2 final_multiplicity_ratio_le_three
  unfold AspisV5FriListCap.multiplicity
  omega

/-- Multiplicities for the four output codes in fold order. -/
theorem output_multiplicities :
    AspisV5FriListCap.multiplicity round0Rate = 10 ∧
      AspisV5FriListCap.multiplicity round1Rate = 9 ∧
      AspisV5FriListCap.multiplicity round2Rate = 6 ∧
      AspisV5FriListCap.multiplicity round3Rate = 3 := by
  rcases AspisV5FriListCap.deployed_multiplicities with
    ⟨_circle, h0, h1, h2⟩
  simpa only [round0Rate, round1Rate, round2Rate,
    AspisV5FriListCap.lineRate0, AspisV5FriListCap.lineRate1,
    AspisV5FriListCap.lineRate2] using
    And.intro h0 (And.intro h1 (And.intro h2 final_multiplicity))

/-- Guruswami--Sudan list-size expression for a selected multiplicity `m`. -/
noncomputable def ell (m : Nat) (rate : Real) : Real :=
  ((m : Real) + 1 / 2) / Real.sqrt rate

/-- Concurrency number selected in Theorem 25 for cubic (`M=3`) curves. -/
noncomputable def concurrencyThreshold
    (m : Nat) (rate : Real) (symbols : Nat) : Real :=
  ((2 * ell m rate ^ 4 / 3) * rate + 1) * 3 * symbols

/-- Challenge threshold `a = ell * b` from Theorem 25. -/
noncomputable def challengeThreshold
    (m : Nat) (rate : Real) (symbols : Nat) : Real :=
  ell m rate * concurrencyThreshold m rate symbols

theorem concurrencyThreshold_ge_three_symbols
    (m : Nat) (rate : Real) (symbols : Nat) (hrate : 0 ≤ rate) :
    (3 * symbols : Nat) ≤ concurrencyThreshold m rate symbols := by
  unfold concurrencyThreshold
  push_cast
  change (3 : Real) * symbols ≤
    (((2 * ell m rate ^ 4 / 3) * rate + 1) * 3) * symbols
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg symbols)
  have hpow : 0 ≤ ell m rate ^ 4 := by positivity
  have hterm : 0 ≤ (2 * ell m rate ^ 4 / 3) * rate := by positivity
  nlinarith

theorem challengeThreshold_nonneg
    (m : Nat) (rate : Real) (symbols : Nat)
    (hrate : 0 < rate) : 0 ≤ challengeThreshold m rate symbols := by
  unfold challengeThreshold concurrencyThreshold ell
  have hsqrt : 0 < Real.sqrt rate := Real.sqrt_pos.2 hrate
  positivity

/-! ## Audit -/

#print axioms all_rounds_in_published_johnson_interval
#print axioms output_multiplicities
#print axioms concurrencyThreshold_ge_three_symbols
#print axioms challengeThreshold_nonneg

end AspisV5FriPublishedThresholds
