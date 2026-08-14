import AspisFormal.V5FriDegreeThreeCorrelatedAgreement

/-!
# Transporting the published RS decoding theorem to a concrete encoder

The correlated-agreement argument ultimately needs the published
degree-three curve-decoding theorem for the codewords produced by the V5
encoders.  A proof that those encoders use a different coefficient basis from
the usual monomial basis must not create a new mathematical assumption.

This file proves the basis-change step once and for all.  If two message
spaces are in bijection and their encoders produce the same codeword under
that bijection, degree-three curve decodability transfers in both directions.
Thus the remaining literature premise can be stated for the ordinary
Reed--Solomon evaluation code; the concrete V5 basis is handled inside Lean.
-/

namespace AspisV5FriCurveDecodabilityTransport

open AspisV5FriDegreeThreeCorrelatedAgreement

variable {K Domain A B : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

/-- Change only the message chosen by a response strategy.  Its agreement
support, and hence its challenge timing, is unchanged. -/
def mapStrategy (e : A → B) (strategy : ProximateStrategy K Domain A) :
    ProximateStrategy K Domain B where
  candidate z := e (strategy.candidate z)
  support := strategy.support

@[simp] theorem mapStrategy_candidate
    (e : A → B) (strategy : ProximateStrategy K Domain A) (z : K) :
    (mapStrategy e strategy).candidate z = e (strategy.candidate z) :=
  rfl

@[simp] theorem mapStrategy_support
    (e : A → B) (strategy : ProximateStrategy K Domain A) (z : K) :
    (mapStrategy e strategy).support z = strategy.support z :=
  rfl

theorem validResponse_mapStrategy_iff
    (encoderA : A → Domain → K) (encoderB : B → Domain → K)
    (e : A ≃ B) (hencoder : ∀ a, encoderA a = encoderB (e a))
    (agreementThreshold : Nat) (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain A) (z : K) :
    ValidResponse encoderB agreementThreshold lanes (mapStrategy e strategy) z ↔
      ValidResponse encoderA agreementThreshold lanes strategy z := by
  constructor
  · rintro ⟨hcard, hagree⟩
    refine ⟨hcard, ?_⟩
    intro x hx
    simpa only [mapStrategy_support, mapStrategy_candidate, ← hencoder] using
      hagree x hx
  · rintro ⟨hcard, hagree⟩
    refine ⟨hcard, ?_⟩
    intro x hx
    simpa only [mapStrategy_support, mapStrategy_candidate, ← hencoder] using
      hagree x hx

theorem goodChallenges_mapStrategy_eq
    (encoderA : A → Domain → K) (encoderB : B → Domain → K)
    (e : A ≃ B) (hencoder : ∀ a, encoderA a = encoderB (e a))
    (agreementThreshold : Nat) (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain A) :
    goodChallenges encoderB agreementThreshold lanes (mapStrategy e strategy) =
      goodChallenges encoderA agreementThreshold lanes strategy := by
  classical
  apply Finset.ext
  intro z
  rw [mem_goodChallenges_iff, mem_goodChallenges_iff]
  exact validResponse_mapStrategy_iff encoderA encoderB e hencoder
    agreementThreshold lanes strategy z

/-- Degree-three curve decodability is invariant under an exact bijective
change of message basis.  No probability, code-distance, or list-size claim
is used in this transport. -/
theorem degreeThreeCurveDecodable_of_equiv
    (encoderA : A → Domain → K) (encoderB : B → Domain → K)
    (e : A ≃ B) (hencoder : ∀ a, encoderA a = encoderB (e a))
    (agreementThreshold challengeThreshold : Nat)
    (hcurve : DegreeThreeCurveDecodable
      encoderB agreementThreshold challengeThreshold) :
    DegreeThreeCurveDecodable
      encoderA agreementThreshold challengeThreshold := by
  intro lanes strategy hmany
  have hmanyB : challengeThreshold <
      (goodChallenges encoderB agreementThreshold lanes
        (mapStrategy e strategy)).card := by
    rw [goodChallenges_mapStrategy_eq encoderA encoderB e hencoder]
    exact hmany
  obtain ⟨componentsB, selected, hselectedB, hlarge, honcurveB⟩ :=
    hcurve lanes (mapStrategy e strategy) hmanyB
  let componentsA : Fin 4 → A := fun i => e.symm (componentsB i)
  refine ⟨componentsA, selected, ?_, hlarge, ?_⟩
  · rw [← goodChallenges_mapStrategy_eq encoderA encoderB e hencoder]
    exact hselectedB
  · intro z hz
    have hc := honcurveB z hz
    unfold CandidateOnCurve at hc ⊢
    rw [hencoder (strategy.candidate z)]
    change encoderB (e (strategy.candidate z)) = _
    have hc' : encoderB (e (strategy.candidate z)) =
        fun x => curveValue (fun i => encoderB (componentsB i)) z x := by
      simpa only [mapStrategy_candidate] using hc
    rw [hc']
    funext x
    congr 1
    funext i
    rw [hencoder (componentsA i)]
    simp only [componentsA, Equiv.apply_symm_apply]

/-! ## Exact bridge from the real threshold in the published theorem

S-two Theorem 25 states its threshold as a real number `a`, whereas an actual
finite challenge set has a natural-number cardinality.  The correct integer
cap is `floor a`: if an integer cardinality is larger than `floor a`, it is
larger than `a`; conversely `floor a ≤ a` when bounding probability. -/

/-- Real-threshold form of degree-three curve decodability.  This mirrors the
form in S-two Theorem 25: more than `challengeThreshold` selected close
codewords yield a curve containing more than `concurrencyThreshold` of them. -/
def RealThresholdDegreeThreeCurveDecodable
    (encoder : A → Domain → K)
    (agreementThreshold : Nat)
    (challengeThreshold concurrencyThreshold : Real) : Prop :=
  ∀ (lanes : Fin 4 → Domain → K)
      (strategy : ProximateStrategy K Domain A),
    challengeThreshold <
        ((goodChallenges encoder agreementThreshold lanes strategy).card : Real) →
      ∃ (components : Fin 4 → A) (selected : Finset K),
        selected ⊆ goodChallenges encoder agreementThreshold lanes strategy ∧
        concurrencyThreshold < (selected.card : Real) ∧
        ∀ z ∈ selected, CandidateOnCurve encoder strategy components z

/-- Turn the real threshold from the published theorem into the exact finite
bad-set cap consumed by the Lean FRI reduction. -/
theorem degreeThreeCurveDecodable_floor
    (encoder : A → Domain → K) (agreementThreshold : Nat)
    (challengeThreshold concurrencyThreshold : Real)
    (hchallenge : 0 ≤ challengeThreshold)
    (hconcurrency : ((3 * Fintype.card Domain : Nat) : Real) ≤
      concurrencyThreshold)
    (hpublished : RealThresholdDegreeThreeCurveDecodable encoder
      agreementThreshold challengeThreshold concurrencyThreshold) :
    DegreeThreeCurveDecodable encoder agreementThreshold
      ⌊challengeThreshold⌋₊ := by
  intro lanes strategy hmany
  have hmanyReal : challengeThreshold <
      ((goodChallenges encoder agreementThreshold lanes strategy).card : Real) :=
    (Nat.floor_lt hchallenge).mp hmany
  obtain ⟨components, selected, hselected, hlargeReal, honcurve⟩ :=
    hpublished lanes strategy hmanyReal
  have hlargeCast :
      (((3 * Fintype.card Domain : Nat) : Real) < (selected.card : Real)) :=
    hconcurrency.trans_lt hlargeReal
  have hlarge : 3 * Fintype.card Domain < selected.card := by
    exact_mod_cast hlargeCast
  exact ⟨components, selected, hselected, hlarge, honcurve⟩

/-- The integer cap never exceeds the real numerator used by the release's
probability arithmetic. -/
theorem floor_challengeThreshold_le
    (challengeThreshold : Real) (hchallenge : 0 ≤ challengeThreshold) :
    ((⌊challengeThreshold⌋₊ : Nat) : Real) ≤ challengeThreshold :=
  Nat.floor_le hchallenge

/-! ## Audit -/

#print axioms degreeThreeCurveDecodable_of_equiv
#print axioms degreeThreeCurveDecodable_floor

end AspisV5FriCurveDecodabilityTransport
