import AspisFormal.V5Width19LaneBatchBinding

/-!
# The actual rare event for batching nineteen committed words

The batching challenge does not have to select one coefficient vector that
works for every member of the FRI decoder list.  That would be false whenever
the list contains two different candidates.  The relevant event follows one
deterministically selected response as the batching challenge varies.

For each challenge, the response contains a nearby candidate and the support
on which the combined received word agrees with that candidate.  A response
is bad only when there is no collection of nineteen codewords which:

* agrees with the nineteen received words on that same support; and
* combines to the selected candidate at that challenge.

This file proves the finite root-counting part of the correlated-agreement
argument.  Its one external input is the published curve-decoding statement,
spelled out as `Width19CurveDecodable`.  The result applies to a strategy that
may select a different bad candidate for every challenge, so no decoder-list
factor is introduced here.  Connecting the deployed transcript to such a
pre-challenge strategy remains a separate implementation and Fiat--Shamir
obligation.
-/

namespace AspisV5Width19CorrelatedAgreement

open AspisV5Width19LaneBatchBinding

variable {K Domain Message : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

/-- Regression check for the rejected event definition.  If two decoder-list
candidates differ, one fixed coefficient vector must mismatch at least one of
them.  Therefore an existential mismatch against one fixed vector is not the
rare correlated-agreement failure event. -/
theorem fixed_coefficients_mismatch_one_of_two_distinct_candidates
    (gamma : K) (columns : Width19Coefficients K)
    (left right : Fin 1024 → K) (hne : left ≠ right) :
    combineWidth19Coefficients gamma columns ≠ left ∨
      combineWidth19Coefficients gamma columns ≠ right := by
  by_cases hleft :
      combineWidth19Coefficients gamma columns = left
  · right
    intro hright
    exact hne (hleft.symm.trans hright)
  · exact Or.inl hleft

/-- Pointwise scalar-power combination of nineteen received words. -/
def width19CurveValue
    (lanes : Fin 19 → Domain → K) (gamma : K) (x : Domain) : K :=
  width19Batch (fun lane ↦ lanes lane x) gamma

/-- One deterministic response for every possible nonzero batching
challenge.  The strategy is fixed before the challenge is sampled. -/
structure Width19ProximateStrategy
    (K Domain Message : Type*) where
  candidate : K → Message
  support : K → Finset Domain

/-- The selected candidate agrees with the combined received word on more
than `agreementThreshold` coordinates. -/
def Width19ValidResponse
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (gamma : K) : Prop :=
  agreementThreshold < (strategy.support gamma).card ∧
    ∀ x ∈ strategy.support gamma,
      width19CurveValue lanes gamma x =
        encoder (strategy.candidate gamma) x

/-- Nonzero challenges at which the response is a valid proximity witness. -/
noncomputable def width19GoodChallenges
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message) : Finset K := by
  classical
  exact (Finset.univ.erase 0).filter
    (Width19ValidResponse encoder agreementThreshold lanes strategy)

@[simp] theorem mem_width19GoodChallenges_iff
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (gamma : K) :
    gamma ∈ width19GoodChallenges encoder agreementThreshold lanes strategy ↔
      gamma ≠ 0 ∧
        Width19ValidResponse encoder agreementThreshold lanes strategy gamma := by
  classical
  simp [width19GoodChallenges]

/-- Coordinates where every received lane agrees with its proposed codeword. -/
noncomputable def width19JointAgreementSet
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (components : Fin 19 → Message) : Finset Domain := by
  classical
  exact Finset.univ.filter fun x ↦
    ∀ lane, lanes lane x = encoder (components lane) x

/-- The selected candidate codeword lies on the degree-eighteen curve formed
by nineteen component codewords. -/
def Width19CandidateOnCurve
    (encoder : Message → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (components : Fin 19 → Message) (gamma : K) : Prop :=
  encoder (strategy.candidate gamma) =
    fun x ↦ width19CurveValue
      (fun lane ↦ encoder (components lane)) gamma x

/-- The response has a decomposition into nineteen codewords on its own
agreement support, and those codewords combine to its selected candidate. -/
def HasMatchingWidth19Decomposition
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (gamma : K) : Prop :=
  ∃ components : Fin 19 → Message,
    strategy.support gamma ⊆
      width19JointAgreementSet encoder lanes components ∧
    Width19CandidateOnCurve encoder strategy components gamma

/-- The exact bad response: it is accepted as close, but the selected
candidate has no matching nineteen-lane decomposition on the same support. -/
def Width19BadResponse
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (gamma : K) : Prop :=
  Width19ValidResponse encoder agreementThreshold lanes strategy gamma ∧
    ¬ HasMatchingWidth19Decomposition encoder lanes strategy gamma

/-- Published curve-decoding interface for the degree-eighteen family.  If a
fixed strategy has more than `challengeThreshold` valid nonzero responses,
then more than `18 * |Domain|` selected candidate codewords lie on one
degree-eighteen curve of codewords. -/
def Width19CurveDecodable
    (encoder : Message → Domain → K)
    (agreementThreshold challengeThreshold : Nat) : Prop :=
  ∀ (lanes : Fin 19 → Domain → K)
      (strategy : Width19ProximateStrategy K Domain Message),
    challengeThreshold <
        (width19GoodChallenges encoder agreementThreshold lanes strategy).card →
      ∃ (components : Fin 19 → Message) (selected : Finset K),
        selected ⊆
          width19GoodChallenges encoder agreementThreshold lanes strategy ∧
        18 * Fintype.card Domain < selected.card ∧
        ∀ gamma ∈ selected,
          Width19CandidateOnCurve encoder strategy components gamma

/-! ## Root counting outside joint agreement -/

/-- The nineteen discrepancies at one domain coordinate. -/
def width19CoordinateDiscrepancy
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (components : Fin 19 → Message) (x : Domain) : Fin 19 → K :=
  fun lane ↦ lanes lane x - encoder (components lane) x

theorem width19CoordinateDiscrepancy_ne_zero_of_not_joint
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (components : Fin 19 → Message) (x : Domain)
    (hx : x ∉ width19JointAgreementSet encoder lanes components) :
    width19CoordinateDiscrepancy encoder lanes components x ≠ 0 := by
  classical
  intro hzero
  apply hx
  simp only [width19JointAgreementSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro lane
  have hlane := congrFun hzero lane
  simpa [width19CoordinateDiscrepancy] using sub_eq_zero.mp hlane

theorem width19CurveValue_sub_curveValue
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (components : Fin 19 → Message) (gamma : K) (x : Domain) :
    width19CurveValue lanes gamma x -
        width19CurveValue (fun lane ↦ encoder (components lane)) gamma x =
      width19Batch
        (width19CoordinateDiscrepancy encoder lanes components x) gamma := by
  simp only [width19CurveValue, width19Batch,
    width19CoordinateDiscrepancy]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro lane _hlane
  ring

/-- Nonzero challenges hiding at least one coordinate outside the joint
agreement set. -/
noncomputable def width19ResolvingChallenges
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (components : Fin 19 → Message) : Finset K := by
  classical
  exact (Finset.univ.filter fun x ↦
      x ∉ width19JointAgreementSet encoder lanes components).biUnion fun x ↦
    width19NonzeroCollisionSet
      (width19CoordinateDiscrepancy encoder lanes components x)

/-- Every disagreeing coordinate contributes at most eighteen roots. -/
theorem width19ResolvingChallenges_card_le
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (components : Fin 19 → Message) :
    (width19ResolvingChallenges encoder lanes components).card ≤
      18 * Fintype.card Domain := by
  classical
  let outside := Finset.univ.filter fun x ↦
    x ∉ width19JointAgreementSet encoder lanes components
  have hroot : ∀ x ∈ outside,
      (width19NonzeroCollisionSet
        (width19CoordinateDiscrepancy encoder lanes components x)).card ≤ 18 := by
    intro x hx
    have hxnot : x ∉ width19JointAgreementSet encoder lanes components := by
      simpa [outside] using hx
    exact width19_nonzero_collision_card_le _
      (width19CoordinateDiscrepancy_ne_zero_of_not_joint
        encoder lanes components x hxnot)
  calc
    (width19ResolvingChallenges encoder lanes components).card =
        (outside.biUnion fun x ↦
          width19NonzeroCollisionSet
            (width19CoordinateDiscrepancy encoder lanes components x)).card := by
          rfl
    _ ≤ outside.card * 18 :=
      Finset.card_biUnion_le_card_mul outside _ 18 hroot
    _ ≤ Fintype.card Domain * 18 := by
      gcongr
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = 18 * Fintype.card Domain := by omega

theorem exists_selected_not_width19Resolving
    (encoder : Message → Domain → K)
    (lanes : Fin 19 → Domain → K)
    (components : Fin 19 → Message) (selected : Finset K)
    (hlarge : 18 * Fintype.card Domain < selected.card) :
    ∃ gamma ∈ selected,
      gamma ∉ width19ResolvingChallenges encoder lanes components := by
  classical
  by_contra hnone
  push Not at hnone
  have hsubset : selected ⊆
      width19ResolvingChallenges encoder lanes components := by
    intro gamma hgamma
    exact hnone gamma hgamma
  have := (Finset.card_le_card hsubset).trans
    (width19ResolvingChallenges_card_le encoder lanes components)
  omega

/-- At a non-resolving nonzero challenge, every point in the response support
is a simultaneous agreement point for all nineteen lanes. -/
theorem width19Support_subset_jointAgreement
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (components : Fin 19 → Message) (gamma : K)
    (hgamma : gamma ≠ 0)
    (hvalid : Width19ValidResponse
      encoder agreementThreshold lanes strategy gamma)
    (honcurve : Width19CandidateOnCurve
      encoder strategy components gamma)
    (hresolve : gamma ∉
      width19ResolvingChallenges encoder lanes components) :
    strategy.support gamma ⊆
      width19JointAgreementSet encoder lanes components := by
  classical
  intro x hx
  have hagree := hvalid.2 x hx
  have hcurve := congrFun honcurve x
  by_contra hnotjoint
  have hdelta : width19Batch
      (width19CoordinateDiscrepancy encoder lanes components x) gamma = 0 := by
    rw [← width19CurveValue_sub_curveValue
      encoder lanes components gamma x]
    rw [hagree, hcurve]
    exact sub_self _
  apply hresolve
  simp only [width19ResolvingChallenges, Finset.mem_biUnion]
  refine ⟨x, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnotjoint
  · simp [width19NonzeroCollisionSet, hgamma, hdelta]

/-! ## Bound the selected bad response, not every list member separately -/

/-- Keep exactly the valid responses which lack a matching decomposition. -/
noncomputable def width19BadStrategy
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message) :
    Width19ProximateStrategy K Domain Message := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun gamma ↦
      if Width19BadResponse encoder agreementThreshold lanes strategy gamma
      then strategy.support gamma
      else ∅
  }

/-- The good challenges of the masked strategy are exactly the nonzero bad
responses of the original strategy. -/
theorem mem_width19BadStrategy_good_iff
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (gamma : K) :
    gamma ∈ width19GoodChallenges encoder agreementThreshold lanes
        (width19BadStrategy encoder agreementThreshold lanes strategy) ↔
      gamma ≠ 0 ∧
        Width19BadResponse encoder agreementThreshold lanes strategy gamma := by
  classical
  rw [mem_width19GoodChallenges_iff]
  constructor
  · intro h
    by_cases hbad :
        Width19BadResponse encoder agreementThreshold lanes strategy gamma
    · exact ⟨h.1, hbad⟩
    · have hempty :
          (width19BadStrategy encoder agreementThreshold lanes strategy).support
              gamma = ∅ := by
        simp [width19BadStrategy, hbad]
      have himpossible : agreementThreshold < 0 := by
        simpa only [hempty, Finset.card_empty] using h.2.1
      exact (Nat.not_lt_zero _ himpossible).elim
  · rintro ⟨hgamma, hbad⟩
    refine ⟨hgamma, ?_⟩
    have hsupport :
        (width19BadStrategy encoder agreementThreshold lanes strategy).support
            gamma = strategy.support gamma := by
      simp [width19BadStrategy, hbad]
    constructor
    · rw [hsupport]
      exact hbad.1.1
    · intro x hx
      rw [hsupport] at hx
      change width19CurveValue lanes gamma x =
        encoder (strategy.candidate gamma) x
      exact hbad.1.2 x hx

/-- The nonzero challenges at which a selected valid candidate lacks a
matching nineteen-lane decomposition are bounded by the published
curve-decoding threshold.  The strategy may choose a different candidate at
each challenge; there is no decoder-list union in this theorem. -/
theorem width19_bad_response_challenges_card_le
    (encoder : Message → Domain → K)
    (agreementThreshold challengeThreshold : Nat)
    (hcurve : Width19CurveDecodable
      encoder agreementThreshold challengeThreshold)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message) :
    (width19GoodChallenges encoder agreementThreshold lanes
      (width19BadStrategy encoder agreementThreshold lanes strategy)).card ≤
        challengeThreshold := by
  classical
  by_contra hnot
  have hmany : challengeThreshold <
      (width19GoodChallenges encoder agreementThreshold lanes
        (width19BadStrategy encoder agreementThreshold lanes strategy)).card :=
    Nat.lt_of_not_ge hnot
  obtain ⟨components, selected, hselected, hlarge, honcurve⟩ :=
    hcurve lanes
      (width19BadStrategy encoder agreementThreshold lanes strategy) hmany
  obtain ⟨gamma, hgammaSelected, hgammaResolve⟩ :=
    exists_selected_not_width19Resolving
      encoder lanes components selected hlarge
  have hgood := hselected hgammaSelected
  have hbad :=
    (mem_width19BadStrategy_good_iff encoder agreementThreshold lanes
      strategy gamma).mp hgood
  have hvalidMasked :=
    (mem_width19GoodChallenges_iff encoder agreementThreshold lanes
      (width19BadStrategy encoder agreementThreshold lanes strategy)
      gamma).mp hgood
  have hsubsetMasked := width19Support_subset_jointAgreement
    encoder agreementThreshold lanes
      (width19BadStrategy encoder agreementThreshold lanes strategy)
      components gamma hvalidMasked.1 hvalidMasked.2
      (honcurve gamma hgammaSelected) hgammaResolve
  have hsupport : strategy.support gamma ⊆
      width19JointAgreementSet encoder lanes components := by
    simpa [width19BadStrategy, hbad.2] using hsubsetMasked
  have honcurveOriginal : Width19CandidateOnCurve
      encoder strategy components gamma := by
    simpa [Width19CandidateOnCurve, width19BadStrategy] using
      honcurve gamma hgammaSelected
  exact hbad.2.2 ⟨components, hsupport, honcurveOriginal⟩

/-! ## Coefficient-level consequence for a linear injective encoder -/

/-- Scalar-power combination in the message space. -/
def combineWidth19Messages [AddCommMonoid Message] [Module K Message]
    (gamma : K) (components : Fin 19 → Message) : Message :=
  ∑ lane, gamma ^ lane.val • components lane

/-- A linear encoder maps the message combination to the pointwise codeword
curve used above. -/
theorem linearMap_combineWidth19Messages
    [AddCommMonoid Message] [Module K Message]
    (encoder : Message →ₗ[K] (Domain → K))
    (gamma : K) (components : Fin 19 → Message) :
    encoder (combineWidth19Messages gamma components) =
      fun x ↦ width19CurveValue
        (fun lane ↦ encoder (components lane)) gamma x := by
  funext x
  simp [combineWidth19Messages, width19CurveValue, width19Batch,
    mul_comm]

/-- A matching codeword decomposition determines the selected coefficient
vector when the encoder is linear and injective. -/
theorem candidate_eq_combineWidth19Messages_of_matching
    [AddCommMonoid Message] [Module K Message]
    (encoder : Message →ₗ[K] (Domain → K))
    (hinjective : Function.Injective encoder)
    (lanes : Fin 19 → Domain → K)
    (strategy : Width19ProximateStrategy K Domain Message)
    (gamma : K)
    (hmatching : HasMatchingWidth19Decomposition
      encoder lanes strategy gamma) :
    ∃ components : Fin 19 → Message,
      strategy.support gamma ⊆
          width19JointAgreementSet encoder lanes components ∧
      strategy.candidate gamma = combineWidth19Messages gamma components := by
  obtain ⟨components, hsupport, honcurve⟩ := hmatching
  refine ⟨components, hsupport, hinjective ?_⟩
  exact honcurve.trans
    (linearMap_combineWidth19Messages encoder gamma components).symm

#print axioms width19ResolvingChallenges_card_le
#print axioms fixed_coefficients_mismatch_one_of_two_distinct_candidates
#print axioms exists_selected_not_width19Resolving
#print axioms width19Support_subset_jointAgreement
#print axioms width19_bad_response_challenges_card_le
#print axioms linearMap_combineWidth19Messages
#print axioms candidate_eq_combineWidth19Messages_of_matching

end AspisV5Width19CorrelatedAgreement
