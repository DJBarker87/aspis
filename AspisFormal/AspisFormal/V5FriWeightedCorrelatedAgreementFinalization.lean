import AspisFormal.V5FriCoherentCandidateExtraction
import AspisFormal.V5FriDegreeThreeCorrelatedAgreement

/-!
# Consistency-weighted finalization for the four V5 FRI rounds

The FRI reduction does not measure agreement uniformly after the first fold.
It gives each later-domain point the number of still-consistent initial query
fibres above it.  For V5 those weights are bounded by `1`, `4`, `16`, and `64`
on domains of size `131072`, `32768`, `8192`, and `2048`.  In every round the
sum of the weights is exactly the number of consistent initial fibres.

This file proves the elementary finalization step with those weights.  Its only
coding-theory premise is `DegreeThreeCurveDecodable`, the degree-three
curve-decoding statement isolated in
`V5FriDegreeThreeCorrelatedAgreement`.  In particular, it does not assume that
a FRI predecessor exists and it does not assume the negation of a
`FoldReductionFailure` predicate.

The V5 section instantiates the exact prefix weights, domain sizes, and integer
agreement floors.  `V5FriCompatibleCandidateChain` applies the generic
valid-but-unmatched theorem to the concrete interleaved coefficient folds.
What remains external is the curve-decodability theorem for each concrete
output code (and, separately, the code/implementation identifications used
elsewhere in the repository).
-/

namespace AspisV5FriWeightedCorrelatedAgreementFinalization

open AspisV5FriCoherentCandidateExtraction
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5ComponentCConcreteFoldLinearity

variable {K Domain Message : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

/-! ## Generic weighted finalization -/

/-- Integer numerator of the consistency weight carried by a finite support.
The common normalizing denominator is irrelevant to all comparisons below. -/
def weightMass (weight : Domain -> Nat) (support : Finset Domain) : Nat :=
  ∑ x ∈ support, weight x

/-- A response agrees with one codeword on a support whose consistency weight
is strictly larger than `weightThreshold`. -/
def WeightedValidResponse
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K) : Prop :=
  weightThreshold < weightMass weight (strategy.support z) /\
    ∀ x ∈ strategy.support z,
      curveValue lanes z x = encoder (strategy.candidate z) x

/-- The previous-round conclusion with the same consistency weights. -/
def HasWeightedJointAgreement
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K) : Prop :=
  ∃ components : Fin 4 -> Message,
    weightThreshold <
      weightMass weight (jointAgreementSet encoder lanes components)

theorem weightMass_le_scale_mul_card
    (weight : Domain -> Nat) (scale : Nat)
    (hweight : ∀ x, weight x ≤ scale) (support : Finset Domain) :
    weightMass weight support ≤ support.card * scale := by
  unfold weightMass
  calc
    ∑ x ∈ support, weight x ≤ ∑ _x ∈ support, scale := by
      exact Finset.sum_le_sum fun x _hx => hweight x
    _ = support.card * scale := by simp

/-- A large weighted support is an ordinary large support when every point has
weight at most `scale`.  This is the domination step used in S-two Theorem 29. -/
theorem card_large_of_weightMass_large
    (weight : Domain -> Nat) (scale weightThreshold agreementCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (support : Finset Domain)
    (hmass : weightThreshold < weightMass weight support) :
    agreementCap < support.card := by
  have hmul : agreementCap * scale < support.card * scale :=
    lt_of_le_of_lt hcap
      (lt_of_lt_of_le hmass
        (weightMass_le_scale_mul_card weight scale hweight support))
  exact (Nat.mul_lt_mul_right hscale).mp hmul

/-- Mask responses that do not meet the weighted threshold.  The underlying
unweighted curve theorem then sees exactly the weighted-good challenges. -/
noncomputable def maskedStrategy
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) :
    ProximateStrategy K Domain Message := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun z =>
      if WeightedValidResponse encoder weight weightThreshold lanes strategy z
      then strategy.support z
      else ∅
  }

theorem validResponse_masked_iff_weighted
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K) :
    ValidResponse encoder agreementCap lanes
        (maskedStrategy encoder weight weightThreshold lanes strategy) z <->
      WeightedValidResponse encoder weight weightThreshold lanes strategy z := by
  classical
  by_cases hvalid :
      WeightedValidResponse encoder weight weightThreshold lanes strategy z
  · have hsupport :
        (maskedStrategy encoder weight weightThreshold lanes strategy).support z =
          strategy.support z := by
      simp [maskedStrategy, hvalid]
    constructor
    · intro _
      exact hvalid
    · intro _
      unfold ValidResponse
      rw [hsupport]
      exact ⟨card_large_of_weightMass_large weight scale weightThreshold
        agreementCap hscale hweight hcap (strategy.support z) hvalid.1,
        hvalid.2⟩
  · have hsupport :
        (maskedStrategy encoder weight weightThreshold lanes strategy).support z =
          ∅ := by
      simp [maskedStrategy, hvalid]
    constructor
    · intro himpossible
      have : agreementCap < 0 := by
        simpa only [hsupport, Finset.card_empty] using himpossible.1
      exact (Nat.not_lt_zero _ this).elim
    · exact fun h => (hvalid h).elim

/-- The exact good-challenge set for weighted responses.  It is implemented by
masking invalid responses, so the external premise remains the ordinary
degree-three curve-decodability theorem. -/
noncomputable def weightedGoodChallenges
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap : Nat)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) : Finset K :=
  goodChallenges encoder agreementCap lanes
    (maskedStrategy encoder weight weightThreshold lanes strategy)

@[simp] theorem mem_weightedGoodChallenges_iff
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K) :
    z ∈ weightedGoodChallenges encoder weight scale weightThreshold
        agreementCap lanes strategy <->
      WeightedValidResponse encoder weight weightThreshold lanes strategy z := by
  rw [weightedGoodChallenges, mem_goodChallenges_iff]
  exact validResponse_masked_iff_weighted encoder weight scale weightThreshold
    agreementCap hscale hweight hcap lanes strategy z

/-- Weighted version of the Theorem-28/29 finalization.  All selected
challenges come from the weighted-good set, so the support found by the root
argument retains its full consistency weight. -/
theorem hasWeightedJointAgreement_of_many_good
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap challengeThreshold : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementCap challengeThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (hmany : challengeThreshold <
      (weightedGoodChallenges encoder weight scale weightThreshold
        agreementCap lanes strategy).card) :
    HasWeightedJointAgreement encoder weight weightThreshold lanes := by
  classical
  let masked := maskedStrategy encoder weight weightThreshold lanes strategy
  obtain ⟨components, selected, hselected, hlarge, honcurve⟩ :=
    hcurve lanes masked hmany
  obtain ⟨z, hzselected, hzresolve⟩ :=
    exists_selected_not_resolving encoder lanes components selected hlarge
  have hzgood : z ∈ weightedGoodChallenges encoder weight scale
      weightThreshold agreementCap lanes strategy := hselected hzselected
  have hzweighted :
      WeightedValidResponse encoder weight weightThreshold lanes strategy z :=
    (mem_weightedGoodChallenges_iff encoder weight scale weightThreshold
      agreementCap hscale hweight hcap lanes strategy z).mp hzgood
  have hzvalid : ValidResponse encoder agreementCap lanes masked z :=
    (mem_goodChallenges_iff encoder agreementCap lanes masked z).mp hzgood
  have hsubsetMasked := support_subset_jointAgreement
    encoder agreementCap lanes masked components z hzvalid
      (honcurve z hzselected) hzresolve
  have hsubset : strategy.support z ⊆
      jointAgreementSet encoder lanes components := by
    simpa only [masked, maskedStrategy, hzweighted, if_true] using hsubsetMasked
  refine ⟨components, hzweighted.1.trans_le ?_⟩
  exact Finset.sum_le_sum_of_subset hsubset

/-- Contrapositive/cardinality form for a random weighted fold challenge. -/
theorem weightedGoodChallenges_card_le_of_no_jointAgreement
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap challengeThreshold : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementCap challengeThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (hfalse : ¬ HasWeightedJointAgreement
      encoder weight weightThreshold lanes) :
    (weightedGoodChallenges encoder weight scale weightThreshold
      agreementCap lanes strategy).card ≤ challengeThreshold := by
  by_contra hnot
  exact hfalse (hasWeightedJointAgreement_of_many_good
    encoder weight scale weightThreshold agreementCap challengeThreshold
    hscale hweight hcap hcurve lanes strategy (Nat.lt_of_not_ge hnot))

/-- One accepted weighted response either yields the previous-round joint
agreement, or its challenge belongs to the explicit small set fixed by the
response strategy. -/
theorem accepted_weighted_response_is_counted
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap challengeThreshold : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementCap challengeThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K)
    (hvalid : WeightedValidResponse
      encoder weight weightThreshold lanes strategy z) :
    HasWeightedJointAgreement encoder weight weightThreshold lanes ∨
      (z ∈ weightedGoodChallenges encoder weight scale weightThreshold
          agreementCap lanes strategy /\
        (weightedGoodChallenges encoder weight scale weightThreshold
          agreementCap lanes strategy).card ≤ challengeThreshold) := by
  by_cases hprevious :
      HasWeightedJointAgreement encoder weight weightThreshold lanes
  · exact Or.inl hprevious
  · exact Or.inr ⟨
      (mem_weightedGoodChallenges_iff encoder weight scale weightThreshold
        agreementCap hscale hweight hcap lanes strategy z).mpr hvalid,
      weightedGoodChallenges_card_le_of_no_jointAgreement
        encoder weight scale weightThreshold agreementCap challengeThreshold
        hscale hweight hcap hcurve lanes strategy hprevious⟩

/-! ## Valid-but-unmatched challenges

The preceding theorem is the ordinary weighted correlated-agreement statement.
For FRI we need a sharper conclusion: the extracted predecessor must fold at
the *same challenge* to the codeword selected by that response.  The following
version retains the selected challenge from the curve-decoding proof and uses
`CandidateOnCurve` there, so it bounds exactly the valid responses for which no
matching predecessor exists.
-/

variable {Predecessor : Type*}

/-- A response has a previous-layer object that is close under the fixed
prefix weights and whose actual challenge fold is its selected candidate. -/
def HasMatchingPredecessor
    (fold : K -> Predecessor -> Message)
    (previousNear : Predecessor -> Prop)
    (strategy : ProximateStrategy K Domain Message) (z : K) : Prop :=
  ∃ predecessor,
    previousNear predecessor /\
      fold z predecessor = strategy.candidate z

/-- The exact bad event for one FRI reduction: the response is valid, but no
previous-layer object both has the required weighted agreement and folds to
the selected next-layer candidate. -/
def ValidButUnmatched
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (fold : K -> Predecessor -> Message)
    (previousNear : Predecessor -> Prop) (z : K) : Prop :=
  WeightedValidResponse encoder weight weightThreshold lanes strategy z /\
    ¬ HasMatchingPredecessor fold previousNear strategy z

/-- Mask every response except the valid-but-unmatched ones.  Curve decoding
is therefore applied to exactly the event whose cardinality we need. -/
noncomputable def unmatchedStrategy
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (fold : K -> Predecessor -> Message)
    (previousNear : Predecessor -> Prop) :
    ProximateStrategy K Domain Message := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun z =>
      if ValidButUnmatched encoder weight weightThreshold lanes strategy
          fold previousNear z
      then strategy.support z
      else ∅
  }

/-- Challenges at which the response is valid but no matching predecessor
exists.  The definition through `goodChallenges` lets the external theorem be
used without strengthening its interface. -/
noncomputable def unmatchedChallenges
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold agreementCap : Nat)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (fold : K -> Predecessor -> Message)
    (previousNear : Predecessor -> Prop) : Finset K :=
  goodChallenges encoder agreementCap lanes
    (unmatchedStrategy encoder weight weightThreshold lanes strategy
      fold previousNear)

@[simp] theorem mem_unmatchedChallenges_iff
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (fold : K -> Predecessor -> Message)
    (previousNear : Predecessor -> Prop) (z : K) :
    z ∈ unmatchedChallenges encoder weight weightThreshold agreementCap
        lanes strategy fold previousNear <->
      ValidButUnmatched encoder weight weightThreshold lanes strategy
        fold previousNear z := by
  classical
  rw [unmatchedChallenges, mem_goodChallenges_iff]
  by_cases hunmatched : ValidButUnmatched encoder weight weightThreshold
      lanes strategy fold previousNear z
  · have hsupport :
        (unmatchedStrategy encoder weight weightThreshold lanes strategy
          fold previousNear).support z = strategy.support z := by
      simp [unmatchedStrategy, hunmatched]
    constructor
    · exact fun _ => hunmatched
    · intro _
      unfold ValidResponse
      rw [hsupport]
      exact ⟨card_large_of_weightMass_large weight scale weightThreshold
        agreementCap hscale hweight hcap (strategy.support z) hunmatched.1.1,
        hunmatched.1.2⟩
  · have hsupport :
        (unmatchedStrategy encoder weight weightThreshold lanes strategy
          fold previousNear).support z = ∅ := by
      simp [unmatchedStrategy, hunmatched]
    constructor
    · intro himpossible
      have : agreementCap < 0 := by
        simpa only [hsupport, Finset.card_empty] using himpossible.1
      exact (Nat.not_lt_zero _ this).elim
    · exact fun h => (hunmatched h).elim

/-- The valid-but-unmatched set is small.  The two deterministic premises are
exactly what an encoder/fold implementation must establish:

* joint component agreement constructs a previous-layer object with the
  required weighted proximity; and
* a component-codeword curve at `z` means that object's concrete fold equals
  the response candidate at `z`.

No predecessor-existence or `FoldReductionFailure` premise is assumed. -/
theorem unmatchedChallenges_card_le
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap challengeThreshold : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementCap challengeThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (assemble : (Fin 4 -> Message) -> Predecessor)
    (fold : K -> Predecessor -> Message)
    (previousNear : Predecessor -> Prop)
    (hnear : ∀ components,
      weightThreshold <
          weightMass weight (jointAgreementSet encoder lanes components) ->
        previousNear (assemble components))
    (hfold : ∀ components z,
      CandidateOnCurve encoder strategy components z ->
        fold z (assemble components) = strategy.candidate z) :
    (unmatchedChallenges encoder weight weightThreshold agreementCap
      lanes strategy fold previousNear).card ≤ challengeThreshold := by
  classical
  by_contra hnot
  have hmany : challengeThreshold <
      (unmatchedChallenges encoder weight weightThreshold agreementCap
        lanes strategy fold previousNear).card := Nat.lt_of_not_ge hnot
  let masked := unmatchedStrategy encoder weight weightThreshold lanes strategy
    fold previousNear
  obtain ⟨components, selected, hselected, hlarge, honcurve⟩ :=
    hcurve lanes masked hmany
  obtain ⟨z, hzselected, hzresolve⟩ :=
    exists_selected_not_resolving encoder lanes components selected hlarge
  have hzbad : z ∈ unmatchedChallenges encoder weight weightThreshold
      agreementCap lanes strategy fold previousNear := hselected hzselected
  have hzunmatched : ValidButUnmatched encoder weight weightThreshold
      lanes strategy fold previousNear z :=
    (mem_unmatchedChallenges_iff encoder weight scale weightThreshold
      agreementCap hscale hweight hcap lanes strategy fold previousNear z).mp hzbad
  have hzvalid : ValidResponse encoder agreementCap lanes masked z :=
    (mem_goodChallenges_iff encoder agreementCap lanes masked z).mp hzbad
  have hsubsetMasked := support_subset_jointAgreement
    encoder agreementCap lanes masked components z hzvalid
      (honcurve z hzselected) hzresolve
  have hsupport : masked.support z = strategy.support z := by
    simp [masked, unmatchedStrategy, hzunmatched]
  have hsubset : strategy.support z ⊆
      jointAgreementSet encoder lanes components := by
    simpa only [hsupport] using hsubsetMasked
  have hjointMass : weightThreshold <
      weightMass weight (jointAgreementSet encoder lanes components) :=
    hzunmatched.1.1.trans_le (Finset.sum_le_sum_of_subset hsubset)
  have hcurveOriginal : CandidateOnCurve encoder strategy components z := by
    have hc := honcurve z hzselected
    unfold CandidateOnCurve at hc ⊢
    change encoder (strategy.candidate z) = _
    change encoder (strategy.candidate z) = _ at hc
    exact hc
  apply hzunmatched.2
  exact ⟨assemble components, hnear components hjointMass,
    hfold components z hcurveOriginal⟩

/-- Inclusion form used by one round of backward FRI extraction. -/
theorem accepted_weighted_response_has_matching_predecessor_or_counted
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap challengeThreshold : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementCap challengeThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message)
    (assemble : (Fin 4 -> Message) -> Predecessor)
    (fold : K -> Predecessor -> Message)
    (previousNear : Predecessor -> Prop)
    (hnear : ∀ components,
      weightThreshold <
          weightMass weight (jointAgreementSet encoder lanes components) ->
        previousNear (assemble components))
    (hfold : ∀ components z,
      CandidateOnCurve encoder strategy components z ->
        fold z (assemble components) = strategy.candidate z)
    (z : K)
    (hvalid : WeightedValidResponse
      encoder weight weightThreshold lanes strategy z) :
    HasMatchingPredecessor fold previousNear strategy z ∨
      (z ∈ unmatchedChallenges encoder weight weightThreshold agreementCap
          lanes strategy fold previousNear /\
        (unmatchedChallenges encoder weight weightThreshold agreementCap
          lanes strategy fold previousNear).card ≤ challengeThreshold) := by
  by_cases hmatch : HasMatchingPredecessor fold previousNear strategy z
  · exact Or.inl hmatch
  · apply Or.inr
    constructor
    · apply (mem_unmatchedChallenges_iff encoder weight scale weightThreshold
        agreementCap hscale hweight hcap lanes strategy fold previousNear z).mpr
      exact ⟨hvalid, hmatch⟩
    · exact unmatchedChallenges_card_le encoder weight scale weightThreshold
        agreementCap challengeThreshold hscale hweight hcap hcurve lanes strategy
        assemble fold previousNear hnear hfold

/-! ## Exact V5 prefix-consistency weights -/

section V5

variable {F : Type*} [Field F] [Algebra F K]

/-- Number of members of a fixed initial-fibre support above one point of a
projected domain. -/
noncomputable def projectedSupportWeight
    (source : Finset (Fin 131072))
    {D : Type*} [Fintype D] [DecidableEq D]
    (projection : Fin 131072 -> D) (x : D) : Nat :=
  (source.filter fun q => projection q = x).card

/-- The first fold equation only.  This predicate is fixed after `alpha0` and
the first response word have been absorbed, hence before `alpha1`. -/
def Round0Consistent
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (q : Fin 131072) : Prop :=
  circleFoldLayer 131072 (schedule.alpha 0)
      schedule.circleInv2x schedule.circleInv2y transcript.layer0 q =
    transcript.layer1 q

/-- The first two fold equations.  This is fixed before `alpha2`. -/
def Round01Consistent
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (q : Fin 131072) : Prop :=
  Round0Consistent schedule transcript q /\
    lineFoldLayer 32768 (schedule.alpha 1) schedule.line1Inverse
      transcript.layer1 (queryParent1 q) = transcript.layer2 (queryParent1 q)

/-- The first three fold equations.  This is fixed before `alpha3`. -/
def Round012Consistent
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (q : Fin 131072) : Prop :=
  Round01Consistent schedule transcript q /\
    lineFoldLayer 8192 (schedule.alpha 2) schedule.line2Inverse
      transcript.layer2 (queryParent2 q) = transcript.layer3 (queryParent2 q)

noncomputable def beforeRound0Set : Finset (Fin 131072) := Finset.univ

noncomputable def beforeRound1Set
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Finset (Fin 131072) := by
  classical
  exact Finset.univ.filter (Round0Consistent schedule transcript)

noncomputable def beforeRound2Set
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Finset (Fin 131072) := by
  classical
  exact Finset.univ.filter (Round01Consistent schedule transcript)

noncomputable def beforeRound3Set
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Finset (Fin 131072) := by
  classical
  exact Finset.univ.filter (Round012Consistent schedule transcript)

def round0Projection (q : Fin 131072) : Fin 131072 := q
def round1Projection (q : Fin 131072) : Fin 32768 := queryParent1 q
def round2Projection (q : Fin 131072) : Fin 8192 := queryParent2 q
def round3Projection (q : Fin 131072) : Fin 2048 := queryParent3 q

noncomputable def round0Weight
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :=
  projectedSupportWeight beforeRound0Set round0Projection

noncomputable def round1Weight
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :=
  projectedSupportWeight (beforeRound1Set schedule transcript) round1Projection

noncomputable def round2Weight
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :=
  projectedSupportWeight (beforeRound2Set schedule transcript) round2Projection

noncomputable def round3Weight
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :=
  projectedSupportWeight (beforeRound3Set schedule transcript) round3Projection

/-- Fibrewise counting neither loses nor duplicates consistency weight. -/
theorem sum_projectedSupportWeight
    (source : Finset (Fin 131072))
    {D : Type*} [Fintype D] [DecidableEq D]
    (projection : Fin 131072 -> D) :
    ∑ x, projectedSupportWeight source projection x = source.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := projection) (s := source)
    (t := (Finset.univ : Finset D)) (fun q _hq => Finset.mem_univ (projection q))
  simpa only [projectedSupportWeight, Finset.sum_const_zero,
    Finset.sum_attach, Finset.sum_coe_sort] using h.symm

private theorem projectedWeight_le_of_remainder_injective
    {Source Target : Type*} [DecidableEq Source] [DecidableEq Target]
    {scale : Nat} (source : Finset Source) (projection : Source -> Target)
    (remainder : Source -> Fin scale) (x : Target)
    (hinjective : (source.filter fun q => projection q = x : Set Source).InjOn
      remainder) :
    ((source.filter fun q => projection q = x).card) ≤ scale := by
  classical
  calc
    (source.filter fun q => projection q = x).card ≤
        (Finset.univ : Finset (Fin scale)).card := by
      apply Finset.card_le_card_of_injOn remainder
      · intro q _hq
        exact Finset.mem_univ (remainder q)
      · exact hinjective
    _ = scale := by simp

theorem round0Weight_le_one
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    ∀ q, round0Weight schedule transcript q ≤ 1 := by
  classical
  intro q
  unfold round0Weight projectedSupportWeight round0Projection
  have hsub :
      (beforeRound0Set.filter fun x => x = q) ⊆ {q} := by
    intro x hx
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hx).2
  exact (Finset.card_le_card hsub).trans (by simp)

set_option maxRecDepth 10000 in
theorem round1Weight_le_four
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    ∀ x, round1Weight schedule transcript x ≤ 4 := by
  intro x
  unfold round1Weight projectedSupportWeight
  apply projectedWeight_le_of_remainder_injective
    (beforeRound1Set schedule transcript)
    round1Projection (fun q : Fin 131072 => ⟨q.val % 4, by omega⟩) x
  intro a ha b hb hab
  have hdiva : a.val / 4 = x.val := by
    exact congrArg Fin.val (Finset.mem_filter.mp ha).2
  have hdivb : b.val / 4 = x.val := by
    exact congrArg Fin.val (Finset.mem_filter.mp hb).2
  have hmod : a.val % 4 = b.val % 4 := Fin.ext_iff.mp hab
  apply Fin.ext
  omega

set_option maxRecDepth 10000 in
theorem round2Weight_le_sixteen
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    ∀ x, round2Weight schedule transcript x ≤ 16 := by
  intro x
  unfold round2Weight projectedSupportWeight
  apply projectedWeight_le_of_remainder_injective
    (beforeRound2Set schedule transcript)
    round2Projection (fun q : Fin 131072 => ⟨q.val % 16, by omega⟩) x
  intro a ha b hb hab
  have hdiva : a.val / 16 = x.val := by
    exact congrArg Fin.val (Finset.mem_filter.mp ha).2
  have hdivb : b.val / 16 = x.val := by
    exact congrArg Fin.val (Finset.mem_filter.mp hb).2
  have hmod : a.val % 16 = b.val % 16 := Fin.ext_iff.mp hab
  apply Fin.ext
  omega

set_option maxRecDepth 10000 in
theorem round3Weight_le_sixty_four
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    ∀ x, round3Weight schedule transcript x ≤ 64 := by
  intro x
  unfold round3Weight projectedSupportWeight
  apply projectedWeight_le_of_remainder_injective
    (beforeRound3Set schedule transcript)
    round3Projection (fun q : Fin 131072 => ⟨q.val % 64, by omega⟩) x
  intro a ha b hb hab
  have hdiva : a.val / 64 = x.val := by
    exact congrArg Fin.val (Finset.mem_filter.mp ha).2
  have hdivb : b.val / 64 = x.val := by
    exact congrArg Fin.val (Finset.mem_filter.mp hb).2
  have hmod : a.val % 64 = b.val % 64 := Fin.ext_iff.mp hab
  apply Fin.ext
  omega

/-- Each measure has the exact prefix-consistency numerator available before
that round's challenge.  Unlike a full-path indicator, these weights do not
depend on the challenge being bounded or on later responses. -/
theorem v5_prefix_weight_sums
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    (∑ x, round0Weight schedule transcript x) =
        beforeRound0Set.card /\
      (∑ x, round1Weight schedule transcript x) =
        (beforeRound1Set schedule transcript).card /\
      (∑ x, round2Weight schedule transcript x) =
        (beforeRound2Set schedule transcript).card /\
      (∑ x, round3Weight schedule transcript x) =
        (beforeRound3Set schedule transcript).card := by
  exact ⟨sum_projectedSupportWeight beforeRound0Set round0Projection,
    sum_projectedSupportWeight (beforeRound1Set schedule transcript) round1Projection,
    sum_projectedSupportWeight (beforeRound2Set schedule transcript) round2Projection,
    sum_projectedSupportWeight (beforeRound3Set schedule transcript) round3Projection⟩

/-- The projected denominators all equal the initial `131072` query fibres,
and the common numerator threshold `6082` dominates each ordinary agreement
floor after rescaling. -/
theorem v5_weight_scales_and_floors :
    1 * 131072 = 131072 /\
      4 * 32768 = 131072 /\
      16 * 8192 = 131072 /\
      64 * 2048 = 131072 /\
      6082 * 1 ≤ 6082 /\
      1520 * 4 ≤ 6082 /\
      380 * 16 ≤ 6082 /\
      95 * 64 ≤ 6082 := by
  norm_num

private theorem sqrt_rate_sq :
    Real.sqrt (1 / 512 : Real) ^ 2 = 1 / 512 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_rate_nonneg :
    0 ≤ Real.sqrt (1 / 512 : Real) := Real.sqrt_nonneg _

/-- The final `4 -> 2048` code uses agreement floor `95`, completing the four
output-code floors `6082, 1520, 380, 95`. -/
theorem final_output_agreement_floor :
    (95 : Real) ≤ (21 / 20) * Real.sqrt (1 / 512) * 2048 /\
      (21 / 20) * Real.sqrt (1 / 512) * 2048 < 96 := by
  have hs := sqrt_rate_sq
  have hn := sqrt_rate_nonneg
  constructor <;> nlinarith

end V5

/-! ## Axiom audit -/

#print axioms card_large_of_weightMass_large
#print axioms hasWeightedJointAgreement_of_many_good
#print axioms weightedGoodChallenges_card_le_of_no_jointAgreement
#print axioms accepted_weighted_response_is_counted
#print axioms unmatchedChallenges_card_le
#print axioms accepted_weighted_response_has_matching_predecessor_or_counted
#print axioms v5_prefix_weight_sums
#print axioms v5_weight_scales_and_floors
#print axioms final_output_agreement_floor

end AspisV5FriWeightedCorrelatedAgreementFinalization
