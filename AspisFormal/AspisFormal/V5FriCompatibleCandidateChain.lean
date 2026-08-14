import AspisFormal.V5FriConcreteEncoderCommutation
import AspisFormal.V5FriWeightedCorrelatedAgreementFinalization

/-!
# What one correlated-agreement witness gives, and what is needed for a chain

This file proves the deterministic algebra needed after an arity-four
correlated-agreement step.

Four message vectors can be put back into one coefficient vector in the exact
fibre-major order used by the verifier.  Their scalar-power combination at the
sampled challenge is then exactly the natural coefficient fold of that vector.
Consequently, joint agreement of four received lanes with four codewords gives
a genuine next-layer codeword on the same support.  This part needs no FRI
soundness assumption.

The file also proves the terminal uniqueness step.  More than `6082` units of
the final projected consistency weight imply more than three agreeing native
positions (in fact more than ninety-five).  Thus the standard degree-three
final-code overlap bound forces the folded coefficients to equal the published
four coefficients.

There is one important limit.  Four *independent* applications of correlated
agreement need not choose compatible intermediate codewords: their large
supports can be different.  Therefore the theorem at the end accepts an
explicit `CompatibleWeightedChain` produced by the prefix-measure,
round-by-round S-two reduction.  It does not replace that premise with four
unrelated `HasWeightedJointAgreement` hypotheses.  The prefix measures must be
fixed before their respective fold challenges.  At the terminal check the
round-three prefix weight is restricted by the final fold-consistency equation;
the weight itself still does not depend on `alpha3` or the published response.
-/

namespace AspisV5FriCompatibleCandidateChain

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriWeightedCorrelatedAgreementFinalization

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-! ## Reassembling the four coefficient lanes -/

/-- Put four length-`n` coefficient lanes back into the verifier's flat,
fibre-major length-`4*n` coefficient vector. -/
def assembleCoefficientLanes {n : Nat}
    (components : Fin 4 -> Fin n -> K) : Fin (4 * n) -> K :=
  fun k => components (slotIndex k) (parentIndex k)

@[simp] theorem assembleCoefficientLanes_childIndex {n : Nat}
    (components : Fin 4 -> Fin n -> K) (i : Fin n) (slot : Fin 4) :
    assembleCoefficientLanes components (childIndex i slot) =
      components slot i := by
  simp [assembleCoefficientLanes]

@[simp] theorem coefficientLane_assembleCoefficientLanes {n : Nat}
    (components : Fin 4 -> Fin n -> K) (slot : Fin 4) :
    coefficientLane (K := K) n slot (assembleCoefficientLanes components) =
      components slot := by
  funext i
  simp

/-- Folding a reassembled vector is pointwise scalar-power combination of its
four component messages. -/
theorem coefficientFoldLayer_assembleCoefficientLanes {n : Nat}
    (components : Fin 4 -> Fin n -> K) (alpha : K) :
    coefficientFoldLayer n alpha (assembleCoefficientLanes components) =
      fun i => coefficientFoldValue alpha (fun slot => components slot i) := by
  funext i
  simp [coefficientFoldLayer_apply]

/-- Linearity of a code encoder turns the natural coefficient fold into the
same degree-three curve of the four encoded component messages. -/
theorem encode_folded_assembled_eq_curve {n m : Nat}
    (encoder : (Fin n -> K) →ₗ[K] (Fin m -> K))
    (components : Fin 4 -> Fin n -> K) (alpha : K) (x : Fin m) :
    encoder
        (coefficientFoldLayer n alpha
          (assembleCoefficientLanes components)) x =
      curveValue (fun slot => encoder (components slot)) alpha x := by
  rw [encoder_coefficientFoldLayer_apply]
  simp only [coefficientLane_assembleCoefficientLanes]
  unfold curveValue AspisV5FunctionalBatching.batchedDiscrepancy
    coefficientFoldValue
  ring

/-- A joint-agreement point therefore gives agreement with the deterministic
folded candidate at the sampled challenge.  No independently selected response
candidate appears in this statement. -/
theorem jointAgreement_implies_folded_candidate_agreement {n m : Nat}
    [Fintype K] [DecidableEq K]
    (encoder : (Fin n -> K) →ₗ[K] (Fin m -> K))
    (lanes : Fin 4 -> Fin m -> K)
    (components : Fin 4 -> Fin n -> K) (alpha : K) (x : Fin m)
    (hx : x ∈ jointAgreementSet encoder lanes components) :
    curveValue lanes alpha x =
      encoder
        (coefficientFoldLayer n alpha
          (assembleCoefficientLanes components)) x := by
  classical
  have hall : ∀ slot, lanes slot x = encoder (components slot) x := by
    simpa [jointAgreementSet] using hx
  rw [encode_folded_assembled_eq_curve]
  unfold curveValue AspisV5FunctionalBatching.batchedDiscrepancy
  change lanes 0 x + lanes 1 x * alpha + lanes 2 x * alpha ^ 2 +
      lanes 3 x * alpha ^ 3 =
    encoder (components 0) x + encoder (components 1) x * alpha +
      encoder (components 2) x * alpha ^ 2 +
        encoder (components 3) x * alpha ^ 3
  rw [hall 0, hall 1, hall 2, hall 3]

/-- The curve selected by correlated agreement is not merely a codeword
identity: injectivity of the next-layer encoder turns it into the exact natural
coefficient-fold equality needed by the backwards FRI chain. -/
theorem fold_assembled_eq_candidate_of_onCurve {n m : Nat}
    [Fintype K] [DecidableEq K]
    (encoder : (Fin n -> K) →ₗ[K] (Fin m -> K))
    (hencoder : Function.Injective encoder)
    (strategy : ProximateStrategy K (Fin m) (Fin n -> K))
    (components : Fin 4 -> Fin n -> K) (z : K)
    (honcurve : CandidateOnCurve encoder strategy components z) :
    coefficientFoldLayer n z (assembleCoefficientLanes components) =
      strategy.candidate z := by
  apply hencoder
  have hfoldCurve :
      encoder
          (coefficientFoldLayer n z
            (assembleCoefficientLanes components)) =
        fun x => curveValue (fun slot => encoder (components slot)) z x := by
    funext x
    exact encode_folded_assembled_eq_curve encoder components z x
  exact hfoldCurve.trans honcurve.symm

/-! ## Count only valid responses with no matching predecessor -/

section Unmatched

variable {Domain Message : Type*}
  [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

/-- A response has a compatible correlated-agreement predecessor when the
four component codewords agree jointly with the received lanes at sufficient
weight and their codeword curve is exactly the selected response codeword. -/
def HasCompatibleWeightedPredecessor
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K) : Prop :=
  ∃ components : Fin 4 -> Message,
    weightThreshold <
      weightMass weight (jointAgreementSet encoder lanes components) /\
    CandidateOnCurve encoder strategy components z

/-- The responses that need to be charged to the fold soundness error: the
response is valid, but no compatible predecessor exists for the codeword it
actually selected. -/
def WeightedUnmatchedResponse
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K) : Prop :=
  WeightedValidResponse encoder weight weightThreshold lanes strategy z /\
    ¬ HasCompatibleWeightedPredecessor
      encoder weight weightThreshold lanes strategy z

/-- Keep precisely the valid-but-unmatched responses.  This is the masking
that makes the correlated-agreement contradiction target the *same* selected
next-layer codeword, rather than merely finding an unrelated predecessor. -/
noncomputable def unmatchedMaskedStrategy
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold : Nat) (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) :
    ProximateStrategy K Domain Message := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun z =>
      if WeightedUnmatchedResponse encoder weight weightThreshold
          lanes strategy z
      then strategy.support z
      else ∅
  }

theorem valid_unmatchedMaskedStrategy_iff
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K) :
    ValidResponse encoder agreementCap lanes
        (unmatchedMaskedStrategy encoder weight weightThreshold lanes strategy) z
      <-> WeightedUnmatchedResponse encoder weight weightThreshold
        lanes strategy z := by
  classical
  by_cases hunmatched : WeightedUnmatchedResponse encoder weight
      weightThreshold lanes strategy z
  · have hsupport :
        (unmatchedMaskedStrategy encoder weight weightThreshold lanes strategy).support z =
          strategy.support z := by
      simp [unmatchedMaskedStrategy, hunmatched]
    constructor
    · intro _
      exact hunmatched
    · intro _
      unfold ValidResponse
      rw [hsupport]
      exact ⟨card_large_of_weightMass_large weight scale weightThreshold
        agreementCap hscale hweight hcap (strategy.support z)
          hunmatched.1.1,
        hunmatched.1.2⟩
  · have hsupport :
        (unmatchedMaskedStrategy encoder weight weightThreshold lanes strategy).support z =
          ∅ := by
      simp [unmatchedMaskedStrategy, hunmatched]
    constructor
    · intro himpossible
      have : agreementCap < 0 := by
        simpa only [hsupport, Finset.card_empty] using himpossible.1
      exact (Nat.not_lt_zero _ this).elim
    · exact fun h => (hunmatched h).elim

/-- The fixed pre-challenge set of valid responses that lack a compatible
predecessor. -/
noncomputable def unmatchedChallenges
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (weightThreshold agreementCap : Nat)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) : Finset K :=
  goodChallenges encoder agreementCap lanes
    (unmatchedMaskedStrategy encoder weight weightThreshold lanes strategy)

@[simp] theorem mem_unmatchedChallenges_iff
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) (z : K) :
    z ∈ unmatchedChallenges encoder weight weightThreshold agreementCap
        lanes strategy <->
      WeightedUnmatchedResponse encoder weight weightThreshold
        lanes strategy z := by
  rw [unmatchedChallenges, mem_goodChallenges_iff]
  exact valid_unmatchedMaskedStrategy_iff encoder weight scale weightThreshold
    agreementCap hscale hweight hcap lanes strategy z

/-- Set-specific correlated agreement bounds the *unmatched* responses, not
all valid responses.  If there were too many, curve decoding would find a
selected response whose own support is a weighted joint-agreement support and
whose own selected codeword lies on that component curve, contradicting its
definition as unmatched. -/
theorem unmatchedChallenges_card_le
    (encoder : Message -> Domain -> K) (weight : Domain -> Nat)
    (scale weightThreshold agreementCap challengeCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementCap challengeCap)
    (lanes : Fin 4 -> Domain -> K)
    (strategy : ProximateStrategy K Domain Message) :
    (unmatchedChallenges encoder weight weightThreshold agreementCap
      lanes strategy).card ≤ challengeCap := by
  classical
  by_contra hnot
  have hmany : challengeCap <
      (unmatchedChallenges encoder weight weightThreshold agreementCap
        lanes strategy).card := Nat.lt_of_not_ge hnot
  let masked := unmatchedMaskedStrategy encoder weight weightThreshold
    lanes strategy
  obtain ⟨components, selected, hselected, hlarge, honcurve⟩ :=
    hcurve lanes masked hmany
  obtain ⟨z, hzselected, hzresolve⟩ :=
    exists_selected_not_resolving encoder lanes components selected hlarge
  have hzgood : z ∈ unmatchedChallenges encoder weight weightThreshold
      agreementCap lanes strategy := hselected hzselected
  have hzunmatched : WeightedUnmatchedResponse encoder weight
      weightThreshold lanes strategy z :=
    (mem_unmatchedChallenges_iff encoder weight scale weightThreshold
      agreementCap hscale hweight hcap lanes strategy z).mp hzgood
  have hzvalid : ValidResponse encoder agreementCap lanes masked z :=
    (mem_goodChallenges_iff encoder agreementCap lanes masked z).mp hzgood
  have hsubsetMasked : masked.support z ⊆
      jointAgreementSet encoder lanes components :=
    support_subset_jointAgreement encoder agreementCap lanes masked components
      z hzvalid (honcurve z hzselected) hzresolve
  have hsubset : strategy.support z ⊆
      jointAgreementSet encoder lanes components := by
    simpa only [masked, unmatchedMaskedStrategy, hzunmatched, if_true] using
      hsubsetMasked
  have hmass : weightThreshold <
      weightMass weight (jointAgreementSet encoder lanes components) :=
    hzunmatched.1.1.trans_le (Finset.sum_le_sum_of_subset hsubset)
  apply hzunmatched.2
  refine ⟨components, hmass, ?_⟩
  unfold CandidateOnCurve at *
  simpa only [masked, unmatchedMaskedStrategy] using honcurve z hzselected

/-! ### Turn codeword-curve compatibility into an exact coefficient fold -/

/-- A previous coefficient vector is both close in the desired previous-round
relation and folds to the response's selected next-layer coefficients. -/
def HasFoldPredecessor {n m : Nat}
    (previousNear : (Fin (4 * n) -> K) -> Prop)
    (strategy : ProximateStrategy K (Fin m) (Fin n -> K)) (z : K) : Prop :=
  ∃ previous : Fin (4 * n) -> K,
    previousNear previous /\
      coefficientFoldLayer n z previous = strategy.candidate z

/-- The valid responses for which the exact coefficient-fold predecessor is
missing. -/
noncomputable def foldUnmatchedChallenges {n m : Nat}
    (encoder : (Fin n -> K) →ₗ[K] (Fin m -> K))
    (weight : Fin m -> Nat) (weightThreshold agreementCap : Nat)
    (lanes : Fin 4 -> Fin m -> K)
    (previousNear : (Fin (4 * n) -> K) -> Prop)
    (strategy : ProximateStrategy K (Fin m) (Fin n -> K)) : Finset K := by
  classical
  exact Finset.univ.filter fun z =>
    WeightedValidResponse encoder weight weightThreshold lanes strategy z /\
      ¬ HasFoldPredecessor previousNear strategy z

@[simp] theorem mem_foldUnmatchedChallenges_iff {n m : Nat}
    (encoder : (Fin n -> K) →ₗ[K] (Fin m -> K))
    (weight : Fin m -> Nat) (weightThreshold agreementCap : Nat)
    (lanes : Fin 4 -> Fin m -> K)
    (previousNear : (Fin (4 * n) -> K) -> Prop)
    (strategy : ProximateStrategy K (Fin m) (Fin n -> K)) (z : K) :
    z ∈ foldUnmatchedChallenges encoder weight weightThreshold agreementCap
        lanes previousNear strategy <->
      WeightedValidResponse encoder weight weightThreshold lanes strategy z /\
        ¬ HasFoldPredecessor previousNear strategy z := by
  simp [foldUnmatchedChallenges]

/-- The exact fold-list-commutation theorem.  Its only non-generic input is
`hprevious`: joint agreement of the four decoded lanes must imply the chosen
previous-round proximity predicate for the reassembled coefficient vector.
For the V5 encoders this is the local radix-four reconstruction/counting lemma.
-/
theorem foldUnmatchedChallenges_card_le {n m : Nat}
    (encoder : (Fin n -> K) →ₗ[K] (Fin m -> K))
    (hencoder : Function.Injective encoder)
    (weight : Fin m -> Nat)
    (scale weightThreshold agreementCap challengeCap : Nat)
    (hscale : 0 < scale) (hweight : ∀ x, weight x ≤ scale)
    (hcap : agreementCap * scale ≤ weightThreshold)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementCap challengeCap)
    (lanes : Fin 4 -> Fin m -> K)
    (previousNear : (Fin (4 * n) -> K) -> Prop)
    (hprevious : ∀ components : Fin 4 -> Fin n -> K,
      weightThreshold <
          weightMass weight (jointAgreementSet encoder lanes components) ->
        previousNear (assembleCoefficientLanes components))
    (strategy : ProximateStrategy K (Fin m) (Fin n -> K)) :
    (foldUnmatchedChallenges encoder weight weightThreshold agreementCap
      lanes previousNear strategy).card ≤ challengeCap := by
  classical
  apply (Finset.card_le_card ?_).trans
    (unmatchedChallenges_card_le encoder weight scale weightThreshold
      agreementCap challengeCap hscale hweight hcap hcurve lanes strategy)
  intro z hz
  rw [mem_foldUnmatchedChallenges_iff] at hz
  rw [mem_unmatchedChallenges_iff encoder weight scale weightThreshold
    agreementCap hscale hweight hcap lanes strategy z]
  refine ⟨hz.1, ?_⟩
  intro hcompatible
  rcases hcompatible with ⟨components, hmass, honcurve⟩
  apply hz.2
  refine ⟨assembleCoefficientLanes components, hprevious components hmass, ?_⟩
  apply hencoder
  have hfoldCurve :
      encoder
          (coefficientFoldLayer n z
            (assembleCoefficientLanes components)) =
        fun x => curveValue (fun slot => encoder (components slot)) z x := by
    funext x
    exact encode_folded_assembled_eq_curve encoder components z x
  exact hfoldCurve.trans honcurve.symm

end Unmatched

/-! ## The four decoded V5 lane families -/

section V5DecodedLanes

variable [Fintype K] [DecidableEq K] [DecidableEq F]

/-- Coefficient lanes obtained by locally decoding each authenticated initial
circle fibre. -/
def circleDecodedLanes
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Fin 4 -> Fin 131072 -> K :=
  fun lane q =>
    radix4Decode
      (algebraMap F K (schedule.circleInv2y q))
      (-algebraMap F K (schedule.circleInv2y q))
      (algebraMap F K (schedule.circleInv2x q))
      (fun slot => transcript.layer0 (childIndex q slot)) lane

/-- Locally decoded lanes of the first committed line word. -/
def line1DecodedLanes
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Fin 4 -> Fin 32768 -> K :=
  fun lane x =>
    radix4Decode
      (algebraMap F K (schedule.line1Inverse x 0))
      (algebraMap F K (schedule.line1Inverse x 1))
      (algebraMap F K (schedule.line1Inverse x 2))
      (fun slot => transcript.layer1 (childIndex x slot)) lane

/-- Locally decoded lanes of the second committed line word. -/
def line2DecodedLanes
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Fin 4 -> Fin 8192 -> K :=
  fun lane x =>
    radix4Decode
      (algebraMap F K (schedule.line2Inverse x 0))
      (algebraMap F K (schedule.line2Inverse x 1))
      (algebraMap F K (schedule.line2Inverse x 2))
      (fun slot => transcript.layer2 (childIndex x slot)) lane

/-- Locally decoded lanes of the third committed line word. -/
def line3DecodedLanes
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Fin 4 -> Fin 2048 -> K :=
  fun lane x =>
    radix4Decode
      (algebraMap F K (schedule.line3Inverse x 0))
      (algebraMap F K (schedule.line3Inverse x 1))
      (algebraMap F K (schedule.line3Inverse x 2))
      (fun slot => transcript.layer3 (childIndex x slot)) lane

theorem curveValue_eq_coefficientFoldValue
    {D : Type*} (lanes : Fin 4 -> D -> K) (z : K) (x : D) :
    curveValue lanes z x =
      coefficientFoldValue z (fun lane => lanes lane x) := by
  unfold curveValue AspisV5FunctionalBatching.batchedDiscrepancy
    coefficientFoldValue
  ring

/-- Decoding and evaluating the four local coefficient lanes is exactly the
deployed circle fold. -/
theorem curve_circleDecodedLanes_eq_circleFold
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (q : Fin 131072) :
    curveValue (circleDecodedLanes schedule transcript)
        (schedule.alpha 0) q =
      circleFoldLayer 131072 (schedule.alpha 0)
        schedule.circleInv2x schedule.circleInv2y transcript.layer0 q := by
  rw [curveValue_eq_coefficientFoldValue, circleFoldLayer_apply]
  symm
  apply circleFoldValue_eq_coefficientFoldValue_decode
    (schedule.alpha 0)
    (algebraMap F K (points.circleX q))
    (algebraMap F K (points.circleY q))
  · exact inverse_identity_ext _ _ (htables.circleX q)
  · exact inverse_identity_ext _ _ (htables.circleY q)

theorem curve_line1DecodedLanes_eq_lineFold
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (x : Fin 32768) :
    curveValue (line1DecodedLanes schedule transcript)
        (schedule.alpha 1) x =
      lineFoldLayer 32768 (schedule.alpha 1) schedule.line1Inverse
        transcript.layer1 x := by
  rw [curveValue_eq_coefficientFoldValue, lineFoldLayer_apply]
  symm
  apply lineFoldValue_eq_coefficientFoldValue_decode
    (schedule.alpha 1)
    (algebraMap F K (points.line1 x 0))
    (algebraMap F K (points.line1 x 1))
    (algebraMap F K (points.line1 x 2))
  · exact inverse_identity_ext _ _ (htables.line1 x 0)
  · exact inverse_identity_ext _ _ (htables.line1 x 1)
  · exact inverse_identity_ext _ _ (htables.line1 x 2)

theorem curve_line2DecodedLanes_eq_lineFold
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (x : Fin 8192) :
    curveValue (line2DecodedLanes schedule transcript)
        (schedule.alpha 2) x =
      lineFoldLayer 8192 (schedule.alpha 2) schedule.line2Inverse
        transcript.layer2 x := by
  rw [curveValue_eq_coefficientFoldValue, lineFoldLayer_apply]
  symm
  apply lineFoldValue_eq_coefficientFoldValue_decode
    (schedule.alpha 2)
    (algebraMap F K (points.line2 x 0))
    (algebraMap F K (points.line2 x 1))
    (algebraMap F K (points.line2 x 2))
  · exact inverse_identity_ext _ _ (htables.line2 x 0)
  · exact inverse_identity_ext _ _ (htables.line2 x 1)
  · exact inverse_identity_ext _ _ (htables.line2 x 2)

theorem curve_line3DecodedLanes_eq_lineFold
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (x : Fin 2048) :
    curveValue (line3DecodedLanes schedule transcript)
        (schedule.alpha 3) x =
      lineFoldLayer 2048 (schedule.alpha 3) schedule.line3Inverse
        transcript.layer3 x := by
  rw [curveValue_eq_coefficientFoldValue, lineFoldLayer_apply]
  symm
  apply lineFoldValue_eq_coefficientFoldValue_decode
    (schedule.alpha 3)
    (algebraMap F K (points.line3 x 0))
    (algebraMap F K (points.line3 x 1))
    (algebraMap F K (points.line3 x 2))
  · exact inverse_identity_ext _ _ (htables.line3 x 0)
  · exact inverse_identity_ext _ _ (htables.line3 x 1)
  · exact inverse_identity_ext _ _ (htables.line3 x 2)

/-! ### Exact local reconstruction -/

theorem circleDecodedLanes_reconstruct
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (q : Fin 131072) :
    radix4Evaluate
        (algebraMap F K (points.circleY q))
        (-algebraMap F K (points.circleY q))
        (algebraMap F K (points.circleX q))
        (fun lane => circleDecodedLanes schedule transcript lane q) =
      fun slot => transcript.layer0 (childIndex q slot) := by
  apply radix4Evaluate_radix4Decode
  · exact inverse_identity_ext _ _ (htables.circleY q)
  · simpa only [neg_mul, mul_neg, neg_neg] using
      (inverse_identity_ext (K := K) _ _ (htables.circleY q))
  · exact inverse_identity_ext _ _ (htables.circleX q)

theorem line1DecodedLanes_reconstruct
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (x : Fin 32768) :
    radix4Evaluate
        (algebraMap F K (points.line1 x 0))
        (algebraMap F K (points.line1 x 1))
        (algebraMap F K (points.line1 x 2))
        (fun lane => line1DecodedLanes schedule transcript lane x) =
      fun slot => transcript.layer1 (childIndex x slot) := by
  apply radix4Evaluate_radix4Decode
  · exact inverse_identity_ext _ _ (htables.line1 x 0)
  · exact inverse_identity_ext _ _ (htables.line1 x 1)
  · exact inverse_identity_ext _ _ (htables.line1 x 2)

theorem line2DecodedLanes_reconstruct
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (x : Fin 8192) :
    radix4Evaluate
        (algebraMap F K (points.line2 x 0))
        (algebraMap F K (points.line2 x 1))
        (algebraMap F K (points.line2 x 2))
        (fun lane => line2DecodedLanes schedule transcript lane x) =
      fun slot => transcript.layer2 (childIndex x slot) := by
  apply radix4Evaluate_radix4Decode
  · exact inverse_identity_ext _ _ (htables.line2 x 0)
  · exact inverse_identity_ext _ _ (htables.line2 x 1)
  · exact inverse_identity_ext _ _ (htables.line2 x 2)

theorem line3DecodedLanes_reconstruct
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K) (x : Fin 2048) :
    radix4Evaluate
        (algebraMap F K (points.line3 x 0))
        (algebraMap F K (points.line3 x 1))
        (algebraMap F K (points.line3 x 2))
        (fun lane => line3DecodedLanes schedule transcript lane x) =
      fun slot => transcript.layer3 (childIndex x slot) := by
  apply radix4Evaluate_radix4Decode
  · exact inverse_identity_ext _ _ (htables.line3 x 0)
  · exact inverse_identity_ext _ _ (htables.line3 x 1)
  · exact inverse_identity_ext _ _ (htables.line3 x 2)

set_option maxHeartbeats 1000000 in
theorem encoder0_assemble_eq_layer0_on_joint
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff1 K) (q : Fin 131072)
    (hjoint : q ∈ jointAgreementSet (encoder1 schedule points)
      (circleDecodedLanes schedule transcript) components) :
    ∀ slot,
      encoder0 schedule points (assembleCoefficientLanes components)
          (childIndex q slot) =
        transcript.layer0 (childIndex q slot) := by
  classical
  have hlanes : ∀ lane,
      circleDecodedLanes schedule transcript lane q =
        encoder1 schedule points (components lane) q := by
    simpa [jointAgreementSet] using hjoint
  intro slot
  calc
    encoder0 schedule points (assembleCoefficientLanes components)
        (childIndex q slot) =
      radix4Evaluate
        (algebraMap F K (points.circleY q))
        (-algebraMap F K (points.circleY q))
        (algebraMap F K (points.circleX q))
        (fun lane => encoder1 schedule points (components lane) q) slot := by
          unfold encoder0 circleLiftEncoder
          rw [radix4LiftEncoder_apply_child]
          simp only [extend1, Pi.neg_apply,
            coefficientLane_assembleCoefficientLanes]
    _ = radix4Evaluate
        (algebraMap F K (points.circleY q))
        (-algebraMap F K (points.circleY q))
        (algebraMap F K (points.circleX q))
        (fun lane => circleDecodedLanes schedule transcript lane q) slot := by
          congr 1
          funext lane
          exact (hlanes lane).symm
    _ = transcript.layer0 (childIndex q slot) := by
      have hreconstruct := congrFun
        (circleDecodedLanes_reconstruct schedule points htables transcript q) slot
      exact hreconstruct

set_option maxHeartbeats 1000000 in
theorem encoder1_assemble_eq_layer1_on_joint
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff2 K) (x : Fin 32768)
    (hjoint : x ∈ jointAgreementSet (encoder2 schedule points)
      (line1DecodedLanes schedule transcript) components) :
    ∀ slot,
      encoder1 schedule points (assembleCoefficientLanes components)
          (childIndex x slot) =
        transcript.layer1 (childIndex x slot) := by
  classical
  have hlanes : ∀ lane,
      line1DecodedLanes schedule transcript lane x =
        encoder2 schedule points (components lane) x := by
    simpa [jointAgreementSet] using hjoint
  intro slot
  calc
    encoder1 schedule points (assembleCoefficientLanes components)
        (childIndex x slot) =
      radix4Evaluate
        (algebraMap F K (points.line1 x 0))
        (algebraMap F K (points.line1 x 1))
        (algebraMap F K (points.line1 x 2))
        (fun lane => encoder2 schedule points (components lane) x) slot := by
          simpa only [encoder1,
            coefficientLane_assembleCoefficientLanes] using
            (radix4LiftEncoder_apply_child (K := K) (n := 64) (m := 32768)
              (encoder2 schedule points)
              (fun i => algebraMap F K (points.line1 i 0))
              (fun i => algebraMap F K (points.line1 i 1))
              (fun i => algebraMap F K (points.line1 i 2))
              (assembleCoefficientLanes components) x slot)
    _ = radix4Evaluate
        (algebraMap F K (points.line1 x 0))
        (algebraMap F K (points.line1 x 1))
        (algebraMap F K (points.line1 x 2))
        (fun lane => line1DecodedLanes schedule transcript lane x) slot := by
          congr 1
          funext lane
          exact (hlanes lane).symm
    _ = transcript.layer1 (childIndex x slot) := by
      have hreconstruct := congrFun
        (line1DecodedLanes_reconstruct schedule points htables transcript x) slot
      exact hreconstruct

set_option maxHeartbeats 1000000 in
theorem encoder2_assemble_eq_layer2_on_joint
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff3 K) (x : Fin 8192)
    (hjoint : x ∈ jointAgreementSet (encoder3 schedule points)
      (line2DecodedLanes schedule transcript) components) :
    ∀ slot,
      encoder2 schedule points (assembleCoefficientLanes components)
          (childIndex x slot) =
        transcript.layer2 (childIndex x slot) := by
  classical
  have hlanes : ∀ lane,
      line2DecodedLanes schedule transcript lane x =
        encoder3 schedule points (components lane) x := by
    simpa [jointAgreementSet] using hjoint
  intro slot
  calc
    encoder2 schedule points (assembleCoefficientLanes components)
        (childIndex x slot) =
      radix4Evaluate
        (algebraMap F K (points.line2 x 0))
        (algebraMap F K (points.line2 x 1))
        (algebraMap F K (points.line2 x 2))
        (fun lane => encoder3 schedule points (components lane) x) slot := by
          simpa only [encoder2,
            coefficientLane_assembleCoefficientLanes] using
            (radix4LiftEncoder_apply_child (K := K) (n := 16) (m := 8192)
              (encoder3 schedule points)
              (fun i => algebraMap F K (points.line2 i 0))
              (fun i => algebraMap F K (points.line2 i 1))
              (fun i => algebraMap F K (points.line2 i 2))
              (assembleCoefficientLanes components) x slot)
    _ = radix4Evaluate
        (algebraMap F K (points.line2 x 0))
        (algebraMap F K (points.line2 x 1))
        (algebraMap F K (points.line2 x 2))
        (fun lane => line2DecodedLanes schedule transcript lane x) slot := by
          congr 1
          funext lane
          exact (hlanes lane).symm
    _ = transcript.layer2 (childIndex x slot) := by
      have hreconstruct := congrFun
        (line2DecodedLanes_reconstruct schedule points htables transcript x) slot
      exact hreconstruct

set_option maxHeartbeats 1000000 in
theorem encoder3_assemble_eq_layer3_on_joint
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff4 K) (x : Fin 2048)
    (hjoint : x ∈ jointAgreementSet (encoder4 schedule)
      (line3DecodedLanes schedule transcript) components) :
    ∀ slot,
      encoder3 schedule points (assembleCoefficientLanes components)
          (childIndex x slot) =
        transcript.layer3 (childIndex x slot) := by
  classical
  have hlanes : ∀ lane,
      line3DecodedLanes schedule transcript lane x =
        encoder4 schedule (components lane) x := by
    simpa [jointAgreementSet] using hjoint
  intro slot
  calc
    encoder3 schedule points (assembleCoefficientLanes components)
        (childIndex x slot) =
      radix4Evaluate
        (algebraMap F K (points.line3 x 0))
        (algebraMap F K (points.line3 x 1))
        (algebraMap F K (points.line3 x 2))
        (fun lane => encoder4 schedule (components lane) x) slot := by
          simpa only [encoder3,
            coefficientLane_assembleCoefficientLanes] using
            (radix4LiftEncoder_apply_child (K := K) (n := 4) (m := 2048)
              (encoder4 schedule)
              (fun i => algebraMap F K (points.line3 i 0))
              (fun i => algebraMap F K (points.line3 i 1))
              (fun i => algebraMap F K (points.line3 i 2))
              (assembleCoefficientLanes components) x slot)
    _ = radix4Evaluate
        (algebraMap F K (points.line3 x 0))
        (algebraMap F K (points.line3 x 1))
        (algebraMap F K (points.line3 x 2))
        (fun lane => line3DecodedLanes schedule transcript lane x) slot := by
          congr 1
          funext lane
          exact (hlanes lane).symm
    _ = transcript.layer3 (childIndex x slot) := by
      have hreconstruct := congrFun
        (line3DecodedLanes_reconstruct schedule points htables transcript x) slot
      exact hreconstruct

end V5DecodedLanes

/-! ## Prefix-weighted proximity relations -/

section PrefixNear

variable [Fintype K] [DecidableEq K] [DecidableEq F]

/-- Counting a projected support with fibre weights is exactly counting the
source points whose projection lies in that support. -/
theorem weightMass_projectedSupportWeight_eq_card
    (source : Finset (Fin 131072))
    {D : Type*} [Fintype D] [DecidableEq D]
    (projection : Fin 131072 -> D) (support : Finset D) :
    weightMass (projectedSupportWeight source projection) support =
      (source.filter fun q => projection q ∈ support).card := by
  classical
  let lifted := source.filter fun q => projection q ∈ support
  have hmaps : Set.MapsTo projection (lifted : Set (Fin 131072))
      (support : Set D) := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hcount := Finset.card_eq_sum_card_fiberwise hmaps
  unfold weightMass projectedSupportWeight
  calc
    (∑ x ∈ support, (source.filter fun q => projection q = x).card) =
        ∑ x ∈ support, (lifted.filter fun q => projection q = x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      ext q
      simp only [lifted, Finset.mem_filter]
      constructor
      · intro h
        exact ⟨⟨h.1, by simpa [h.2] using hx⟩, h.2⟩
      · intro h
        exact ⟨h.1.1, h.2⟩
    _ = lifted.card := hcount.symm
    _ = (source.filter fun q => projection q ∈ support).card := rfl

/-- Prefix agreement with the first committed line word, measured after only
the first fold equation has been absorbed. -/
noncomputable def prefixAgreement1
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (transcript : IdealTranscript K) (candidate : Coeff1 K) :
    Finset (Fin 131072) := by
  classical
  exact (beforeRound1Set schedule transcript).filter fun q =>
    transcript.layer1 q = encoder1 schedule points candidate q

/-- Prefix agreement with the second committed word, lifted to initial query
fibres after the first two fold equations. -/
noncomputable def prefixAgreement2
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (transcript : IdealTranscript K) (candidate : Coeff2 K) :
    Finset (Fin 131072) := by
  classical
  exact (beforeRound2Set schedule transcript).filter fun q =>
    transcript.layer2 (queryParent1 q) =
      encoder2 schedule points candidate (queryParent1 q)

/-- Prefix agreement with the third committed word, lifted to initial query
fibres after the first three fold equations. -/
noncomputable def prefixAgreement3
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (transcript : IdealTranscript K) (candidate : Coeff3 K) :
    Finset (Fin 131072) := by
  classical
  exact (beforeRound3Set schedule transcript).filter fun q =>
    transcript.layer3 (queryParent2 q) =
      encoder3 schedule points candidate (queryParent2 q)

def PrefixNear1
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (transcript : IdealTranscript K) (candidate : Coeff1 K) : Prop :=
  6082 < (prefixAgreement1 schedule points transcript candidate).card

def PrefixNear2
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (transcript : IdealTranscript K) (candidate : Coeff2 K) : Prop :=
  6082 < (prefixAgreement2 schedule points transcript candidate).card

def PrefixNear3
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (transcript : IdealTranscript K) (candidate : Coeff3 K) : Prop :=
  6082 < (prefixAgreement3 schedule points transcript candidate).card

@[simp] theorem parentIndex_query_as_layer1 (q : Fin 131072) :
    parentIndex q = queryParent1 q := by
  apply Fin.ext
  rfl

@[simp] theorem parentIndex_queryParent1 (q : Fin 131072) :
    parentIndex (queryParent1 q) = queryParent2 q := by
  apply Fin.ext
  simp only [parentIndex, queryParent1, queryParent2]
  omega

@[simp] theorem parentIndex_queryParent2 (q : Fin 131072) :
    parentIndex (queryParent2 q) = queryParent3 q := by
  apply Fin.ext
  simp only [parentIndex, queryParent2, queryParent3]
  omega

theorem childIndex_queryParent1_slotIndex (q : Fin 131072) :
    childIndex (queryParent1 q) (slotIndex (n := 32768) q) = q := by
  rw [← parentIndex_query_as_layer1]
  exact childIndex_parentIndex_slotIndex (n := 32768) q

theorem childIndex_queryParent2_slotIndex (q : Fin 131072) :
    childIndex (queryParent2 q) (slotIndex (n := 8192) (queryParent1 q)) =
      queryParent1 q := by
  rw [← parentIndex_queryParent1]
  exact childIndex_parentIndex_slotIndex (n := 8192) (queryParent1 q)

theorem childIndex_queryParent3_slotIndex (q : Fin 131072) :
    childIndex (queryParent3 q) (slotIndex (n := 2048) (queryParent2 q)) =
      queryParent2 q := by
  rw [← parentIndex_queryParent2]
  exact childIndex_parentIndex_slotIndex (n := 2048) (queryParent2 q)

/-- If every four-symbol fibre above `support` is reconstructed by one
codeword, then that codeword has at least four times as many agreeing symbols.
Keeping this lemma polymorphic avoids expanding the concrete V5 domain sizes
inside the finite-set injection proof. -/
theorem four_fibre_reconstruction_card_le {n : Nat}
    (support : Finset (Fin n))
    (received encoded : Fin (4 * n) -> K)
    (hreconstruct : ∀ q ∈ support, ∀ slot : Fin 4,
      encoded (childIndex q slot) = received (childIndex q slot)) :
    support.card * 4 ≤ (agreementSet received encoded).card := by
  classical
  have hinjective : Function.Injective
      (fun pair : Fin n × Fin 4 => childIndex pair.1 pair.2) := by
    intro left right h
    apply Prod.ext
    · have hp := congrArg (parentIndex (n := n)) h
      simpa using hp
    · have hs := congrArg (slotIndex (n := n)) h
      simpa using hs
  calc
    support.card * 4 =
        (support.product (Finset.univ : Finset (Fin 4))).card := by simp
    _ ≤ (agreementSet received encoded).card := by
      apply Finset.card_le_card_of_injOn
        (fun pair : Fin n × Fin 4 => childIndex pair.1 pair.2)
      · intro pair hpair
        have hpair' : pair ∈
            support.product (Finset.univ : Finset (Fin 4)) :=
          Finset.mem_coe.mp hpair
        have hq : pair.1 ∈ support := (Finset.mem_product.mp hpair').1
        apply Finset.mem_coe.mpr
        simpa [agreementSet] using
          (hreconstruct pair.1 hq pair.2).symm
      · intro left _hleft right _hright heq
        exact hinjective heq

/-- Expand a set of initial fibre indices to its four layer-zero symbols. -/
noncomputable def expandInitialFibres (support : Finset (Fin 131072)) :
    Finset (Fin 524288) := by
  classical
  exact (support.product (Finset.univ : Finset (Fin 4))).image fun pair =>
    childIndex pair.1 pair.2

theorem childIndex_pair_injective :
    Function.Injective
      (fun pair : Fin 131072 × Fin 4 =>
        (childIndex pair.1 pair.2 : Fin 524288)) := by
  intro left right h
  apply Prod.ext
  · have hp := congrArg (parentIndex (n := 131072)) h
    simpa using hp
  · have hs := congrArg (slotIndex (n := 131072)) h
    simpa using hs

theorem expandInitialFibres_card (support : Finset (Fin 131072)) :
    (expandInitialFibres support).card = support.card * 4 := by
  classical
  unfold expandInitialFibres
  calc
    (Finset.image
        (fun pair : Fin 131072 × Fin 4 =>
          (childIndex pair.1 pair.2 : Fin 524288))
        (support.product Finset.univ)).card =
      (support.product (Finset.univ : Finset (Fin 4))).card :=
        Finset.card_image_of_injective _ childIndex_pair_injective
    _ = support.card * (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_product support Finset.univ
    _ = support.card * 4 := by simp

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- The first correlated-agreement witness reconstructs an actual initial
codeword on four symbols per jointly agreeing fibre, which is enough for the
deployed initial decoder threshold. -/
theorem joint_circle_weight_implies_Near0
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff1 K)
    (hmass : 6082 <
      weightMass (round0Weight schedule transcript)
        (jointAgreementSet (encoder1 schedule points)
          (circleDecodedLanes schedule transcript) components)) :
    Near0 (concreteCodeEncoders schedule points) transcript
      (assembleCoefficientLanes components) := by
  classical
  let joint := jointAgreementSet (encoder1 schedule points)
    (circleDecodedLanes schedule transcript) components
  have hmass' : 6082 <
      weightMass (round0Weight schedule transcript) joint := by
    simpa only [joint] using hmass
  have hweightEq :
      weightMass (round0Weight schedule transcript) joint = joint.card := by
    unfold weightMass
    calc
      (∑ q ∈ joint, round0Weight schedule transcript q) =
          ∑ _q ∈ joint, 1 := by
        apply Finset.sum_congr rfl
        intro q _hq
        unfold round0Weight projectedSupportWeight
        have hsingleton :
            (beforeRound0Set.filter fun x => round0Projection x = q) = {q} := by
          ext x
          simp [beforeRound0Set, round0Projection]
        rw [hsingleton]
        simp
      _ = joint.card := by simp
  have hjointCard : 6082 < joint.card := by
    rw [hweightEq] at hmass'
    exact hmass'
  have hcardLower : joint.card * 4 ≤
      (agreementSet transcript.layer0
        ((concreteCodeEncoders schedule points).layer0
          (assembleCoefficientLanes components))).card := by
    apply four_fibre_reconstruction_card_le
    intro q hq slot
    exact encoder0_assemble_eq_layer0_on_joint schedule points htables
      transcript components q hq slot
  unfold Near0 agreementCap0
  have hlarge : 24328 < joint.card * 4 := by omega
  exact hlarge.trans_le hcardLower

/-- Joint decoded-lane agreement in round one reconstructs a genuine
prefix-close layer-one coefficient vector. -/
theorem joint_line1_weight_implies_PrefixNear1
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff2 K)
    (hmass : 6082 <
      weightMass (round1Weight schedule transcript)
        (jointAgreementSet (encoder2 schedule points)
          (line1DecodedLanes schedule transcript) components)) :
    PrefixNear1 schedule points transcript
      (assembleCoefficientLanes components) := by
  classical
  let joint := jointAgreementSet (encoder2 schedule points)
    (line1DecodedLanes schedule transcript) components
  let lifted := (beforeRound1Set schedule transcript).filter fun q =>
    queryParent1 q ∈ joint
  have hmassEq :
      weightMass (round1Weight schedule transcript) joint = lifted.card := by
    exact weightMass_projectedSupportWeight_eq_card
      (beforeRound1Set schedule transcript) queryParent1 joint
  have hmass' : 6082 <
      weightMass (round1Weight schedule transcript) joint := by
    simpa only [joint] using hmass
  have hlift : 6082 < lifted.card := by
    rw [hmassEq] at hmass'
    exact hmass'
  have hsubset : lifted ⊆
      prefixAgreement1 schedule points transcript
        (assembleCoefficientLanes components) := by
    intro q hq
    have hqparts := Finset.mem_filter.mp hq
    have hjoint : queryParent1 q ∈ joint := hqparts.2
    have hreconstruct := encoder1_assemble_eq_layer1_on_joint
      schedule points htables transcript components (queryParent1 q)
      hjoint (slotIndex (n := 32768) q)
    rw [childIndex_queryParent1_slotIndex] at hreconstruct
    simp only [prefixAgreement1, Finset.mem_filter]
    exact ⟨hqparts.1, hreconstruct.symm⟩
  unfold PrefixNear1
  exact hlift.trans_le (Finset.card_le_card hsubset)

/-- Joint decoded-lane agreement in round two reconstructs a genuine
prefix-close layer-two coefficient vector. -/
theorem joint_line2_weight_implies_PrefixNear2
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff3 K)
    (hmass : 6082 <
      weightMass (round2Weight schedule transcript)
        (jointAgreementSet (encoder3 schedule points)
          (line2DecodedLanes schedule transcript) components)) :
    PrefixNear2 schedule points transcript
      (assembleCoefficientLanes components) := by
  classical
  let joint := jointAgreementSet (encoder3 schedule points)
    (line2DecodedLanes schedule transcript) components
  let lifted := (beforeRound2Set schedule transcript).filter fun q =>
    queryParent2 q ∈ joint
  have hmassEq :
      weightMass (round2Weight schedule transcript) joint = lifted.card := by
    exact weightMass_projectedSupportWeight_eq_card
      (beforeRound2Set schedule transcript) queryParent2 joint
  have hmass' : 6082 <
      weightMass (round2Weight schedule transcript) joint := by
    simpa only [joint] using hmass
  have hlift : 6082 < lifted.card := by
    rw [hmassEq] at hmass'
    exact hmass'
  have hsubset : lifted ⊆
      prefixAgreement2 schedule points transcript
        (assembleCoefficientLanes components) := by
    intro q hq
    have hqparts := Finset.mem_filter.mp hq
    have hjoint : queryParent2 q ∈ joint := hqparts.2
    have hreconstruct := encoder2_assemble_eq_layer2_on_joint
      schedule points htables transcript components (queryParent2 q)
      hjoint (slotIndex (n := 8192) (queryParent1 q))
    rw [childIndex_queryParent2_slotIndex] at hreconstruct
    simp only [prefixAgreement2, Finset.mem_filter]
    exact ⟨hqparts.1, hreconstruct.symm⟩
  unfold PrefixNear2
  exact hlift.trans_le (Finset.card_le_card hsubset)

/-- Joint decoded-lane agreement in round three reconstructs a genuine
prefix-close layer-three coefficient vector. -/
theorem joint_line3_weight_implies_PrefixNear3
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (transcript : IdealTranscript K)
    (components : Fin 4 -> Coeff4 K)
    (hmass : 6082 <
      weightMass (round3Weight schedule transcript)
        (jointAgreementSet (encoder4 schedule)
          (line3DecodedLanes schedule transcript) components)) :
    PrefixNear3 schedule points transcript
      (assembleCoefficientLanes components) := by
  classical
  let joint := jointAgreementSet (encoder4 schedule)
    (line3DecodedLanes schedule transcript) components
  let lifted := (beforeRound3Set schedule transcript).filter fun q =>
    queryParent3 q ∈ joint
  have hmassEq :
      weightMass (round3Weight schedule transcript) joint = lifted.card := by
    exact weightMass_projectedSupportWeight_eq_card
      (beforeRound3Set schedule transcript) queryParent3 joint
  have hmass' : 6082 <
      weightMass (round3Weight schedule transcript) joint := by
    simpa only [joint] using hmass
  have hlift : 6082 < lifted.card := by
    rw [hmassEq] at hmass'
    exact hmass'
  have hsubset : lifted ⊆
      prefixAgreement3 schedule points transcript
        (assembleCoefficientLanes components) := by
    intro q hq
    have hqparts := Finset.mem_filter.mp hq
    have hjoint : queryParent3 q ∈ joint := hqparts.2
    have hreconstruct := encoder3_assemble_eq_layer3_on_joint
      schedule points htables transcript components (queryParent3 q)
      hjoint (slotIndex (n := 2048) (queryParent2 q))
    rw [childIndex_queryParent3_slotIndex] at hreconstruct
    simp only [prefixAgreement3, Finset.mem_filter]
    exact ⟨hqparts.1, hreconstruct.symm⟩
  unfold PrefixNear3
  exact hlift.trans_le (Finset.card_le_card hsubset)

end PrefixNear

/-! ## The exact final uniqueness implication -/

section FiniteField

variable [Fintype K] [DecidableEq K] [DecidableEq F]

/-- The only coding fact needed at the terminal layer: distinct four-term
final polynomials agree at no more than three native evaluation positions. -/
def FinalEncoderOverlapAtMostThree
    (schedule : FixedSchedule F K) : Prop :=
  ∀ left right : Coeff4 K, left ≠ right ->
    (agreementSet (encoder4 schedule left)
      (encoder4 schedule right)).card ≤ 3

/-- Weighted final agreement above the V5 threshold forces coefficient
equality.  Round-three projected weights are bounded by `64`; hence distinct
degree-three codewords could carry weight at most `3*64 = 192`, far below
`6083`. -/
theorem final_coefficients_eq_of_weighted_agreement
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (candidate published : Coeff4 K)
    (hoverlap : FinalEncoderOverlapAtMostThree schedule)
    (hmass : 6082 <
      weightMass (round3Weight schedule transcript)
        (agreementSet (encoder4 schedule candidate)
          (encoder4 schedule published))) :
    candidate = published := by
  by_contra hne
  have hcard :
      (agreementSet (encoder4 schedule candidate)
        (encoder4 schedule published)).card ≤ 3 :=
    hoverlap candidate published hne
  have hweight := weightMass_le_scale_mul_card
    (round3Weight schedule transcript) 64
    (round3Weight_le_sixty_four schedule transcript)
    (agreementSet (encoder4 schedule candidate)
      (encoder4 schedule published))
  have hupper :
      weightMass (round3Weight schedule transcript)
        (agreementSet (encoder4 schedule candidate)
          (encoder4 schedule published)) ≤ 192 := by
    exact hweight.trans (Nat.mul_le_mul_right 64 hcard)
  omega

/-- A stronger, often convenient form: the V5 weighted threshold supplies
more than the ordinary final agreement floor of `95` native positions. -/
theorem final_agreement_card_gt_ninety_five
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (candidate published : Coeff4 K)
    (hmass : 6082 <
      weightMass (round3Weight schedule transcript)
        (agreementSet (encoder4 schedule candidate)
          (encoder4 schedule published))) :
    95 < (agreementSet (encoder4 schedule candidate)
      (encoder4 schedule published)).card := by
  exact card_large_of_weightMass_large
    (round3Weight schedule transcript) 64 6082 95
    (by decide) (round3Weight_le_sixty_four schedule transcript)
    (by norm_num) _ hmass

/-! ## Honest interface to the still-needed cross-round theorem -/

/-- The output that the prefix-measure, round-by-round FRI reduction must
produce outside its explicit small challenge sets.

Unlike four independent proximity witnesses, this object contains one initial
candidate and its actual deterministic folds.  `final_weighted_agreement` is
the only field consumed by the terminal uniqueness proof below; the preceding
three fields make the cross-round compatibility inspectable rather than hiding
it in an existential final-match statement. -/
structure CompatibleWeightedChain
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) where
  initial : Coeff0 K
  layer1 : Coeff1 K
  layer2 : Coeff2 K
  layer3 : Coeff3 K
  final : Coeff4 K
  layer1_eq : layer1 = fold0 schedule initial
  layer2_eq : layer2 = fold1 schedule layer1
  layer3_eq : layer3 = fold2 schedule layer2
  final_eq : final = fold3 schedule layer3
  initial_supported : SupportedNear0 schedule encoders transcript initial
  final_weighted_agreement : 6082 <
    weightMass (round3Weight schedule transcript)
      (agreementSet (encoder4 schedule final)
        (encoder4 schedule transcript.publishedFinal))

/-- Once the native round-reduction supplies one compatible chain, the final
overlap theorem turns its weighted terminal agreement into the exact published
coefficient equality. -/
theorem compatibleWeightedChain_final_eq_published
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (hoverlap : FinalEncoderOverlapAtMostThree schedule)
    (chain : CompatibleWeightedChain schedule encoders transcript) :
    chain.final = transcript.publishedFinal :=
  final_coefficients_eq_of_weighted_agreement schedule transcript
    chain.final transcript.publishedFinal hoverlap
    chain.final_weighted_agreement

end FiniteField

end AspisV5FriCompatibleCandidateChain
