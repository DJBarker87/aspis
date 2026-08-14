import AspisFormal.V5FriAdaptiveUnmatched
import AspisFormal.V5FriCompatibleCandidateChain
import AspisFormal.V5FriExactRSDistance
import AspisFormal.V5FriInitialListBound
import AspisFormal.V5FriPublishedOutputEncoderDecoding
import AspisFormal.V5FriReleasedLineGeometry

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Four concrete adaptive V5 FRI reductions

This file instantiates the four generic weighted correlated-agreement steps
with the released V5 encoders.  The chronology is explicit:

```
initial word
  -> z0 -> first line word
  -> z1 -> second line word
  -> z2 -> third line word
  -> z3 -> published four coefficients.
```

For a fixed transcript prefix, the word, decoded lanes, and prefix weight used
at a round are fixed before that round's challenge.  A backwards selector may
use a fixed later challenge suffix to choose which decoder candidate to follow;
as the current challenge varies this is represented by one `ProximateStrategy`.
The generic curve theorem therefore bounds one honest challenge fibre, rather
than assuming a probability for a named ``fold failure''.

The only coding-theory premise is
`PublishedOrdinaryPolynomialCurveDecoding`.  The released line geometry turns
that one ordinary Reed--Solomon statement into the four exact output-code
statements.  Exact decoded lanes, prefix weights, reconstruction, coefficient
folds, and the initial list bound are all discharged in Lean.
-/

namespace AspisV5FriReleasedAdaptiveExtraction

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAdaptiveUnmatched
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriExactRSDistance
open AspisV5FriInitialListBound
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriPublishedThresholds
open AspisV5FriReleasedLineGeometry
open AspisV5FriWeightedCorrelatedAgreementFinalization
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## Released caps and encoder facts -/

/-- The four integer challenge-fibre caps, in transcript order. -/
noncomputable def releasedChallengeCap : Fin 4 -> Nat := ![
  ⌊challengeThreshold 10 round0Rate 131072⌋₊,
  ⌊challengeThreshold 9 round1Rate 32768⌋₊,
  ⌊challengeThreshold 6 round2Rate 8192⌋₊,
  ⌊challengeThreshold 3 round3Rate 2048⌋₊]

@[simp] theorem releasedChallengeCap_zero :
    releasedChallengeCap 0 = ⌊challengeThreshold 10 round0Rate 131072⌋₊ := rfl

@[simp] theorem releasedChallengeCap_one :
    releasedChallengeCap 1 = ⌊challengeThreshold 9 round1Rate 32768⌋₊ := rfl

@[simp] theorem releasedChallengeCap_two :
    releasedChallengeCap 2 = ⌊challengeThreshold 6 round2Rate 8192⌋₊ := rfl

@[simp] theorem releasedChallengeCap_three :
    releasedChallengeCap 3 = ⌊challengeThreshold 3 round3Rate 2048⌋₊ := rfl

/-- One published ordinary-RS theorem supplies all four released V5 output
curve-decoding statements. -/
theorem released_output_curve_decoding
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    V5OutputEncoderCurveDecoding schedule releasedEvaluationPoints :=
  published_curve_decoding_applies_to_v5_outputs schedule
    releasedEvaluationPoints
    (releasedLineEvaluationIdentities schedule hfinal)
    (releasedFinalDomainDistinct schedule hfinal) hpublished

/-- The one published ordinary polynomial-evaluation/Reed--Solomon decoding theorem applies
to the four encoders that the released verifier actually uses after its four
folds.  The same statement also records their exact maximum overlaps, hence
their exact minimum-distance numerators:

* `131072 - 255`;
* `32768 - 63`;
* `8192 - 15`; and
* `2048 - 3`.

The encoder identities, point order, and distance claims are proved here; the
decoding theorem itself remains the one named published-result premise.  The
initial circle encoder is a separate code and its released distance/list bound
is proved by `releasedInitialEncoderDistance`. -/
theorem released_four_encoders_have_published_decoding_and_exact_distance
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    V5OutputEncoderCurveDecoding schedule releasedEvaluationPoints /\
      V5OutputExactDistances schedule releasedEvaluationPoints := by
  constructor
  · exact released_output_curve_decoding schedule hfinal hpublished
  · exact exactV5OutputDistances schedule releasedEvaluationPoints
      (releasedLineEvaluationIdentities schedule hfinal)
      (releasedFinalDomainDistinct schedule hfinal)

/-- Injectivity of all four fold-output encoders at the released points. -/
theorem released_output_encoders_injective
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints) :
    Function.Injective (encoder1 schedule releasedEvaluationPoints) /\
      Function.Injective (encoder2 schedule releasedEvaluationPoints) /\
      Function.Injective (encoder3 schedule releasedEvaluationPoints) /\
      Function.Injective (encoder4 schedule) := by
  have h4 : Function.Injective (encoder4 schedule) :=
    encoder4_injective_of_distinct schedule
      (releasedFinalDomainDistinct schedule hfinal)
  rcases concrete_encoders_injective schedule releasedEvaluationPoints
      htables h4 with ⟨h3, h2, h1, _h0⟩
  exact ⟨h1, h2, h3, h4⟩

/-- The released initial circle encoder's actual decoder list is never larger
than the public cap `240` (the proved integer bound is in fact `222`). -/
theorem released_initial_candidate_list_card_le_240
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule) :
    (initialCandidateList
      (concreteCodeEncoders schedule releasedEvaluationPoints)
      transcript).card ≤ 240 :=
  initialCandidateList_card_le_240
    (concreteCodeEncoders schedule releasedEvaluationPoints) transcript
    (releasedInitialEncoderDistance schedule hfinal)

/-! ## Exact one-round bad sets -/

/-- Round zero uses the decoded initial circle fibres and the unit prefix
weight.  The predecessor is an actual 1024-coefficient initial candidate. -/
noncomputable def round0Bad
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 131072) (Coeff1 K)) : Finset K :=
  AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges
    (encoder1 schedule releasedEvaluationPoints)
    (round0Weight schedule transcript) 6082 6082
    (circleDecodedLanes schedule transcript) strategy
    (fun z previous => coefficientFoldLayer 256 z previous)
    (Near0 (concreteCodeEncoders schedule releasedEvaluationPoints) transcript)

/-- Round one uses the first committed line word and the exact four-to-one
prefix weight. -/
noncomputable def round1Bad
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 32768) (Coeff2 K)) : Finset K :=
  AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges
    (encoder2 schedule releasedEvaluationPoints)
    (round1Weight schedule transcript) 6082 1520
    (line1DecodedLanes schedule transcript) strategy
    (fun z previous => coefficientFoldLayer 64 z previous)
    (PrefixNear1 schedule releasedEvaluationPoints transcript)

/-- Round two uses the second committed line word and the exact sixteen-to-one
prefix weight. -/
noncomputable def round2Bad
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 8192) (Coeff3 K)) : Finset K :=
  AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges
    (encoder3 schedule releasedEvaluationPoints)
    (round2Weight schedule transcript) 6082 380
    (line2DecodedLanes schedule transcript) strategy
    (fun z previous => coefficientFoldLayer 16 z previous)
    (PrefixNear2 schedule releasedEvaluationPoints transcript)

/-- Round three uses the third committed line word and the exact
sixty-four-to-one prefix weight. -/
noncomputable def round3Bad
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (strategy : ProximateStrategy K (Fin 2048) (Coeff4 K)) : Finset K :=
  AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges
    (encoder4 schedule)
    (round3Weight schedule transcript) 6082 95
    (line3DecodedLanes schedule transcript) strategy
    (fun z previous => coefficientFoldLayer 4 z previous)
    (PrefixNear3 schedule releasedEvaluationPoints transcript)

/-! ## Four concrete one-round reductions -/

theorem round0_matching_predecessor_or_counted
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 131072) (Coeff1 K)) (z : K)
    (hvalid : WeightedValidResponse
      (encoder1 schedule releasedEvaluationPoints)
      (round0Weight schedule transcript) 6082
      (circleDecodedLanes schedule transcript) strategy z) :
    HasMatchingPredecessor
        (fun z previous => coefficientFoldLayer 256 z previous)
        (Near0 (concreteCodeEncoders schedule releasedEvaluationPoints) transcript)
        strategy z \/
      (z ∈ round0Bad schedule transcript strategy /\
        (round0Bad schedule transcript strategy).card ≤
          releasedChallengeCap 0) := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round0
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).1
  simpa only [round0Bad, releasedChallengeCap_zero] using
    (accepted_weighted_response_has_matching_predecessor_or_counted
      (encoder1 schedule releasedEvaluationPoints)
      (round0Weight schedule transcript) 1 6082 6082
      ⌊challengeThreshold 10 round0Rate 131072⌋₊
      (by decide) (round0Weight_le_one schedule transcript) (by decide)
      hcurve (circleDecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 256 z previous)
      (Near0 (concreteCodeEncoders schedule releasedEvaluationPoints) transcript)
      (joint_circle_weight_implies_Near0 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder1 schedule releasedEvaluationPoints) hinjective strategy
          components z honcurve)
      z hvalid)

theorem round1_matching_predecessor_or_counted
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 32768) (Coeff2 K)) (z : K)
    (hvalid : WeightedValidResponse
      (encoder2 schedule releasedEvaluationPoints)
      (round1Weight schedule transcript) 6082
      (line1DecodedLanes schedule transcript) strategy z) :
    HasMatchingPredecessor
        (fun z previous => coefficientFoldLayer 64 z previous)
        (PrefixNear1 schedule releasedEvaluationPoints transcript)
        strategy z \/
      (z ∈ round1Bad schedule transcript strategy /\
        (round1Bad schedule transcript strategy).card ≤
          releasedChallengeCap 1) := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round1
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).2.1
  simpa only [round1Bad, releasedChallengeCap_one] using
    (accepted_weighted_response_has_matching_predecessor_or_counted
      (encoder2 schedule releasedEvaluationPoints)
      (round1Weight schedule transcript) 4 6082 1520
      ⌊challengeThreshold 9 round1Rate 32768⌋₊
      (by decide) (round1Weight_le_four schedule transcript) (by decide)
      hcurve (line1DecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 64 z previous)
      (PrefixNear1 schedule releasedEvaluationPoints transcript)
      (joint_line1_weight_implies_PrefixNear1 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder2 schedule releasedEvaluationPoints) hinjective strategy
          components z honcurve)
      z hvalid)

theorem round2_matching_predecessor_or_counted
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 8192) (Coeff3 K)) (z : K)
    (hvalid : WeightedValidResponse
      (encoder3 schedule releasedEvaluationPoints)
      (round2Weight schedule transcript) 6082
      (line2DecodedLanes schedule transcript) strategy z) :
    HasMatchingPredecessor
        (fun z previous => coefficientFoldLayer 16 z previous)
        (PrefixNear2 schedule releasedEvaluationPoints transcript)
        strategy z \/
      (z ∈ round2Bad schedule transcript strategy /\
        (round2Bad schedule transcript strategy).card ≤
          releasedChallengeCap 2) := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round2
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).2.2.1
  simpa only [round2Bad, releasedChallengeCap_two] using
    (accepted_weighted_response_has_matching_predecessor_or_counted
      (encoder3 schedule releasedEvaluationPoints)
      (round2Weight schedule transcript) 16 6082 380
      ⌊challengeThreshold 6 round2Rate 8192⌋₊
      (by decide) (round2Weight_le_sixteen schedule transcript) (by decide)
      hcurve (line2DecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 16 z previous)
      (PrefixNear2 schedule releasedEvaluationPoints transcript)
      (joint_line2_weight_implies_PrefixNear2 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder3 schedule releasedEvaluationPoints) hinjective strategy
          components z honcurve)
      z hvalid)

theorem round3_matching_predecessor_or_counted
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 2048) (Coeff4 K)) (z : K)
    (hvalid : WeightedValidResponse
      (encoder4 schedule) (round3Weight schedule transcript) 6082
      (line3DecodedLanes schedule transcript) strategy z) :
    HasMatchingPredecessor
        (fun z previous => coefficientFoldLayer 4 z previous)
        (PrefixNear3 schedule releasedEvaluationPoints transcript)
        strategy z \/
      (z ∈ round3Bad schedule transcript strategy /\
        (round3Bad schedule transcript strategy).card ≤
          releasedChallengeCap 3) := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round3
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).2.2.2
  simpa only [round3Bad, releasedChallengeCap_three] using
    (accepted_weighted_response_has_matching_predecessor_or_counted
      (encoder4 schedule) (round3Weight schedule transcript) 64 6082 95
      ⌊challengeThreshold 3 round3Rate 2048⌋₊
      (by decide) (round3Weight_le_sixty_four schedule transcript) (by decide)
      hcurve (line3DecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 4 z previous)
      (PrefixNear3 schedule releasedEvaluationPoints transcript)
      (joint_line3_weight_implies_PrefixNear3 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder4 schedule) hinjective strategy components z honcurve)
      z hvalid)

/-! The same four applications, with only their cardinality conclusions.
These do not assume that the sampled response is valid. -/

theorem round0Bad_card_le
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 131072) (Coeff1 K)) :
    (round0Bad schedule transcript strategy).card ≤ releasedChallengeCap 0 := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round0
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).1
  simpa only [round0Bad, releasedChallengeCap_zero] using
    (AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges_card_le
      (encoder1 schedule releasedEvaluationPoints)
      (round0Weight schedule transcript) 1 6082 6082
      ⌊challengeThreshold 10 round0Rate 131072⌋₊
      (by decide) (round0Weight_le_one schedule transcript) (by decide)
      hcurve (circleDecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 256 z previous)
      (Near0 (concreteCodeEncoders schedule releasedEvaluationPoints) transcript)
      (joint_circle_weight_implies_Near0 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder1 schedule releasedEvaluationPoints) hinjective strategy
          components z honcurve))

theorem round1Bad_card_le
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 32768) (Coeff2 K)) :
    (round1Bad schedule transcript strategy).card ≤ releasedChallengeCap 1 := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round1
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).2.1
  simpa only [round1Bad, releasedChallengeCap_one] using
    (AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges_card_le
      (encoder2 schedule releasedEvaluationPoints)
      (round1Weight schedule transcript) 4 6082 1520
      ⌊challengeThreshold 9 round1Rate 32768⌋₊
      (by decide) (round1Weight_le_four schedule transcript) (by decide)
      hcurve (line1DecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 64 z previous)
      (PrefixNear1 schedule releasedEvaluationPoints transcript)
      (joint_line1_weight_implies_PrefixNear1 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder2 schedule releasedEvaluationPoints) hinjective strategy
          components z honcurve))

theorem round2Bad_card_le
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 8192) (Coeff3 K)) :
    (round2Bad schedule transcript strategy).card ≤ releasedChallengeCap 2 := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round2
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).2.2.1
  simpa only [round2Bad, releasedChallengeCap_two] using
    (AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges_card_le
      (encoder3 schedule releasedEvaluationPoints)
      (round2Weight schedule transcript) 16 6082 380
      ⌊challengeThreshold 6 round2Rate 8192⌋₊
      (by decide) (round2Weight_le_sixteen schedule transcript) (by decide)
      hcurve (line2DecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 16 z previous)
      (PrefixNear2 schedule releasedEvaluationPoints transcript)
      (joint_line2_weight_implies_PrefixNear2 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder3 schedule releasedEvaluationPoints) hinjective strategy
          components z honcurve))

theorem round3Bad_card_le
    (schedule : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain schedule)
    (htables : InverseTablesMatch schedule releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategy : ProximateStrategy K (Fin 2048) (Coeff4 K)) :
    (round3Bad schedule transcript strategy).card ≤ releasedChallengeCap 3 := by
  have hcurve := (released_output_curve_decoding schedule hfinal hpublished).round3
  have hinjective :=
    (released_output_encoders_injective schedule hfinal htables).2.2.2
  simpa only [round3Bad, releasedChallengeCap_three] using
    (AspisV5FriWeightedCorrelatedAgreementFinalization.unmatchedChallenges_card_le
      (encoder4 schedule) (round3Weight schedule transcript) 64 6082 95
      ⌊challengeThreshold 3 round3Rate 2048⌋₊
      (by decide) (round3Weight_le_sixty_four schedule transcript) (by decide)
      hcurve (line3DecodedLanes schedule transcript) strategy
      assembleCoefficientLanes
      (fun z previous => coefficientFoldLayer 4 z previous)
      (PrefixNear3 schedule releasedEvaluationPoints transcript)
      (joint_line3_weight_implies_PrefixNear3 schedule releasedEvaluationPoints
        htables transcript)
      (fun components z honcurve =>
        fold_assembled_eq_candidate_of_onCurve
          (encoder4 schedule) hinjective strategy components z honcurve))

/-! ## Causally ordered words and challenges -/

/-- A prover may choose each later word only after seeing the earlier fold
challenges.  This is the actual FRI order used by the release. -/
structure CausalTranscriptFamily (K : Type*) where
  layer0 : Word0 K
  layer1 : K -> Word1 K
  layer2 : K -> K -> Word2 K
  layer3 : K -> K -> K -> Word3 K
  final : K -> K -> K -> K -> Coeff4 K

/-- Replace only the four fold challenges in a fixed public schedule. -/
def scheduleAt (base : FixedSchedule (ZMod P) K)
    (z0 z1 z2 z3 : K) : FixedSchedule (ZMod P) K :=
  { base with alpha := ![z0, z1, z2, z3] }

/-- The public schedule immediately after the first challenge. -/
def scheduleAfter0 (base : FixedSchedule (ZMod P) K) (z0 : K) :
    FixedSchedule (ZMod P) K :=
  scheduleAt base z0 0 0 0

/-- The public schedule immediately after the second challenge. -/
def scheduleAfter1 (base : FixedSchedule (ZMod P) K) (z0 z1 : K) :
    FixedSchedule (ZMod P) K :=
  scheduleAt base z0 z1 0 0

/-- The public schedule immediately after the third challenge. -/
def scheduleAfter2 (base : FixedSchedule (ZMod P) K) (z0 z1 z2 : K) :
    FixedSchedule (ZMod P) K :=
  scheduleAt base z0 z1 z2 0

/-- The word data fixed before the first challenge. -/
def transcriptBeforeRound0 (family : CausalTranscriptFamily K) :
    IdealTranscript K where
  layer0 := family.layer0
  layer1 := 0
  layer2 := 0
  layer3 := 0
  publishedFinal := 0

/-- The word data fixed before the second challenge. -/
def transcriptBeforeRound1 (family : CausalTranscriptFamily K) (z0 : K) :
    IdealTranscript K where
  layer0 := family.layer0
  layer1 := family.layer1 z0
  layer2 := 0
  layer3 := 0
  publishedFinal := 0

/-- The word data fixed before the third challenge. -/
def transcriptBeforeRound2 (family : CausalTranscriptFamily K) (z0 z1 : K) :
    IdealTranscript K where
  layer0 := family.layer0
  layer1 := family.layer1 z0
  layer2 := family.layer2 z0 z1
  layer3 := 0
  publishedFinal := 0

/-- The word data fixed before the fourth challenge. -/
def transcriptBeforeRound3 (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K) : IdealTranscript K where
  layer0 := family.layer0
  layer1 := family.layer1 z0
  layer2 := family.layer2 z0 z1
  layer3 := family.layer3 z0 z1 z2
  publishedFinal := 0

/-- The complete transcript at one sampled four-challenge tuple. -/
def fullTranscript (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) : IdealTranscript K where
  layer0 := family.layer0
  layer1 := family.layer1 z0
  layer2 := family.layer2 z0 z1
  layer3 := family.layer3 z0 z1 z2
  publishedFinal := family.final z0 z1 z2 z3

/-- Changing fold challenges does not change the released final domain. -/
theorem finalXMatches_scheduleAt
    (base : FixedSchedule (ZMod P) K) (z0 z1 z2 z3 : K)
    (hfinal : FinalXMatchesReleasedDomain base) :
    FinalXMatchesReleasedDomain (scheduleAt base z0 z1 z2 z3) := by
  intro i
  simpa [scheduleAt] using hfinal i

/-- Changing fold challenges does not change any released inverse table. -/
theorem inverseTablesMatch_scheduleAt
    (base : FixedSchedule (ZMod P) K) (z0 z1 z2 z3 : K)
    (htables : InverseTablesMatch base releasedEvaluationPoints) :
    InverseTablesMatch (scheduleAt base z0 z1 z2 z3)
      releasedEvaluationPoints where
  circleX i := by simpa [scheduleAt] using htables.circleX i
  circleY i := by simpa [scheduleAt] using htables.circleY i
  line1 i s := by simpa [scheduleAt] using htables.line1 i s
  line2 i s := by simpa [scheduleAt] using htables.line2 i s
  line3 i s := by simpa [scheduleAt] using htables.line3 i s

/-! ## Suffix-conditioned strategy families -/

/-- Strategies used by backwards extraction.  Each field omits precisely the
challenge varied by that strategy.  Dependence on a fixed later suffix merely
selects which candidate is followed; the committed word and weights used at
the varied round depend only on the earlier prefix. -/
structure AdaptiveStrategies where
  round0 : K -> K -> K ->
    ProximateStrategy K (Fin 131072) (Coeff1 K)
  round1 : K -> K -> K ->
    ProximateStrategy K (Fin 32768) (Coeff2 K)
  round2 : K -> K -> K ->
    ProximateStrategy K (Fin 8192) (Coeff3 K)
  round3 : K -> K -> K ->
    ProximateStrategy K (Fin 2048) (Coeff4 K)

/-- The four valid-but-unmatched challenge fibres for a causal prover.  At
round `r`, the authenticated word, decoded lanes, and prefix weight contain
only challenges `z0,...,z(r-1)` already sampled before that round. -/
noncomputable def adaptiveBadSets
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategies : AdaptiveStrategies (K := K)) :
    SuffixConditionedBadSets K releasedChallengeCap where
  round0 z1 z2 z3 :=
    round0Bad base (transcriptBeforeRound0 family)
      (strategies.round0 z1 z2 z3)
  round1 z0 z2 z3 :=
    round1Bad (scheduleAfter0 base z0) (transcriptBeforeRound1 family z0)
      (strategies.round1 z0 z2 z3)
  round2 z0 z1 z3 :=
    round2Bad (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1)
      (strategies.round2 z0 z1 z3)
  round3 z0 z1 z2 :=
    round3Bad (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2)
      (strategies.round3 z0 z1 z2)
  round0_card_le := by
    intro z1 z2 z3
    exact round0Bad_card_le base (transcriptBeforeRound0 family)
      hfinal htables hpublished (strategies.round0 z1 z2 z3)
  round1_card_le := by
    intro z0 z2 z3
    exact round1Bad_card_le (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0)
      (finalXMatches_scheduleAt base z0 0 0 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 0 0 0 htables)
      hpublished (strategies.round1 z0 z2 z3)
  round2_card_le := by
    intro z0 z1 z3
    exact round2Bad_card_le (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1)
      (finalXMatches_scheduleAt base z0 z1 0 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 z1 0 0 htables)
      hpublished (strategies.round2 z0 z1 z3)
  round3_card_le := by
    intro z0 z1 z2
    exact round3Bad_card_le (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2)
      (finalXMatches_scheduleAt base z0 z1 z2 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 z1 z2 0 htables)
      hpublished (strategies.round3 z0 z1 z2)

theorem adaptiveBadChallengeTuples_card_le
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategies : AdaptiveStrategies (K := K)) :
    (allBadChallengeTuples
      (adaptiveBadSets base family hfinal htables hpublished strategies)).card ≤
      Fintype.card K ^ 3 *
        (releasedChallengeCap 0 + releasedChallengeCap 1 +
          releasedChallengeCap 2 + releasedChallengeCap 3) :=
  allBadChallengeTuples_card_le
    (adaptiveBadSets base family hfinal htables hpublished strategies)

theorem adaptiveBadChallengeProbability_le
    [Nonempty K]
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategies : AdaptiveStrategies (K := K)) :
    uniformBadChallengeProbability
        (adaptiveBadSets base family hfinal htables hpublished strategies) ≤
      (releasedChallengeCap 0 + releasedChallengeCap 1 +
        releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
          Fintype.card K :=
  uniformBadChallengeProbability_le
    (adaptiveBadSets base family hfinal htables hpublished strategies)

/-! ## Backwards selection at one accepted challenge tuple -/

def Round3Matches
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (strategies : AdaptiveStrategies (K := K))
    (z0 z1 z2 z3 : K) : Prop :=
  HasMatchingPredecessor
    (fun z previous => coefficientFoldLayer 4 z previous)
    (PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
      (transcriptBeforeRound3 family z0 z1 z2))
    (strategies.round3 z0 z1 z2) z3

def Round2Matches
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (strategies : AdaptiveStrategies (K := K))
    (z0 z1 z2 z3 : K) : Prop :=
  HasMatchingPredecessor
    (fun z previous => coefficientFoldLayer 16 z previous)
    (PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
      (transcriptBeforeRound2 family z0 z1))
    (strategies.round2 z0 z1 z3) z2

def Round1Matches
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (strategies : AdaptiveStrategies (K := K))
    (z0 z1 z2 z3 : K) : Prop :=
  HasMatchingPredecessor
    (fun z previous => coefficientFoldLayer 64 z previous)
    (PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0))
    (strategies.round1 z0 z2 z3) z1

/-- Deterministic response and candidate-selection facts at one challenge
tuple.  The structure does not assume a matching predecessor or assign any
probability to failure.  Its fields are the remaining bridge from accepted,
authenticated verifier words to the response facts consumed below. -/
structure CausalBackwardSelection
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (strategies : AdaptiveStrategies (K := K))
    (z0 z1 z2 z3 : K) : Prop where
  final_candidate :
    (strategies.round3 z0 z1 z2).candidate z3 =
      family.final z0 z1 z2 z3
  round3_valid :
    6082 < (consistencySet (scheduleAt base z0 z1 z2 z3)
        (fullTranscript family z0 z1 z2 z3)).card ->
      WeightedValidResponse (encoder4 (scheduleAfter2 base z0 z1 z2))
        (round3Weight (scheduleAfter2 base z0 z1 z2)
          (transcriptBeforeRound3 family z0 z1 z2)) 6082
        (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
          (transcriptBeforeRound3 family z0 z1 z2))
        (strategies.round3 z0 z1 z2) z3
  choose3 : Round3Matches base family strategies z0 z1 z2 z3 ->
    PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
        (transcriptBeforeRound3 family z0 z1 z2)
        ((strategies.round2 z0 z1 z3).candidate z2) /\
      coefficientFoldLayer 4 z3
          ((strategies.round2 z0 z1 z3).candidate z2) =
        (strategies.round3 z0 z1 z2).candidate z3
  round2_valid : Round3Matches base family strategies z0 z1 z2 z3 ->
    WeightedValidResponse
      (encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints)
      (round2Weight (scheduleAfter1 base z0 z1)
        (transcriptBeforeRound2 family z0 z1)) 6082
      (line2DecodedLanes (scheduleAfter1 base z0 z1)
        (transcriptBeforeRound2 family z0 z1))
      (strategies.round2 z0 z1 z3) z2
  choose2 : Round2Matches base family strategies z0 z1 z2 z3 ->
    PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
        (transcriptBeforeRound2 family z0 z1)
        ((strategies.round1 z0 z2 z3).candidate z1) /\
      coefficientFoldLayer 16 z2
          ((strategies.round1 z0 z2 z3).candidate z1) =
        (strategies.round2 z0 z1 z3).candidate z2
  round1_valid : Round2Matches base family strategies z0 z1 z2 z3 ->
    WeightedValidResponse
      (encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints)
      (round1Weight (scheduleAfter0 base z0)
        (transcriptBeforeRound1 family z0)) 6082
      (line1DecodedLanes (scheduleAfter0 base z0)
        (transcriptBeforeRound1 family z0))
      (strategies.round1 z0 z2 z3) z1
  choose1 : Round1Matches base family strategies z0 z1 z2 z3 ->
    PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
        (transcriptBeforeRound1 family z0)
        ((strategies.round0 z1 z2 z3).candidate z0) /\
      coefficientFoldLayer 64 z1
          ((strategies.round0 z1 z2 z3).candidate z0) =
        (strategies.round1 z0 z2 z3).candidate z1
  round0_valid : Round1Matches base family strategies z0 z1 z2 z3 ->
    WeightedValidResponse (encoder1 base releasedEvaluationPoints)
      (round0Weight base (transcriptBeforeRound0 family)) 6082
      (circleDecodedLanes base (transcriptBeforeRound0 family))
      (strategies.round0 z1 z2 z3) z0

/-- The implementation-facing bridge must supply one strategy family that
works simultaneously for every four-challenge tuple.  This global quantifier
prevents choosing a different strategy after seeing the sampled tuple, which
would make the bad-set count invalid. -/
def GlobalCausalBackwardSelection
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (strategies : AdaptiveStrategies (K := K)) : Prop :=
  ∀ z0 z1 z2 z3,
    CausalBackwardSelection base family strategies z0 z1 z2 z3

/-- For an accepted q18 transcript, either all queries hit a consistency set
of size at most `6082`, one of the four explicitly bounded challenge fibres
occurs, or one member of the released initial decoder list follows the exact
four coefficient folds to the published final polynomial.  The list has at
most `240` entries. -/
theorem accepted_ideal_fri_extracts_initial_candidate_or_counted
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategies : AdaptiveStrategies (K := K))
    (z0 z1 z2 z3 : K)
    (selection : CausalBackwardSelection base family strategies z0 z1 z2 z3)
    (haccepts : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript family z0 z1 z2 z3) queries \/
      (adaptiveBadSets base family hfinal htables hpublished strategies).Occurs
        z0 z1 z2 z3 \/
      ∃ c0 : Coeff0 K,
        c0 ∈ initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family) /\
        (initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family)).card ≤ 240 /\
        coefficientFoldLayer 4 z3
          (coefficientFoldLayer 16 z2
            (coefficientFoldLayer 64 z1
              (coefficientFoldLayer 256 z0 c0))) =
            family.final z0 z1 z2 z3 := by
  classical
  let bad := adaptiveBadSets base family hfinal htables hpublished strategies
  by_cases hquery : QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries
  · exact Or.inl hquery
  apply Or.inr
  have hdense : 6082 < (consistencySet (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3)).card :=
    dense_consistency_of_accepts_not_queryFailure
      (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries haccepts hquery
  have h3 := round3_matching_predecessor_or_counted
    (scheduleAfter2 base z0 z1 z2)
    (transcriptBeforeRound3 family z0 z1 z2)
    (finalXMatches_scheduleAt base z0 z1 z2 0 hfinal)
    (inverseTablesMatch_scheduleAt base z0 z1 z2 0 htables)
    hpublished (strategies.round3 z0 z1 z2) z3
    (selection.round3_valid hdense)
  rcases h3 with hmatch3 | hbad3
  · have hselected3 := selection.choose3 hmatch3
    have h2 := round2_matching_predecessor_or_counted
      (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1)
      (finalXMatches_scheduleAt base z0 z1 0 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 z1 0 0 htables)
      hpublished (strategies.round2 z0 z1 z3) z2
      (selection.round2_valid hmatch3)
    rcases h2 with hmatch2 | hbad2
    · have hselected2 := selection.choose2 hmatch2
      have h1 := round1_matching_predecessor_or_counted
        (scheduleAfter0 base z0) (transcriptBeforeRound1 family z0)
        (finalXMatches_scheduleAt base z0 0 0 0 hfinal)
        (inverseTablesMatch_scheduleAt base z0 0 0 0 htables)
        hpublished (strategies.round1 z0 z2 z3) z1
        (selection.round1_valid hmatch2)
      rcases h1 with hmatch1 | hbad1
      · have hselected1 := selection.choose1 hmatch1
        have h0 := round0_matching_predecessor_or_counted base
          (transcriptBeforeRound0 family) hfinal htables hpublished
          (strategies.round0 z1 z2 z3) z0
          (selection.round0_valid hmatch1)
        rcases h0 with ⟨c0, hc0near, hc0fold⟩ | hbad0
        · apply Or.inr
          refine ⟨c0, ?_, ?_, ?_⟩
          · exact (mem_initialCandidateList_iff
              (concreteCodeEncoders base releasedEvaluationPoints)
              (transcriptBeforeRound0 family) c0).2 hc0near
          · exact released_initial_candidate_list_card_le_240 base
              (transcriptBeforeRound0 family) hfinal
          · have hc0fold' := hc0fold
            change coefficientFoldLayer 256 z0 c0 =
              (strategies.round0 z1 z2 z3).candidate z0 at hc0fold'
            rw [hc0fold', hselected1.2, hselected2.2, hselected3.2,
              selection.final_candidate]
        · apply Or.inl
          exact Or.inl (by
            change z0 ∈ bad.round0 z1 z2 z3
            simpa only [bad, adaptiveBadSets] using hbad0.1)
      · apply Or.inl
        exact Or.inr (Or.inl (by
          change z1 ∈ bad.round1 z0 z2 z3
          simpa only [bad, adaptiveBadSets] using hbad1.1))
    · apply Or.inl
      exact Or.inr (Or.inr (Or.inl (by
        change z2 ∈ bad.round2 z0 z1 z3
        simpa only [bad, adaptiveBadSets] using hbad2.1)))
  · apply Or.inl
    exact Or.inr (Or.inr (Or.inr (by
      change z3 ∈ bad.round3 z0 z1 z2
      simpa only [bad, adaptiveBadSets] using hbad3.1)))

/-- The same inclusion under the correctly quantified implementation bridge:
one fixed causal transcript family and one fixed strategy family cover the
whole challenge space. -/
theorem accepted_ideal_fri_extracts_of_global_selection
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (strategies : AdaptiveStrategies (K := K))
    (selection : GlobalCausalBackwardSelection base family strategies)
    (z0 z1 z2 z3 : K)
    (haccepts : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript family z0 z1 z2 z3) queries \/
      (adaptiveBadSets base family hfinal htables hpublished strategies).Occurs
        z0 z1 z2 z3 \/
      ∃ c0 : Coeff0 K,
        c0 ∈ initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family) /\
        (initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family)).card ≤ 240 /\
        coefficientFoldLayer 4 z3
          (coefficientFoldLayer 16 z2
            (coefficientFoldLayer 64 z1
              (coefficientFoldLayer 256 z0 c0))) =
            family.final z0 z1 z2 z3 :=
  accepted_ideal_fri_extracts_initial_candidate_or_counted base family queries
    hfinal htables hpublished strategies z0 z1 z2 z3
    (selection z0 z1 z2 z3) haccepts

/-! ## Audit -/

#print axioms released_output_curve_decoding
#print axioms released_four_encoders_have_published_decoding_and_exact_distance
#print axioms released_initial_candidate_list_card_le_240
#print axioms round0Bad_card_le
#print axioms round1Bad_card_le
#print axioms round2Bad_card_le
#print axioms round3Bad_card_le
#print axioms adaptiveBadChallengeTuples_card_le
#print axioms adaptiveBadChallengeProbability_le
#print axioms accepted_ideal_fri_extracts_initial_candidate_or_counted
#print axioms accepted_ideal_fri_extracts_of_global_selection

end AspisV5FriReleasedAdaptiveExtraction
