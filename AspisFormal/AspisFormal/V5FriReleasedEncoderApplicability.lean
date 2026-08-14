import AspisFormal.V5FriReleasedAdaptiveExtraction

/-!
# Published decoding for the released V5 encoders

This file removes the last arbitrary-domain parameter from the coding-theory
application.  It fixes the final evaluation table to the released bit-reversed
M31 line domain and then records two separate facts:

* the four committed-word encoders have the distance bounds used by the list
  argument; and
* S-two's ordinary Reed--Solomon curve-decoding theorem gives the four
  fold-output decoding statements used by the reduction.

The distance statements are proved in Lean.  The only mathematical premise of
the decoding statement is the published Reed--Solomon theorem itself, expressed
by `PublishedOrdinaryPolynomialCurveDecoding`.  This file does not claim that
the Rust-generated table has been extracted into Lean; identifying the
production `RATE512_FINAL_X` table with this released table is a separate,
small source-correspondence fact.
-/

namespace AspisV5FriReleasedEncoderApplicability

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriExactRSDistance
open AspisV5FriInitialListBound
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- Replace only the final evaluation table by the exact released V5 table.
The challenges, inverse tables, and query-index fields are left unchanged;
none of them changes the four encoder functions considered here. -/
def withReleasedFinalDomain
    (schedule : FixedSchedule (ZMod P) K) : FixedSchedule (ZMod P) K :=
  { schedule with finalX := storedLine11X }

/-- The released-domain condition is true by construction, rather than an
assumption about an arbitrary schedule. -/
theorem withReleasedFinalDomain_matches
    (schedule : FixedSchedule (ZMod P) K) :
    FinalXMatchesReleasedDomain (withReleasedFinalDomain schedule) := by
  intro i
  rfl

/-- The exact four committed-word distance bounds used by the V5 list proof:

* initial circle word: distinct codewords overlap in at most `1024` of
  `524288` positions;
* first line word: overlap at most `255` of `131072`;
* second line word: overlap at most `63` of `32768`; and
* third line word: overlap at most `15` of `8192`.

No published decoding theorem is a premise of this result. -/
theorem exact_released_committed_encoder_distance_bounds
    (schedule : FixedSchedule (ZMod P) K) :
    InitialEncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) /\
      Layer1EncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) /\
      Layer2EncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) /\
      Layer3EncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) :=
  releasedCommittedEncoderDistances (withReleasedFinalDomain schedule)
    (withReleasedFinalDomain_matches schedule)

/-- The four fold-output encoders are the exact released Reed--Solomon
evaluation codes and have exact maximum overlaps `255`, `63`, `15`, and `3`.
Equivalently, their minimum-distance numerators are
`131072 - 255`, `32768 - 63`, `8192 - 15`, and `2048 - 3`. -/
theorem exact_released_output_encoder_distances
    (schedule : FixedSchedule (ZMod P) K) :
    V5OutputExactDistances (withReleasedFinalDomain schedule)
      releasedEvaluationPoints :=
  exactV5OutputDistances (withReleasedFinalDomain schedule)
    releasedEvaluationPoints
    (releasedLineEvaluationIdentities (withReleasedFinalDomain schedule)
      (withReleasedFinalDomain_matches schedule))
    (releasedFinalDomainDistinct (withReleasedFinalDomain schedule)
      (withReleasedFinalDomain_matches schedule))

/-- S-two's published ordinary Reed--Solomon curve-decoding theorem applies to
the exact four released fold-output encoders.  All V5-specific domain,
coefficient-basis, degree, distance, agreement-floor, Johnson-interval, and
multiplicity checks have been discharged in Lean. -/
theorem published_decoding_applies_to_exact_released_output_encoders
    (schedule : FixedSchedule (ZMod P) K)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    V5OutputEncoderCurveDecoding (withReleasedFinalDomain schedule)
      releasedEvaluationPoints :=
  released_output_curve_decoding (withReleasedFinalDomain schedule)
    (withReleasedFinalDomain_matches schedule) hpublished

/-- One statement containing the published decoding result and both sets of
distance facts.  The sole non-Lean mathematical input is `hpublished`. -/
theorem released_encoder_decoding_and_distances
    (schedule : FixedSchedule (ZMod P) K)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    V5OutputEncoderCurveDecoding (withReleasedFinalDomain schedule)
        releasedEvaluationPoints /\
      V5OutputExactDistances (withReleasedFinalDomain schedule)
        releasedEvaluationPoints /\
      InitialEncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) /\
      Layer1EncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) /\
      Layer2EncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) /\
      Layer3EncoderDistance
        (concreteCodeEncoders (withReleasedFinalDomain schedule)
          releasedEvaluationPoints) := by
  refine ⟨published_decoding_applies_to_exact_released_output_encoders
      schedule hpublished,
    exact_released_output_encoder_distances schedule, ?_⟩
  exact exact_released_committed_encoder_distance_bounds schedule

/-! ## Audit -/

#print axioms withReleasedFinalDomain_matches
#print axioms exact_released_committed_encoder_distance_bounds
#print axioms exact_released_output_encoder_distances
#print axioms published_decoding_applies_to_exact_released_output_encoders
#print axioms released_encoder_decoding_and_distances

end AspisV5FriReleasedEncoderApplicability
