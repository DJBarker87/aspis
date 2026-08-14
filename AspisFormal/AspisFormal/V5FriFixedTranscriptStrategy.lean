import AspisFormal.V5FriFixedFamilyExperiment

set_option maxRecDepth 100000

/-!
# FRI extraction for one fixed ideal transcript

The noninteractive verifier receives commitments, authenticated openings, and
the final polynomial.  It does not receive all four full FRI words as bytes.
After the separate Merkle/reference-transcript argument has supplied one
fixed `IdealTranscript`, its four words and final polynomial do not change
when the challenges are varied in this ideal arithmetic experiment.

This file embeds any one fixed `IdealTranscript` into the more general causal
family used by `V5FriGlobalCausalStrategy`.  It then specializes the global
strategy and accepted-proof inclusion theorem back to that fixed ideal
transcript.  Consequently, the deterministic arithmetic inclusion does not
need a caller-supplied existential family or strategy in this special case.

This does not prove the Merkle/reference-transcript bridge or the
Fiat--Shamir step.  A malicious prover may choose each later commitment after
seeing earlier SHA-256 outputs and may choose the final proof after adaptive
oracle queries.  Holding the eventual transcript constant while varying
challenges therefore does not by itself preserve the adversary's real oracle
distribution.  A random-oracle/forking or reprogramming reduction must still
connect that experiment to the uniform fixed-transcript count below.
-/

namespace AspisV5FriFixedTranscriptStrategy

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAdaptiveUnmatched
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriFixedFamilyExperiment
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*}

/-- Regard one fixed ideal transcript as a causal family.  Constant response
functions are valid for deterministic counterfactual re-verification of that
same mathematical transcript; this definition does not claim that a malicious
Fiat--Shamir prover chose it independently of the oracle challenges. -/
def fixedTranscriptFamily (transcript : IdealTranscript K) :
    CausalTranscriptFamily K where
  layer0 := transcript.layer0
  layer1 := fun _ => transcript.layer1
  layer2 := fun _ _ => transcript.layer2
  layer3 := fun _ _ _ => transcript.layer3
  final := fun _ _ _ _ => transcript.publishedFinal

@[simp] theorem fixedTranscriptFamily_layer0
    (transcript : IdealTranscript K) :
    (fixedTranscriptFamily transcript).layer0 = transcript.layer0 := rfl

@[simp] theorem fixedTranscriptFamily_layer1
    (transcript : IdealTranscript K) (z0 : K) :
    (fixedTranscriptFamily transcript).layer1 z0 = transcript.layer1 := rfl

@[simp] theorem fixedTranscriptFamily_layer2
    (transcript : IdealTranscript K) (z0 z1 : K) :
    (fixedTranscriptFamily transcript).layer2 z0 z1 = transcript.layer2 := rfl

@[simp] theorem fixedTranscriptFamily_layer3
    (transcript : IdealTranscript K) (z0 z1 z2 : K) :
    (fixedTranscriptFamily transcript).layer3 z0 z1 z2 =
      transcript.layer3 := rfl

@[simp] theorem fixedTranscriptFamily_final
    (transcript : IdealTranscript K) (z0 z1 z2 z3 : K) :
    (fixedTranscriptFamily transcript).final z0 z1 z2 z3 =
      transcript.publishedFinal := rfl

/-- At every four-challenge tuple, the complete transcript of the constant
family is exactly the fixed ideal transcript. -/
@[simp] theorem fullTranscript_fixedTranscriptFamily
    (transcript : IdealTranscript K) (z0 z1 z2 z3 : K) :
    fullTranscript (fixedTranscriptFamily transcript) z0 z1 z2 z3 =
      transcript := by
  cases transcript
  rfl

/-- The constant counterfactual transcript function supplies the first field
of `ProductionFiatShamirFixedFamilyConnection`.  The remaining production
transcript, failure-inclusion, and hash-distribution fields are intentionally
not discharged here. -/
theorem constantCounterfactualTranscriptsMatchFixedFamily
    (transcript : IdealTranscript K) :
    CounterfactualTranscriptsMatchFixedFamily
      (fixedTranscriptFamily transcript) (fun _ => transcript) := by
  intro challenges
  rcases challenges with ⟨⟨⟨z0, z1⟩, z2⟩, z3⟩
  simp [fullTranscriptForTuple]

section InitialList

variable [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod P) K]

/-- The initial decoder list of the fixed-family prefix is exactly the decoder
list of the fixed ideal transcript. -/
theorem initialCandidateList_fixedTranscriptFamily
    (base : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K) :
    initialCandidateList
        (concreteCodeEncoders base releasedEvaluationPoints)
        (transcriptBeforeRound0 (fixedTranscriptFamily transcript)) =
      initialCandidateList
        (concreteCodeEncoders base releasedEvaluationPoints) transcript := by
  apply initialCandidateList_eq_of_layer0_eq
  rfl

end InitialList

section ReleasedExtraction

variable [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- The single backwards strategy used for one fixed ideal transcript. -/
noncomputable def fixedTranscriptStrategies
    (base : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K) :
    AdaptiveStrategies (K := K) :=
  constructedAdaptiveStrategies base (fixedTranscriptFamily transcript)

/-- The four bad challenge fibres for one fixed ideal transcript. -/
noncomputable def fixedTranscriptBadSets
    (base : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    SuffixConditionedBadSets K releasedChallengeCap :=
  fixedFamilyBadSets base (fixedTranscriptFamily transcript) hfinal htables
    hpublished

/-- The exact four-round bad-tuple bound for a fixed ideal transcript.
There is no existentially chosen strategy or family in the counted event. -/
theorem fixedTranscriptBadChallengeTuples_card_le
    (base : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    (allBadChallengeTuples
      (fixedTranscriptBadSets base transcript hfinal htables hpublished)).card <=
      Fintype.card K ^ 3 *
        (releasedChallengeCap 0 + releasedChallengeCap 1 +
          releasedChallengeCap 2 + releasedChallengeCap 3) := by
  simpa only [fixedTranscriptBadSets, fixedFamilyBadChallengeTuples,
    fixedFamilyBadSets, fixedTranscriptStrategies] using
    fixedFamilyBadChallengeTuples_card_le base
      (fixedTranscriptFamily transcript) hfinal htables hpublished

/-- Uniform probability of the bad event for one fixed ideal transcript. -/
noncomputable def fixedTranscriptUniformBadProbability
    (base : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) : Rat :=
  fixedFamilyUniformBadProbability base (fixedTranscriptFamily transcript)
    hfinal htables hpublished

/-- The fixed transcript inherits the proved uniform bound for one fixed
causal family.  Applying this number to a malicious Fiat--Shamir prover still
requires the production connection described above. -/
theorem fixedTranscriptUniformBadProbability_le
    (base : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    fixedTranscriptUniformBadProbability base transcript hfinal htables
        hpublished ≤
      (releasedChallengeCap 0 + releasedChallengeCap 1 +
        releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
          Fintype.card K :=
  fixedFamilyUniformBadProbability_le base (fixedTranscriptFamily transcript)
    hfinal htables hpublished

/-- Accepted ideal verification of one fixed ideal transcript either
misses the inconsistency set at all eighteen queries, hits one of the four
counted challenge fibres, or yields one member of the at-most-240 initial list
whose four exact folds reach the fixed final polynomial. -/
theorem accepted_fixed_transcript_extracts_or_counted
    (base : FixedSchedule (ZMod P) K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K)
    (haccepts : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      transcript queries) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3) transcript queries \/
      (fixedTranscriptBadSets base transcript hfinal htables hpublished).Occurs
        z0 z1 z2 z3 \/
      ∃ c0 : Coeff0 K,
        c0 ∈ initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints) transcript /\
        (initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          transcript).card <= 240 /\
        coefficientFoldLayer 4 z3
          (coefficientFoldLayer 16 z2
            (coefficientFoldLayer 64 z1
              (coefficientFoldLayer 256 z0 c0))) =
            transcript.publishedFinal := by
  have h := accepted_ideal_fri_extracts_with_constructed_strategy base
    (fixedTranscriptFamily transcript) queries hfinal htables hpublished
    z0 z1 z2 z3 (by simpa using haccepts)
  rcases h with hquery | hbad | hextracted
  · exact Or.inl (by simpa using hquery)
  · exact Or.inr (Or.inl hbad)
  · rcases hextracted with ⟨c0, hc0, hcard, hfold⟩
    refine Or.inr (Or.inr ⟨c0, ?_, ?_, ?_⟩)
    · rw [← initialCandidateList_fixedTranscriptFamily base transcript]
      exact hc0
    · rw [← initialCandidateList_fixedTranscriptFamily base transcript]
      exact hcard
    · simpa using hfold

#print axioms fullTranscript_fixedTranscriptFamily
#print axioms constantCounterfactualTranscriptsMatchFixedFamily
#print axioms initialCandidateList_fixedTranscriptFamily
#print axioms fixedTranscriptBadChallengeTuples_card_le
#print axioms fixedTranscriptUniformBadProbability_le
#print axioms accepted_fixed_transcript_extracts_or_counted

end ReleasedExtraction

end AspisV5FriFixedTranscriptStrategy
