import AspisFormal.V5FriGlobalCausalStrategy
import AspisFormal.V5FriRoundByRoundSoundness

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Forward, round-by-round soundness for the released four-fold FRI path

The backwards candidate selector is useful for one-shot extraction, but its
early bad fibres depend on later challenges.  This file gives the separate
forward argument needed for state restoration and Fiat--Shamir.

At every transcript checkpoint, `chooseNearCandidate` fixes a deterministic
response strategy for *every possible next challenge*.  It uses only the
causal prover response available after that challenge: the next committed
word.  If that next word has a sufficiently close codeword, the strategy
chooses one such codeword; otherwise the next state is still doomed.  The
one-round `unmatchedChallenges` theorem then says that a transition from a
doomed state to a non-doomed state can happen only on an already-fixed bad
challenge set of the released cardinality.

The final published four coefficients are themselves the last codeword, so a
dense accepted query path cannot remain doomed after round three.  Therefore
an accepted proof whose initial word has no close codeword either is a query
miss or crosses one of four prefix-conditioned bad sets.

This is a deterministic ideal-FRI theorem.  It does not identify the ideal
challenges with SHA-256, account for oracle queries or proof of work, prove
that an initial close codeword satisfies the spend relation, or prove Merkle
binding.  Those are separate interfaces.
-/

namespace AspisV5FriForwardDoomSoundness

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5FriRoundByRoundSoundness
open AspisV5FriWeightedCorrelatedAgreementFinalization
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## Deterministic choices made from the causal transcript prefix -/

/-- Choose one object satisfying a proximity predicate, returning zero only
when no such object exists.  This is a proof-side deterministic decoder
choice, not a message added to the protocol. -/
noncomputable def chooseNearCandidate {Candidate : Type*} [Zero Candidate]
    (near : Candidate -> Prop) : Candidate := by
  classical
  exact if h : exists candidate, near candidate then Classical.choose h else 0

theorem chooseNearCandidate_spec {Candidate : Type*} [Zero Candidate]
    (near : Candidate -> Prop) (h : exists candidate, near candidate) :
    near (chooseNearCandidate near) := by
  classical
  simp only [chooseNearCandidate, dif_pos h]
  exact (Classical.choose_spec h)

/-- Candidate for the first committed line word.  As a function of `z0`, it
is fixed before `z0` is sampled by the causal prover algorithm. -/
noncomputable def forwardCandidate1
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K) : Coeff1 K :=
  chooseNearCandidate fun candidate =>
    PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0) candidate

/-- Candidate for the second committed line word. -/
noncomputable def forwardCandidate2
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K) : Coeff2 K :=
  chooseNearCandidate fun candidate =>
    PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
      (transcriptBeforeRound2 family z0 z1) candidate

/-- Candidate for the third committed line word. -/
noncomputable def forwardCandidate3
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K) : Coeff3 K :=
  chooseNearCandidate fun candidate =>
    PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
      (transcriptBeforeRound3 family z0 z1 z2) candidate

theorem forwardCandidate1_spec
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K)
    (h : exists candidate,
      PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
        (transcriptBeforeRound1 family z0) candidate) :
    PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0)
      (forwardCandidate1 base family z0) := by
  exact chooseNearCandidate_spec _ h

theorem forwardCandidate2_spec
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K)
    (h : exists candidate,
      PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
        (transcriptBeforeRound2 family z0 z1) candidate) :
    PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
      (transcriptBeforeRound2 family z0 z1)
      (forwardCandidate2 base family z0 z1) := by
  exact chooseNearCandidate_spec _ h

theorem forwardCandidate3_spec
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K)
    (h : exists candidate,
      PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
        (transcriptBeforeRound3 family z0 z1 z2) candidate) :
    PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
      (transcriptBeforeRound3 family z0 z1 z2)
      (forwardCandidate3 base family z0 z1 z2) := by
  exact chooseNearCandidate_spec _ h

/-! ## Exact strategies and bad sets fixed before each challenge -/

noncomputable def forwardRound0Strategy
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K) :
    ProximateStrategy K (Fin 131072) (Coeff1 K) :=
  exactResponseStrategy
    (encoder1 base releasedEvaluationPoints)
    (circleDecodedLanes base (transcriptBeforeRound0 family))
    (forwardCandidate1 base family)

noncomputable def forwardRound1Strategy
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K) : ProximateStrategy K (Fin 32768) (Coeff2 K) :=
  exactResponseStrategy
    (encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints)
    (line1DecodedLanes (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0))
    (forwardCandidate2 base family z0)

noncomputable def forwardRound2Strategy
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K) : ProximateStrategy K (Fin 8192) (Coeff3 K) :=
  exactResponseStrategy
    (encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints)
    (line2DecodedLanes (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1))
    (forwardCandidate3 base family z0 z1)

noncomputable def forwardRound3Strategy
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K) : ProximateStrategy K (Fin 2048) (Coeff4 K) :=
  exactResponseStrategy
    (encoder4 (scheduleAfter2 base z0 z1 z2))
    (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2))
    (family.final z0 z1 z2)

/-- The four concrete bad sets used by the forward argument.  Each is an
`unmatchedChallenges` set for one strategy fixed at the displayed prefix. -/
noncomputable def releasedForwardBadSets
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    PrefixConditionedBadSets K releasedChallengeCap where
  round0 := round0Bad base (transcriptBeforeRound0 family)
    (forwardRound0Strategy base family)
  round1 z0 := round1Bad (scheduleAfter0 base z0)
    (transcriptBeforeRound1 family z0) (forwardRound1Strategy base family z0)
  round2 z0 z1 := round2Bad (scheduleAfter1 base z0 z1)
    (transcriptBeforeRound2 family z0 z1)
    (forwardRound2Strategy base family z0 z1)
  round3 z0 z1 z2 := round3Bad (scheduleAfter2 base z0 z1 z2)
    (transcriptBeforeRound3 family z0 z1 z2)
    (forwardRound3Strategy base family z0 z1 z2)
  round0_card_le := round0Bad_card_le base (transcriptBeforeRound0 family)
    hfinal htables hpublished (forwardRound0Strategy base family)
  round1_card_le := by
    intro z0
    exact round1Bad_card_le (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0)
      (finalXMatches_scheduleAt base z0 0 0 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 0 0 0 htables)
      hpublished (forwardRound1Strategy base family z0)
  round2_card_le := by
    intro z0 z1
    exact round2Bad_card_le (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1)
      (finalXMatches_scheduleAt base z0 z1 0 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 z1 0 0 htables)
      hpublished (forwardRound2Strategy base family z0 z1)
  round3_card_le := by
    intro z0 z1 z2
    exact round3Bad_card_le (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2)
      (finalXMatches_scheduleAt base z0 z1 z2 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 z1 z2 0 htables)
      hpublished (forwardRound3Strategy base family z0 z1 z2)

/-! ## Doomed states -/

/-- Initially doomed means that the initial received circle word has no
codeword above the released agreement threshold. -/
def InitialDoomed
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K) :
    Prop :=
  ¬ (exists candidate,
    Near0 (concreteCodeEncoders base releasedEvaluationPoints)
      (transcriptBeforeRound0 family) candidate)

/-- After `z0`, the first line word has no prefix-close codeword. -/
def Round1Doomed
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K) : Prop :=
  ¬ (exists candidate,
    PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0) candidate)

/-- After `z1`, the second line word has no prefix-close codeword. -/
def Round2Doomed
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K) : Prop :=
  ¬ (exists candidate,
    PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
      (transcriptBeforeRound2 family z0 z1) candidate)

/-- After `z2`, the third line word has no prefix-close codeword. -/
def Round3Doomed
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K) : Prop :=
  ¬ (exists candidate,
    PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
      (transcriptBeforeRound3 family z0 z1 z2) candidate)

/-! ## A doomed state either persists or crosses its pre-challenge bad set -/

theorem round0_doomed_transition
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 : K) (hdoom : InitialDoomed base family) :
    Round1Doomed base family z0 ∨
      z0 ∈ (releasedForwardBadSets base family hfinal htables hpublished).round0 := by
  classical
  by_cases hnext : Round1Doomed base family z0
  · exact Or.inl hnext
  apply Or.inr
  have hexists : exists candidate,
      PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
        (transcriptBeforeRound1 family z0) candidate := by
    simpa only [Round1Doomed, not_not] using hnext
  have hvalid := round0_exactResponse_valid_of_prefixNear1
    base family htables (forwardCandidate1 base family) z0
    (forwardCandidate1_spec base family z0 hexists)
  have hstep := round0_matching_predecessor_or_counted base
    (transcriptBeforeRound0 family) hfinal htables hpublished
    (forwardRound0Strategy base family) z0
    (by simpa only [forwardRound0Strategy] using hvalid)
  rcases hstep with hmatch | hbad
  · rcases hmatch with ⟨candidate, hnear, _hfold⟩
    exact (hdoom ⟨candidate, hnear⟩).elim
  · simpa only [releasedForwardBadSets] using hbad.1

theorem round1_doomed_transition
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 : K) (hdoom : Round1Doomed base family z0) :
    Round2Doomed base family z0 z1 ∨
      z1 ∈ (releasedForwardBadSets base family hfinal htables hpublished).round1 z0 := by
  classical
  by_cases hnext : Round2Doomed base family z0 z1
  · exact Or.inl hnext
  apply Or.inr
  have hexists : exists candidate,
      PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
        (transcriptBeforeRound2 family z0 z1) candidate := by
    simpa only [Round2Doomed, not_not] using hnext
  have hvalid := round1_exactResponse_valid_of_prefixNear2
    base family htables (forwardCandidate2 base family z0) z0 z1
    (forwardCandidate2_spec base family z0 z1 hexists)
  have hstep := round1_matching_predecessor_or_counted
    (scheduleAfter0 base z0) (transcriptBeforeRound1 family z0)
    (finalXMatches_scheduleAt base z0 0 0 0 hfinal)
    (inverseTablesMatch_scheduleAt base z0 0 0 0 htables)
    hpublished (forwardRound1Strategy base family z0) z1
    (by simpa only [forwardRound1Strategy] using hvalid)
  rcases hstep with hmatch | hbad
  · rcases hmatch with ⟨candidate, hnear, _hfold⟩
    exact (hdoom ⟨candidate, hnear⟩).elim
  · simpa only [releasedForwardBadSets] using hbad.1

theorem round2_doomed_transition
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 : K) (hdoom : Round2Doomed base family z0 z1) :
    Round3Doomed base family z0 z1 z2 ∨
      z2 ∈ (releasedForwardBadSets base family hfinal htables hpublished).round2 z0 z1 := by
  classical
  by_cases hnext : Round3Doomed base family z0 z1 z2
  · exact Or.inl hnext
  apply Or.inr
  have hexists : exists candidate,
      PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
        (transcriptBeforeRound3 family z0 z1 z2) candidate := by
    simpa only [Round3Doomed, not_not] using hnext
  have hvalid := round2_exactResponse_valid_of_prefixNear3
    base family htables (forwardCandidate3 base family z0 z1) z0 z1 z2
    (forwardCandidate3_spec base family z0 z1 z2 hexists)
  have hstep := round2_matching_predecessor_or_counted
    (scheduleAfter1 base z0 z1) (transcriptBeforeRound2 family z0 z1)
    (finalXMatches_scheduleAt base z0 z1 0 0 hfinal)
    (inverseTablesMatch_scheduleAt base z0 z1 0 0 htables)
    hpublished (forwardRound2Strategy base family z0 z1) z2
    (by simpa only [forwardRound2Strategy] using hvalid)
  rcases hstep with hmatch | hbad
  · rcases hmatch with ⟨candidate, hnear, _hfold⟩
    exact (hdoom ⟨candidate, hnear⟩).elim
  · simpa only [releasedForwardBadSets] using hbad.1

/-- A dense accepted path cannot remain doomed after the fourth fold because
the published four coefficients are already a final-layer codeword. -/
theorem round3_doomed_hits_bad
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K) (hdoom : Round3Doomed base family z0 z1 z2)
    (hdense : 6082 < (consistencySet (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3)).card) :
    z3 ∈ (releasedForwardBadSets base family hfinal htables hpublished).round3
      z0 z1 z2 := by
  classical
  have hvalid := round3_exactResponse_valid_of_dense_consistency
    base family htables z0 z1 z2 z3 hdense
  have hstep := round3_matching_predecessor_or_counted
    (scheduleAfter2 base z0 z1 z2)
    (transcriptBeforeRound3 family z0 z1 z2)
    (finalXMatches_scheduleAt base z0 z1 z2 0 hfinal)
    (inverseTablesMatch_scheduleAt base z0 z1 z2 0 htables)
    hpublished (forwardRound3Strategy base family z0 z1 z2) z3
    (by simpa only [forwardRound3Strategy] using hvalid)
  rcases hstep with hmatch | hbad
  · rcases hmatch with ⟨candidate, hnear, _hfold⟩
    exact (hdoom ⟨candidate, hnear⟩).elim
  · simpa only [releasedForwardBadSets] using hbad.1

/-! ## Accepted-proof inclusion in the forward event -/

/-- **Forward round-by-round FRI inclusion.**  If the ideal verifier accepts
an initial word with no close released-code candidate, then either all 18
queries missed a consistency set of size at most `6082`, or the sampled fold
challenges cross a bad set fixed before the corresponding challenge. -/
theorem accepted_far_initial_hits_forward_bad_or_query_failure
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K)
    (haccepts : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries)
    (hdoom : InitialDoomed base family) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript family z0 z1 z2 z3) queries ∨
      (releasedForwardBadSets base family hfinal htables hpublished).Occurs
        z0 z1 z2 z3 := by
  classical
  by_cases hquery : QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries
  · exact Or.inl hquery
  apply Or.inr
  have hdense : 6082 < (consistencySet (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3)).card :=
    dense_consistency_of_accepts_not_queryFailure
      (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries haccepts hquery
  rcases round0_doomed_transition base family hfinal htables hpublished z0 hdoom with
    hdoom1 | hbad0
  · rcases round1_doomed_transition base family hfinal htables hpublished
      z0 z1 hdoom1 with hdoom2 | hbad1
    · rcases round2_doomed_transition base family hfinal htables hpublished
        z0 z1 z2 hdoom2 with hdoom3 | hbad2
      · exact Or.inr (Or.inr (Or.inr
          (round3_doomed_hits_bad base family hfinal htables hpublished
            z0 z1 z2 z3 hdoom3 hdense)))
      · exact Or.inr (Or.inr (Or.inl hbad2))
    · exact Or.inr (Or.inl hbad1)
  · exact Or.inl hbad0

/-- Equivalent positive form: every dense accepted ideal proof either has an
initial candidate in the released decoder list or crosses the forward bad
event.  Unlike the old backwards theorem, the event has the timing needed by
state restoration. -/
theorem accepted_ideal_fri_has_initial_candidate_or_forward_bad
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K)
    (haccepts : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript family z0 z1 z2 z3) queries ∨
      (releasedForwardBadSets base family hfinal htables hpublished).Occurs
        z0 z1 z2 z3 ∨
      exists candidate : Coeff0 K,
        candidate ∈ initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family) /\
        (initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family)).card <= 240 := by
  classical
  by_cases hcandidate : exists candidate,
      Near0 (concreteCodeEncoders base releasedEvaluationPoints)
        (transcriptBeforeRound0 family) candidate
  · apply Or.inr
    apply Or.inr
    rcases hcandidate with ⟨candidate, hnear⟩
    exact ⟨candidate, (mem_initialCandidateList_iff
      (concreteCodeEncoders base releasedEvaluationPoints)
      (transcriptBeforeRound0 family) candidate).2 hnear,
      released_initial_candidate_list_card_le_240 base
        (transcriptBeforeRound0 family) hfinal⟩
  · rcases accepted_far_initial_hits_forward_bad_or_query_failure
      base family queries hfinal htables hpublished z0 z1 z2 z3 haccepts
      hcandidate with hquery | hbad
    · exact Or.inl hquery
    · exact Or.inr (Or.inl hbad)

/-- The released four caps give the same raw one-path count, now for an event
whose bad set at every round is fixed by the preceding transcript prefix. -/
theorem releasedForwardBadChallengeTuples_card_le
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    (prefixBadChallengeTuples
      (releasedForwardBadSets base family hfinal htables hpublished)).card <=
      Fintype.card K ^ 3 *
        (releasedChallengeCap 0 + releasedChallengeCap 1 +
          releasedChallengeCap 2 + releasedChallengeCap 3) :=
  prefixBadChallengeTuples_card_le
    (releasedForwardBadSets base family hfinal htables hpublished)

/-- Exact raw probability bound for one independently uniform four-challenge
path.  No random-oracle query multiplier or work factor is present here. -/
theorem releasedForwardBadProbability_le
    [Nonempty K]
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    prefixUniformBadProbability
        (releasedForwardBadSets base family hfinal htables hpublished) <=
      (releasedChallengeCap 0 + releasedChallengeCap 1 +
        releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
          Fintype.card K :=
  prefixUniformBadProbability_le
    (releasedForwardBadSets base family hfinal htables hpublished)

/-! ## Audit -/

#print axioms chooseNearCandidate_spec
#print axioms releasedForwardBadChallengeTuples_card_le
#print axioms releasedForwardBadProbability_le
#print axioms round0_doomed_transition
#print axioms round1_doomed_transition
#print axioms round2_doomed_transition
#print axioms round3_doomed_hits_bad
#print axioms accepted_far_initial_hits_forward_bad_or_query_failure
#print axioms accepted_ideal_fri_has_initial_candidate_or_forward_bad

end AspisV5FriForwardDoomSoundness
