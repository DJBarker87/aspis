import AspisFormal.V5ForwardAcceptedFalseInclusion

set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

/-!
# Prefix-timed restoration of one complete FRI candidate chain

The earlier forward theorem tracks only whether each committed word has some
near codeword.  That is enough for low-degree proximity, but it does not show
that one initial candidate follows all four folds to the published final
polynomial: independently selected near candidates at adjacent layers need
not be compatible.

This file strengthens the forward construction.  Before each challenge it
fixes a response strategy which, for every possible challenge, selects a
near next-layer candidate that has no compatible near predecessor whenever
such a candidate exists.  The existing correlated-agreement theorem then
bounds precisely those challenges.  Outside the resulting prefix-timed bad
sets, *every* near next-layer candidate has a compatible near predecessor.
Starting from the published final polynomial and restoring predecessors
round by round therefore yields one initial decoder-list member whose four
folds are exactly the published final coefficients.

No later challenge is used to define an earlier bad set.
-/

namespace AspisV5FriForwardCompatibleChain

open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FiatShamirAdaptiveQueryBudget
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriForwardDoomSoundness
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5FriRoundByRoundSoundness
open AspisV5FriWeightedCorrelatedAgreementFinalization
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5ForwardAcceptedFalseInclusion
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## Causal selectors for unmatched next-layer candidates -/

def Round0CandidateUnmatched
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K) (candidate : Coeff1 K) : Prop :=
  PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0) candidate /\
    ¬ ∃ predecessor,
      Near0 (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family) predecessor /\
        coefficientFoldLayer 256 z0 predecessor = candidate

def Round1CandidateUnmatched
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K) (candidate : Coeff2 K) : Prop :=
  PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
      (transcriptBeforeRound2 family z0 z1) candidate /\
    ¬ ∃ predecessor,
      PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
          (transcriptBeforeRound1 family z0) predecessor /\
        coefficientFoldLayer 64 z1 predecessor = candidate

def Round2CandidateUnmatched
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K) (candidate : Coeff3 K) : Prop :=
  PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
      (transcriptBeforeRound3 family z0 z1 z2) candidate /\
    ¬ ∃ predecessor,
      PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
          (transcriptBeforeRound2 family z0 z1) predecessor /\
        coefficientFoldLayer 16 z2 predecessor = candidate

noncomputable def firstUnmatched1
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K) : Coeff1 K :=
  chooseNearCandidate (Round0CandidateUnmatched base family z0)

noncomputable def firstUnmatched2
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K) : Coeff2 K :=
  chooseNearCandidate (Round1CandidateUnmatched base family z0 z1)

noncomputable def firstUnmatched3
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K) : Coeff3 K :=
  chooseNearCandidate (Round2CandidateUnmatched base family z0 z1 z2)

theorem firstUnmatched1_spec
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K) (h : ∃ candidate, Round0CandidateUnmatched base family z0 candidate) :
    Round0CandidateUnmatched base family z0 (firstUnmatched1 base family z0) :=
  chooseNearCandidate_spec _ h

theorem firstUnmatched2_spec
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K)
    (h : ∃ candidate, Round1CandidateUnmatched base family z0 z1 candidate) :
    Round1CandidateUnmatched base family z0 z1
      (firstUnmatched2 base family z0 z1) :=
  chooseNearCandidate_spec _ h

theorem firstUnmatched3_spec
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 : K)
    (h : ∃ candidate, Round2CandidateUnmatched base family z0 z1 z2 candidate) :
    Round2CandidateUnmatched base family z0 z1 z2
      (firstUnmatched3 base family z0 z1 z2) :=
  chooseNearCandidate_spec _ h

/-! ## Prefix-timed compatibility bad sets -/

noncomputable def compatibilityRound0Strategy
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K) :
    ProximateStrategy K (Fin 131072) (Coeff1 K) :=
  exactResponseStrategy
    (encoder1 base releasedEvaluationPoints)
    (circleDecodedLanes base (transcriptBeforeRound0 family))
    (firstUnmatched1 base family)

noncomputable def compatibilityRound1Strategy
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 : K) : ProximateStrategy K (Fin 32768) (Coeff2 K) :=
  exactResponseStrategy
    (encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints)
    (line1DecodedLanes (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0))
    (firstUnmatched2 base family z0)

noncomputable def compatibilityRound2Strategy
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 : K) : ProximateStrategy K (Fin 8192) (Coeff3 K) :=
  exactResponseStrategy
    (encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints)
    (line2DecodedLanes (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1))
    (firstUnmatched3 base family z0 z1)

noncomputable def releasedCompatibilityBadSets
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    PrefixConditionedBadSets K releasedChallengeCap where
  round0 := round0Bad base (transcriptBeforeRound0 family)
    (compatibilityRound0Strategy base family)
  round1 z0 := round1Bad (scheduleAfter0 base z0)
    (transcriptBeforeRound1 family z0)
    (compatibilityRound1Strategy base family z0)
  round2 z0 z1 := round2Bad (scheduleAfter1 base z0 z1)
    (transcriptBeforeRound2 family z0 z1)
    (compatibilityRound2Strategy base family z0 z1)
  round3 z0 z1 z2 := round3Bad (scheduleAfter2 base z0 z1 z2)
    (transcriptBeforeRound3 family z0 z1 z2)
    (forwardRound3Strategy base family z0 z1 z2)
  round0_card_le := round0Bad_card_le base (transcriptBeforeRound0 family)
    hfinal htables hpublished (compatibilityRound0Strategy base family)
  round1_card_le := by
    intro z0
    exact round1Bad_card_le (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0)
      (finalXMatches_scheduleAt base z0 0 0 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 0 0 0 htables)
      hpublished (compatibilityRound1Strategy base family z0)
  round2_card_le := by
    intro z0 z1
    exact round2Bad_card_le (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1)
      (finalXMatches_scheduleAt base z0 z1 0 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 z1 0 0 htables)
      hpublished (compatibilityRound2Strategy base family z0 z1)
  round3_card_le := by
    intro z0 z1 z2
    exact round3Bad_card_le (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2)
      (finalXMatches_scheduleAt base z0 z1 z2 0 hfinal)
      (inverseTablesMatch_scheduleAt base z0 z1 z2 0 htables)
      hpublished (forwardRound3Strategy base family z0 z1 z2)

/-! ## State restoration at each round -/

theorem round0_restore_or_bad
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 : K) (candidate : Coeff1 K)
    (hnear : PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0) candidate) :
    (∃ predecessor,
      Near0 (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family) predecessor /\
        coefficientFoldLayer 256 z0 predecessor = candidate) ∨
      z0 ∈ (releasedCompatibilityBadSets base family hfinal htables
        hpublished).round0 := by
  classical
  by_cases hmatching : ∃ predecessor,
      Near0 (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family) predecessor /\
        coefficientFoldLayer 256 z0 predecessor = candidate
  · exact Or.inl hmatching
  apply Or.inr
  have hunmatchedExists : ∃ candidate,
      Round0CandidateUnmatched base family z0 candidate :=
    ⟨candidate, hnear, hmatching⟩
  have hselected := firstUnmatched1_spec base family z0 hunmatchedExists
  have hvalid := round0_exactResponse_valid_of_prefixNear1 base family htables
    (firstUnmatched1 base family) z0 hselected.1
  have hstep := round0_matching_predecessor_or_counted base
    (transcriptBeforeRound0 family) hfinal htables hpublished
    (compatibilityRound0Strategy base family) z0
    (by simpa only [compatibilityRound0Strategy] using hvalid)
  rcases hstep with hpredecessor | hbad
  · exact False.elim (hselected.2 (by
      simpa only [compatibilityRound0Strategy,
        exactResponseStrategy_candidate, HasMatchingPredecessor]
        using hpredecessor))
  · simpa only [releasedCompatibilityBadSets] using hbad.1

theorem round1_restore_or_bad
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 : K) (candidate : Coeff2 K)
    (hnear : PrefixNear2 (scheduleAfter1 base z0 z1)
      releasedEvaluationPoints (transcriptBeforeRound2 family z0 z1)
      candidate) :
    (∃ predecessor,
      PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
          (transcriptBeforeRound1 family z0) predecessor /\
        coefficientFoldLayer 64 z1 predecessor = candidate) ∨
      z1 ∈ (releasedCompatibilityBadSets base family hfinal htables
        hpublished).round1 z0 := by
  classical
  by_cases hmatching : ∃ predecessor,
      PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
          (transcriptBeforeRound1 family z0) predecessor /\
        coefficientFoldLayer 64 z1 predecessor = candidate
  · exact Or.inl hmatching
  apply Or.inr
  have hunmatchedExists : ∃ candidate,
      Round1CandidateUnmatched base family z0 z1 candidate :=
    ⟨candidate, hnear, hmatching⟩
  have hselected := firstUnmatched2_spec base family z0 z1 hunmatchedExists
  have hvalid := round1_exactResponse_valid_of_prefixNear2 base family htables
    (firstUnmatched2 base family z0) z0 z1 hselected.1
  have hstep := round1_matching_predecessor_or_counted
    (scheduleAfter0 base z0) (transcriptBeforeRound1 family z0)
    (finalXMatches_scheduleAt base z0 0 0 0 hfinal)
    (inverseTablesMatch_scheduleAt base z0 0 0 0 htables)
    hpublished (compatibilityRound1Strategy base family z0) z1
    (by simpa only [compatibilityRound1Strategy] using hvalid)
  rcases hstep with hpredecessor | hbad
  · exact False.elim (hselected.2 (by
      simpa only [compatibilityRound1Strategy,
        exactResponseStrategy_candidate, HasMatchingPredecessor]
        using hpredecessor))
  · simpa only [releasedCompatibilityBadSets] using hbad.1

theorem round2_restore_or_bad
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 : K) (candidate : Coeff3 K)
    (hnear : PrefixNear3 (scheduleAfter2 base z0 z1 z2)
      releasedEvaluationPoints (transcriptBeforeRound3 family z0 z1 z2)
      candidate) :
    (∃ predecessor,
      PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
          (transcriptBeforeRound2 family z0 z1) predecessor /\
        coefficientFoldLayer 16 z2 predecessor = candidate) ∨
      z2 ∈ (releasedCompatibilityBadSets base family hfinal htables
        hpublished).round2 z0 z1 := by
  classical
  by_cases hmatching : ∃ predecessor,
      PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
          (transcriptBeforeRound2 family z0 z1) predecessor /\
        coefficientFoldLayer 16 z2 predecessor = candidate
  · exact Or.inl hmatching
  apply Or.inr
  have hunmatchedExists : ∃ candidate,
      Round2CandidateUnmatched base family z0 z1 z2 candidate :=
    ⟨candidate, hnear, hmatching⟩
  have hselected := firstUnmatched3_spec base family z0 z1 z2 hunmatchedExists
  have hvalid := round2_exactResponse_valid_of_prefixNear3 base family htables
    (firstUnmatched3 base family z0 z1) z0 z1 z2 hselected.1
  have hstep := round2_matching_predecessor_or_counted
    (scheduleAfter1 base z0 z1) (transcriptBeforeRound2 family z0 z1)
    (finalXMatches_scheduleAt base z0 z1 0 0 hfinal)
    (inverseTablesMatch_scheduleAt base z0 z1 0 0 htables)
    hpublished (compatibilityRound2Strategy base family z0 z1) z2
    (by simpa only [compatibilityRound2Strategy] using hvalid)
  rcases hstep with hpredecessor | hbad
  · exact False.elim (hselected.2 (by
      simpa only [compatibilityRound2Strategy,
        exactResponseStrategy_candidate, HasMatchingPredecessor]
        using hpredecessor))
  · simpa only [releasedCompatibilityBadSets] using hbad.1

theorem round3_restore_final_or_bad
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K)
    (hdense : 6082 < (consistencySet (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3)).card) :
    (∃ predecessor,
      PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
          (transcriptBeforeRound3 family z0 z1 z2) predecessor /\
        coefficientFoldLayer 4 z3 predecessor =
          family.final z0 z1 z2 z3) ∨
      z3 ∈ (releasedCompatibilityBadSets base family hfinal htables
        hpublished).round3 z0 z1 z2 := by
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
  rcases hstep with hpredecessor | hbad
  · exact Or.inl (by
      simpa only [forwardRound3Strategy, exactResponseStrategy_candidate,
        HasMatchingPredecessor] using hpredecessor)
  · exact Or.inr (by
      simpa only [releasedCompatibilityBadSets] using hbad.1)

/-! ## A complete compatible chain from acceptance -/

/-- Outside a concrete query miss and four prefix-timed bad challenge sets,
ideal FRI acceptance restores one initial decoder-list member whose exact
four folds equal the published final polynomial. -/
theorem accepted_ideal_fri_restores_complete_chain_or_prefix_bad
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
      (releasedCompatibilityBadSets base family hfinal htables hpublished).Occurs
        z0 z1 z2 z3 ∨
      (InitialListHasFinalMatch (scheduleAt base z0 z1 z2 z3)
          (concreteCodeEncoders base releasedEvaluationPoints)
          (fullTranscript family z0 z1 z2 z3) /\
        (initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (fullTranscript family z0 z1 z2 z3)).card ≤ 240) := by
  classical
  let encoders := concreteCodeEncoders base releasedEvaluationPoints
  let transcript := fullTranscript family z0 z1 z2 z3
  by_cases hquery : QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries
  · exact Or.inl hquery
  have hdense : 6082 < (consistencySet (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3)).card :=
    dense_consistency_of_accepts_not_queryFailure
      (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries haccepts hquery
  rcases round3_restore_final_or_bad base family hfinal htables hpublished
      z0 z1 z2 z3 hdense with hround3 | hbad3
  · rcases hround3 with ⟨candidate3, hnear3, hfold3⟩
    rcases round2_restore_or_bad base family hfinal htables hpublished
        z0 z1 z2 candidate3 hnear3 with hround2 | hbad2
    · rcases hround2 with ⟨candidate2, hnear2, hfold2⟩
      rcases round1_restore_or_bad base family hfinal htables hpublished
          z0 z1 candidate2 hnear2 with hround1 | hbad1
      · rcases hround1 with ⟨candidate1, hnear1, hfold1⟩
        rcases round0_restore_or_bad base family hfinal htables hpublished
            z0 candidate1 hnear1 with hround0 | hbad0
        · rcases hround0 with ⟨candidate0, hnear0, hfold0⟩
          apply Or.inr
          apply Or.inr
          have hlistEq :
              initialCandidateList encoders (transcriptBeforeRound0 family) =
                initialCandidateList encoders transcript :=
            initialCandidateList_eq_of_layer0_eq encoders
              (transcriptBeforeRound0 family) transcript (by rfl)
          have hmemberPrefix : candidate0 ∈
              initialCandidateList encoders (transcriptBeforeRound0 family) :=
            (mem_initialCandidateList_iff encoders
              (transcriptBeforeRound0 family) candidate0).2 hnear0
          have hmemberFull : candidate0 ∈
              initialCandidateList encoders transcript := by
            rw [← hlistEq]
            exact hmemberPrefix
          have hfinalMatch :
              finalCoefficientMap (scheduleAt base z0 z1 z2 z3) candidate0 =
                transcript.publishedFinal := by
            rw [finalCoefficientMap_eq_four_folds]
            change coefficientFoldLayer 4 z3
                (coefficientFoldLayer 16 z2
                  (coefficientFoldLayer 64 z1
                    (coefficientFoldLayer 256 z0 candidate0))) =
              family.final z0 z1 z2 z3
            rw [hfold0, hfold1, hfold2, hfold3]
          refine ⟨⟨⟨candidate0, hmemberFull⟩, hfinalMatch⟩, ?_⟩
          rw [← hlistEq]
          exact released_initial_candidate_list_card_le_240 base
            (transcriptBeforeRound0 family) hfinal
        · exact Or.inr (Or.inl (Or.inl hbad0))
      · exact Or.inr (Or.inl (Or.inr (Or.inl hbad1)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl hbad2))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr hbad3))))

/-- Consequently, the accepted terminal-match failure identified by the
relation bridge is itself contained in the concrete query miss or the new
prefix-timed compatibility event. -/
theorem accepted_terminal_match_failure_implies_query_or_prefix_bad
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K)
    (hfailure : AcceptedInitialListTerminalMatchFailure
      (scheduleAt base z0 z1 z2 z3)
      (concreteCodeEncoders base releasedEvaluationPoints)
      (fullTranscript family z0 z1 z2 z3) queries) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript family z0 z1 z2 z3) queries ∨
      (releasedCompatibilityBadSets base family hfinal htables hpublished).Occurs
        z0 z1 z2 z3 := by
  rcases accepted_ideal_fri_restores_complete_chain_or_prefix_bad
      base family queries hfinal htables hpublished z0 z1 z2 z3 hfailure.1 with
    hquery | hbad | hmatching
  · exact Or.inl hquery
  · exact Or.inr hbad
  · exact False.elim (hfailure.2.2 hmatching.1)

/-! ## Exact counting -/

theorem releasedCompatibilityBadChallengeTuples_card_le
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    (prefixBadChallengeTuples
      (releasedCompatibilityBadSets base family hfinal htables hpublished)).card ≤
      Fintype.card K ^ 3 *
        (releasedChallengeCap 0 + releasedChallengeCap 1 +
          releasedChallengeCap 2 + releasedChallengeCap 3) :=
  prefixBadChallengeTuples_card_le
    (releasedCompatibilityBadSets base family hfinal htables hpublished)

theorem releasedCompatibilityBadProbability_le
    [Nonempty K]
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    prefixUniformBadProbability
        (releasedCompatibilityBadSets base family hfinal htables hpublished) ≤
      (releasedChallengeCap 0 + releasedChallengeCap 1 +
        releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
          Fintype.card K :=
  prefixUniformBadProbability_le
    (releasedCompatibilityBadSets base family hfinal htables hpublished)

/-- Specialized saved-prefix bound for the compatibility sets.  A prover may
restore and adaptively choose any previously saved checkpoint of this round;
every fresh ideal challenge still costs at most `cap(round) / |K|`. -/
theorem compatibilityRestorationFailureProbability_le_freshQueries_mul_raw
    [Nonempty K]
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (round : Fin 4)
    (plan : ReleasedPrefixRestorationPlan
      (releasedCompatibilityBadSets base family hfinal htables hpublished)
      round)
    (freshChallenges : Nat) :
    adaptiveFailureProbabilityFromStart plan.toFreshOraclePlan freshChallenges ≤
      (freshChallenges : Rat) *
        releasedRoundRawChallengeBound (K := K) round :=
  restorationFailureProbability_le_freshQueries_mul_raw plan freshChallenges

/-- Specialized work-qualified adaptive bound.  Under the explicit ideal
product-oracle experiment, every arbitrary nonce trial costs at most
`cap(round) / (2^workBits(round) * |K|)`. -/
theorem compatibilityNonceTrialFailureProbability_le_hashQueries_mul
    [Nonempty K]
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (round : Fin 4)
    (plan : ReleasedPrefixNonceTrialPlan
      (releasedCompatibilityBadSets base family hfinal htables hpublished)
      round)
    (nonceTrials : Nat) :
    adaptiveFailureProbabilityFromStart plan.toFreshOraclePlan nonceTrials ≤
      (nonceTrials : Rat) *
        releasedRoundPerNonceTrialBound (K := K) round :=
  nonceTrialFailureProbability_le_hashQueries_mul plan nonceTrials

/-!
## Separate production boundary

The preceding two theorems are ideal-oracle statements.  Applying them to
the deployed verifier still requires both of the following, neither of which
is asserted here:

1. the universal Rust-to-source-driver equality for every accepted body and
   statement, including the exact challenge/query values consumed by the
   verifier; and
2. a computational SHA-256/Fiat--Shamir reduction which realizes each saved
   prefix as the ideal fresh-oracle experiment above and realizes a nonce
   trial as the separate work-tag/challenge product distribution.

Known-answer vectors and released-proof trace tests are evidence for the
first item on tested inputs, not proofs of the universal equality.  Digest
width alone supplies no numerical bound for the second item.
-/

/-! ## Accepted false relation executions -/

/-- **Prefix-timed accepted-false inclusion.**  Ideal FRI acceptance restores
one exact initial-to-final candidate chain outside the query miss and the four
causal compatibility sets.  The existing relation theorem can therefore use
that candidate directly; no terminal-match branch and no backwards
suffix-conditioned event remains. -/
theorem released_ideal_accepted_false_prefix_inclusion
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (base : FixedSchedule (ZMod P) K)
    (causalFamily : CausalTranscriptFamily K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K)
    (relationFamily : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList
        (concreteCodeEncoders base releasedEvaluationPoints)
        (fullTranscript causalFamily z0 z1 z2 z3)})
    (records : CandidateRecords
      {candidate // candidate ∈ initialCandidateList
        (concreteCodeEncoders base releasedEvaluationPoints)
        (fullTranscript causalFamily z0 z1 z2 z3)} K)
    (statement : V5PublicStatement)
    (challenges : TwelveRelationChallenges K)
    (halpha : ScheduleMatchesRelationChallenges
      (scheduleAt base z0 z1 z2 z3) challenges)
    (hfamily : FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (fullTranscript causalFamily z0 z1 z2 z3) relationFamily challenges)
    (hmodeled : ∃ output,
      runModeledRelationVerifier relationFamily challenges = some output)
    (hfri : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      (fullTranscript causalFamily z0 z1 z2 z3) queries)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript causalFamily z0 z1 z2 z3) queries ∨
    (releasedCompatibilityBadSets base causalFamily hfinal htables
      hpublished).Occurs z0 z1 z2 z3 ∨
    (∃ candidate,
      CandidateEarlierFailure rc (relationFamily.execution candidate)
        challenges statement (records candidate)) ∨
    (Fintype.card
        {candidate // candidate ∈ initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (fullTranscript causalFamily z0 z1 z2 z3)} ≤ 240 /\
      challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (relationFamily.execution candidate).adaptiveData)) := by
  classical
  let encoders := concreteCodeEncoders base releasedEvaluationPoints
  let transcript := fullTranscript causalFamily z0 z1 z2 z3
  have hallAccepts : AllCandidateRelationChecksAccept relationFamily challenges :=
    modeled_success_implies_all_candidate_relation_checks_accept
      relationFamily challenges hmodeled
  rcases accepted_ideal_fri_restores_complete_chain_or_prefix_bad
      base causalFamily queries hfinal htables hpublished z0 z1 z2 z3 hfri with
    hquery | hbad | hchain
  · exact Or.inl hquery
  · exact Or.inr (Or.inl hbad)
  · have hcandidateCard :
        Fintype.card
          {candidate // candidate ∈ initialCandidateList encoders transcript} ≤
            240 := by
      simpa only [Fintype.card_coe] using hchain.2
    by_cases hearlier : ∃ candidate,
        CandidateEarlierFailure rc (relationFamily.execution candidate)
          challenges statement (records candidate)
    · exact Or.inr (Or.inr (Or.inl hearlier))
    have hallFalse : AllCandidatesFalse relationFamily challenges :=
      false_statement_outside_all_candidate_failures rc poseidon relationFamily
        records challenges statement noWitness (by
          intro candidate hfailure
          exact hearlier ⟨candidate, hfailure⟩)
    have hmatching : HasMatchingCandidate relationFamily challenges :=
      (initialListHasFinalMatch_iff_relationHasMatchingCandidate
        (scheduleAt base z0 z1 z2 z3) encoders transcript relationFamily
        challenges halpha hfamily).mp hchain.1
    have htwo : (2 : K) ≠ 0 := NeZero.ne _
    have hfour : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero htwo htwo
    have hrepair : challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (relationFamily.execution candidate).adaptiveData) :=
      matching_false_candidate_mem_boundedCandidateRepairEvent
        (fun candidate => relationFamily.execution candidate) challenges hfour
        hallAccepts hallFalse hmatching
    exact Or.inr (Or.inr (Or.inr ⟨hcandidateCard, hrepair⟩))

/-! ## Audit -/

#print axioms round0_restore_or_bad
#print axioms round1_restore_or_bad
#print axioms round2_restore_or_bad
#print axioms round3_restore_final_or_bad
#print axioms accepted_ideal_fri_restores_complete_chain_or_prefix_bad
#print axioms accepted_terminal_match_failure_implies_query_or_prefix_bad
#print axioms releasedCompatibilityBadChallengeTuples_card_le
#print axioms releasedCompatibilityBadProbability_le
#print axioms compatibilityRestorationFailureProbability_le_freshQueries_mul_raw
#print axioms compatibilityNonceTrialFailureProbability_le_hashQueries_mul
#print axioms released_ideal_accepted_false_prefix_inclusion

end AspisV5FriForwardCompatibleChain
