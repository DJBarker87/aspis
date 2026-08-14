import AspisFormal.V5FriForwardDoomSoundness
import AspisFormal.V5Tag67AcceptedFalseInclusion

set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

/-!
# Accepted false executions using forward-timed FRI bad sets

`V5FriForwardDoomSoundness` proves the round-by-round statement needed for
Fiat--Shamir: a far initial word can become non-doomed only at a bad set fixed
before the current challenge.  This file connects that result to the Tag-67
relation proof.

The connection exposes one additional fact that the low-degree theorem does
not provide.  The relation proof needs one initial decoder-list member whose
four deterministic folds equal the four coefficients published at the end of
FRI.  Merely proving that the initial word has a close codeword does not prove
that terminal equality.  `InitialListTerminalMatchFailure` is the exact
remaining event.

The main theorem therefore returns five honest alternatives:

* the concrete 18-query miss;
* one of the four prefix-conditioned FRI bad challenges;
* an earlier candidate/statement binding failure;
* no initial list member has the required final equality; or
* the already-counted relation repair event.

No backwards suffix-conditioned FRI event is used in this file.
-/

namespace AspisV5ForwardAcceptedFalseInclusion

open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriAdaptiveUnmatched
open AspisV5FriForwardDoomSoundness
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5FriRoundByRoundSoundness
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## The exact terminal equality still needed by the relation proof -/

/-- At least one member of the fixed initial decoder list reaches the final
four coefficients published by the transcript under the four actual fold
challenges. -/
def InitialListHasFinalMatch
    (schedule : FixedSchedule (ZMod P) K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) : Prop :=
  exists candidate :
      {candidate // candidate ∈ initialCandidateList encoders transcript},
    finalCoefficientMap schedule candidate.1 = transcript.publishedFinal

/-- Exact extra event left by the forward low-degree proof: the initial list
may be nonempty, while none of its members' four-fold chains reaches the
published final coefficients. -/
def InitialListTerminalMatchFailure
    (schedule : FixedSchedule (ZMod P) K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) : Prop :=
  ¬ InitialListHasFinalMatch schedule encoders transcript

/-- The terminal-match failure restricted to an actually accepted ideal FRI
path outside the separately counted small-consistency query miss. -/
def AcceptedInitialListTerminalMatchFailure
    (schedule : FixedSchedule (ZMod P) K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072) : Prop :=
  IdealAccepts schedule transcript queries ∧
    ¬ QueryPhaseFailure schedule transcript queries ∧
    InitialListTerminalMatchFailure schedule encoders transcript

/-- Under the already-proved alpha and family equalities, the FRI terminal
match is exactly the relation proof's `HasMatchingCandidate`; it is not a
stronger or differently selected condition. -/
theorem initialListHasFinalMatch_iff_relationHasMatchingCandidate
    (schedule : FixedSchedule (ZMod P) K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (family : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList encoders transcript})
    (challenges : TwelveRelationChallenges K)
    (halpha : ScheduleMatchesRelationChallenges schedule challenges)
    (hfamily : FamilyMatchesFriTranscript encoders transcript family challenges) :
    InitialListHasFinalMatch schedule encoders transcript ↔
      HasMatchingCandidate family challenges := by
  constructor
  · rintro ⟨candidate, hfinal⟩
    exact ⟨candidate, finalMatches_of_extracted_candidate schedule encoders
      transcript family challenges halpha hfamily candidate hfinal⟩
  · rintro ⟨candidate, hmatch⟩
    refine ⟨candidate, ?_⟩
    unfold AcceptedCandidateExecution.FinalMatches at hmatch
    change family.publishedFinal challenges =
      (family.execution candidate).candidateFinal challenges at hmatch
    rw [hfamily.2,
      candidateFinal_eq_finalCoefficientMap schedule encoders transcript
        family challenges halpha hfamily candidate] at hmatch
    exact hmatch.symm

theorem initialListTerminalMatchFailure_iff_noCandidateFinalMatch
    (schedule : FixedSchedule (ZMod P) K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (family : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList encoders transcript})
    (challenges : TwelveRelationChallenges K)
    (halpha : ScheduleMatchesRelationChallenges schedule challenges)
    (hfamily : FamilyMatchesFriTranscript encoders transcript family challenges) :
    InitialListTerminalMatchFailure schedule encoders transcript ↔
      NoCandidateFinalMatch (fun candidate => family.execution candidate)
        challenges := by
  simpa only [InitialListTerminalMatchFailure, NoCandidateFinalMatch,
    HasMatchingCandidate, not_exists] using not_congr
      (initialListHasFinalMatch_iff_relationHasMatchingCandidate schedule
        encoders transcript family challenges halpha hfamily)

/-! ## Why initial proximity alone cannot discharge terminal matching -/

/-- Changing only the published final coefficients preserves initial
proximity but can make the chosen initial candidate's four-fold result differ.
Thus an initial close candidate is not, by itself, enough for the relation
repair theorem. -/
theorem close_initial_candidate_does_not_force_its_final_match
    (schedule : FixedSchedule (ZMod P) K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff0 K)
    (hnear : Near0 encoders transcript candidate) :
    exists altered : IdealTranscript K,
      altered.layer0 = transcript.layer0 ∧
      Near0 encoders altered candidate ∧
      finalCoefficientMap schedule candidate ≠ altered.publishedFinal := by
  classical
  let expected := finalCoefficientMap schedule candidate
  let changed : Coeff4 K :=
    Function.update expected (0 : Fin 4) (expected 0 + 1)
  have hchanged : expected ≠ changed := by
    intro heq
    have hzero := congrFun heq (0 : Fin 4)
    simp [changed] at hzero
  let altered : IdealTranscript K :=
    { transcript with publishedFinal := changed }
  refine ⟨altered, rfl, ?_, ?_⟩
  · simpa only [altered, Near0] using hnear
  · simpa only [altered, expected] using hchanged

/-! ## Exact finite terminal-failure event -/

/-- Four fold challenges for which the fixed causal transcript has no initial
decoder-list member reaching its published final coefficients. -/
noncomputable def terminalMatchFailureTuples
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K) :
    Finset (AspisV5FriAdaptiveUnmatched.FourChallenges K) := by
  classical
  exact Finset.univ.filter fun tuple =>
    InitialListTerminalMatchFailure
      (scheduleAt base tuple.1.1.1 tuple.1.1.2 tuple.1.2 tuple.2)
      (concreteCodeEncoders base releasedEvaluationPoints)
      (fullTranscript family tuple.1.1.1 tuple.1.1.2 tuple.1.2 tuple.2)

@[simp] theorem mem_terminalMatchFailureTuples_iff
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K) (z0 z1 z2 z3 : K) :
    (((z0, z1), z2), z3) ∈ terminalMatchFailureTuples base family ↔
      InitialListTerminalMatchFailure (scheduleAt base z0 z1 z2 z3)
        (concreteCodeEncoders base releasedEvaluationPoints)
        (fullTranscript family z0 z1 z2 z3) := by
  simp [terminalMatchFailureTuples]

/-- The only unconditional cardinality bound currently available for the
terminal-match event is the full challenge space.  A smaller bound requires a
round-by-round *matching/knowledge* theorem, not merely the forward
low-degree/proximity theorem. -/
theorem terminalMatchFailureTuples_card_le_full_space
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K) :
    (terminalMatchFailureTuples base family).card ≤ Fintype.card K ^ 4 := by
  classical
  calc
    (terminalMatchFailureTuples base family).card ≤
        (Finset.univ : Finset
          (AspisV5FriAdaptiveUnmatched.FourChallenges K)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card K ^ 4 := by
      simp [AspisV5FriAdaptiveUnmatched.FourChallenges]
      ring

/-- Named interface for any future nontrivial terminal-match theorem.  It is
kept separate from the four already-proved prefix bad-set caps. -/
def ReleasedTerminalMatchCardinalityBound
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K) (cap : Nat) : Prop :=
  (terminalMatchFailureTuples base family).card ≤ cap

/-- Accepted terminal failures for a counterfactual query schedule at each
four-challenge tuple.  This is the event a future round-by-round knowledge
theorem must bound. -/
noncomputable def acceptedTerminalMatchFailureTuples
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queriesAt : AspisV5FriAdaptiveUnmatched.FourChallenges K →
      QuerySchedule 18 131072) :
    Finset (AspisV5FriAdaptiveUnmatched.FourChallenges K) := by
  classical
  exact Finset.univ.filter fun tuple =>
    AcceptedInitialListTerminalMatchFailure
      (scheduleAt base tuple.1.1.1 tuple.1.1.2 tuple.1.2 tuple.2)
      (concreteCodeEncoders base releasedEvaluationPoints)
      (fullTranscript family tuple.1.1.1 tuple.1.1.2 tuple.1.2 tuple.2)
      (queriesAt tuple)

/-- No nontrivial bound for this event follows from the current forward
proximity theorem; the unconditional finite bound is the full challenge
space. -/
theorem acceptedTerminalMatchFailureTuples_card_le_full_space
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queriesAt : AspisV5FriAdaptiveUnmatched.FourChallenges K →
      QuerySchedule 18 131072) :
    (acceptedTerminalMatchFailureTuples base family queriesAt).card ≤
      Fintype.card K ^ 4 := by
  classical
  calc
    (acceptedTerminalMatchFailureTuples base family queriesAt).card ≤
        (Finset.univ : Finset
          (AspisV5FriAdaptiveUnmatched.FourChallenges K)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card K ^ 4 := by
      simp [AspisV5FriAdaptiveUnmatched.FourChallenges]
      ring

/-- Exact named premise for replacing the terminal branch by a useful
cardinality term in future security accounting. -/
def ReleasedAcceptedTerminalMatchCardinalityBound
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queriesAt : AspisV5FriAdaptiveUnmatched.FourChallenges K →
      QuerySchedule 18 131072)
    (cap : Nat) : Prop :=
  (acceptedTerminalMatchFailureTuples base family queriesAt).card ≤ cap

/-! ## Relation to the existing one-shot extraction theorem -/

/-- For a fixed accepted transcript, terminal-match failure is already
contained in the query-miss event or the existing backwards
suffix-conditioned bad event.  Indeed, the third branch of backwards
extraction supplies an initial-list member whose four exact folds equal the
published final coefficients, contradicting terminal-match failure.

This result preserves the previously proved one-shot inclusion.  It does
*not* make the suffix-conditioned event suitable for round-by-round
Fiat--Shamir reasoning: its strategy still selects candidates using later
challenges.  The missing theorem is a prefix-timed/adaptive bound for the
accepted terminal-match event itself. -/
theorem accepted_terminal_match_failure_implies_query_or_backward_suffix
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
      (adaptiveBadSets base family hfinal htables hpublished
        (constructedAdaptiveStrategies base family)).Occurs z0 z1 z2 z3 := by
  classical
  let encoders := concreteCodeEncoders base releasedEvaluationPoints
  let transcript := fullTranscript family z0 z1 z2 z3
  have hextracted := accepted_ideal_fri_extracts_with_constructed_strategy
    base family queries hfinal htables hpublished z0 z1 z2 z3 hfailure.1
  rcases hextracted with hquery | hbad | hextracted
  · exact Or.inl hquery
  · exact Or.inr hbad
  · rcases hextracted with ⟨candidate, hmember, _hcard, hfold⟩
    have hlistEq :
        initialCandidateList encoders (transcriptBeforeRound0 family) =
          initialCandidateList encoders transcript :=
      initialCandidateList_eq_of_layer0_eq encoders
        (transcriptBeforeRound0 family) transcript (by rfl)
    have hmemberFull : candidate ∈ initialCandidateList encoders transcript := by
      rw [← hlistEq]
      exact hmember
    have hfinalMatch :
        finalCoefficientMap (scheduleAt base z0 z1 z2 z3) candidate =
          transcript.publishedFinal := by
      rw [finalCoefficientMap_eq_four_folds]
      change coefficientFoldLayer 4 z3
          (coefficientFoldLayer 16 z2
            (coefficientFoldLayer 64 z1
              (coefficientFoldLayer 256 z0 candidate))) =
        family.final z0 z1 z2 z3
      exact hfold
    exact False.elim (hfailure.2.2 ⟨⟨candidate, hmemberFull⟩, hfinalMatch⟩)

/-! ## Released accepted-false inclusion -/

/-- **Forward-timed accepted-false inclusion.**  This is the relation-chain
analogue of the previous backwards-extraction theorem, but it uses only the
prefix-conditioned FRI event.

The terminal-match branch is explicit because the forward low-degree theorem
returns an initial close candidate, whereas the relation repair theorem needs
one candidate whose exact four folds equal the published final polynomial. -/
theorem released_ideal_accepted_false_forward_inclusion
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
    (hmodeled : exists output,
      runModeledRelationVerifier relationFamily challenges = some output)
    (hfri : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      (fullTranscript causalFamily z0 z1 z2 z3) queries)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript causalFamily z0 z1 z2 z3) queries ∨
    (releasedForwardBadSets base causalFamily hfinal htables hpublished).Occurs
      z0 z1 z2 z3 ∨
    (exists candidate,
      CandidateEarlierFailure rc (relationFamily.execution candidate)
        challenges statement (records candidate)) ∨
    AcceptedInitialListTerminalMatchFailure (scheduleAt base z0 z1 z2 z3)
      (concreteCodeEncoders base releasedEvaluationPoints)
      (fullTranscript causalFamily z0 z1 z2 z3) queries ∨
    (Fintype.card
        {candidate // candidate ∈ initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (fullTranscript causalFamily z0 z1 z2 z3)} ≤ 240 ∧
      challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (relationFamily.execution candidate).adaptiveData)) := by
  classical
  let encoders := concreteCodeEncoders base releasedEvaluationPoints
  let transcript := fullTranscript causalFamily z0 z1 z2 z3
  have hallAccepts : AllCandidateRelationChecksAccept relationFamily challenges :=
    modeled_success_implies_all_candidate_relation_checks_accept
      relationFamily challenges hmodeled
  by_cases hquery : QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
      (fullTranscript causalFamily z0 z1 z2 z3) queries
  · exact Or.inl hquery
  have hforward := accepted_ideal_fri_has_initial_candidate_or_forward_bad
    base causalFamily queries hfinal htables hpublished z0 z1 z2 z3 hfri
  rcases hforward with hqueryFailure | hbad | hinitial
  · exact False.elim (hquery hqueryFailure)
  · exact Or.inr (Or.inl hbad)
  · rcases hinitial with ⟨_candidate, _hmember, hcardBefore⟩
    have hlistEq :
        initialCandidateList encoders (transcriptBeforeRound0 causalFamily) =
          initialCandidateList encoders transcript :=
      initialCandidateList_eq_of_layer0_eq encoders
        (transcriptBeforeRound0 causalFamily) transcript (by rfl)
    have hcardFull :
        (initialCandidateList encoders transcript).card ≤ 240 := by
      rw [← hlistEq]
      exact hcardBefore
    have hcandidateCard :
        Fintype.card
          {candidate // candidate ∈ initialCandidateList encoders transcript} ≤
            240 := by
      simpa only [Fintype.card_coe] using hcardFull
    by_cases hearlier : exists candidate,
        CandidateEarlierFailure rc (relationFamily.execution candidate)
          challenges statement (records candidate)
    · exact Or.inr (Or.inr (Or.inl hearlier))
    have hallFalse : AllCandidatesFalse relationFamily challenges :=
      false_statement_outside_all_candidate_failures rc poseidon relationFamily
        records challenges statement noWitness (by
          intro candidate hfailure
          exact hearlier ⟨candidate, hfailure⟩)
    by_cases hterminal : InitialListTerminalMatchFailure
        (scheduleAt base z0 z1 z2 z3) encoders transcript
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hfri, hquery, hterminal⟩)))
    have hmatching : HasMatchingCandidate relationFamily challenges :=
      (initialListHasFinalMatch_iff_relationHasMatchingCandidate
        (scheduleAt base z0 z1 z2 z3) encoders transcript relationFamily
        challenges halpha hfamily).mp (by
          simpa only [InitialListTerminalMatchFailure, not_not] using hterminal)
    have htwo : (2 : K) ≠ 0 := NeZero.ne _
    have hfour : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero htwo htwo
    have hrepair : challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (relationFamily.execution candidate).adaptiveData) :=
      matching_false_candidate_mem_boundedCandidateRepairEvent
        (fun candidate => relationFamily.execution candidate) challenges hfour
        hallAccepts hallFalse hmatching
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hcandidateCard, hrepair⟩)))

/-! ## Axiom audit -/

#print axioms initialListHasFinalMatch_iff_relationHasMatchingCandidate
#print axioms initialListTerminalMatchFailure_iff_noCandidateFinalMatch
#print axioms close_initial_candidate_does_not_force_its_final_match
#print axioms terminalMatchFailureTuples_card_le_full_space
#print axioms acceptedTerminalMatchFailureTuples_card_le_full_space
#print axioms accepted_terminal_match_failure_implies_query_or_backward_suffix
#print axioms released_ideal_accepted_false_forward_inclusion

end AspisV5ForwardAcceptedFalseInclusion
