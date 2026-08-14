import AspisFormal.V5FriCoherentCandidateExtraction
import AspisFormal.V5Tag67CandidateTraceExtraction
import AspisFormal.V5Tag67ModeledRelationAcceptanceBridge

/-!
# Accepted false Tag-67 executions: the final deterministic inclusion

This file composes the three deterministic pieces proved in the neighbouring
files.  For the one initial FRI decoder list, a raw accepted false execution
has one of five outcomes:

* the raw Rust success was not reproduced by the maintained relation model;
* the raw FRI success was not reproduced by the ideal arithmetic model;
* one of the explicit query, fold-reduction, or list-size failures occurred;
* one member of the initial list hits a concrete earlier failure in claim
  batching, lane binding, public fields, arithmetic rows, or hash/Merkle rows;
  or
* the twelve relation challenges belong to the union of repair events for
  that single initial list, whose cardinality is at most 240.

The last alternative is the proved custom-relation inclusion.  The first four
alternatives are deliberately still visible: this theorem does not assign
them probability bounds and therefore is not an end-to-end deployed
soundness theorem.
-/

namespace AspisV5Tag67AcceptedFalseInclusion

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriRelationCandidateBridge
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5WithoutReplacementQuerySoundness

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-! ## Exact, non-circular boundaries -/

/-- The four FRI fold challenges are the four alphas in the relation
challenge tuple. -/
def ScheduleMatchesRelationChallenges
    (schedule : FixedSchedule F K)
    (challenges : TwelveRelationChallenges K) : Prop :=
  schedule.alpha 0 = (round0Block challenges).2 /\
  schedule.alpha 1 = (round1Block challenges).2 /\
  schedule.alpha 2 = (round2Block challenges).2 /\
  schedule.alpha 3 = (round3Block challenges).2

/-- The relation family is built from the one initial FRI decoder list and
uses the same four published final coefficients. -/
def FamilyMatchesFriTranscript
    [Fintype K] [DecidableEq K]
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (family : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList encoders transcript})
    (challenges : TwelveRelationChallenges K) : Prop :=
  (∀ candidate, family.initialValues candidate = candidate.1) /\
  family.publishedFinal challenges = transcript.publishedFinal

/-- Concrete code/model failure for the relation sub-verifier.  Its
conclusion is failure of the explicit early-return model, not a restatement
of `RelationAccepts` or of repair-event membership. -/
def RawRelationModelFailure
    [Fintype K] [DecidableEq K]
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (rawAccepts : TwelveRelationChallenges K → Prop)
    (challenges : TwelveRelationChallenges K) : Prop :=
  rawAccepts challenges /\
    ¬ ∃ output, runModeledRelationVerifier family challenges = some output

/-- Concrete raw/ideal FRI boundary. -/
def RawFriArithmeticFailure
    [Fintype K] [DecidableEq K]
    (rawAccepts : TwelveRelationChallenges K → Prop)
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (challenges : TwelveRelationChallenges K) : Prop :=
  rawAccepts challenges /\ ¬ IdealAccepts schedule transcript queries

section FiniteField

variable [Fintype K] [DecidableEq K]

/-! ## FRI final-coefficient match -/

/-- Exact four-fold equality between one list candidate and its relation
execution, provided the FRI and relation alphas are the same. -/
theorem candidateFinal_eq_finalCoefficientMap
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (family : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList encoders transcript})
    (challenges : TwelveRelationChallenges K)
    (halpha : ScheduleMatchesRelationChallenges schedule challenges)
    (hfamily : FamilyMatchesFriTranscript encoders transcript family challenges)
    (candidate : {c // c ∈ initialCandidateList encoders transcript}) :
    (family.execution candidate).candidateFinal challenges =
      finalCoefficientMap schedule candidate.1 := by
  rcases halpha with ⟨h0, h1, h2, h3⟩
  rw [finalCoefficientMap_eq_four_folds]
  simp only [AcceptedCandidateExecution.candidateFinal,
    AcceptedCandidateExecution.values3, AcceptedCandidateExecution.values2,
    AcceptedCandidateExecution.values1, CoherentCandidateFamily.execution,
    RelationRoundMessages.nextValues, fold0, fold1, fold2, fold3]
  rw [hfamily.1 candidate]
  rw [h0, h1, h2, h3]
  rfl

/-- An extracted initial candidate whose four FRI folds reach the published
final polynomial satisfies the relation proof's `FinalMatches` predicate. -/
theorem finalMatches_of_extracted_candidate
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (family : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList encoders transcript})
    (challenges : TwelveRelationChallenges K)
    (halpha : ScheduleMatchesRelationChallenges schedule challenges)
    (hfamily : FamilyMatchesFriTranscript encoders transcript family challenges)
    (candidate : {c // c ∈ initialCandidateList encoders transcript})
    (hfinal : finalCoefficientMap schedule candidate.1 =
      transcript.publishedFinal) :
    (family.execution candidate).FinalMatches challenges := by
  unfold AcceptedCandidateExecution.FinalMatches
  change family.publishedFinal challenges =
    (family.execution candidate).candidateFinal challenges
  rw [hfamily.2, candidateFinal_eq_finalCoefficientMap schedule encoders
    transcript family challenges halpha hfamily candidate, hfinal]

/-! ## Final deterministic inclusion -/

set_option maxRecDepth 10000

/-- Every accepted false execution is in one explicit unfinished boundary or
in the counted repair-event union for the single initial decoder list.

There is no `240^4` selection: the candidate type below is exactly the
subtype of `initialCandidateList`; all later coefficient layers are the
deterministic folds in `family.execution`. -/
theorem raw_accepted_false_failure_or_single_list_repair
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (family : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList encoders transcript})
    (records : CandidateRecords
      {candidate // candidate ∈ initialCandidateList encoders transcript} K)
    (statement : V5PublicStatement)
    (rawAccepts : TwelveRelationChallenges K → Prop)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (halpha : ScheduleMatchesRelationChallenges schedule challenges)
    (hfamily : FamilyMatchesFriTranscript encoders transcript family challenges)
    (hraw : rawAccepts challenges)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    RawRelationModelFailure family rawAccepts challenges ∨
    RawFriArithmeticFailure rawAccepts schedule transcript queries challenges ∨
    FriSideFailure schedule encoders transcript queries ∨
    (∃ candidate,
      CandidateEarlierFailure rc (family.execution candidate) challenges
        statement (records candidate)) ∨
    (Fintype.card
        {candidate // candidate ∈ initialCandidateList encoders transcript} ≤ 240 /\
      challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (family.execution candidate).adaptiveData)) := by
  classical
  by_cases hrelation : ∃ output,
      runModeledRelationVerifier family challenges = some output
  · have hallAccepts : AllCandidateRelationChecksAccept family challenges :=
      modeled_success_implies_all_candidate_relation_checks_accept
        family challenges hrelation
    by_cases hfri : IdealAccepts schedule transcript queries
    · rcases accepted_ideal_fri_failure_or_bounded_matching_candidate
        schedule encoders transcript queries hfri with hfriFailure | hextracted
      · exact Or.inr (Or.inr (Or.inl hfriFailure))
      · rcases hextracted with ⟨candidate, hfinal, hcard⟩
        by_cases hearlier : ∃ candidate,
            CandidateEarlierFailure rc (family.execution candidate) challenges
              statement (records candidate)
        · exact Or.inr (Or.inr (Or.inr (Or.inl hearlier)))
        · have hallFalse : AllCandidatesFalse family challenges :=
            false_statement_outside_all_candidate_failures rc poseidon family
              records challenges statement noWitness (by
                intro candidate hfailure
                exact hearlier ⟨candidate, hfailure⟩)
          have hmatches :
              (family.execution candidate).FinalMatches challenges :=
            finalMatches_of_extracted_candidate schedule encoders transcript
              family challenges halpha hfamily candidate hfinal
          have hrepair :=
            matching_false_candidate_mem_boundedCandidateRepairEvent
              (fun candidate => family.execution candidate) challenges hfour
              hallAccepts hallFalse ⟨candidate, hmatches⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hcard, hrepair⟩)))
    · exact Or.inr (Or.inl ⟨hraw, hfri⟩)
  · exact Or.inl ⟨hraw, hrelation⟩

/-- Direct inclusion form.  Once the four explicitly named unfinished
boundaries are excluded, a raw accepted proof of a statement with no spend
witness is in the repair-event union for the one initial decoder list, and
that list contains at most 240 candidates. -/
theorem raw_accepted_false_mem_single_list_repair
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (family : CoherentCandidateFamily K
      {candidate // candidate ∈ initialCandidateList encoders transcript})
    (records : CandidateRecords
      {candidate // candidate ∈ initialCandidateList encoders transcript} K)
    (statement : V5PublicStatement)
    (rawAccepts : TwelveRelationChallenges K → Prop)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (halpha : ScheduleMatchesRelationChallenges schedule challenges)
    (hfamily : FamilyMatchesFriTranscript encoders transcript family challenges)
    (hraw : rawAccepts challenges)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode)
    (hrelation : ∃ output,
      runModeledRelationVerifier family challenges = some output)
    (hfri : IdealAccepts schedule transcript queries)
    (hnoFriFailure : ¬ FriSideFailure schedule encoders transcript queries)
    (hnoEarlierFailure : ∀ candidate,
      ¬ CandidateEarlierFailure rc (family.execution candidate) challenges
        statement (records candidate)) :
    Fintype.card
        {candidate // candidate ∈ initialCandidateList encoders transcript} ≤ 240 /\
      challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (family.execution candidate).adaptiveData) := by
  rcases raw_accepted_false_failure_or_single_list_repair rc poseidon schedule
      encoders transcript queries family records statement rawAccepts challenges
      hfour halpha hfamily hraw noWitness with
    hrelationFailure | hfriFailure | hfriSide | hearlier | hrepair
  · exact False.elim (hrelationFailure.2 hrelation)
  · exact False.elim (hfriFailure.2 hfri)
  · exact False.elim (hnoFriFailure hfriSide)
  · rcases hearlier with ⟨candidate, hfailure⟩
    exact False.elim (hnoEarlierFailure candidate hfailure)
  · exact hrepair

#print axioms candidateFinal_eq_finalCoefficientMap
#print axioms finalMatches_of_extracted_candidate
#print axioms raw_accepted_false_failure_or_single_list_repair
#print axioms raw_accepted_false_mem_single_list_repair

end FiniteField

end AspisV5Tag67AcceptedFalseInclusion
