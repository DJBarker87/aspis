import AspisFormal.V5FriInitialListBound
import AspisFormal.V5Tag67AcceptedFalseInclusion

/-!
# The Tag-67 candidate list is fixed before the relation challenges

The V5 verifier fixes the two layer-zero Merkle roots and then samples the
batching challenge `gamma` before it begins the four relation rounds.  Thus,
after conditioning on the transcript at that point, the effective layer-zero
word is fixed before the eight OOD-mix challenges and four fold challenges.

Later FRI words, claimed values, and the final polynomial may depend on the
earlier relation challenges.  Candidate extraction may therefore select a
different member for different complete challenge tuples.  That does not
allow a different *list*: the initial decoder list depends only on the fixed
layer-zero word.

This file records that timing fact in a form suitable for the probability
argument.  It provides:

* one list constructed directly from the pre-round layer-zero word;
* a transport from every pointwise transcript's candidate subtype to that one
  fixed subtype; and
* an exact inclusion theorem showing that a candidate selected after seeing
  the complete challenge tuple is still covered by the union over the fixed
  family.  There is no extra factor for the number of selection functions.

The premise that every modeled continuation has the same layer-zero word is
the remaining commitment/transcript boundary.  This file does not prove
Merkle binding or Fiat--Shamir security.
-/

namespace AspisV5Tag67FixedCandidateTiming

open AspisV5FriCoherentCandidateExtraction
open AspisV5FriInitialListBound
open AspisV5FriRelationCandidateBridge
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67RelationListInclusion

variable {K : Type*} [Field K]

set_option maxRecDepth 10000

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- The initial decoder list written without any later transcript fields.

This is the set that must be fixed when the twelve relation challenges begin.
-/
noncomputable def fixedInitialCandidateList
    (encoders : CodeEncoders K) (layer0 : Word0 K) : Finset (Coeff0 K) := by
  classical
  exact Finset.univ.filter fun candidate =>
    agreementCap0 < (agreementSet layer0 (encoders.layer0 candidate)).card

omit [Field K] in
@[simp] theorem mem_fixedInitialCandidateList_iff
    (encoders : CodeEncoders K) (layer0 : Word0 K)
    (candidate : Coeff0 K) :
    candidate ∈ fixedInitialCandidateList encoders layer0 ↔
      agreementCap0 <
        (agreementSet layer0 (encoders.layer0 candidate)).card := by
  simp [fixedInitialCandidateList]

omit [Field K] in
/-- The original transcript-indexed definition is exactly the list made from
its layer-zero word; none of the three later words or final coefficients occur
in it. -/
theorem initialCandidateList_eq_fixedInitialCandidateList
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) :
    initialCandidateList encoders transcript =
      fixedInitialCandidateList encoders transcript.layer0 := by
  classical
  apply Finset.ext
  intro candidate
  simp [initialCandidateList, fixedInitialCandidateList, Near0]

/-- The elementary Johnson argument applies directly to the word-only list.
The only coding-theory premise is the initial encoder's distance bound. -/
theorem fixedInitialCandidateList_card_le_222
    (encoders : CodeEncoders K) (layer0 : Word0 K)
    (hdistance : InitialEncoderDistance encoders) :
    (fixedInitialCandidateList encoders layer0).card ≤ 222 := by
  let transcript : IdealTranscript K := {
    layer0 := layer0
    layer1 := fun _ => 0
    layer2 := fun _ => 0
    layer3 := fun _ => 0
    publishedFinal := fun _ => 0
  }
  rw [← initialCandidateList_eq_fixedInitialCandidateList encoders transcript]
  exact initialCandidateList_card_le_222 encoders transcript hdistance

/-- The deployed cap follows from the stronger bound `222`. -/
theorem fixedInitialCandidateList_card_le_240
    (encoders : CodeEncoders K) (layer0 : Word0 K)
    (hdistance : InitialEncoderDistance encoders) :
    (fixedInitialCandidateList encoders layer0).card ≤ 240 :=
  (fixedInitialCandidateList_card_le_222 encoders layer0 hdistance).trans
    (by omega)

/-- A possibly challenge-dependent continuation of one pre-round layer-zero
word.  The later words and final polynomial are deliberately unrestricted;
only the data that determines the initial list is fixed. -/
structure FixedLayer0Continuation (K Challenge : Type*) where
  layer0 : Word0 K
  transcript : Challenge → IdealTranscript K
  layer0_eq : ∀ challenge, (transcript challenge).layer0 = layer0

omit [Field K] in
/-- Every continuation has the same initial list. -/
theorem FixedLayer0Continuation.initialCandidateList_eq
    {Challenge : Type*}
    (continuation : FixedLayer0Continuation K Challenge)
    (encoders : CodeEncoders K) (challenge : Challenge) :
    initialCandidateList encoders (continuation.transcript challenge) =
      fixedInitialCandidateList encoders continuation.layer0 := by
  rw [initialCandidateList_eq_fixedInitialCandidateList,
    continuation.layer0_eq challenge]

/-- The single candidate type fixed before the relation challenges. -/
abbrev FixedInitialCandidate
    (encoders : CodeEncoders K) (layer0 : Word0 K) :=
  {candidate // candidate ∈ fixedInitialCandidateList encoders layer0}

/-- The subtype used to index the fixed repair-event union also has at most
240 members. -/
theorem fixedInitialCandidate_fintype_card_le_240
    (encoders : CodeEncoders K) (layer0 : Word0 K)
    (hdistance : InitialEncoderDistance encoders) :
    Fintype.card (FixedInitialCandidate encoders layer0) ≤ 240 := by
  change Fintype.card
    {candidate : Coeff0 K // candidate ∈
      fixedInitialCandidateList encoders layer0} ≤ 240
  rw [Fintype.card_coe]
  exact fixedInitialCandidateList_card_le_240 encoders layer0 hdistance

/-- Transport a candidate extracted from a complete, challenge-dependent
continuation into the one pre-round candidate family. -/
def FixedLayer0Continuation.toFixedCandidate
    {Challenge : Type*}
    (continuation : FixedLayer0Continuation K Challenge)
    (encoders : CodeEncoders K) (challenge : Challenge)
    (candidate :
      {candidate // candidate ∈
        initialCandidateList encoders (continuation.transcript challenge)}) :
    FixedInitialCandidate encoders continuation.layer0 :=
  ⟨candidate.1, by
    rw [← continuation.initialCandidateList_eq encoders challenge]
    exact candidate.2⟩

/-- Transport a member of the fixed family back to a pointwise transcript's
presentation of the same list. -/
def FixedLayer0Continuation.toTranscriptCandidate
    {Challenge : Type*}
    (continuation : FixedLayer0Continuation K Challenge)
    (encoders : CodeEncoders K) (challenge : Challenge)
    (candidate : FixedInitialCandidate encoders continuation.layer0) :
    {candidate // candidate ∈
      initialCandidateList encoders (continuation.transcript challenge)} :=
  ⟨candidate.1, by
    rw [continuation.initialCandidateList_eq encoders challenge]
    exact candidate.2⟩

omit [Field K] in
/-- Pointwise candidate selection is covered by a union over the one fixed
family.  The selected member may be an arbitrary function of the complete
challenge tuple. -/
theorem pointwise_selected_event_subset_fixed_family_union
    {Challenge : Type*} [Fintype Challenge] [DecidableEq Challenge]
    (continuation : FixedLayer0Continuation K Challenge)
    (encoders : CodeEncoders K)
    (accepted : Finset Challenge)
    (event : FixedInitialCandidate encoders continuation.layer0 →
      Finset Challenge)
    (hextract : ∀ challenge, challenge ∈ accepted →
      ∃ candidate :
        {candidate // candidate ∈
          initialCandidateList encoders (continuation.transcript challenge)},
        challenge ∈ event
          (continuation.toFixedCandidate encoders challenge candidate)) :
    accepted ⊆ Finset.univ.biUnion event := by
  classical
  intro challenge haccepts
  rcases hextract challenge haccepts with ⟨candidate, hevent⟩
  rw [Finset.mem_biUnion]
  exact ⟨continuation.toFixedCandidate encoders challenge candidate,
    Finset.mem_univ _, hevent⟩

/-! ## Exact specialization to the relation repair events -/

/-- Even if FRI extraction selects its matching candidate pointwise after all
twelve relation challenges, every accepted false tuple is covered by the
repair-event union for the fixed pre-round candidate family.

The execution attached to each fixed candidate is one adaptive strategy:
later round messages may depend on earlier challenge prefixes as represented
by `AcceptedCandidateExecution`. -/
theorem falseAcceptEvent_subset_fixedCandidateRepairEvent
    (continuation :
      FixedLayer0Continuation K (TwelveRelationChallenges K))
    (encoders : CodeEncoders K)
    (executions : FixedInitialCandidate encoders continuation.layer0 →
      AcceptedCandidateExecution K)
    (FalseAccept : TwelveRelationChallenges K → Prop)
    (hfour : (4 : K) ≠ 0)
    (hextract : ∀ {challenges}, FalseAccept challenges →
      ∃ candidate :
        {candidate // candidate ∈
          initialCandidateList encoders
            (continuation.transcript challenges)},
        let fixed := continuation.toFixedCandidate encoders challenges candidate
        (executions fixed).RelationAccepts challenges ∧
        (executions fixed).FinalMatches challenges ∧
        (executions fixed).FalseForCandidate challenges) :
    falseAcceptEvent FalseAccept ⊆
      boundedCandidateRepairEvent
        (fun candidate => (executions candidate).adaptiveData) := by
  classical
  apply pointwise_selected_event_subset_fixed_family_union
    continuation encoders (falseAcceptEvent FalseAccept)
      (fun candidate =>
        adaptiveFixedCandidateRepairEvent (executions candidate).adaptiveData)
  intro challenges hfalseEvent
  have hfalse : FalseAccept challenges := by
    simpa [falseAcceptEvent] using hfalseEvent
  rcases hextract hfalse with ⟨candidate, haccepts, hfinal, hcandidateFalse⟩
  let fixed := continuation.toFixedCandidate encoders challenges candidate
  have hrepair := (executions fixed).accepted_false_mem_repairEvent
    challenges hfour haccepts hfinal hcandidateFalse
  exact ⟨candidate, hrepair⟩

/-- With the pre-round list bounded by 240, the preceding pointwise
extraction has exactly the existing `240 * 32 * |K|^11` count.  No factor for
challenge-dependent candidate selection is introduced. -/
theorem falseAcceptEvent_card_le_240_of_fixed_initial_list
    (continuation :
      FixedLayer0Continuation K (TwelveRelationChallenges K))
    (encoders : CodeEncoders K)
    (executions : FixedInitialCandidate encoders continuation.layer0 →
      AcceptedCandidateExecution K)
    (FalseAccept : TwelveRelationChallenges K → Prop)
    (hfour : (4 : K) ≠ 0)
    (hdistance : InitialEncoderDistance encoders)
    (hextract : ∀ {challenges}, FalseAccept challenges →
      ∃ candidate :
        {candidate // candidate ∈
          initialCandidateList encoders
            (continuation.transcript challenges)},
        let fixed := continuation.toFixedCandidate encoders challenges candidate
        (executions fixed).RelationAccepts challenges ∧
        (executions fixed).FinalMatches challenges ∧
        (executions fixed).FalseForCandidate challenges) :
    (falseAcceptEvent FalseAccept).card ≤
      240 * (32 * Fintype.card K ^ 11) := by
  have hsubset := falseAcceptEvent_subset_fixedCandidateRepairEvent
    continuation encoders executions FalseAccept hfour hextract
  have hfixedCard :
      Fintype.card (FixedInitialCandidate encoders continuation.layer0) ≤
        240 :=
    fixedInitialCandidate_fintype_card_le_240 encoders continuation.layer0
      hdistance
  exact (Finset.card_le_card hsubset).trans
    (boundedCandidateRepairEvent_card_le_240
      (fun candidate => (executions candidate).adaptiveData) hfixedCard)

/-- Probability form of the fixed-family theorem.  Pointwise extraction from
challenge-dependent continuations still costs one union over at most 240
pre-round candidates, giving the existing `32 * 240 / |K|` relation bound. -/
theorem uniformFalseAcceptProbability_le_240_of_fixed_initial_list
    (continuation :
      FixedLayer0Continuation K (TwelveRelationChallenges K))
    (encoders : CodeEncoders K)
    (executions : FixedInitialCandidate encoders continuation.layer0 →
      AcceptedCandidateExecution K)
    (FalseAccept : TwelveRelationChallenges K → Prop)
    (hfour : (4 : K) ≠ 0)
    (hdistance : InitialEncoderDistance encoders)
    (hextract : ∀ {challenges}, FalseAccept challenges →
      ∃ candidate :
        {candidate // candidate ∈
          initialCandidateList encoders
            (continuation.transcript challenges)},
        let fixed := continuation.toFixedCandidate encoders challenges candidate
        (executions fixed).RelationAccepts challenges ∧
        (executions fixed).FinalMatches challenges ∧
        (executions fixed).FalseForCandidate challenges) :
    uniformFalseAcceptProbability FalseAccept ≤
      (32 * 240 : ℚ) / Fintype.card K := by
  have hfixedCard :
      Fintype.card (FixedInitialCandidate encoders continuation.layer0) ≤
        240 :=
    fixedInitialCandidate_fintype_card_le_240 encoders continuation.layer0
      hdistance
  apply uniformFalseAcceptProbability_le_240 executions FalseAccept hfour
    hfixedCard
  intro challenges hfalse
  rcases hextract hfalse with ⟨candidate, haccepts, hfinal, hcandidateFalse⟩
  exact ⟨continuation.toFixedCandidate encoders challenges candidate,
    haccepts, hfinal, hcandidateFalse⟩

#print axioms initialCandidateList_eq_fixedInitialCandidateList
#print axioms fixedInitialCandidateList_card_le_222
#print axioms fixedInitialCandidateList_card_le_240
#print axioms fixedInitialCandidate_fintype_card_le_240
#print axioms FixedLayer0Continuation.initialCandidateList_eq
#print axioms pointwise_selected_event_subset_fixed_family_union
#print axioms falseAcceptEvent_subset_fixedCandidateRepairEvent
#print axioms falseAcceptEvent_card_le_240_of_fixed_initial_list
#print axioms uniformFalseAcceptProbability_le_240_of_fixed_initial_list

end FiniteField

end AspisV5Tag67FixedCandidateTiming
