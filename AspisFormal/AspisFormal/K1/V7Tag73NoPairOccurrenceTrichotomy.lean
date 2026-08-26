import AspisFormal.K1.V7Tag73AtomicPairFork

/-!
# Deterministic no-pair-occurrence audit for one Tag-73 squeeze

For one generated atomic squeeze pair, the frozen first-run history has an
executable trichotomy:

1. one of the pair inputs occurs, with its first occurrence computed by
   `firstEitherInputOccurrence`;
2. neither pair input occurs and no recorded input literally begins with the
   unknown advance-state bytes; or
3. neither pair input occurs and there is a first such literal state-prefix
   input.  That input determines a singleton causal target for the missing
   256-bit advance answer.

The word `literal` is essential.  `QueryRecord` stores only the final byte
string, not an information-flow derivation.  An adversary may transform an
advance answer before forming a later query, and raw query history cannot
distinguish that from a hard-coded byte string.  The final section gives an
explicit erasure countermodel.  Consequently this module proves no
probability coefficient and does not claim a semantic failure cover.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73NoPairOccurrenceTrichotomy

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7FsAokExperiment

/-! ## First literal occurrence of an advance-state prefix -/

/-- The operationally observable fragment of "this input uses the state": the
exact 32 state bytes occur as the initial bytes of the recorded SHA input. -/
def HasLiteralStatePrefix (state : Digest256) (input : ShaInput) : Prop :=
  bytes state = input.take 32

instance (state : Digest256) (input : ShaInput) :
    Decidable (HasLiteralStatePrefix state input) := by
  unfold HasLiteralStatePrefix
  exact inferInstance

structure StatePrefixOccurrence where
  before : List QueryRecord
  chosen : QueryRecord
  after : List QueryRecord

def firstStatePrefixOccurrence (state : Digest256) :
    List QueryRecord → Option StatePrefixOccurrence
  | [] => none
  | record :: rest =>
      if HasLiteralStatePrefix state record.input then
        some { before := [], chosen := record, after := rest }
      else
        match firstStatePrefixOccurrence state rest with
        | none => none
        | some occurrence => some
            { before := record :: occurrence.before
              chosen := occurrence.chosen
              after := occurrence.after }

theorem first_state_prefix_occurrence_spec
    (state : Digest256) (records : List QueryRecord)
    (occurrence : StatePrefixOccurrence)
    (found : firstStatePrefixOccurrence state records = some occurrence) :
    records = occurrence.before ++ occurrence.chosen :: occurrence.after ∧
      (∀ prior ∈ occurrence.before,
        ¬ HasLiteralStatePrefix state prior.input) ∧
      HasLiteralStatePrefix state occurrence.chosen.input := by
  induction records generalizing occurrence with
  | nil => simp [firstStatePrefixOccurrence] at found
  | cons record rest ih =>
      by_cases hit : HasLiteralStatePrefix state record.input
      · simp only [firstStatePrefixOccurrence, hit, if_true,
          Option.some.injEq] at found
        cases found
        exact ⟨rfl, by simp, hit⟩
      · cases recursive : firstStatePrefixOccurrence state rest with
        | none =>
            simp [firstStatePrefixOccurrence, hit, recursive] at found
        | some tailOccurrence =>
            simp only [firstStatePrefixOccurrence, hit, if_false, recursive,
              Option.some.injEq] at found
            cases found
            obtain ⟨decomposition, beforeFresh, chosen⟩ :=
              ih tailOccurrence recursive
            refine ⟨by simp [decomposition], ?_, chosen⟩
            intro prior member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact hit
            · exact beforeFresh prior member

theorem first_state_prefix_occurrence_none_iff
    (state : Digest256) (records : List QueryRecord) :
    firstStatePrefixOccurrence state records = none ↔
      ∀ record ∈ records, ¬ HasLiteralStatePrefix state record.input := by
  induction records with
  | nil => simp [firstStatePrefixOccurrence]
  | cons record rest ih =>
      by_cases hit : HasLiteralStatePrefix state record.input
      · constructor
        · intro impossible
          simp only [firstStatePrefixOccurrence, hit, if_true] at impossible
          cases impossible
        · intro allRecords
          exact ((allRecords record (by simp)) hit).elim
      · constructor
        · intro noOccurrence queried member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact hit
          · have tailNone : firstStatePrefixOccurrence state rest = none := by
              cases recursive : firstStatePrefixOccurrence state rest with
              | none => rfl
              | some occurrence =>
                  simp only [firstStatePrefixOccurrence, hit, if_false,
                    recursive] at noOccurrence
                  cases noOccurrence
            exact (ih.mp tailNone) queried member
        · intro allRecords
          have tailAll : ∀ queried ∈ rest,
              ¬ HasLiteralStatePrefix state queried.input := by
            intro queried member
            exact allRecords queried (by simp [member])
          have tailNone : firstStatePrefixOccurrence state rest = none :=
            ih.mpr tailAll
          simp only [firstStatePrefixOccurrence, hit, if_false, tailNone]

theorem first_either_input_occurrence_none_iff
    (outputInput advanceInput : ShaInput) (records : List QueryRecord) :
    firstEitherInputOccurrence outputInput advanceInput records = none ↔
      ∀ record ∈ records,
        record.input ≠ outputInput ∧ record.input ≠ advanceInput := by
  induction records with
  | nil => simp [firstEitherInputOccurrence]
  | cons record rest ih =>
      by_cases hit : record.input = outputInput ∨
        record.input = advanceInput
      · constructor
        · intro impossible
          simp only [firstEitherInputOccurrence, hit, if_true] at impossible
          cases impossible
        · intro allRecords
          have headFresh := allRecords record (by simp)
          exact (hit.elim headFresh.1 headFresh.2).elim
      · constructor
        · intro noOccurrence queried member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨fun equal => hit (Or.inl equal),
              fun equal => hit (Or.inr equal)⟩
          · have tailNone : firstEitherInputOccurrence outputInput
                advanceInput rest = none := by
              cases recursive : firstEitherInputOccurrence outputInput
                  advanceInput rest with
              | none => rfl
              | some occurrence =>
                  simp only [firstEitherInputOccurrence, hit, if_false,
                    recursive] at noOccurrence
                  cases noOccurrence
            exact (ih.mp tailNone) queried member
        · intro allRecords
          have tailAll : ∀ queried ∈ rest,
              queried.input ≠ outputInput ∧
                queried.input ≠ advanceInput := by
            intro queried member
            exact allRecords queried (by simp [member])
          have tailNone : firstEitherInputOccurrence outputInput
              advanceInput rest = none := ih.mpr tailAll
          simp only [firstEitherInputOccurrence, hit, if_false, tailNone]

/-! ## The exact deterministic trichotomy -/

inductive PairAdvanceHistoryCase
    (outputInput advanceInput : ShaInput)
    (advanceState : Digest256) (records : List QueryRecord) : Type where
  | pairOccurs (occurrence : PairOccurrenceSplit)
      (found : firstEitherInputOccurrence outputInput advanceInput records =
        some occurrence)
  | noLiteralAdvanceReference
      (noPair : firstEitherInputOccurrence outputInput advanceInput records =
        none)
      (noReference : firstStatePrefixOccurrence advanceState records = none)
  | firstLiteralForwardReference (occurrence : StatePrefixOccurrence)
      (noPair : firstEitherInputOccurrence outputInput advanceInput records =
        none)
      (found : firstStatePrefixOccurrence advanceState records =
        some occurrence)

def classifyPairAdvanceHistory
    (outputInput advanceInput : ShaInput)
    (advanceState : Digest256) (records : List QueryRecord) :
    PairAdvanceHistoryCase outputInput advanceInput advanceState records := by
  cases pairFound : firstEitherInputOccurrence outputInput advanceInput records with
  | some occurrence => exact .pairOccurs occurrence pairFound
  | none =>
      cases referenceFound : firstStatePrefixOccurrence advanceState records with
      | none => exact .noLiteralAdvanceReference pairFound referenceFound
      | some occurrence =>
          exact .firstLiteralForwardReference occurrence pairFound referenceFound

theorem exact_pair_or_no_literal_reference_or_first_forward_reference
    (outputInput advanceInput : ShaInput)
    (advanceState : Digest256) (records : List QueryRecord) :
    (∃ occurrence : PairOccurrenceSplit,
      firstEitherInputOccurrence outputInput advanceInput records =
        some occurrence) ∨
    (firstEitherInputOccurrence outputInput advanceInput records = none ∧
      firstStatePrefixOccurrence advanceState records = none) ∨
    (∃ occurrence : StatePrefixOccurrence,
      firstEitherInputOccurrence outputInput advanceInput records = none ∧
      firstStatePrefixOccurrence advanceState records = some occurrence) := by
  cases classifyPairAdvanceHistory outputInput advanceInput
      advanceState records with
  | pairOccurs occurrence found => exact Or.inl ⟨occurrence, found⟩
  | noLiteralAdvanceReference noPair noReference =>
      exact Or.inr (Or.inl ⟨noPair, noReference⟩)
  | firstLiteralForwardReference occurrence noPair found =>
      exact Or.inr (Or.inr ⟨occurrence, noPair, found⟩)

theorem no_literal_reference_branch_is_pointwise
    (outputInput advanceInput : ShaInput)
    (advanceState : Digest256) (records : List QueryRecord)
    (noPair : firstEitherInputOccurrence outputInput advanceInput records = none)
    (noReference : firstStatePrefixOccurrence advanceState records = none) :
    (∀ record ∈ records,
      record.input ≠ outputInput ∧ record.input ≠ advanceInput) ∧
    (∀ record ∈ records,
      ¬ HasLiteralStatePrefix advanceState record.input) := by
  exact ⟨(first_either_input_occurrence_none_iff
      outputInput advanceInput records).mp noPair,
    (first_state_prefix_occurrence_none_iff advanceState records).mp
      noReference⟩

theorem first_literal_forward_reference_is_exact
    (outputInput advanceInput : ShaInput)
    (advanceState : Digest256) (records : List QueryRecord)
    (occurrence : StatePrefixOccurrence)
    (noPair : firstEitherInputOccurrence outputInput advanceInput records = none)
    (found : firstStatePrefixOccurrence advanceState records = some occurrence) :
    records = occurrence.before ++ occurrence.chosen :: occurrence.after ∧
    (∀ record ∈ records,
      record.input ≠ outputInput ∧ record.input ≠ advanceInput) ∧
    (∀ prior ∈ occurrence.before,
      ¬ HasLiteralStatePrefix advanceState prior.input) ∧
    HasLiteralStatePrefix advanceState occurrence.chosen.input := by
  have occurrenceSpec :=
    first_state_prefix_occurrence_spec advanceState records occurrence found
  exact ⟨occurrenceSpec.1,
    (first_either_input_occurrence_none_iff
      outputInput advanceInput records).mp noPair,
    occurrenceSpec.2.1, occurrenceSpec.2.2⟩

/-! ## A literal forward reference is a singleton causal target -/

def literalStatePrefixTarget (input : ShaInput) : Set Digest256 :=
  { state | HasLiteralStatePrefix state input }

theorem literal_state_prefix_target_subsingleton (input : ShaInput) :
    Set.Subsingleton (literalStatePrefixTarget input) := by
  intro first firstMember second secondMember
  change bytes first = input.take 32 at firstMember
  change bytes second = input.take 32 at secondMember
  apply List.ofFn_injective
  simpa [bytes] using firstMember.trans secondMember.symm

theorem first_literal_forward_reference_is_singleton_target
    (advanceState : Digest256) (records : List QueryRecord)
    (occurrence : StatePrefixOccurrence)
    (found : firstStatePrefixOccurrence advanceState records = some occurrence) :
    advanceState ∈ literalStatePrefixTarget occurrence.chosen.input ∧
      Set.Subsingleton
        (literalStatePrefixTarget occurrence.chosen.input) := by
  have spec :=
    first_state_prefix_occurrence_spec advanceState records occurrence found
  exact ⟨spec.2.2,
    literal_state_prefix_target_subsingleton occurrence.chosen.input⟩

/-! ## Specialization to one generated squeeze and frozen Q1 -/

noncomputable def classifyGeneratedSqueezeInFrozenQ1
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (advanceAnswer : Digest256) :
    PairAdvanceHistoryCase
      (generatedPairInput execution generated .output)
      (generatedPairInput execution generated .advance)
      advanceAnswer (freezeAdversaryQ1 stateAtAdversaryHalt) :=
  classifyPairAdvanceHistory
    (generatedPairInput execution generated .output)
    (generatedPairInput execution generated .advance)
    advanceAnswer (freezeAdversaryQ1 stateAtAdversaryHalt)

theorem generated_first_literal_forward_reference_is_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (advanceAnswer : Digest256)
    (occurrence : StatePrefixOccurrence)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1 stateAtAdversaryHalt
      execution generated = none)
    (found : firstStatePrefixOccurrence advanceAnswer
      (freezeAdversaryQ1 stateAtAdversaryHalt) = some occurrence) :
    freezeAdversaryQ1 stateAtAdversaryHalt =
        occurrence.before ++ occurrence.chosen :: occurrence.after ∧
      (∀ prior ∈ occurrence.before,
        ¬ HasLiteralStatePrefix advanceAnswer prior.input) ∧
      HasLiteralStatePrefix advanceAnswer occurrence.chosen.input ∧
      occurrence.chosen.input ≠
        generatedPairInput execution generated .output ∧
      occurrence.chosen.input ≠
        generatedPairInput execution generated .advance ∧
      occurrence.chosen.actor = .adversary ∧
      advanceAnswer ∈
        literalStatePrefixTarget occurrence.chosen.input ∧
      Set.Subsingleton
        (literalStatePrefixTarget occurrence.chosen.input) := by
  have noPair' : firstEitherInputOccurrence
      (generatedPairInput execution generated .output)
      (generatedPairInput execution generated .advance)
      (freezeAdversaryQ1 stateAtAdversaryHalt) = none := by
    simpa [firstGeneratedPairOccurrenceInFrozenQ1] using noPair
  have exactReference := first_literal_forward_reference_is_exact
    (generatedPairInput execution generated .output)
    (generatedPairInput execution generated .advance)
    advanceAnswer (freezeAdversaryQ1 stateAtAdversaryHalt)
    occurrence noPair' found
  have chosenMember : occurrence.chosen ∈
      freezeAdversaryQ1 stateAtAdversaryHalt := by
    rw [exactReference.1]
    simp
  have target := first_literal_forward_reference_is_singleton_target
    advanceAnswer (freezeAdversaryQ1 stateAtAdversaryHalt) occurrence found
  exact ⟨exactReference.1, exactReference.2.2.1,
    exactReference.2.2.2,
    (exactReference.2.1 occurrence.chosen chosenMember).1,
    (exactReference.2.1 occurrence.chosen chosenMember).2,
    frozen_q1_contains_only_adversary_calls stateAtAdversaryHalt
      occurrence.chosen chosenMember,
    target.1, target.2⟩

/-! ## Why raw history cannot express arbitrary semantic dependence -/

inductive InputDependencyProvenance where
  | independent
  | derivedFromAdvance
  deriving DecidableEq, Repr

structure ProvenancedInput where
  input : ShaInput
  provenance : InputDependencyProvenance

def ProvenancedInput.erase (annotated : ProvenancedInput) : ShaInput :=
  annotated.input

/-- Two operationally identical query inputs can carry opposite dependency
provenance.  Erasing to `QueryRecord.input` therefore cannot reconstruct the
semantic dependency relation needed for transformed uses of an advance
answer. -/
theorem raw_query_input_erases_dependency_provenance (input : ShaInput) :
    ∃ independent derived : ProvenancedInput,
      independent.provenance = .independent ∧
      derived.provenance = .derivedFromAdvance ∧
      independent.erase = derived.erase := by
  exact ⟨⟨input, .independent⟩, ⟨input, .derivedFromAdvance⟩,
    rfl, rfl, rfl⟩

/-- The two annotations above are genuinely distinct even though their raw
SHA input erasures are equal. -/
theorem equal_raw_inputs_do_not_determine_dependency (input : ShaInput) :
    let independent : ProvenancedInput := ⟨input, .independent⟩
    let derived : ProvenancedInput := ⟨input, .derivedFromAdvance⟩
    independent.erase = derived.erase ∧ independent ≠ derived := by
  simp [ProvenancedInput.erase]

#print axioms first_state_prefix_occurrence_spec
#print axioms first_state_prefix_occurrence_none_iff
#print axioms first_either_input_occurrence_none_iff
#print axioms exact_pair_or_no_literal_reference_or_first_forward_reference
#print axioms no_literal_reference_branch_is_pointwise
#print axioms first_literal_forward_reference_is_exact
#print axioms literal_state_prefix_target_subsingleton
#print axioms first_literal_forward_reference_is_singleton_target
#print axioms generated_first_literal_forward_reference_is_exact
#print axioms raw_query_input_erases_dependency_provenance
#print axioms equal_raw_inputs_do_not_determine_dependency

end AspisK1.V7Tag73NoPairOccurrenceTrichotomy
