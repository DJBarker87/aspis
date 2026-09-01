import AspisFormal.K1.V7Tag73FinalWorkEarliestExposure

/-!
# Earliest exact accepted final-work exposure

The input-only chronological selector is useful for raw grammar arguments,
but the production cover also needs the selected answer to be the exact value
looked up by the accepted root execution.  This module selects the earlier of
the two already-proved exact root records:

* the selected final-work input with its accepted 34-bit digest; and
* the following nonce-absorb input with the returned q16-base digest.

The controller remains causal because the finite trial inventory contains
every exposure index and its slot decision still sees only the pre-answer
input.  The exact answer is used solely to prove event inclusion after the
run, not to construct the controller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFinalWorkEarliestExposure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FinalWorkEarliestExposure
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The two literal accepted records, including their exact returned values. -/
def IsExactFinalWorkPairRecord (key : RawFinalWorkKey)
    (workAnswer q16Base : Digest256) : UnifiedExposureRecord → Prop
  | .machineFresh _actor input answer =>
      (input = key.workInput ∧ answer = workAnswer) ∨
        (input = key.absorbInput ∧ answer = q16Base)
  | .padding _ | .forkOutput _ _ _ _ _ | .forkAdvance _ => False

instance (key : RawFinalWorkKey) (workAnswer q16Base : Digest256) :
    DecidablePred (IsExactFinalWorkPairRecord key workAnswer q16Base) :=
  fun record => by
    cases record <;>
      simp [IsExactFinalWorkPairRecord] <;> infer_instance

/-- Proof-relevant first occurrence of either exact accepted record. -/
inductive EarliestExactFinalWorkPairOccurrence
    (key : RawFinalWorkKey) (workAnswer q16Base : Digest256) :
    List UnifiedExposureRecord → Nat → Prop where
  | hit (record : UnifiedExposureRecord) (rest : List UnifiedExposureRecord)
      (pair : IsExactFinalWorkPairRecord key workAnswer q16Base record) :
      EarliestExactFinalWorkPairOccurrence key workAnswer q16Base
        (record :: rest) 0
  | skip (record : UnifiedExposureRecord) (rest : List UnifiedExposureRecord)
      (index : Nat)
      (notPair : ¬ IsExactFinalWorkPairRecord key workAnswer q16Base record)
      (tail : EarliestExactFinalWorkPairOccurrence key workAnswer q16Base
        rest index) :
      EarliestExactFinalWorkPairOccurrence key workAnswer q16Base
        (record :: rest) (index + 1)

theorem earliest_exact_pair_exists_of_member
    (key : RawFinalWorkKey) (workAnswer q16Base : Digest256) :
    ∀ (records : List UnifiedExposureRecord) (target : UnifiedExposureRecord),
      target ∈ records →
      IsExactFinalWorkPairRecord key workAnswer q16Base target →
      ∃ index, EarliestExactFinalWorkPairOccurrence key workAnswer q16Base
        records index := by
  intro records
  induction records with
  | nil =>
      intro target member _pair
      simp at member
  | cons head rest ih =>
      intro target member targetPair
      by_cases headPair :
          IsExactFinalWorkPairRecord key workAnswer q16Base head
      · exact ⟨0, .hit head rest headPair⟩
      · simp only [List.mem_cons] at member
        rcases member with targetExact | tailMember
        · subst target
          exact False.elim (headPair targetPair)
        · obtain ⟨index, tail⟩ := ih target tailMember targetPair
          exact ⟨index + 1, .skip head rest index headPair tail⟩

theorem earliest_exact_pair_index_lt_length
    {key : RawFinalWorkKey} {workAnswer q16Base : Digest256}
    {records : List UnifiedExposureRecord} {index : Nat}
    (earliest : EarliestExactFinalWorkPairOccurrence key workAnswer q16Base
      records index) :
    index < records.length := by
  induction earliest with
  | hit => simp
  | skip record rest index notPair tail ih =>
      simp only [List.length_cons]
      omega

theorem earliest_exact_pair_trace_decomposition
    {key : RawFinalWorkKey} {workAnswer q16Base : Digest256}
    {records : List UnifiedExposureRecord} {index : Nat}
    (earliest : EarliestExactFinalWorkPairOccurrence key workAnswer q16Base
      records index) :
    ∃ prior selected later,
      records = prior ++ selected :: later ∧
      prior.length = index ∧
      IsExactFinalWorkPairRecord key workAnswer q16Base selected := by
  induction earliest with
  | hit record rest pair =>
      exact ⟨[], record, rest, rfl, rfl, pair⟩
  | skip record rest index notPair tail ih =>
      obtain ⟨prior, selected, later, traceExact, lengthExact, pair⟩ := ih
      exact ⟨record :: prior, selected, later, by simp [traceExact],
        by simp [lengthExact], pair⟩

theorem exact_final_work_pair_record_cases
    (key : RawFinalWorkKey) (workAnswer q16Base : Digest256)
    (record : UnifiedExposureRecord)
    (pair : IsExactFinalWorkPairRecord key workAnswer q16Base record) :
    ∃ actor,
      record = .machineFresh actor key.workInput workAnswer ∨
      record = .machineFresh actor key.absorbInput q16Base := by
  cases record with
  | padding answer => simp [IsExactFinalWorkPairRecord] at pair
  | machineFresh actor input answer =>
      simp only [IsExactFinalWorkPairRecord] at pair
      rcases pair with work | absorb
      · exact ⟨actor, Or.inl (by rw [work.1, work.2])⟩
      · exact ⟨actor, Or.inr (by rw [absorb.1, absorb.2])⟩
  | forkOutput history outputInput advanceInput template answer =>
      simp [IsExactFinalWorkPairRecord] at pair
  | forkAdvance scheduled => simp [IsExactFinalWorkPairRecord] at pair

/-- Strict source acceptance constructs one exact `Fin F` trial at the earlier
of its accepted work and q16-base first-creation records. -/
theorem exact_compiler_accepted_final_work_has_exact_earliest_exposure_trial
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest workAnswer q16Base : Digest256)
        (trial : ExactCompilerExposureTrial parameters),
      FinalWork34Accepted workAnswer ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      EarliestExactFinalWorkPairOccurrence
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer q16Base
        (runExactPlainRom transitionFuel configuration sample).trace
        trial.val := by
  obtain ⟨digest, workActor, workAnswer, absorbActor, q16Base, accepted,
      workMember, _absorbMember, q16BaseExact⟩ :=
    exact_compiler_full_trace_contains_final_work_pair_fresh input
  let key := literalFinalWorkKey digest
    (exactOperationalTape input).messages.finalGrinding.selected
  have workPair : IsExactFinalWorkPairRecord key workAnswer q16Base
      (.machineFresh workActor
        (bytes digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer) := by
    exact Or.inl ⟨by rfl, rfl⟩
  obtain ⟨index, earliest⟩ := earliest_exact_pair_exists_of_member key
    workAnswer q16Base
    (runExactPlainRom transitionFuel configuration sample).trace
    (.machineFresh workActor
      (bytes digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.finalGrinding.selected)
      workAnswer) workMember workPair
  have indexLtLength := earliest_exact_pair_index_lt_length earliest
  have indexLtCap : index < unifiedFull256ExposureCap parameters := by
    rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
    exact indexLtLength
  let trial : ExactCompilerExposureTrial parameters := ⟨index, indexLtCap⟩
  exact ⟨digest, workAnswer, q16Base, trial, accepted, q16BaseExact, earliest⟩

#print axioms earliest_exact_pair_exists_of_member
#print axioms earliest_exact_pair_index_lt_length
#print axioms earliest_exact_pair_trace_decomposition
#print axioms exact_final_work_pair_record_cases
#print axioms exact_compiler_accepted_final_work_has_exact_earliest_exposure_trial

end

end AspisK1.V7Tag73ExactFinalWorkEarliestExposure
