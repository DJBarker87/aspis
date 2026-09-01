import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
import AspisFormal.K1.V7Tag73FinalWorkQ16CandidateController
import AspisFormal.K1.V7Tag73ExactProbabilityCoverageAudit

/-!
# Earliest accepted final-work exposure

The accepted final-work query and its following nonce absorb both have literal
first-creation records in the fixed-length production exposure trace.  The
causal controller must begin at whichever of those records occurs first: if it
started at the later record, it could miss the earlier q16-base answer.

This module makes that chronological choice proof-relevant, proves its index
is a member of the exact conservative `Fin F` trial inventory, and retains an
exact decomposition of the production trace at the chosen record.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FinalWorkEarliestExposure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73FinalWorkDigestProbability

noncomputable section

/-- Exactly the two machine-fresh input forms that can anchor one accepted
final-work/q16 trial.  Actors and answers are intentionally unrestricted. -/
def IsFinalWorkPairRecord (key : RawFinalWorkKey) :
    UnifiedExposureRecord → Prop
  | .machineFresh _actor input _answer =>
      input = key.workInput ∨ input = key.absorbInput
  | .padding _ | .forkOutput _ _ _ _ _ | .forkAdvance _ => False

instance (key : RawFinalWorkKey) :
    DecidablePred (IsFinalWorkPairRecord key) := fun record => by
  cases record <;> simp [IsFinalWorkPairRecord] <;> infer_instance

/-- Proof-relevant first occurrence.  Every skipped record is certified not to
be either member of the pair; the hit therefore cannot be a retrospective
choice of a later occurrence. -/
inductive EarliestFinalWorkPairOccurrence (key : RawFinalWorkKey) :
    List UnifiedExposureRecord → Nat → Prop where
  | hit (record : UnifiedExposureRecord) (rest : List UnifiedExposureRecord)
      (pair : IsFinalWorkPairRecord key record) :
      EarliestFinalWorkPairOccurrence key (record :: rest) 0
  | skip (record : UnifiedExposureRecord) (rest : List UnifiedExposureRecord)
      (index : Nat) (notPair : ¬ IsFinalWorkPairRecord key record)
      (tail : EarliestFinalWorkPairOccurrence key rest index) :
      EarliestFinalWorkPairOccurrence key (record :: rest) (index + 1)

theorem earliest_final_work_pair_exists_of_member
    (key : RawFinalWorkKey) :
    ∀ (records : List UnifiedExposureRecord) (target : UnifiedExposureRecord),
      target ∈ records → IsFinalWorkPairRecord key target →
        ∃ index, EarliestFinalWorkPairOccurrence key records index := by
  intro records
  induction records with
  | nil =>
      intro target member _pair
      simp at member
  | cons head rest ih =>
      intro target member targetPair
      by_cases headPair : IsFinalWorkPairRecord key head
      · exact ⟨0, .hit head rest headPair⟩
      · simp only [List.mem_cons] at member
        rcases member with targetExact | tailMember
        · subst target
          exact False.elim (headPair targetPair)
        · obtain ⟨index, tail⟩ := ih target tailMember targetPair
          exact ⟨index + 1, .skip head rest index headPair tail⟩

theorem earliest_final_work_pair_index_lt_length
    {key : RawFinalWorkKey} {records : List UnifiedExposureRecord}
    {index : Nat}
    (earliest : EarliestFinalWorkPairOccurrence key records index) :
    index < records.length := by
  induction earliest with
  | hit => simp
  | skip record rest index notPair tail ih => simp only [List.length_cons]; omega

/-- Exact prefix/selected/suffix decomposition at the chronological hit. -/
theorem earliest_final_work_pair_trace_decomposition
    {key : RawFinalWorkKey} {records : List UnifiedExposureRecord}
    {index : Nat}
    (earliest : EarliestFinalWorkPairOccurrence key records index) :
    ∃ prior selected later,
      records = prior ++ selected :: later ∧
      prior.length = index ∧
      IsFinalWorkPairRecord key selected := by
  induction earliest with
  | hit record rest pair =>
      exact ⟨[], record, rest, rfl, rfl, pair⟩
  | skip record rest index notPair tail ih =>
      obtain ⟨prior, selected, later, traceExact, lengthExact, pair⟩ := ih
      refine ⟨record :: prior, selected, later, ?_, by simp [lengthExact], pair⟩
      simp [traceExact]

/-- No record before the selected coordinate has either pair input. -/
theorem earliest_final_work_pair_prior_is_clean
    {key : RawFinalWorkKey} {records : List UnifiedExposureRecord}
    {index : Nat}
    (earliest : EarliestFinalWorkPairOccurrence key records index) :
    ∃ prior selected later,
      records = prior ++ selected :: later ∧
      prior.length = index ∧
      IsFinalWorkPairRecord key selected ∧
      ∀ record ∈ prior, ¬ IsFinalWorkPairRecord key record := by
  induction earliest with
  | hit record rest pair =>
      exact ⟨[], record, rest, rfl, rfl, pair, by simp⟩
  | skip record rest index notPair tail ih =>
      obtain ⟨prior, selected, later, traceExact, lengthExact, pair,
          priorClean⟩ := ih
      refine ⟨record :: prior, selected, later, ?_, by simp [lengthExact], pair,
        ?_⟩
      · simp [traceExact]
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact notPair
        · exact priorClean candidate member

theorem final_work_pair_record_cases
    (key : RawFinalWorkKey) (record : UnifiedExposureRecord)
    (pair : IsFinalWorkPairRecord key record) :
    ∃ actor answer,
      record = .machineFresh actor key.workInput answer ∨
      record = .machineFresh actor key.absorbInput answer := by
  cases record with
  | padding answer => simp [IsFinalWorkPairRecord] at pair
  | machineFresh actor input answer =>
      simp only [IsFinalWorkPairRecord] at pair
      rcases pair with work | absorb
      · exact ⟨actor, answer, Or.inl (by rw [work])⟩
      · exact ⟨actor, answer, Or.inr (by rw [absorb])⟩
  | forkOutput history outputInput advanceInput template answer =>
      simp [IsFinalWorkPairRecord] at pair
  | forkAdvance scheduled => simp [IsFinalWorkPairRecord] at pair

/-! ## Exact compiler trial -/

theorem exact_compiler_full_trace_length
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runExactPlainRom transitionFuel configuration sample).trace.length =
      unifiedFull256ExposureCap parameters := by
  rw [← exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
    transitionFuel configuration sample]
  unfold exactCompilerUnifiedExposureTrace
  exact run_unified_exposure_trace_length_exact transitionFuel
    (unifiedFull256ExposureCap parameters)
    (exactPlainRomCursor configuration sample.1).erase
    (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
      (unifiedFull256ExposureCap parameters)
      (exactCompilerOperationalIndexedTape parameters sample.2))

/-- Every accepted exact source execution selects a genuine `Fin F` trial at
the earlier of the final-work and final-nonce-absorb first exposures. -/
theorem exact_compiler_accepted_final_work_has_earliest_exposure_trial
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
      EarliestFinalWorkPairOccurrence
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        (runExactPlainRom transitionFuel configuration sample).trace
        trial.val := by
  obtain ⟨digest, workActor, workAnswer, absorbActor, q16Base, accepted,
      workMember, _absorbMember, q16BaseExact⟩ :=
    exact_compiler_full_trace_contains_final_work_pair_fresh input
  let key := literalFinalWorkKey digest
    (exactOperationalTape input).messages.finalGrinding.selected
  have workPair : IsFinalWorkPairRecord key
      (.machineFresh workActor
        (bytes digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer) := by
    exact Or.inl (by rfl)
  obtain ⟨index, earliest⟩ := earliest_final_work_pair_exists_of_member key
    (runExactPlainRom transitionFuel configuration sample).trace
    (.machineFresh workActor
      (bytes digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.finalGrinding.selected)
      workAnswer) workMember workPair
  have indexLtLength := earliest_final_work_pair_index_lt_length earliest
  have indexLtCap : index < unifiedFull256ExposureCap parameters := by
    rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
    exact indexLtLength
  let trial : ExactCompilerExposureTrial parameters := ⟨index, indexLtCap⟩
  exact ⟨digest, workAnswer, q16Base, trial, accepted, q16BaseExact, earliest⟩

#print axioms earliest_final_work_pair_exists_of_member
#print axioms earliest_final_work_pair_index_lt_length
#print axioms earliest_final_work_pair_trace_decomposition
#print axioms earliest_final_work_pair_prior_is_clean
#print axioms final_work_pair_record_cases
#print axioms exact_compiler_full_trace_length
#print axioms exact_compiler_accepted_final_work_has_earliest_exposure_trial

end

end AspisK1.V7Tag73FinalWorkEarliestExposure
