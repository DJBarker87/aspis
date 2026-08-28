import AspisFormal.K1.V7Tag73ActualQ16DecoderExtraction
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence

/-!
# Exact compiler occurrence of the first q16 output query

The accepted work-erased evaluator runs a nonempty `earlier ++ [selected]`
candidate list.  This module exposes the first candidate's first squeeze
lookup, transports that lookup to the actual final root table, and locates its
literal first creation in the result-carrying compiler trace.  The creator may
be the adversary or verifier; no role is reassigned after the fact.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerQ16TraceOccurrence

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan

noncomputable section

/-- Every successfully evaluated candidate performs a positive first squeeze
lookup from its literal post-counter-absorb digest. -/
theorem run_candidate_first_q16_output_lookup
    (table : FixedOracleTable) (state final : EvalState)
    (spec : CandidateSpec)
    (run : runCandidate table state spec = some final) :
    ∃ initialDigest answer,
      tableLookup table (q16OutputInput initialDigest) = some answer := by
  obtain ⟨afterCounter, blocks, afterBlocks, _absorbRun, squeezeRun,
      _finalExact, _blocksLength, _recordMember⟩ :=
    run_candidate_exposes_exact_record table state final spec run
  obtain ⟨answer, found⟩ := squeeze_many_positive_first_output_lookup table
    (.queryCandidate spec.counter) spec.outcome.blocksUsed
    (candidate_outcome_blocks_positive spec.outcome) afterCounter afterBlocks
    blocks squeezeRun
  exact ⟨afterCounter.digest, answer, by
    simpa [q16OutputInput] using found⟩

/-- A successful q16 scan exposes the first literal candidate specification
and that candidate's first output lookup. -/
theorem run_q16_first_candidate_output_lookup
    (table : FixedOracleTable) (state final : EvalState) (tape : Q16Tape)
    (run : runQ16 table state tape = some final) :
    ∃ first rest initialDigest answer,
      tape.earlier ++ [tape.selected] = first :: rest ∧
      tableLookup table (q16OutputInput initialDigest) = some answer := by
  rw [runQ16] at run
  obtain ⟨beforeSelected, earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp run
  cases earlierExact : tape.earlier with
  | nil =>
      rw [earlierExact, runDiscardedCandidates] at earlierRun
      have beforeExact : beforeSelected = state :=
        (Option.some.inj earlierRun).symm
      subst beforeSelected
      obtain ⟨initialDigest, answer, found⟩ :=
        run_candidate_first_q16_output_lookup table state final tape.selected
          selectedRun
      exact ⟨tape.selected, [], initialDigest, answer, by simp, found⟩
  | cons first rest =>
      rw [earlierExact, runDiscardedCandidates] at earlierRun
      obtain ⟨afterFirst, firstRun, _remainingRun⟩ :=
        Option.bind_eq_some_iff.mp earlierRun
      obtain ⟨initialDigest, answer, found⟩ :=
        run_candidate_first_q16_output_lookup table state afterFirst first
          firstRun
      exact ⟨first, rest ++ [tape.selected], initialDigest, answer, by simp,
        found⟩

/-- The exact accepted source evaluator forces a first q16 output lookup, and
the returned specification is exactly the head of the source candidate plan. -/
theorem exact_operational_q16_first_output_lookup
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
    ∃ first rest initialDigest answer,
      q16SpecsOfSearch (exactOperationalTape input).search = first :: rest ∧
      tableLookup (exactOperationalTable input)
        (q16OutputInput initialDigest) = some answer := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨first, rest, initialDigest, answer, planExact, found⟩ :=
    run_q16_first_candidate_output_lookup (exactOperationalTable input)
      evaluator.prefixState evaluator.afterQ16
      (q16TapeOfSearch (exactOperationalTape input).search) evaluator.q16Run
  refine ⟨first, rest, initialDigest, answer, ?_, found⟩
  simpa [q16SpecsOfSearch, q16TapeOfSearch] using planExact

/-- The actual result-carrying compiler trace contains the first creation of
the accepted evaluator's first q16-output table entry. -/
theorem exact_compiler_full_trace_contains_q16_output_fresh
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
    ∃ first rest initialDigest actor answer,
      q16SpecsOfSearch (exactOperationalTape input).search = first :: rest ∧
      (.machineFresh actor (q16OutputInput initialDigest) answer :
        UnifiedExposureRecord) ∈
          (runExactPlainRom transitionFuel configuration sample).trace := by
  obtain ⟨first, rest, initialDigest, answer, planExact, found⟩ :=
    exact_operational_q16_first_output_lookup input
  obtain ⟨actor, rootMember⟩ := exact_final_table_lookup_has_root_record input
    (q16OutputInput initialDigest) answer found
  refine ⟨first, rest, initialDigest, actor, answer, planExact, ?_⟩
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample input.package]
  exact List.mem_append_left _ rootMember

/-- The exhaustive actual compiler scan pauses at the first q16 output's
literal first exposure, irrespective of which root actor created it. -/
theorem exact_compiler_full_q16_target_scan_paused
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
    ∃ first rest initialDigest,
      q16SpecsOfSearch (exactOperationalTape input).search = first :: rest ∧
      ∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (q16OutputInput initialDigest),
        exactCompilerFullTargetScan input (q16OutputInput initialDigest) =
          .paused pause := by
  obtain ⟨first, rest, initialDigest, actor, answer, planExact, member⟩ :=
    exact_compiler_full_trace_contains_q16_output_fresh input
  obtain ⟨pause, paused⟩ := exact_compiler_full_target_scan_paused_of_trace_mem
    input (q16OutputInput initialDigest) actor answer member
  exact ⟨first, rest, initialDigest, planExact, pause, paused⟩

#print axioms run_candidate_first_q16_output_lookup
#print axioms run_q16_first_candidate_output_lookup
#print axioms exact_operational_q16_first_output_lookup
#print axioms exact_compiler_full_trace_contains_q16_output_fresh
#print axioms exact_compiler_full_q16_target_scan_paused

end

end AspisK1.V7Tag73ExactCompilerQ16TraceOccurrence
