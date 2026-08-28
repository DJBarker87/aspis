import AspisFormal.K1.V7Tag73ActualQ16InitialDigest

/-!
# Exact compiler q16 initial-digest map

Choose the complete evaluator already constructed by strict source refinement,
then lift every production-derived post-counter digest through the actual final
root table to its literal adversary-or-verifier first exposure.  This yields a
scheduler-native pause for every counter through the selected counter without
assigning a role from the raw SHA input grammar.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap

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
open AspisK1.V7Tag73ActualQ16InitialDigest

noncomputable section

/-- Canonical complete evaluator selected from the literal strict-refinement
construction. -/
noncomputable def exactOperationalQ16Evaluator
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
    CompleteWorkErasedEvaluatorRun (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input) :=
  Classical.choice (exact_operational_input_constructs_complete_evaluator input)

/-- The exact source-derived post-counter digest map for this compiler root. -/
noncomputable def exactOperationalQ16InitialDigest
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Fin 64 → Digest256 :=
  let evaluator := exactOperationalQ16Evaluator input
  acceptedQ16InitialDigest (exactOperationalTable input) evaluator.prefixState
    evaluator.afterQ16 (exactOperationalTape input).search evaluator.q16Run

theorem exact_operational_q16_initial_digest_has_candidate_run
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    ∃ before after afterCounter,
      runCandidate (exactOperationalTable input) before
          { counter := counter,
            outcome := (exactOperationalTape input).search.outcome counter } =
        some after ∧
      absorbStep (exactOperationalTable input) before
          (.queryCandidate counter) = some afterCounter ∧
      afterCounter.digest = exactOperationalQ16InitialDigest input counter := by
  exact accepted_q16_initial_digest_has_literal_candidate_run
    (exactOperationalTable input)
    (exactOperationalQ16Evaluator input).prefixState
    (exactOperationalQ16Evaluator input).afterQ16
    (exactOperationalTape input).search
    (exactOperationalQ16Evaluator input).q16Run counter beforeSelected

theorem exact_operational_q16_initial_digest_lookup
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    ∃ answer,
      tableLookup (exactOperationalTable input)
          (q16OutputInput (exactOperationalQ16InitialDigest input counter)) =
        some answer := by
  exact accepted_q16_initial_digest_first_output_lookup
    (exactOperationalTable input)
    (exactOperationalQ16Evaluator input).prefixState
    (exactOperationalQ16Evaluator input).afterQ16
    (exactOperationalTape input).search
    (exactOperationalQ16Evaluator input).q16Run counter beforeSelected

theorem exact_compiler_trace_contains_each_q16_initial_output
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    ∃ actor answer,
      (.machineFresh actor
          (q16OutputInput (exactOperationalQ16InitialDigest input counter))
          answer : UnifiedExposureRecord) ∈
        (runExactPlainRom transitionFuel configuration sample).trace := by
  obtain ⟨answer, found⟩ := exact_operational_q16_initial_digest_lookup input
    counter beforeSelected
  obtain ⟨actor, rootMember⟩ := exact_final_table_lookup_has_root_record input
    (q16OutputInput (exactOperationalQ16InitialDigest input counter)) answer
    found
  refine ⟨actor, answer, ?_⟩
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample input.package]
  exact List.mem_append_left _ rootMember

theorem exact_compiler_each_q16_initial_target_scan_paused
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    ∃ pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (q16OutputInput (exactOperationalQ16InitialDigest input counter)),
      exactCompilerFullTargetScan input
          (q16OutputInput (exactOperationalQ16InitialDigest input counter)) =
        .paused pause := by
  obtain ⟨actor, answer, member⟩ :=
    exact_compiler_trace_contains_each_q16_initial_output input counter
      beforeSelected
  exact exact_compiler_full_target_scan_paused_of_trace_mem input
    (q16OutputInput (exactOperationalQ16InitialDigest input counter)) actor
    answer member

#print axioms exact_operational_q16_initial_digest_has_candidate_run
#print axioms exact_operational_q16_initial_digest_lookup
#print axioms exact_compiler_trace_contains_each_q16_initial_output
#print axioms exact_compiler_each_q16_initial_target_scan_paused

end

end AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
