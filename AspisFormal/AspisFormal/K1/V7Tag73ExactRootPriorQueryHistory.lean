import AspisFormal.K1.V7Tag73ProjectedFreshPriorQueryHistory
import AspisFormal.K1.V7Tag73SourceAnchoredNativeCursorFactorization

/-!
# Exact root-machine prior-query histories

This file instantiates the positional projected-trace theorem at Tag-73's two
literal root callbacks.  A verifier request retains both the complete earlier
adversary history and its own earlier fresh-query prefix.  These are the
source-side states later identified with the target-clean certificate at the
same global scheduler prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootPriorQueryHistory

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RootSuccessForcesFullCompletion
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SourceAnchoredNativeCursorFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Exact request state for a positional adversary-root fresh query. -/
theorem exact_root_adversary_query_has_local_prior_history
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (positive : 0 < transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior : List (ShaInput × Digest256)) (target : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        prior ++ (target, answer) :: later) :
    ∃ requestState : OracleState,
      (∀ query ∈ prior,
        projectedFreshQueryRecord .adversary query ∈ requestState.history) ∧
      IsExactSchedulerNativeMachineFreshRequest .adversary requestState target
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (.machine configuration.machine.adversaryLimits
              configuration.rootLimitBounds.adversary .adversary emptyOracle
              (schedulerStageProgram
                (SchedulerNativePlainRomResult TapeIdentity Statement
                  Tag73K12ParsedProof Payload Result)
                (totalizeOracleMachine configuration.machine.adversaryFuel
                  (configuration.machine.blackBox.start sample.1
                    configuration.machine.observation)))
              configuration.machine.adversaryFuel
              empty_oracle_history_total_coherent
              (fullRootAdversaryReturnedContinuation configuration sample.1))
            (prior.map Prod.snd))) := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  obtain ⟨requestState, _entryPrefix, priorHistory, requestExact⟩ :=
    projected_fresh_trace_has_native_request_with_prior_history
      transitionFuel positive configuration.machine.adversaryLimits
      configuration.rootLimitBounds.adversary .adversary
      (fullRootAdversaryReturnedContinuation configuration sample.1)
      empty_oracle_history_total_coherent prefixes.adversary.trace prior target
      answer later (by simpa [prefixes] using decomposition)
  exact ⟨requestState, priorHistory, requestExact⟩

/-- Exact request state for a positional verifier-root fresh query.  Every
adversary fresh query is already in the verifier entry history, and every
earlier verifier query is retained at this request coordinate. -/
theorem exact_root_verifier_query_has_local_prior_history
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (positive : 0 < transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior : List (ShaInput × Digest256)) (target : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        prior ++ (target, answer) :: later) :
    ∃ requestState : OracleState,
      (∀ query ∈
          input.package.root.full.projection.rootPrefixes.adversary.freshQueries,
        projectedFreshQueryRecord .adversary query ∈ requestState.history) ∧
      (∀ query ∈ prior,
        projectedFreshQueryRecord .verifier query ∈ requestState.history) ∧
      IsExactSchedulerNativeMachineFreshRequest .verifier requestState target
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (fullRootVerifierCursor configuration sample.1
              input.package.root.full.projection.rootPrefixes.adversaryValue
              input.package.root.full.projection.rootPrefixes.adversary.finalState
              input.package.root.full.projection.rootPrefixes.adversary.finalCoherent)
            (prior.map Prod.snd))) := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  obtain ⟨requestState, entryPrefix, priorHistory, requestExact⟩ :=
    projected_fresh_trace_has_native_request_with_prior_history
      transitionFuel positive configuration.machine.verifierLimits
      configuration.rootLimitBounds.verifier .verifier
      (fullRootVerifierReturnedContinuation configuration sample.1
        prefixes.adversaryValue prefixes.adversary.finalState)
      prefixes.adversary.finalCoherent prefixes.verifier.trace prior target
      answer later (by simpa [prefixes] using decomposition)
  refine ⟨requestState, ?_, priorHistory, ?_⟩
  · intro query member
    apply entryPrefix.subset
    exact projected_fresh_query_record_mem_final_history
      configuration.machine.adversaryLimits .adversary
      prefixes.adversary.trace query member
  · simpa [fullRootVerifierCursor, prefixes] using requestExact

/-- Adversary-local chronology transported to the literal full root cursor. -/
theorem exact_root_adversary_query_has_global_prior_history
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior : List (ShaInput × Digest256)) (target : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        prior ++ (target, answer) :: later) :
    ∃ requestState : OracleState,
      (∀ query ∈ prior,
        projectedFreshQueryRecord .adversary query ∈ requestState.history) ∧
      IsExactSchedulerNativeMachineFreshRequest .adversary requestState target
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration sample.1)
            (prior.map Prod.snd))) := by
  obtain ⟨requestState, priorHistory, requestExact⟩ :=
    exact_root_adversary_query_has_local_prior_history (by omega) input prior
      target answer later decomposition
  have rootListCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed input.package.root.fixedRoot.base.runtime
          input.package.root.fixedRoot.base.clientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact input.package.root.fixedRoot.base.rootCompleted
  let stages := completed_root_constructs_operational_stages transitionFuel
    (by omega) configuration.machine sample.1 configuration.rootLimitBounds
    configuration.restorationConfiguration (freshAnswerTapeToList sample.2)
    input.package.root.fixedRoot.base.runtime
    input.package.root.fixedRoot.base.clientRun (by
      simpa [exactPlainRomRootCursor] using rootListCompleted)
  have rootCursorExact := exact_plain_rom_cursor_eq_root_machine_of_room
    configuration sample.1 stages.adversaryRoom
  refine ⟨requestState, priorHistory, ?_⟩
  rw [rootCursorExact]
  exact requestExact

/-- Verifier-local chronology transported across the exact
adversary-to-verifier callback boundary. -/
theorem exact_root_verifier_query_has_global_prior_history
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior : List (ShaInput × Digest256)) (target : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        prior ++ (target, answer) :: later) :
    ∃ requestState : OracleState,
      (∀ query ∈
          input.package.root.full.projection.rootPrefixes.adversary.freshQueries,
        projectedFreshQueryRecord .adversary query ∈ requestState.history) ∧
      (∀ query ∈ prior,
        projectedFreshQueryRecord .verifier query ∈ requestState.history) ∧
      IsExactSchedulerNativeMachineFreshRequest .verifier requestState target
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration sample.1)
            ((input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
              prior).map Prod.snd))) := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  obtain ⟨requestState, adversaryHistory, verifierHistory, requestExact⟩ :=
    exact_root_verifier_query_has_local_prior_history (by omega) input prior
      target answer later decomposition
  have verifierNonempty : prefixes.verifier.freshQueries ≠ [] := by
    rw [show prefixes.verifier.freshQueries =
        prior ++ (target, answer) :: later by
      simpa [prefixes] using decomposition]
    simp
  have boundary := exact_compiler_adversary_boundary_seek_eq_verifier
    transitionRoom input verifierNonempty
  refine ⟨requestState, adversaryHistory, verifierHistory, ?_⟩
  rw [List.map_append, scheduler_native_prefix_cursor_append]
  cases prior with
  | nil =>
      simp only [List.map_nil, schedulerNativePrefixCursor]
      rw [boundary]
      exact requestExact
  | cons head rest =>
      rcases head with ⟨headInput, headAnswer⟩
      simp only [List.map_cons]
      rw [scheduler_native_prefix_cursor_cons_congr_of_seek_eq transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (prefixes.adversary.freshQueries.map Prod.snd))
        (fullRootVerifierCursor configuration sample.1
          prefixes.adversaryValue prefixes.adversary.finalState
          prefixes.adversary.finalCoherent) headAnswer
        (rest.map Prod.snd) boundary]
      simpa [prefixes] using requestExact

#print axioms exact_root_adversary_query_has_local_prior_history
#print axioms exact_root_verifier_query_has_local_prior_history
#print axioms exact_root_adversary_query_has_global_prior_history
#print axioms exact_root_verifier_query_has_global_prior_history

end

end AspisK1.V7Tag73ExactRootPriorQueryHistory
