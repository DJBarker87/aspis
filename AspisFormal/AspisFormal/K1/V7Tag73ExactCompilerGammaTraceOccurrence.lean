import AspisFormal.K1.V7Tag73OperationalSemanticReplay
import AspisFormal.K1.V7Tag73K12CollisionSchedulerTree
import AspisFormal.K1.V7Tag73CausalProgrammingFreshness
import AspisFormal.K1.V7Tag73ExactCompilerSchedulerPauseBinding
import AspisFormal.K1.V7Tag73SchedulerNativeGammaReplay

/-!
# Exact compiler occurrence of the first gamma query

The strict source refinement reconstructs the deployed work-erased evaluator
against the literal final root-oracle table.  This file extracts the first
duplex lookup of the gamma sampler and proves that the table entry was created
by one of the two projected root machines.  Consequently the corresponding
`machineFresh` coordinate occurs in the exact result-carrying compiler trace.

The proof does not assume that the verifier itself first queried the input:
the adversary may have created the same table entry earlier.  The final-table
factorization handles both cases and retains the literal input as well as the
answer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73CausalProgrammingFreshness
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73AtomicForkUniformScheduler

noncomputable section

/-! ## Exact fresh input/output enumeration -/

/-- Fresh query coordinates, retaining both the literal input and answer. -/
def freshQueryEnumeration : List QueryRecord → List (ShaInput × Digest256)
  | [] => []
  | record :: rest =>
      match record.origin with
      | .fresh => (record.input, record.output) :: freshQueryEnumeration rest
      | .programmed | .cached => freshQueryEnumeration rest

@[simp] theorem fresh_query_enumeration_append
    (first second : List QueryRecord) :
    freshQueryEnumeration (first ++ second) =
      freshQueryEnumeration first ++ freshQueryEnumeration second := by
  induction first with
  | nil => rfl
  | cons record rest ih =>
      rcases record with ⟨input, output, actor, origin⟩
      cases origin <;> simp [freshQueryEnumeration, ih]

@[simp] theorem fresh_query_enumeration_map_snd
    (records : List QueryRecord) :
    (freshQueryEnumeration records).map Prod.snd =
      freshAnswerEnumeration records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      rcases record with ⟨input, output, actor, origin⟩
      cases origin <;> simp [freshQueryEnumeration, freshAnswerEnumeration, ih]

theorem fresh_query_enumeration_eq_nil_of_answers_eq_nil
    (records : List QueryRecord)
    (empty : freshAnswerEnumeration records = []) :
    freshQueryEnumeration records = [] := by
  have mapped : (freshQueryEnumeration records).map Prod.snd = [] := by
    simpa using empty
  exact List.map_eq_nil_iff.mp mapped

theorem fresh_table_entries_eq_fresh_query_enumeration
    (records : List QueryRecord) :
    ((records.filter fun record => record.origin = .fresh).map
        freshTableEntryOfRecord) =
      (freshQueryEnumeration records).map (fun query =>
        ({ input := query.1, output := query.2, source := .fresh } :
          AspisK1.V7FsAokExperiment.TableEntry)) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      rcases record with ⟨input, output, actor, origin⟩
      cases origin <;>
        simp [freshQueryEnumeration, freshTableEntryOfRecord, ih]

/-- The projected machine certificate preserves the exact fresh input/output
coordinates, not only the answer projection used by the master tape. -/
theorem projected_fresh_returned_trace_fresh_query_enumeration_exact
    {MachineResult : Type}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps) :
    freshQueryEnumeration (historySince entryState finalState) =
      freshQueries := by
  induction trace with
  | returned fuel state program coherent result finalState steps sought =>
      have preserved := seek_next_fresh_oracle_preserves_projected_suffix
        limits actor state.history [] fuel state program coherent
          (projected_fresh_suffix_initial state)
      rw [sought] at preserved
      rcases preserved with ⟨appended, historyExact, answersExact⟩
      have finalHistory : finalState.history = state.history ++ appended := by
        simpa [seekNextFreshOracle] using historyExact
      unfold historySince
      rw [finalHistory]
      simp only [List.drop_left]
      exact fresh_query_enumeration_eq_nil_of_answers_eq_nil appended
        (by simpa using answersExact)
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail ih =>
      have requestSuffix := seek_next_fresh_request_preserves_projected_suffix
        limits actor state.history [] fuel state requestState program input next
          remainingFuel cachedSteps coherent requestCoherent totalRoom freshRoom
          missing (projected_fresh_suffix_initial state) sought
      rcases requestSuffix with ⟨before, requestHistory, beforeAnswers⟩
      have tailSuffix := projected_fresh_returned_trace_preserves_suffix
        limits actor
          (freshQueryState actor requestState input answer).history []
          remainingFuel (freshQueryState actor requestState input answer)
          (next answer) rest result finalState tailSteps
          (projected_fresh_suffix_initial
            (freshQueryState actor requestState input answer)) tail
      rcases tailSuffix with ⟨after, finalHistory, _afterAnswers⟩
      have beforeEmpty : freshQueryEnumeration before = [] :=
        fresh_query_enumeration_eq_nil_of_answers_eq_nil before
          (by simpa using beforeAnswers)
      have tailSince :
          historySince (freshQueryState actor requestState input answer)
              finalState = after := by
        unfold historySince
        rw [finalHistory]
        simp
      have afterExact : freshQueryEnumeration after = rest := by
        rw [← tailSince]
        exact ih
      unfold historySince
      rw [finalHistory, freshQueryState, requestHistory]
      simp only [List.append_assoc, List.drop_left,
        fresh_query_enumeration_append, beforeEmpty, List.nil_append]
      simp [freshQueryEnumeration, afterExact]

/-- Exact table suffix produced by a returned projected machine prefix. -/
theorem projected_machine_prefix_table_eq_fresh_coordinates
    {MachineResult : Type}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel entryState
      program available) :
    returned.finalState.table = entryState.table ++
      returned.freshQueries.map (fun query =>
        ({ input := query.1, output := query.2, source := .fresh } :
          AspisK1.V7FsAokExperiment.TableEntry)) := by
  have coherent := projected_returned_trace_entry_coherent limits actor fuel
    entryState program returned.freshQueries returned.result
      returned.finalState returned.steps returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor
    fuel entryState program available returned coherent
  have extension := (run_machine_exact_fresh_extension
    (controllerFromProjectedFreshAnswers entryState.history
      (returned.freshQueries.map Prod.snd)) limits actor fuel entryState
      program).1
  rw [runExact] at extension
  rw [extension]
  unfold verifierFreshTableEntries verifierFreshRecords
  have freshExact :=
    projected_fresh_returned_trace_fresh_query_enumeration_exact limits actor
      fuel entryState program returned.freshQueries returned.result
        returned.finalState returned.steps returned.trace
  apply congrArg (List.append entryState.table)
  rw [fresh_table_entries_eq_fresh_query_enumeration, freshExact]

theorem machine_fresh_mem_projected_records
    (actor : QueryActor) (queries : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256)
    (member : (input, answer) ∈ queries) :
    (.machineFresh actor input answer : UnifiedExposureRecord) ∈
      projectedMachineFreshRecords actor queries := by
  induction queries with
  | nil => simp at member
  | cons query rest ih =>
      rcases query with ⟨headInput, headAnswer⟩
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with head | later
      · rcases head with ⟨rfl, rfl⟩
        simp [projectedMachineFreshRecords]
      · simp [projectedMachineFreshRecords, ih later]

/-! ## The literal pre-gamma table lookup -/

/-- Events immediately after the semantic rounds and before gamma. -/
def beforeGammaTailEvents (messages : Messages) : List MachineEvent :=
  [.absorb (.pointClaims messages.pointClaims),
   .check .semanticTerminal,
   .grind .batch messages.batchGrinding,
   .check .batchWork,
   .absorb (.batchNonce messages.batchGrinding.selected)]

theorem after_semantic_tail_events_gamma_split (messages : Messages) :
    afterSemanticTailEvents messages =
      beforeGammaTailEvents messages ++
        challengeEvent messages .gamma ::
          ([.absorb (.inactiveClaim messages.inactiveClaim),
            challengeEvent messages .kappa] ++
            oodEvents messages ++
            [.absorb (.relationRound 0 (messages.relationSent 0)),
             .grind .fold messages.foldGrinding,
             .check .foldWork,
             .absorb (.foldNonce messages.foldGrinding.selected),
             challengeEvent messages (.alpha 0),
             .absorb (.final256 messages.finalValues),
             .grind .final messages.finalGrinding,
            .check .finalWork,
             .absorb (.finalNonce messages.finalGrinding.selected)]) := by
  simp [afterSemanticTailEvents, beforeGammaTailEvents]

theorem squeeze_many_positive_first_output_lookup
    (table : FixedOracleTable) (owner : SqueezeOwner)
    (count : Nat) (positive : 0 < count)
    (state finalState : EvalState) (outputs : List Digest256)
    (run : squeezeMany table owner count state = some (outputs, finalState)) :
    ∃ output,
      tableLookup table (bytes state.digest ++ [domSqueeze]) = some output := by
  cases count with
  | zero => omega
  | succ remaining =>
      rw [squeezeMany, squeezeManyFrom] at run
      obtain ⟨pair, firstRun, _tail⟩ := Option.bind_eq_some_iff.mp run
      rcases pair with ⟨output, next⟩
      exact ⟨output,
        (squeeze_step_emits_two_distinct_queries table state next owner 0 output
          firstRun).1⟩

/-- Strict refinement of the actual source proof forces a literal lookup at
the first gamma squeeze input.  The digest is the operational state reached
immediately before the gamma event. -/
theorem exact_operational_gamma_output_lookup
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
    ∃ initialDigest answer,
      tableLookup (exactOperationalTable input)
        (gammaOutputInput initialDigest) = some answer := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input) evaluator
  have splitRun := segments.afterSemanticRun
  rw [after_semantic_tail_events_gamma_split] at splitRun
  obtain ⟨beforeGamma, _prefixRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeGammaTailEvents (exactOperationalTape input).messages)
      (challengeEvent (exactOperationalTape input).messages .gamma ::
        ([.absorb (.inactiveClaim
            (exactOperationalTape input).messages.inactiveClaim),
          challengeEvent (exactOperationalTape input).messages .kappa] ++
          oodEvents (exactOperationalTape input).messages ++
          [.absorb (.relationRound 0
            ((exactOperationalTape input).messages.relationSent 0)),
           .grind .fold (exactOperationalTape input).messages.foldGrinding,
           .check .foldWork,
           .absorb (.foldNonce
            (exactOperationalTape input).messages.foldGrinding.selected),
           challengeEvent (exactOperationalTape input).messages (.alpha 0),
           .absorb (.final256
            (exactOperationalTape input).messages.finalValues),
           .grind .final (exactOperationalTape input).messages.finalGrinding,
           .check .finalWork,
           .absorb (.finalNonce
            (exactOperationalTape input).messages.finalGrinding.selected)]))
      segments.afterSemantic evaluator.prefixState).mp splitRun
  simp only [runMachineEventsWorkErased] at restRun
  obtain ⟨afterGamma, gammaRun, _tailRun⟩ :=
    Option.bind_eq_some_iff.mp restRun
  have gammaRun' : runMachineEventWorkErased (exactOperationalTable input)
      beforeGamma (.challenge .gamma
        ((exactOperationalTape input).messages.challengeUse .gamma)) =
        some afterGamma := by
    simpa [challengeEvent] using gammaRun
  obtain ⟨blocks, afterBlocks, squeezeRun, _next, _length, _member⟩ :=
    challenge_event_work_erased_exposes_record
      (exactOperationalTable input) beforeGamma afterGamma .gamma
      ((exactOperationalTape input).messages.challengeUse .gamma) gammaRun'
  obtain ⟨answer, found⟩ := squeeze_many_positive_first_output_lookup
    (exactOperationalTable input) (.challenge .gamma)
    ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed
    ((exactOperationalTape input).messages.challengeUse .gamma).consumesBlock
    beforeGamma afterBlocks blocks squeezeRun
  exact ⟨beforeGamma.digest, answer, by simpa [gammaOutputInput] using found⟩

/-! ## Actual compiler trace occurrence -/

/-- Every lookup in the exact final root table comes from one literal fresh
coordinate in the adversary/verifier root prefix. -/
theorem exact_final_table_lookup_has_root_record
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
    (target : ShaInput) (answer : Digest256)
    (found : tableLookup (exactOperationalTable input) target = some answer) :
    ∃ actor,
      (.machineFresh actor target answer : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have runtimeExact : (exactK12Runtime input).verifierFinalOracle =
      prefixes.verifier.finalState := by
    have exact := congrArg
      (fun runtime => runtime.verifierFinalOracle) prefixes.runtimeExact
    simpa [exactK12Runtime, prefixes, operationalRootRuntime] using exact
  change tableLookup
      (fixedTableOfOracleState (exactK12Runtime input).verifierFinalOracle)
        target = some answer at found
  rw [fixed_table_lookup_eq_lookup_entry_output] at found
  change (lookupEntry (exactK12Runtime input).verifierFinalOracle target).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some answer at found
  rw [runtimeExact] at found
  cases selected : lookupEntry prefixes.verifier.finalState target with
  | none => simp [selected] at found
  | some entry =>
      have outputExact : entry.output = answer := by
        simpa [selected] using found
      have inputExact : entry.input = target := by
        unfold lookupEntry at selected
        exact of_decide_eq_true (List.find?_eq_some_iff_append.mp selected).1
      have entryMember : entry ∈ prefixes.verifier.finalState.table := by
        unfold lookupEntry at selected
        exact List.mem_of_find?_eq_some selected
      have adversaryTable := projected_machine_prefix_table_eq_fresh_coordinates
        configuration.machine.adversaryLimits .adversary
        configuration.machine.adversaryFuel emptyOracle
        (schedulerStageProgram
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (totalizeOracleMachine configuration.machine.adversaryFuel
            (configuration.machine.blackBox.start sample.1
              configuration.machine.observation)))
        (freshAnswerTapeToList sample.2) prefixes.adversary
      have verifierTable := projected_machine_prefix_table_eq_fresh_coordinates
        configuration.machine.verifierLimits .verifier
        configuration.machine.verifierFuel prefixes.adversary.finalState
        (schedulerStageProgram
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (totalizeOracleMachine configuration.machine.verifierFuel
            (initialRawFutureFreeProgram configuration.machine.environment
              prefixes.adversaryValue.rawMessages
              configuration.machine.driverFuel)))
        prefixes.adversary.remaining prefixes.verifier
      rw [verifierTable, adversaryTable] at entryMember
      simp only [emptyOracle, List.nil_append, List.mem_append,
        List.mem_map] at entryMember
      rcases entryMember with adversaryMember | verifierMember
      · obtain ⟨query, queryMember, queryExact⟩ := adversaryMember
        rcases query with ⟨queryInput, queryAnswer⟩
        subst entry
        change queryInput = target at inputExact
        change queryAnswer = answer at outputExact
        subst target
        subst answer
        refine ⟨.adversary, ?_⟩
        unfold exactFixedRootRecords fullProjectedRootRecords
        exact List.mem_append_left _
          (machine_fresh_mem_projected_records .adversary _ _ _ queryMember)
      · obtain ⟨query, queryMember, queryExact⟩ := verifierMember
        rcases query with ⟨queryInput, queryAnswer⟩
        subst entry
        change queryInput = target at inputExact
        change queryAnswer = answer at outputExact
        subst target
        subst answer
        refine ⟨.verifier, ?_⟩
        unfold exactFixedRootRecords fullProjectedRootRecords
        exact List.mem_append_right _
          (machine_fresh_mem_projected_records .verifier _ _ _ queryMember)

/-- The actual result-carrying compiler trace contains the first gamma-output
table creation, regardless of whether it was first made by the adversary or
by the verifier. -/
theorem exact_compiler_full_trace_contains_gamma_output_fresh
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
    ∃ initialDigest actor answer,
      (.machineFresh actor (gammaOutputInput initialDigest) answer :
        UnifiedExposureRecord) ∈
          (runExactPlainRom transitionFuel configuration sample).trace := by
  obtain ⟨initialDigest, answer, found⟩ :=
    exact_operational_gamma_output_lookup input
  obtain ⟨actor, rootMember⟩ := exact_final_table_lookup_has_root_record
    input (gammaOutputInput initialDigest) answer found
  refine ⟨initialDigest, actor, answer, ?_⟩
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample input.package]
  exact List.mem_append_left _ rootMember

/-- The exhaustive scanner on the actual result-carrying compiler cannot take
its absent branch at the first gamma-output input.  This is the direct source
bridge needed by scheduler-native counterfactual replay. -/
theorem exact_compiler_full_gamma_target_scan_paused
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
    ∃ initialDigest,
      ∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (gammaOutputInput initialDigest),
        exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
          .paused pause := by
  obtain ⟨initialDigest, actor, answer, member⟩ :=
    exact_compiler_full_trace_contains_gamma_output_fresh input
  obtain ⟨pause, paused⟩ := exact_compiler_full_target_scan_paused_of_trace_mem
    input (gammaOutputInput initialDigest) actor answer member
  exact ⟨initialDigest, pause, paused⟩

#print axioms projected_fresh_returned_trace_fresh_query_enumeration_exact
#print axioms projected_machine_prefix_table_eq_fresh_coordinates
#print axioms exact_operational_gamma_output_lookup
#print axioms exact_final_table_lookup_has_root_record
#print axioms exact_compiler_full_trace_contains_gamma_output_fresh
#print axioms exact_compiler_full_gamma_target_scan_paused

end

end AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
