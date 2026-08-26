import AspisFormal.K1.V7Tag73ExactCompilerResources
import AspisFormal.K1.V7Tag73SchedulerNativePlainRomExperiment
import AspisFormal.K1.V7Tag73FullFromStartRestoration

/-!
# Target-clean executions of the exact Tag-73 compiler scheduler

This leaf gives the deterministic complement of the exact causal target
event.  A fixed hidden tape and fixed master tape are *target-clean* exactly
when the already-constructed causal tree never hits; cleanliness is not an
acceptance, compiler-success, or extraction premise.

For an atomic pair node, target cleanliness proves that both sampled
coordinates avoid every target available before them and that the advance
coordinate differs from the immediately preceding output coordinate.  The
deployed output/advance SHA inputs themselves are distinct by their literal
`S || 0x01` and `S || 0x02` forms.  Separately, successful concrete pair
programming is proved to install exactly those two sampled coordinates while
preserving query counters and adding exactly two table/programming records.

There is one deliberate boundary.  A pre-existing lookup conflict is a fact
about the oracle table before either new fork coordinate is sampled.  The
current `forkPair` constructor stores only its frozen query history, not a
proof that the two inputs are absent from the captured programming table.
Indeed the conflict result is independent of both sampled coordinates.  Thus
target cleanliness alone cannot eliminate such a conflict.  The remaining
operational lemma must derive pair-input absence from concrete prefix
preparation (including programmed-table coverage), or map the checkpoint
digest to the earlier master-tape coordinate at which its literal reference
was targeted.  No conclusion-shaped replacement for that lemma is introduced
here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerTargetClean

set_option maxRecDepth 8192

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73FullFromStartRestoration
open AspisK1.V7Tag73ScheduledReplacementAccounting
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources

noncomputable section

/-! ## Literal complement of the exact target event -/

/-- Deterministic target cleanliness for one fixed master tape.  The native
cursor is erased into the very same result-free cursor used by the proved
probability theorem. -/
def ExactCompilerTargetClean
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) : Prop :=
  ¬ (exactCompilerTargetTree parameters transitionFuel cursor.erase).everHits
    masterTape

theorem exact_compiler_target_clean_iff_not_mem_event
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    ExactCompilerTargetClean parameters transitionFuel cursor masterTape ↔
      masterTape ∉ causalHitEvent
        (exactCompilerTargetTree parameters transitionFuel cursor.erase) := by
  rfl

/-- The executable target checker accepts every target-clean tape. -/
theorem check_causal_targets_ok_of_clean :
    ∀ {caps : List Nat} (tree : CausalTargetTree Digest256 caps)
      (tape : FreshAnswerTape Digest256 caps.length),
      ¬ tree.everHits tape → checkCausalTargets tree tape = .ok PUnit.unit
  | [], .done, _tape, _clean => by
      rfl
  | _cap :: _caps, .step targets _targetCardLe next, tape, clean => by
      have headClean : tape.1 ∉ targets := by
        intro member
        exact clean (Or.inl member)
      have tailClean : ¬ (next tape.1).everHits tape.2 := by
        intro hit
        exact clean (Or.inr hit)
      simp only [checkCausalTargets, headClean, ↓reduceDIte]
      exact check_causal_targets_ok_of_clean (next tape.1) tape.2 tailClean

theorem exact_compiler_target_clean_checker_ok
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (clean : ExactCompilerTargetClean parameters transitionFuel cursor
      masterTape) :
    checkCausalTargets
      (exactCompilerTargetTree parameters transitionFuel cursor.erase)
      masterTape = .ok PUnit.unit :=
  check_causal_targets_ok_of_clean _ _ clean

/-! ## Local causal facts at one actual pair exposure -/

structure DirectForkCoordinatesClean
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256) : Prop where
  outputAvoidsTargets :
    forkOutput ∉ operationalForkTargets seen frozenHistory outputInput
      advanceInput
  advanceAvoidsTargets :
    forkAdvance ∉ operationalForkTargets (insert forkOutput seen)
      frozenHistory outputInput advanceInput

theorem direct_fork_clean_advance_ne_output
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256)
    (clean : DirectForkCoordinatesClean seen frozenHistory outputInput
      advanceInput forkOutput forkAdvance) :
    forkAdvance ≠ forkOutput := by
  intro equal
  apply clean.advanceAvoidsTargets
  subst forkAdvance
  simp [operationalForkTargets, operationalHistoryTargets]

theorem direct_fork_clean_coordinates_avoid_literal_inputs
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256)
    (clean : DirectForkCoordinatesClean seen frozenHistory outputInput
      advanceInput forkOutput forkAdvance) :
    ¬ HasLiteralStatePrefix forkOutput outputInput ∧
      ¬ HasLiteralStatePrefix forkOutput advanceInput ∧
      ¬ HasLiteralStatePrefix forkAdvance outputInput ∧
      ¬ HasLiteralStatePrefix forkAdvance advanceInput := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro prefixProof
    exact clean.outputAvoidsTargets
      (output_input_literal_prefix_is_fork_target seen frozenHistory
        outputInput advanceInput forkOutput prefixProof)
  · intro prefixProof
    exact clean.outputAvoidsTargets
      (advance_input_literal_prefix_is_fork_target seen frozenHistory
        outputInput advanceInput forkOutput prefixProof)
  · intro prefixProof
    exact clean.advanceAvoidsTargets
      (output_input_literal_prefix_is_fork_target (insert forkOutput seen)
        frozenHistory outputInput advanceInput forkAdvance prefixProof)
  · intro prefixProof
    exact clean.advanceAvoidsTargets
      (advance_input_literal_prefix_is_fork_target (insert forkOutput seen)
        frozenHistory outputInput advanceInput forkAdvance prefixProof)

/-- Two head coordinates of the actual causal tree give the local clean-pair
facts.  The theorem uses the scheduler's own `forkPair`/`forkAdvance`
constructors, not a separately supplied target set. -/
theorem unified_tree_clean_direct_fork_pair
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (seen : Finset Digest256)
    (seenBound : seen.card ≤ step)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      UnifiedExposureCursor globalOracleCalls)
    (forkOutput forkAdvance : Digest256)
    (tail : FreshAnswerTape Digest256
      (operationalCapsFrom (step + 1 + 1) remaining
        globalOracleCalls).length)
    (clean : ¬
      (unifiedExposureTargetTreeFrom globalOracleCalls
        (transitionFuel + 1) step (Nat.succ (Nat.succ remaining)) seen
        seenBound
        (.forkPair frozenHistory pairRoom outputInput advanceInput template
          next)).everHits (forkOutput, (forkAdvance, tail))) :
    DirectForkCoordinatesClean seen frozenHistory outputInput advanceInput
      forkOutput forkAdvance := by
  constructor
  · intro member
    apply clean
    exact Or.inl member
  · intro member
    apply clean
    exact Or.inr (Or.inl member)

/-! ## Deployed pair inputs are distinct -/

/-- Any `some` value returned by the executable transition projection is the
literal deployed `S || 0x01`, `S || 0x02` pair and is therefore distinct. -/
theorem squeeze_pair_inputs_of_transition_are_distinct
    (transition : FutureFreeTransition)
    (outputInput advanceInput : ShaInput)
    (exactInputs : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput)) :
    outputInput ≠ advanceInput := by
  let state : FutureFreeVerifierState :=
    { current := transition.after
      seen := []
      transitions := [transition] }
  let location : LocatedFutureFreeSqueeze state outputInput advanceInput :=
    { transition := transition
      found := by
        simp [state, firstMatchingSqueezeTransition, exactInputs] }
  obtain ⟨_owner, _block, _reply, _event, outputExact, advanceExact⟩ :=
    located_future_free_squeeze_has_literal_pair_state location
  intro equalInputs
  have literalInputsEqual :
      bytes location.transition.before.core.digest ++ [domSqueeze] =
        bytes location.transition.before.core.digest ++ [domAdvance] :=
    outputExact.symm.trans (equalInputs.trans advanceExact)
  exact (squeeze_output_and_advance_inputs_are_distinct
    location.transition.before.core.digest) literalInputsEqual

/-! ## Successful concrete programming installs exactly the sampled pair -/

structure ConcretePairInstalledExactly
    (state afterBoth : OracleState)
    (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256) : Prop where
  inputsDistinct : outputInput ≠ advanceInput
  outputInitiallyMissing : lookupEntry state outputInput = none
  advanceInitiallyMissing : lookupEntry state advanceInput = none
  historyUnchanged : afterBoth.history = state.history
  totalCallsUnchanged : afterBoth.totalCalls = state.totalCalls
  freshCallsUnchanged : afterBoth.freshCalls = state.freshCalls
  tableLengthExact : afterBoth.table.length = state.table.length + 2
  programmingLengthExact :
    afterBoth.programmingHistory.length = state.programmingHistory.length + 2
  outputInstalled :
    (lookupEntry afterBoth outputInput).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some forkOutput
  advanceInstalled :
    (lookupEntry afterBoth advanceInput).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some forkAdvance

private theorem two_successful_programs_install_exactly
    (limits : OracleLimits) (state afterFirst afterBoth : OracleState)
    (firstInput secondInput : ShaInput)
    (firstOutput secondOutput : Digest256)
    (first : programConcreteHalf limits state firstInput firstOutput =
      .ok afterFirst)
    (second : programConcreteHalf limits afterFirst secondInput secondOutput =
      .ok afterBoth) :
    afterBoth.history = state.history ∧
      afterBoth.totalCalls = state.totalCalls ∧
      afterBoth.freshCalls = state.freshCalls ∧
      afterBoth.table.length = state.table.length + 2 ∧
      afterBoth.programmingHistory.length =
        state.programmingHistory.length + 2 ∧
      (lookupEntry afterBoth firstInput).map
          AspisK1.V7FsAokExperiment.TableEntry.output = some firstOutput ∧
      (lookupEntry afterBoth secondInput).map
          AspisK1.V7FsAokExperiment.TableEntry.output = some secondOutput := by
  have first' : programOracle limits .extractorReplay state
      { input := firstInput, output := firstOutput } = .ok afterFirst := by
    simpa [programConcreteHalf] using first
  have second' : programOracle limits .extractorReplay afterFirst
      { input := secondInput, output := secondOutput } = .ok afterBoth := by
    simpa [programConcreteHalf] using second
  have firstFacts := program_oracle_success_exact limits .extractorReplay
    state afterFirst { input := firstInput, output := firstOutput } first'
  have secondFacts := program_oracle_success_exact limits .extractorReplay
    afterFirst afterBoth { input := secondInput, output := secondOutput } second'
  have firstCounters := successful_program_oracle_preserves_call_counters
    limits .extractorReplay state afterFirst
    { input := firstInput, output := firstOutput } first'
  have secondCounters := successful_program_oracle_preserves_call_counters
    limits .extractorReplay afterFirst afterBoth
    { input := secondInput, output := secondOutput } second'
  have firstInstalled := program_oracle_success_preserves_lookup_answer
    limits .extractorReplay afterFirst afterBoth
    { input := secondInput, output := secondOutput } second'
    firstInput firstOutput firstFacts.2.2.2
  refine ⟨secondFacts.1.trans firstFacts.1,
    secondCounters.1.trans firstCounters.1,
    secondCounters.2.trans firstCounters.2, ?_, ?_, firstInstalled,
    secondFacts.2.2.2⟩
  · rw [secondFacts.2.2.1, firstFacts.2.2.1]
    simp
  · rw [secondFacts.2.1, firstFacts.2.1]
    simp

theorem program_concrete_pair_ready_installs_exact_coordinates
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state afterBoth : OracleState)
    (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256)
    (ready : programConcretePair limits order state outputInput advanceInput
      forkOutput forkAdvance = .ready afterBoth) :
    ConcretePairInstalledExactly state afterBoth outputInput advanceInput
      forkOutput forkAdvance := by
  by_cases inputsAlias : outputInput = advanceInput
  · simp [programConcretePair, inputsAlias] at ready
  cases outputFound : lookupEntry state outputInput with
  | some entry =>
      simp [programConcretePair, inputsAlias, outputFound] at ready
  | none =>
      cases advanceFound : lookupEntry state advanceInput with
      | some entry =>
          simp [programConcretePair, inputsAlias, outputFound, advanceFound]
            at ready
      | none =>
          cases order with
          | outputThenAdvance =>
              cases first : programConcreteHalf limits state outputInput
                  forkOutput with
              | error reason =>
                  simp [programConcretePair, inputsAlias, outputFound,
                    advanceFound, first] at ready
              | ok afterFirst =>
                  cases second : programConcreteHalf limits afterFirst
                      advanceInput forkAdvance with
                  | error reason =>
                      simp [programConcretePair, inputsAlias, outputFound,
                        advanceFound, first, second] at ready
                  | ok finalState =>
                      have finalExact : finalState = afterBoth := by
                        simpa [programConcretePair, inputsAlias, outputFound,
                          advanceFound, first, second] using ready
                      subst finalState
                      have facts := two_successful_programs_install_exactly
                        limits state afterFirst afterBoth outputInput
                        advanceInput forkOutput forkAdvance first second
                      exact
                        { inputsDistinct := inputsAlias
                          outputInitiallyMissing := outputFound
                          advanceInitiallyMissing := advanceFound
                          historyUnchanged := facts.1
                          totalCallsUnchanged := facts.2.1
                          freshCallsUnchanged := facts.2.2.1
                          tableLengthExact := facts.2.2.2.1
                          programmingLengthExact := facts.2.2.2.2.1
                          outputInstalled := facts.2.2.2.2.2.1
                          advanceInstalled := facts.2.2.2.2.2.2 }
          | advanceThenOutput =>
              cases first : programConcreteHalf limits state advanceInput
                  forkAdvance with
              | error reason =>
                  simp [programConcretePair, inputsAlias, outputFound,
                    advanceFound, first] at ready
              | ok afterFirst =>
                  cases second : programConcreteHalf limits afterFirst
                      outputInput forkOutput with
                  | error reason =>
                      simp [programConcretePair, inputsAlias, outputFound,
                        advanceFound, first, second] at ready
                  | ok finalState =>
                      have finalExact : finalState = afterBoth := by
                        simpa [programConcretePair, inputsAlias, outputFound,
                          advanceFound, first, second] using ready
                      subst finalState
                      have facts := two_successful_programs_install_exactly
                        limits state afterFirst afterBoth advanceInput
                        outputInput forkAdvance forkOutput first second
                      exact
                        { inputsDistinct := inputsAlias
                          outputInitiallyMissing := outputFound
                          advanceInitiallyMissing := advanceFound
                          historyUnchanged := facts.1
                          totalCallsUnchanged := facts.2.1
                          freshCallsUnchanged := facts.2.2.1
                          tableLengthExact := facts.2.2.2.1
                          programmingLengthExact := facts.2.2.2.2.1
                          outputInstalled := facts.2.2.2.2.2.2
                          advanceInstalled := facts.2.2.2.2.2.1 }

/-! ## Exact obstruction: table conflicts do not depend on sampled coins -/

theorem existing_output_lookup_conflict_is_coordinate_independent
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (distinct : outputInput ≠ advanceInput)
    (found : lookupEntry state outputInput = some entry)
    (forkOutput forkAdvance : Digest256) :
    programConcretePair limits order state outputInput advanceInput forkOutput
      forkAdvance = .failed .outputInputAlreadyDefined 0 := by
  simp [programConcretePair, distinct, found]

theorem existing_advance_lookup_conflict_is_coordinate_independent
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (distinct : outputInput ≠ advanceInput)
    (outputMissing : lookupEntry state outputInput = none)
    (found : lookupEntry state advanceInput = some entry)
    (forkOutput forkAdvance : Digest256) :
    programConcretePair limits order state outputInput advanceInput forkOutput
      forkAdvance = .failed .advanceInputAlreadyDefined 0 := by
  simp [programConcretePair, distinct, outputMissing, found]

/-!
The two coordinate-independence theorems are the precise reason no global
`TargetClean → programming succeeds` theorem is stated.  Such a theorem needs
one additional *operational provenance result*: every `PreparedConcreteRestoration`
returned by `prepareConcreteRestorationFromStartProgram` must carry table
coverage strong enough to prove both pair lookups absent at its
`programmingBase`.  `HistoryTotalCoherent` alone counts calls but says nothing
about programmed table entries, and `SchedulerNativeCursor.forkPair` erases
the programming base entirely.  This missing projection is strictly smaller
than an acceptance/trace-cover theorem.
-/

#print axioms exact_compiler_target_clean_iff_not_mem_event
#print axioms check_causal_targets_ok_of_clean
#print axioms exact_compiler_target_clean_checker_ok
#print axioms direct_fork_clean_advance_ne_output
#print axioms direct_fork_clean_coordinates_avoid_literal_inputs
#print axioms unified_tree_clean_direct_fork_pair
#print axioms squeeze_pair_inputs_of_transition_are_distinct
#print axioms program_concrete_pair_ready_installs_exact_coordinates
#print axioms existing_output_lookup_conflict_is_coordinate_independent
#print axioms existing_advance_lookup_conflict_is_coordinate_independent

end

end AspisK1.V7Tag73ExactCompilerTargetClean
