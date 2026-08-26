import AspisFormal.K1.V7Tag73NoPairOccurrenceTrichotomy
import AspisFormal.K1.V7Tag73ConcreteKnowledgeInsertion
import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner

/-!
# Same-tape replay when a generated squeeze pair is absent from Q1

This module constructs the zero-loss, challenge-independent replay branch.
Starting from a normally returned same-hidden-tape first execution, it:

* proves that an input absent from both the initial table and frozen
  adversary Q1 is absent from the post-adversary table;
* programs two distinct such inputs;
* restarts the exact same start-only adversary program;
* preloads the complete returned first-run query path from the post-adversary
  table; and
* proves that the replay returns the same result and follows the same ordered
  input/output path while never reading either programmed point.

All resource increments are equalities.  The replay performs exactly one
cached call per first-run path element, consumes no fresh answer, and adds
exactly two programming records.  There is no acceptance, extraction,
semantic-provenance, trace-cover, or probability premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73NoPairReplay

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## Table growth is covered by the initial table or actor history -/

def TableCoveredByInitialOrActorHistory
    (initial : OracleState) (actor : QueryActor)
    (current : OracleState) : Prop :=
  ∀ entry ∈ current.table,
    entry ∈ initial.table ∨
      ∃ record ∈ current.history,
        record.actor = actor ∧ record.input = entry.input ∧
          record.output = entry.output

theorem initial_table_is_covered_by_initial_or_actor_history
    (initial : OracleState) (actor : QueryActor) :
    TableCoveredByInitialOrActorHistory initial actor initial := by
  intro entry member
  exact Or.inl member

theorem query_oracle_preserves_initial_or_actor_history_coverage
    (controller : AdaptiveController) (limits : OracleLimits)
    (initial : OracleState) (actor : QueryActor)
    (state nextState : OracleState) (input : ShaInput) (output : ShaOutput)
    (covered : TableCoveredByInitialOrActorHistory initial actor state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    TableCoveredByInitialOrActorHistory initial actor nextState := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      intro candidate member
      rcases covered candidate member with initialMember | historyMember
      · exact Or.inl initialMember
      · rcases historyMember with
          ⟨record, recordMember, actorEq, inputEq, outputEq⟩
        exact Or.inr ⟨record, List.mem_append_left _ recordMember,
          actorEq, inputEq, outputEq⟩
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          intro candidate member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with old | rfl
          · rcases covered candidate old with initialMember | historyMember
            · exact Or.inl initialMember
            · rcases historyMember with
                ⟨record, recordMember, actorEq, inputEq, outputEq⟩
              exact Or.inr ⟨record,
                List.mem_append_left _ recordMember,
                actorEq, inputEq, outputEq⟩
          · let newRecord : QueryRecord :=
              { input := input
                output := answer
                actor := actor
                origin := .fresh }
            exact Or.inr ⟨newRecord,
              List.mem_append_right _ (by simp [newRecord]), rfl, rfl, rfl⟩

theorem run_machine_preserves_initial_or_actor_history_coverage
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (initial : OracleState)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (covered : TableCoveredByInitialOrActorHistory initial actor state) :
    TableCoveredByInitialOrActorHistory initial actor
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simpa [runMachine] using covered
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using covered
      | abort reason => simpa [runMachine] using covered
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simpa using covered
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              exact ih nextState (next output)
                (query_oracle_preserves_initial_or_actor_history_coverage
                  controller limits initial actor state nextState input output
                  covered queryResult)

theorem post_run_lookup_none_of_initial_and_frozen_actor_absence
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (initial : OracleState) (program : OracleMachine Result)
    (input : ShaInput)
    (initialMissing : lookupEntry initial input = none)
    (frozenAbsent : ∀ record ∈
      actorHistory actor
        (runMachine controller limits actor fuel initial program).oracle,
      record.input ≠ input) :
    lookupEntry
      (runMachine controller limits actor fuel initial program).oracle input =
        none := by
  let final := (runMachine controller limits actor fuel initial program).oracle
  have covered : TableCoveredByInitialOrActorHistory initial actor final :=
    run_machine_preserves_initial_or_actor_history_coverage controller limits
      initial actor fuel initial program
      (initial_table_is_covered_by_initial_or_actor_history initial actor)
  cases found : lookupEntry final input with
  | none => rfl
  | some entry =>
      unfold lookupEntry at found
      have foundSpec := List.find?_eq_some_iff_append.mp found
      have entryInput : entry.input = input := by
        exact of_decide_eq_true foundSpec.1
      have entryMember : entry ∈ final.table :=
        List.mem_of_find?_eq_some found
      have contradiction : False := by
        rcases covered entry entryMember with initialMember | historyMember
        · have initialMissing' : initial.table.find?
              (fun candidate => candidate.input = input) = none := by
            simpa [lookupEntry] using initialMissing
          have initialNo :=
            List.find?_eq_none.mp initialMissing' entry initialMember
          exact initialNo (by simpa [entryInput])
        · rcases historyMember with
            ⟨record, recordMember, actorEq, recordInput, _recordOutput⟩
          have actorMember : record ∈ actorHistory actor final := by
            apply List.mem_filter.mpr
            exact ⟨recordMember, by simpa [actorEq]⟩
          exact frozenAbsent record actorMember
            (recordInput.trans entryInput)
      exact contradiction.elim

/-! ## Exact programming states -/

def appendProgrammedPoint (actor : QueryActor) (state : OracleState)
    (programming : Programming) : OracleState :=
  { state with
    table := state.table ++
      [{ input := programming.input, output := programming.output,
         source := .programmed }]
    programmingHistory := state.programmingHistory ++
      [{ input := programming.input, output := programming.output,
         actor := actor }] }

theorem program_oracle_fresh_point_exact
    (limits : OracleLimits) (actor : QueryActor) (state : OracleState)
    (programming : Programming)
    (within : state.programmingHistory.length < limits.programmedPoints)
    (missing : lookupEntry state programming.input = none) :
    programOracle limits actor state programming =
      .ok (appendProgrammedPoint actor state programming) := by
  simp [programOracle, Nat.not_le.mpr within, missing,
    appendProgrammedPoint]

theorem append_programmed_point_preserves_lookup_some
    (actor : QueryActor) (state : OracleState)
    (programming : Programming) (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : lookupEntry state input = some entry) :
    lookupEntry (appendProgrammedPoint actor state programming) input =
      some entry := by
  unfold lookupEntry at found ⊢
  change (state.table ++
      [({ input := programming.input, output := programming.output,
          source := .programmed } :
        AspisK1.V7FsAokExperiment.TableEntry)]).find?
        (fun candidate => candidate.input = input) = some entry
  rw [List.find?_append, found]
  rfl

theorem append_programmed_point_preserves_answer
    (actor : QueryActor) (state : OracleState)
    (programming : Programming) (input : ShaInput) (output : ShaOutput)
    (found : (lookupEntry state input).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some output) :
    (lookupEntry (appendProgrammedPoint actor state programming) input).map
        AspisK1.V7FsAokExperiment.TableEntry.output = some output := by
  cases entryFound : lookupEntry state input with
  | none => simp [entryFound] at found
  | some entry =>
      rw [append_programmed_point_preserves_lookup_some actor state
        programming input entry entryFound]
      simpa [entryFound] using found

theorem append_programmed_point_other_input_remains_missing
    (actor : QueryActor) (state : OracleState)
    (programming : Programming) (input : ShaInput)
    (missing : lookupEntry state input = none)
    (different : programming.input ≠ input) :
    lookupEntry (appendProgrammedPoint actor state programming) input = none := by
  have missing' : state.table.find?
      (fun entry => entry.input = input) = none := by
    simpa [lookupEntry] using missing
  unfold appendProgrammedPoint lookupEntry
  rw [List.find?_append, missing']
  simp [different]

def noPairReplayLimits (state : OracleState) (pathLength : Nat) :
    OracleLimits where
  totalCalls := state.totalCalls + pathLength
  freshCalls := state.freshCalls
  programmedPoints := state.programmingHistory.length + 2

/-! ## Generic cached replay of a concrete machine query path -/

def PreloadedPathAnswers (state : OracleState)
    (pairs : List (ShaInput × ShaOutput)) : Prop :=
  ∀ pair ∈ pairs,
    (lookupEntry state pair.1).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some pair.2

/-- If every answer on a syntactic `MachineQueryPath` is already in the
starting table, replay follows that path without consulting its controller.
The complete state/resource delta is proved by induction on the path. -/
theorem run_machine_replays_preloaded_path_exactly
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (pairs : List (ShaInput × ShaOutput)) (result : Result)
    (path : MachineQueryPath program pairs result)
    (answers : PreloadedPathAnswers state pairs)
    (totalRoom : state.totalCalls + pairs.length ≤ limits.totalCalls)
    (fuelRoom : pairs.length ≤ fuel) :
    ∃ replayRecords : List QueryRecord,
      (runMachine controller limits actor fuel state program).halt =
          .returned result ∧
      (runMachine controller limits actor fuel state program).oracle.history =
          state.history ++ replayRecords ∧
      queryAnswerTrace replayRecords = pairs ∧
      (∀ record ∈ replayRecords, record.actor = actor) ∧
      (runMachine controller limits actor fuel state program).oracle.table =
          state.table ∧
      (runMachine controller limits actor fuel state
          program).oracle.programmingHistory = state.programmingHistory ∧
      (runMachine controller limits actor fuel state program).oracle.totalCalls =
          state.totalCalls + pairs.length ∧
      (runMachine controller limits actor fuel state program).oracle.freshCalls =
          state.freshCalls ∧
      (runMachine controller limits actor fuel state program).steps =
          pairs.length := by
  induction path generalizing state fuel with
  | pure result =>
      refine ⟨[], ?_⟩
      simp [runMachine, queryAnswerTrace]
  | query input next output pairs result tail ih =>
      cases fuel with
      | zero => simp at fuelRoom
      | succ fuel =>
          have headAnswer := answers (input, output) (by simp)
          cases found : lookupEntry state input with
          | none => simp [found] at headAnswer
          | some entry =>
              have outputEq : entry.output = output := by
                simpa [found] using headAnswer
              subst output
              have within : state.totalCalls < limits.totalCalls := by
                simp only [List.length_cons] at totalRoom
                omega
              let headRecord : QueryRecord :=
                { input := input
                  output := entry.output
                  actor := actor
                  origin := cachedOrigin entry.source }
              let nextState : OracleState :=
                { state with
                  history := state.history ++ [headRecord]
                  totalCalls := state.totalCalls + 1 }
              have queried : queryOracle controller limits actor state input =
                  .ok (entry.output, nextState) := by
                simp [queryOracle, Nat.not_le.mpr within, found,
                  nextState, headRecord]
              have tailAnswers : PreloadedPathAnswers nextState pairs := by
                intro pair member
                change Option.map
                  AspisK1.V7FsAokExperiment.TableEntry.output
                    (lookupEntry state pair.1) = some pair.2
                exact answers pair (by simp [member])
              have tailTotalRoom :
                  nextState.totalCalls + pairs.length ≤ limits.totalCalls := by
                change state.totalCalls + 1 + pairs.length ≤ limits.totalCalls
                simp only [List.length_cons] at totalRoom
                omega
              have tailFuelRoom : pairs.length ≤ fuel := by
                simp only [List.length_cons] at fuelRoom
                omega
              obtain ⟨tailRecords, tailHalt, tailHistory, tailTrace,
                  tailActors, tailTable, tailProgramming, tailTotal,
                  tailFresh, tailSteps⟩ :=
                ih fuel nextState tailAnswers
                  tailTotalRoom tailFuelRoom
              refine ⟨headRecord :: tailRecords, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_, ?_, ?_⟩
              · simpa [runMachine, queried] using tailHalt
              · simpa [runMachine, queried, nextState, List.append_assoc]
                  using tailHistory
              · change (input, entry.output) :: queryAnswerTrace tailRecords =
                  (input, entry.output) :: pairs
                exact congrArg (List.cons (input, entry.output)) tailTrace
              · intro record member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · rfl
                · exact tailActors record member
              · simpa [runMachine, queried, nextState] using tailTable
              · simpa [runMachine, queried, nextState] using tailProgramming
              · simpa [runMachine, queried, nextState, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using tailTotal
              · simpa [runMachine, queried, nextState] using tailFresh
              · simpa [runMachine, queried] using tailSteps

theorem run_machine_preloaded_replay_history_since_exact
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (pairs : List (ShaInput × ShaOutput)) (result : Result)
    (path : MachineQueryPath program pairs result)
    (answers : PreloadedPathAnswers state pairs)
    (totalRoom : state.totalCalls + pairs.length ≤ limits.totalCalls)
    (fuelRoom : pairs.length ≤ fuel) :
    let replay := runMachine controller limits actor fuel state program
    replay.halt = .returned result ∧
      queryAnswerTrace (historySince state replay.oracle) = pairs ∧
      (∀ record ∈ historySince state replay.oracle,
        record.actor = actor) ∧
      replay.oracle.table = state.table ∧
      replay.oracle.programmingHistory = state.programmingHistory ∧
      replay.oracle.totalCalls = state.totalCalls + pairs.length ∧
      replay.oracle.freshCalls = state.freshCalls ∧
      replay.steps = pairs.length := by
  obtain ⟨records, halt, finalHistory, trace, actors, table,
      programming, total, fresh, steps⟩ :=
    run_machine_replays_preloaded_path_exactly controller limits actor fuel
      state program pairs result path answers totalRoom fuelRoom
  have since : historySince state
      (runMachine controller limits actor fuel state program).oracle =
        records := by
    unfold historySince
    rw [finalHistory]
    simp
  exact ⟨halt, by simpa [since] using trace,
    by simpa [since] using actors, table, programming, total, fresh, steps⟩

/-! ## Same-hidden-tape source construction -/

theorem same_tape_source_no_pair_replay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (result : Result)
    (returned : source.origin.firstExecution.halt = .returned result)
    (outputInput advanceInput : ShaInput)
    (outputValue advanceValue : ShaOutput)
    (distinct : outputInput ≠ advanceInput)
    (outputInitialMissing :
      lookupEntry source.initialOracle outputInput = none)
    (advanceInitialMissing :
      lookupEntry source.initialOracle advanceInput = none)
    (noPairInFrozenQ1 : firstEitherInputOccurrence outputInput advanceInput
      (freezeAdversaryQ1 source.origin.firstRun.stateAtAdversaryHalt) = none) :
    ∃ pairs : List (ShaInput × ShaOutput),
      let post := source.origin.firstRun.stateAtAdversaryHalt
      let outputProgramming : Programming :=
        { input := outputInput, output := outputValue }
      let advanceProgramming : Programming :=
        { input := advanceInput, output := advanceValue }
      let firstProgrammed := appendProgrammedPoint .extractorReplay post
        outputProgramming
      let bothProgrammed := appendProgrammedPoint .extractorReplay
        firstProgrammed advanceProgramming
      let limits := noPairReplayLimits post pairs.length
      let replayController := recordedPrefixController
        bothProgrammed.history.length (freezeAdversaryQ1 post)
      let replay := runMachine replayController limits .extractorReplay
        pairs.length bothProgrammed
        (source.origin.capability.start source.observation)
      MachineQueryPath (source.origin.capability.start source.observation)
          pairs result ∧
      programOracle limits .extractorReplay post outputProgramming =
          .ok firstProgrammed ∧
      programOracle limits .extractorReplay firstProgrammed
          advanceProgramming = .ok bothProgrammed ∧
      replay.halt = .returned result ∧
      queryAnswerTrace (historySince bothProgrammed replay.oracle) = pairs ∧
      (∀ record ∈ historySince bothProgrammed replay.oracle,
        record.actor = .extractorReplay ∧
          record.input ≠ outputInput ∧ record.input ≠ advanceInput) ∧
      replay.oracle.table = bothProgrammed.table ∧
      replay.oracle.programmingHistory.length =
          post.programmingHistory.length + 2 ∧
      replay.oracle.totalCalls = post.totalCalls + pairs.length ∧
      replay.oracle.freshCalls = post.freshCalls ∧
      replay.steps = pairs.length ∧
      source.origin.capability.tapeIdentity = source.tapeIdentity ∧
      source.origin.capability.start source.observation =
          source.blackBox.start source.hiddenTape source.observation ∧
      source.origin.firstRun.forgery = source.forgeryOf result := by
  have returnedRun :
      (runMachine source.controller source.oracleLimits .adversary
        source.firstRunFuel source.initialOracle
        (source.origin.capability.start source.observation)).halt =
          .returned result := by
    simpa [source_origin_first_execution_starts_capability source] using returned
  obtain ⟨pairs, path, firstTrace, firstActors, finalAnswers⟩ :=
    run_machine_returned_has_exact_query_path source.controller
      source.oracleLimits .adversary source.firstRunFuel source.initialOracle
      (source.origin.capability.start source.observation) result returnedRun
  let post := source.origin.firstRun.stateAtAdversaryHalt
  have postEq : post =
      (runMachine source.controller source.oracleLimits .adversary
        source.firstRunFuel source.initialOracle
        (source.origin.capability.start source.observation)).oracle := by
    rfl
  have frozenFresh := (first_either_input_occurrence_none_iff
    outputInput advanceInput (freezeAdversaryQ1 post)).mp noPairInFrozenQ1
  have outputPostMissing : lookupEntry post outputInput = none := by
    rw [postEq]
    apply post_run_lookup_none_of_initial_and_frozen_actor_absence
      source.controller source.oracleLimits .adversary source.firstRunFuel
      source.initialOracle
      (source.origin.capability.start source.observation) outputInput
      outputInitialMissing
    intro record member
    exact (frozenFresh record member).1
  have advancePostMissing : lookupEntry post advanceInput = none := by
    rw [postEq]
    apply post_run_lookup_none_of_initial_and_frozen_actor_absence
      source.controller source.oracleLimits .adversary source.firstRunFuel
      source.initialOracle
      (source.origin.capability.start source.observation) advanceInput
      advanceInitialMissing
    intro record member
    exact (frozenFresh record member).2
  let outputProgramming : Programming :=
    { input := outputInput, output := outputValue }
  let advanceProgramming : Programming :=
    { input := advanceInput, output := advanceValue }
  let firstProgrammed := appendProgrammedPoint .extractorReplay post
    outputProgramming
  let bothProgrammed := appendProgrammedPoint .extractorReplay
    firstProgrammed advanceProgramming
  let limits := noPairReplayLimits post pairs.length
  have firstBudget :
      post.programmingHistory.length < limits.programmedPoints := by
    simp [limits, noPairReplayLimits]
  have firstProgramming :
      programOracle limits .extractorReplay post outputProgramming =
        .ok firstProgrammed := by
    exact program_oracle_fresh_point_exact limits .extractorReplay post
      outputProgramming firstBudget outputPostMissing
  have advanceAfterFirstMissing :
      lookupEntry firstProgrammed advanceInput = none := by
    apply append_programmed_point_other_input_remains_missing
      .extractorReplay post outputProgramming advanceInput advancePostMissing
    exact distinct
  have secondBudget :
      firstProgrammed.programmingHistory.length <
        limits.programmedPoints := by
    simp [firstProgrammed, appendProgrammedPoint, limits,
      noPairReplayLimits]
  have secondProgramming :
      programOracle limits .extractorReplay firstProgrammed
          advanceProgramming = .ok bothProgrammed := by
    exact program_oracle_fresh_point_exact limits .extractorReplay
      firstProgrammed advanceProgramming secondBudget advanceAfterFirstMissing
  have answersPost : PreloadedPathAnswers post pairs := by
    intro pair member
    rw [postEq]
    rw [← fixed_table_lookup_eq_lookup_entry_output]
    exact finalAnswers pair member
  have answersFirst : PreloadedPathAnswers firstProgrammed pairs := by
    intro pair member
    exact append_programmed_point_preserves_answer .extractorReplay post
      outputProgramming pair.1 pair.2 (answersPost pair member)
  have answersBoth : PreloadedPathAnswers bothProgrammed pairs := by
    intro pair member
    exact append_programmed_point_preserves_answer .extractorReplay
      firstProgrammed advanceProgramming pair.1 pair.2
      (answersFirst pair member)
  let replayController := recordedPrefixController
    bothProgrammed.history.length (freezeAdversaryQ1 post)
  let replay := runMachine replayController limits .extractorReplay
    pairs.length bothProgrammed
    (source.origin.capability.start source.observation)
  have totalRoom : bothProgrammed.totalCalls + pairs.length ≤
      limits.totalCalls := by
    simp [bothProgrammed, firstProgrammed, appendProgrammedPoint,
      limits, noPairReplayLimits]
  obtain ⟨replayHalt, replayTrace, replayActors, replayTable,
      replayProgramming, replayTotal, replayFresh, replaySteps⟩ :=
    run_machine_preloaded_replay_history_since_exact replayController limits
      .extractorReplay pairs.length bothProgrammed
      (source.origin.capability.start source.observation) pairs result path
      answersBoth totalRoom (le_refl _)
  have pairAbsentFromPath : ∀ pair ∈ pairs,
      pair.1 ≠ outputInput ∧ pair.1 ≠ advanceInput := by
    intro pair pairMember
    have mappedMember : pair ∈ queryAnswerTrace
        (historySince source.initialOracle
          (runMachine source.controller source.oracleLimits .adversary
            source.firstRunFuel source.initialOracle
            (source.origin.capability.start source.observation)).oracle) := by
      rw [firstTrace]
      exact pairMember
    obtain ⟨record, recordMember, recordPair⟩ :=
      List.mem_map.mp mappedMember
    have recordActor : record.actor = .adversary :=
      firstActors record recordMember
    have recordFinalMember : record ∈ post.history := by
      rw [postEq]
      exact List.mem_of_mem_drop recordMember
    have recordQ1Member : record ∈ freezeAdversaryQ1 post := by
      apply List.mem_filter.mpr
      exact ⟨recordFinalMember, by simpa [recordActor]⟩
    have fresh := frozenFresh record recordQ1Member
    have inputEq : record.input = pair.1 := by
      exact congrArg Prod.fst recordPair
    exact ⟨fun equal => fresh.1 (inputEq.trans equal),
      fun equal => fresh.2 (inputEq.trans equal)⟩
  refine ⟨pairs, path, firstProgramming, secondProgramming,
    replayHalt, replayTrace, ?_, replayTable,
    ?_, ?_, ?_, replaySteps,
    ?_, source_origin_capability_uses_same_hidden_tape source, ?_⟩
  · intro record member
    have actorEq := replayActors record member
    have pairMember : (record.input, record.output) ∈ pairs := by
      rw [← replayTrace]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    exact ⟨actorEq, (pairAbsentFromPath _ pairMember).1,
      (pairAbsentFromPath _ pairMember).2⟩
  · have lengths := congrArg List.length replayProgramming
    simpa [replayController, limits, post, outputProgramming,
      advanceProgramming, bothProgrammed, firstProgrammed,
      appendProgrammedPoint] using lengths
  · simpa [replayController, limits, post, outputProgramming,
      advanceProgramming, bothProgrammed, firstProgrammed,
      appendProgrammedPoint] using replayTotal
  · simpa [replayController, limits, post, outputProgramming,
      advanceProgramming, bothProgrammed, firstProgrammed,
      appendProgrammedPoint] using replayFresh
  · rfl
  · change returnedForgery source.forgeryOf
      source.origin.firstExecution.halt = source.forgeryOf result
    rw [returned]
    rfl

/-! ## One generated Tag-73 squeeze -/

theorem generated_squeeze_no_pair_replay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (result : Result)
    (returned : source.origin.firstExecution.halt = .returned result)
    (outputValue advanceValue : ShaOutput)
    (outputInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .output) = none)
    (advanceInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .advance) = none)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated = none) :
    ∃ pairs : List (ShaInput × ShaOutput),
      let post := source.origin.firstRun.stateAtAdversaryHalt
      let outputInput := generatedPairInput execution generated .output
      let advanceInput := generatedPairInput execution generated .advance
      let firstProgrammed := appendProgrammedPoint .extractorReplay post
        { input := outputInput, output := outputValue }
      let bothProgrammed := appendProgrammedPoint .extractorReplay
        firstProgrammed { input := advanceInput, output := advanceValue }
      let limits := noPairReplayLimits post pairs.length
      let replay := runMachine
        (recordedPrefixController bothProgrammed.history.length
          (freezeAdversaryQ1 post)) limits .extractorReplay pairs.length
        bothProgrammed (source.origin.capability.start source.observation)
      replay.halt = .returned result ∧
      queryAnswerTrace (historySince bothProgrammed replay.oracle) = pairs ∧
      (∀ record ∈ historySince bothProgrammed replay.oracle,
        record.actor = .extractorReplay ∧
          record.input ≠ outputInput ∧ record.input ≠ advanceInput) ∧
      replay.oracle.table = bothProgrammed.table ∧
      replay.oracle.programmingHistory.length =
        post.programmingHistory.length + 2 ∧
      replay.oracle.totalCalls = post.totalCalls + pairs.length ∧
      replay.oracle.freshCalls = post.freshCalls ∧
      replay.steps = pairs.length ∧
      source.origin.capability.start source.observation =
        source.blackBox.start source.hiddenTape source.observation ∧
      source.origin.firstRun.forgery = source.forgeryOf result := by
  have noPair' : firstEitherInputOccurrence
      (generatedPairInput execution generated .output)
      (generatedPairInput execution generated .advance)
      (freezeAdversaryQ1 source.origin.firstRun.stateAtAdversaryHalt) = none := by
    simpa [firstGeneratedPairOccurrenceInFrozenQ1] using noPair
  obtain ⟨pairs, _path, _firstProgramming, _secondProgramming, halt,
      trace, records, tableEq, programmed, total, fresh, steps,
      _identity, sameTape, forgery⟩ :=
    same_tape_source_no_pair_replay source result returned
      (generatedPairInput execution generated .output)
      (generatedPairInput execution generated .advance)
      outputValue advanceValue
      (generated_pair_inputs_are_distinct execution generated)
      outputInitialMissing advanceInitialMissing noPair'
  exact ⟨pairs, halt, trace, records, tableEq, programmed, total, fresh,
    steps, sameTape, forgery⟩

#print axioms query_oracle_preserves_initial_or_actor_history_coverage
#print axioms run_machine_preserves_initial_or_actor_history_coverage
#print axioms post_run_lookup_none_of_initial_and_frozen_actor_absence
#print axioms program_oracle_fresh_point_exact
#print axioms append_programmed_point_preserves_answer
#print axioms append_programmed_point_other_input_remains_missing
#print axioms run_machine_replays_preloaded_path_exactly
#print axioms run_machine_preloaded_replay_history_since_exact
#print axioms same_tape_source_no_pair_replay
#print axioms generated_squeeze_no_pair_replay

end

end AspisK1.V7Tag73NoPairReplay
