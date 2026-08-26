import AspisFormal.K1.V7Tag73OperationalKnowledgeInput
import AspisFormal.K1.V7Tag73AtomicPairReplay
import AspisFormal.K1.V7Tag73NoPairReplay

/-!
# Verify the actual parsed proof returned by a Tag-73 replay

An atomic same-tape replay may change an early challenge.  Its returned proof
is therefore allowed to contain a different parsed query DAG--in particular a
different challenge-dependent C2 commitment--from the first-run proof.  This
module takes the *actual* checked parsed value returned by the replay and runs
the literal shared-oracle verifier on that returned value's own DAG.

The verifier begins from the replay's final oracle state as both immutable
evidence and evolving shared state.  This module merely constructs that run;
it does not assert that the run returns or accepts.  A further operational
issue remains visible: post-fork adversary calls currently carry actor
`extractorReplay`, whereas historical grinding evidence in
`runFullVerifierPlan` is selected from actor `adversary`.  Changed post-fork
grinding therefore needs an actor-parametric evidence runner or a proved
history projection before a normal-return theorem can be claimed.

There is no original-DAG equality premise, acceptance field, extraction
conclusion, or trace-cover assumption here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ReplayReturnedVerifier

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73NoPairReplay
open AspisK1.V7Tag73OperationalKnowledgeInput
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## Checked adaptive return view -/

theorem checked_returned_value_context_is_exact
    {Statement Proof Payload : Type*}
    (returned : CheckedTag73AdversaryReturnedValue Statement Proof Payload) :
    returned.1.publicProof.proof.dag.tape.messages.context =
      returned.1.publicProof.publicInstance.context := by
  have checked := returned.2
  unfold returnedValueContextMatches at checked
  split at checked
  next equal => exact equal
  next _ => simp at checked

def atomicReplayReturnedValue
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) :
    CheckedTag73AdversaryReturnedValue Statement Proof Payload :=
  output.1.returned

def atomicReplayReturnedPublicProof
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) :
    PublicProof Statement (ParsedTag73Proof Proof Payload) :=
  (atomicReplayReturnedValue output).1.publicProof

def atomicReplayReturnedDag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) : ConcreteDagInstance :=
  (atomicReplayReturnedPublicProof output).proof.dag

/-- The returned DAG and public proof remain context-bound, independently of
whether either equals its first-run counterpart. -/
theorem atomic_replay_returned_dag_matches_returned_public_instance
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) :
    (atomicReplayReturnedDag output).tape.messages.context =
      (atomicReplayReturnedPublicProof output).publicInstance.context := by
  exact checked_returned_value_context_is_exact
    (atomicReplayReturnedValue output)

/-! ## Literal verifier run on the adaptive returned DAG -/

/-- Run the deployed action plan on the replay's actual returned parsed DAG.
The replay-final oracle, which contains both programmed pair entries and all
post-fork calls, is used as the next verifier's starting shared state. -/
def runVerifierOnAtomicReplayReturn
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) : MachineRun VerifierPlanResult :=
  runFullVerifierPlan verifierController verifierLimits verifierFuel
    output.1.replayRun.oracle output.1.replayRun.oracle
      (atomicReplayReturnedDag output).tape

@[simp] theorem verifier_on_atomic_replay_uses_returned_dag_not_frozen_dag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration}
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) :
    runVerifierOnAtomicReplayReturn verifierController verifierLimits
        verifierFuel output =
      runFullVerifierPlan verifierController verifierLimits verifierFuel
        output.1.replayRun.oracle output.1.replayRun.oracle
          output.1.returned.1.publicProof.proof.dag.tape := by
  rfl

/-! ## Successful constructor output supplies the actual next view -/

private theorem operational_atomic_replay_normally_returned
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run}) :
    output.1.replayRun.halt = .returned output.1.returned := by
  have operational := output.2
  rcases operational with
    ⟨_tape, _identity, _q1, _occurrenceFound, _split, _beforeFresh,
      _chosenInput, _actor, _pendingChosen, _halfClassification, _pendingHalf,
      _assigned, _prefixDefinition, _paused, _residual, _trace, _freshOutput,
      _freshAdvance, _distinct, _programmingOrder, _programmed,
      _replayDefinition, _pendingQuery, returned, _initialHistory,
      _replayHistory, _prefixSteps, _replaySteps, _replayFuelBound, _resources,
      _withinBudget⟩
  exact returned

/-- Principal operational bridge.  Successful construction gives the actual
same-tape replay return, its checked public-proof/DAG view, and the literal
next verifier computation.  There is intentionally no equation between
`nextDag` and the original `dag`. -/
theorem successful_atomic_replay_constructs_adaptive_returned_verifier
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement
          (ParsedTag73Proof Proof Payload)
          (CheckedTag73AdversaryReturnedValue Statement Proof Payload) //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration run})
    (success : constructAtomicPairReplay source.toSameTapeSource execution
      generated configuration = .ok output) :
    let returned := atomicReplayReturnedValue output
    let nextProof := atomicReplayReturnedPublicProof output
    let nextDag := atomicReplayReturnedDag output
    output.1.replayRun.halt = .returned returned ∧
      nextProof = returned.1.publicProof ∧
      nextDag = returned.1.publicProof.proof.dag ∧
      nextDag.tape.messages.context = nextProof.publicInstance.context ∧
      runVerifierOnAtomicReplayReturn verifierController verifierLimits
          verifierFuel output =
        runFullVerifierPlan verifierController verifierLimits verifierFuel
          output.1.replayRun.oracle output.1.replayRun.oracle nextDag.tape ∧
      source.origin.capability.start source.observation =
        source.blackBox.start source.hiddenTape source.observation := by
  have _constructed := construct_atomic_pair_replay_success_is_operational
    source.toSameTapeSource execution generated configuration output success
  exact ⟨operational_atomic_replay_normally_returned source execution
      generated configuration output,
    rfl, rfl,
    atomic_replay_returned_dag_matches_returned_public_instance output,
    rfl,
    source_origin_capability_uses_same_hidden_tape source.toSameTapeSource⟩

/-! ## The absent-pair replay and its returned proof -/

/-- The exact state obtained by programming both absent squeeze inputs at the
post-adversary state.  This is the starting state of the proved no-pair cached
replay. -/
def noPairReplayProgrammedOracle
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (outputValue advanceValue : ShaOutput) : OracleState :=
  let post := source.origin.firstRun.stateAtAdversaryHalt
  let outputInput := generatedPairInput execution generated .output
  let advanceInput := generatedPairInput execution generated .advance
  let firstProgrammed := appendProgrammedPoint .extractorReplay post
    { input := outputInput, output := outputValue }
  appendProgrammedPoint .extractorReplay firstProgrammed
    { input := advanceInput, output := advanceValue }

/-- The literal same-tape cached replay constructed in the no-pair branch.
The controller is fixed by the frozen adversary Q1, and all calls are tagged
`extractorReplay`; neither the result nor a replacement DAG is supplied to
this computation. -/
def noPairReplayMachine
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (outputValue advanceValue : ShaOutput)
    (pairs : List (ShaInput × ShaOutput)) :
    MachineRun (CheckedTag73AdversaryReturnedValue Statement Proof Payload) :=
  let post := source.origin.firstRun.stateAtAdversaryHalt
  let programmed := noPairReplayProgrammedOracle source execution generated
    outputValue advanceValue
  let limits := noPairReplayLimits post pairs.length
  runMachine
    (recordedPrefixController programmed.history.length
      (freezeAdversaryQ1 post))
    limits .extractorReplay pairs.length programmed
    (source.origin.capability.start source.observation)

/-- Run the exact verifier action plan on the checked parsed value returned by
the no-pair replay.  The replay-final state is used both as immutable evidence
and as the evolving shared oracle. -/
def runVerifierOnNoPairReplayReturn
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (outputValue advanceValue : ShaOutput)
    (pairs : List (ShaInput × ShaOutput))
    (returned : CheckedTag73AdversaryReturnedValue Statement Proof Payload)
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat) : MachineRun VerifierPlanResult :=
  let replay := noPairReplayMachine source execution generated outputValue
    advanceValue pairs
  runFullVerifierPlan verifierController verifierLimits verifierFuel
    replay.oracle replay.oracle returned.1.publicProof.proof.dag.tape

@[simp] theorem verifier_on_no_pair_replay_uses_returned_parsed_dag
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (outputValue advanceValue : ShaOutput)
    (pairs : List (ShaInput × ShaOutput))
    (returned : CheckedTag73AdversaryReturnedValue Statement Proof Payload)
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat) :
    runVerifierOnNoPairReplayReturn source execution generated outputValue
        advanceValue pairs returned verifierController verifierLimits
        verifierFuel =
      let replay := noPairReplayMachine source execution generated outputValue
        advanceValue pairs
      runFullVerifierPlan verifierController verifierLimits verifierFuel
        replay.oracle replay.oracle returned.1.publicProof.proof.dag.tape := by
  rfl

/-- In the absent-pair branch, the operational replay theorem returns the
same checked value as the first run because neither programmed pair input is
read.  Consequently the next verifier uses that returned value's parsed DAG.
This is an execution theorem, not an assumption that a changed adaptive proof
has the original DAG. -/
theorem successful_no_pair_replay_constructs_returned_verifier
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof Payload)
    (returned : source.origin.firstExecution.halt = .returned returnedValue)
    (outputValue advanceValue : ShaOutput)
    (outputInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .output) = none)
    (advanceInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .advance) = none)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated = none)
    (verifierController : AdaptiveController) (verifierLimits : OracleLimits)
    (verifierFuel : Nat) :
    ∃ pairs : List (ShaInput × ShaOutput),
      let programmed := noPairReplayProgrammedOracle source execution generated
        outputValue advanceValue
      let replay := noPairReplayMachine source execution generated outputValue
        advanceValue pairs
      replay.halt = .returned returnedValue ∧
      queryAnswerTrace (historySince programmed replay.oracle) = pairs ∧
      (∀ record ∈ historySince programmed replay.oracle,
        record.actor = .extractorReplay ∧
          record.input ≠ generatedPairInput execution generated .output ∧
          record.input ≠ generatedPairInput execution generated .advance) ∧
      returnedValue.1.publicProof.proof.dag.tape.messages.context =
        returnedValue.1.publicProof.publicInstance.context ∧
      runVerifierOnNoPairReplayReturn source execution generated outputValue
          advanceValue pairs returnedValue verifierController verifierLimits
          verifierFuel =
        runFullVerifierPlan verifierController verifierLimits verifierFuel
          replay.oracle replay.oracle
            returnedValue.1.publicProof.proof.dag.tape ∧
      source.origin.capability.start source.observation =
        source.blackBox.start source.hiddenTape source.observation := by
  obtain ⟨pairs, halt, trace, replayRecords, _table, _programmed, _total,
      _fresh, _steps, sameTape, _forgery⟩ :=
    generated_squeeze_no_pair_replay source.toSameTapeSource execution
      generated returnedValue returned outputValue advanceValue
      outputInitialMissing advanceInitialMissing noPair
  refine ⟨pairs, ?_⟩
  refine ⟨?_, ?_, ?_, checked_returned_value_context_is_exact returnedValue,
    rfl, sameTape⟩
  · simpa [noPairReplayMachine, noPairReplayProgrammedOracle,
      Tag73SameTapeSource.origin, Tag73SameTapeSource.toSameTapeSource] using
      halt
  · simpa [noPairReplayMachine, noPairReplayProgrammedOracle,
      Tag73SameTapeSource.origin, Tag73SameTapeSource.toSameTapeSource] using
      trace
  · simpa [noPairReplayMachine, noPairReplayProgrammedOracle,
      Tag73SameTapeSource.origin, Tag73SameTapeSource.toSameTapeSource] using
      replayRecords

/-! ## Exact actor-tag boundary for rerunning the deployed verifier -/

theorem extractor_replay_actor_ne_adversary :
    QueryActor.extractorReplay ≠ QueryActor.adversary := by
  decide

/-- A query record created by a replay cannot itself satisfy the exact
historical-evidence predicate used by the deployed shared-oracle verifier.
This is the smallest current obstruction to treating changed post-fork work
searches as ordinary adversary grinding evidence. -/
theorem extractor_replay_record_cannot_be_adversary_evidence_candidate
    (evidence : OracleState) (input : ShaInput) (record : QueryRecord)
    (replayActor : record.actor = .extractorReplay) :
    ¬ (record.input = input ∧ record.actor = .adversary ∧
      cachedEvidenceOutput evidence input = some record.output) := by
  rintro ⟨_input, adversaryActor, _answer⟩
  have impossible : QueryActor.extractorReplay = QueryActor.adversary := by
    rw [← replayActor]
    exact adversaryActor
  exact extractor_replay_actor_ne_adversary impossible

/-- In particular, a replay-tagged record can never be the record selected by
`frozenAdversaryEvidenceRecord`, regardless of its input and output. -/
theorem extractor_replay_record_cannot_be_selected_as_frozen_evidence
    (evidence : OracleState) (input : ShaInput) (record : QueryRecord)
    (replayActor : record.actor = .extractorReplay) :
    frozenAdversaryEvidenceRecord evidence input ≠ some record := by
  intro selected
  unfold frozenAdversaryEvidenceRecord at selected
  have predicate := List.find?_some selected
  have candidate : record.input = input ∧ record.actor = .adversary ∧
      cachedEvidenceOutput evidence input = some record.output :=
    of_decide_eq_true predicate
  exact extractor_replay_record_cannot_be_adversary_evidence_candidate
    evidence input record replayActor candidate

#print axioms checked_returned_value_context_is_exact
#print axioms atomic_replay_returned_dag_matches_returned_public_instance
#print axioms verifier_on_atomic_replay_uses_returned_dag_not_frozen_dag
#print axioms successful_atomic_replay_constructs_adaptive_returned_verifier
#print axioms verifier_on_no_pair_replay_uses_returned_parsed_dag
#print axioms successful_no_pair_replay_constructs_returned_verifier
#print axioms extractor_replay_record_cannot_be_adversary_evidence_candidate
#print axioms extractor_replay_record_cannot_be_selected_as_frozen_evidence

end


end AspisK1.V7Tag73ReplayReturnedVerifier
