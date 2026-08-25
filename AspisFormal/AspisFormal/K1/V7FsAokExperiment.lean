import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Classical-ROM extraction experiment for V7 Tag 73

This file supplies an operational game skeleton.  In particular:

* oracle access is an explicit, fuel-bounded free program;
* the lazy oracle records every query in order and distinguishes the actor;
* programming conflicts and query/program/runtime budget exhaustion abort;
* a restart capability closes over, but does not reveal, one adversary tape;
* the extractor receives black-box replay access, not a public proof-to-witness
  function; and
* fresh acceptance and valid extraction are separate probabilistic events.

No field below states an extraction inequality or says that accepting proofs
extract.  That implication is the missing compiler argument, treated in
`V7FsAokCompiler`.
-/

set_option autoImplicit false

namespace AspisK1.V7FsAokExperiment

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule

abbrev ShaInput := ByteString
abbrev ShaOutput := Digest256

inductive QueryActor where
  | adversary
  | simulator
  | verifier
  | extractorReplay
  deriving DecidableEq, Repr

inductive TableSource where
  | fresh
  | programmed
  deriving DecidableEq, Repr

inductive AnswerOrigin where
  | fresh
  | programmed
  | cached
  deriving DecidableEq, Repr

structure TableEntry where
  input : ShaInput
  output : ShaOutput
  source : TableSource

structure QueryRecord where
  input : ShaInput
  output : ShaOutput
  actor : QueryActor
  origin : AnswerOrigin

structure ProgrammingRecord where
  input : ShaInput
  output : ShaOutput
  actor : QueryActor

structure OracleState where
  table : List TableEntry
  /-- Complete shared-oracle call history, in call order. -/
  history : List QueryRecord
  /-- Programming is kept separate from calls. -/
  programmingHistory : List ProgrammingRecord
  totalCalls : Nat
  freshCalls : Nat

def emptyOracle : OracleState where
  table := []
  history := []
  programmingHistory := []
  totalCalls := 0
  freshCalls := 0

def lookupEntry (state : OracleState) (input : ShaInput) : Option TableEntry :=
  state.table.find? (fun entry => entry.input = input)

inductive ControllerDecision where
  | answer (output : ShaOutput)
  | refuse

/-- During replay the extractor may choose the next answer after seeing the
ordered history and current query. -/
abbrev AdaptiveController :=
  List QueryRecord → ShaInput → ControllerDecision

structure OracleLimits where
  totalCalls : Nat
  freshCalls : Nat
  programmedPoints : Nat

inductive OracleAbort where
  | totalCallBudget
  | freshCallBudget
  | programmingBudget
  | programmingConflict
  | controllerRefused
  deriving DecidableEq, Repr

def cachedOrigin : TableSource → AnswerOrigin
  | .fresh => .cached
  | .programmed => .programmed

def queryOracle (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state : OracleState) (input : ShaInput) :
    Except OracleAbort (ShaOutput × OracleState) :=
  if state.totalCalls ≥ limits.totalCalls then
    .error .totalCallBudget
  else
    match lookupEntry state input with
    | some entry =>
        let record : QueryRecord :=
          { input, output := entry.output, actor, origin := cachedOrigin entry.source }
        .ok (entry.output,
          { state with
            history := state.history ++ [record]
            totalCalls := state.totalCalls + 1 })
    | none =>
        if state.freshCalls ≥ limits.freshCalls then
          .error .freshCallBudget
        else
          match controller state.history input with
          | .refuse => .error .controllerRefused
          | .answer output =>
              let entry : TableEntry := { input, output, source := .fresh }
              let record : QueryRecord := { input, output, actor, origin := .fresh }
              .ok (output,
                { table := state.table ++ [entry]
                  history := state.history ++ [record]
                  programmingHistory := state.programmingHistory
                  totalCalls := state.totalCalls + 1
                  freshCalls := state.freshCalls + 1 })

structure Programming where
  input : ShaInput
  output : ShaOutput

/-- Canonical programming aborts whenever the point was already defined,
even if the old output happens to equal the requested output. -/
def programOracle (limits : OracleLimits) (actor : QueryActor)
    (state : OracleState) (programming : Programming) :
    Except OracleAbort OracleState :=
  if state.programmingHistory.length ≥ limits.programmedPoints then
    .error .programmingBudget
  else if (lookupEntry state programming.input).isSome then
    .error .programmingConflict
  else
    let entry : TableEntry :=
      { input := programming.input, output := programming.output,
        source := .programmed }
    let record : ProgrammingRecord :=
      { input := programming.input, output := programming.output, actor }
    .ok
      { state with
        table := state.table ++ [entry]
        programmingHistory := state.programmingHistory ++ [record] }

def programMany (limits : OracleLimits) (actor : QueryActor) :
    OracleState → List Programming → Except OracleAbort OracleState
  | state, [] => .ok state
  | state, programming :: rest =>
      match programOracle limits actor state programming with
      | .error reason => .error reason
      | .ok next => programMany limits actor next rest

theorem programming_an_existing_point_aborts
    (limits : OracleLimits) (actor : QueryActor) (state : OracleState)
    (programming : Programming)
    (withinBudget : state.programmingHistory.length < limits.programmedPoints)
    (defined : (lookupEntry state programming.input).isSome = true) :
    programOracle limits actor state programming =
      .error .programmingConflict := by
  simp [programOracle, Nat.not_le.mpr withinBudget, defined]

/-! ## Fuel-bounded oracle programs -/

inductive OracleMachine (Result : Type*) where
  | pure (result : Result)
  | query (input : ShaInput) (next : ShaOutput → OracleMachine Result)
  | abort (reason : OracleAbort)

inductive MachineHalt (Result : Type*) where
  | returned (result : Result)
  | oracleAbort (reason : OracleAbort)
  | outOfFuel

structure MachineRun (Result : Type*) where
  halt : MachineHalt Result
  oracle : OracleState
  steps : Nat

def runMachine {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) : Nat → OracleState → OracleMachine Result →
      MachineRun Result
  | _, state, .pure result => { halt := .returned result, oracle := state, steps := 0 }
  | _, state, .abort reason => { halt := .oracleAbort reason, oracle := state, steps := 0 }
  | 0, state, .query _ _ => { halt := .outOfFuel, oracle := state, steps := 0 }
  | fuel + 1, state, .query input next =>
      match queryOracle controller limits actor state input with
      | .error reason => { halt := .oracleAbort reason, oracle := state, steps := 1 }
      | .ok (output, nextState) =>
          let result := runMachine controller limits actor fuel nextState (next output)
          { result with steps := result.steps + 1 }

def actorHistory (actor : QueryActor) (state : OracleState) : List QueryRecord :=
  state.history.filter (fun record => record.actor = actor)

/-- Ganesh et al.'s `Q1` is frozen when the adversary halts.  Later verifier
and extractor calls use the same table but are not appended to `Q1`. -/
def freezeAdversaryQ1 (stateAtAdversaryHalt : OracleState) : List QueryRecord :=
  actorHistory .adversary stateAtAdversaryHalt

theorem frozen_q1_contains_only_adversary_calls (state : OracleState)
    (record : QueryRecord) (member : record ∈ freezeAdversaryQ1 state) :
    record.actor = .adversary := by
  exact of_decide_eq_true (List.mem_filter.mp
    (show record ∈ actorHistory .adversary state from member)).2

/-! ## Same-tape restart/state restoration -/

structure StateRestoringAdversary
    (RandomTape Observation Checkpoint Result : Type*) where
  initialCheckpoint : RandomTape → Observation → Checkpoint
  resume : RandomTape → Observation → Checkpoint → OracleMachine Result

/-- The extractor receives this capability.  The closed-over random tape and
checkpoint are not fields of the capability and therefore cannot be read. -/
structure RestartCapability (Result : Type*) where
  replay : AdaptiveController → OracleState → MachineRun Result

def restartFromCheckpoint
    {RandomTape Observation Checkpoint Result : Type*}
    (adversary : StateRestoringAdversary RandomTape Observation Checkpoint Result)
    (fixedTape : RandomTape) (observation : Observation)
    (checkpoint : Checkpoint) (limits : OracleLimits) (fuel : Nat) :
    RestartCapability Result where
  replay controller oracle :=
    runMachine controller limits .extractorReplay fuel oracle
      (adversary.resume fixedTape observation checkpoint)

def restartProgram
    {RandomTape Observation Checkpoint Result : Type*}
    (adversary : StateRestoringAdversary RandomTape Observation Checkpoint Result)
    (fixedTape : RandomTape) (observation : Observation)
    (checkpoint : Checkpoint) : OracleMachine Result :=
  adversary.resume fixedTape observation checkpoint

/-- Same-randomness replay is definitional in the constructed capability; it
is not an adversary-supplied promise. -/
theorem restart_preserves_random_tape
    {RandomTape Observation Checkpoint Result : Type*}
    (adversary : StateRestoringAdversary RandomTape Observation Checkpoint Result)
    (fixedTape : RandomTape) (observation : Observation)
    (checkpoint : Checkpoint) :
    restartProgram adversary fixedTape observation checkpoint =
      adversary.resume fixedTape observation checkpoint := by
  rfl

/-! ## Observed/simulated proofs and freshness -/

structure PublicInstance (Statement : Type*) where
  context : Context
  statement : Statement

structure PublicProof (Statement Proof : Type*) where
  publicInstance : PublicInstance Statement
  proof : Proof

structure SimulatedProof (Statement Proof : Type*) where
  publicInstance : PublicInstance Statement
  proof : Proof
  programming : List Programming

def PairFresh {Statement Proof : Type*}
    (history : List (SimulatedProof Statement Proof))
    (forgery : PublicProof Statement Proof) : Prop :=
  ∀ record ∈ history,
    (record.publicInstance, record.proof) ≠
      (forgery.publicInstance, forgery.proof)

def AttemptFresh {Statement Proof : Type*}
    (history : List (SimulatedProof Statement Proof))
    (forgery : PublicProof Statement Proof) : Prop :=
  ∀ record ∈ history,
    record.publicInstance.context.attemptId ≠
      forgery.publicInstance.context.attemptId

theorem attempt_fresh_implies_pair_fresh
    {Statement Proof : Type*}
    (history : List (SimulatedProof Statement Proof))
    (forgery : PublicProof Statement Proof)
    (fresh : AttemptFresh history forgery) : PairFresh history forgery := by
  intro record member equalPair
  apply fresh record member
  exact congrArg (fun pair => pair.1.context.attemptId) equalPair

/-! Weak unique response is only needed for the observed/simulated-proof
lifting.  Plain BCS state-restoration extraction does not assume it. -/

structure WurCandidate
    (Statement Prefix Challenge Response : Type*) where
  statement : Statement
  transcriptPrefix : Prefix
  challenge : Challenge
  response : Response
  accepts : Bool

def FSWurBreak
    {Statement Prefix Challenge Response : Type*}
    (left right : WurCandidate Statement Prefix Challenge Response) : Prop :=
  left.statement = right.statement ∧
  left.transcriptPrefix = right.transcriptPrefix ∧
  left.challenge = right.challenge ∧
  left.accepts = true ∧
  right.accepts = true ∧
  left.response ≠ right.response

def WeakUniqueResponseOn
    {Statement Prefix Challenge Response : Type*}
    (candidates : Set (WurCandidate Statement Prefix Challenge Response)) : Prop :=
  ∀ left ∈ candidates, ∀ right ∈ candidates,
    ¬ FSWurBreak left right

/-! ## Extractor and resource accounting -/

structure ResourceBudget where
  adversaryOracleCalls : Nat
  simulatorOracleCalls : Nat
  verifierOracleCalls : Nat
  extractorOracleCalls : Nat
  freshOracleAnswers : Nat
  programmedPoints : Nat
  /-- Ganesh et al.'s `q_sim`: the number of prior simulated proofs, not the
  number of SHA calls made while producing them. -/
  simulatedProofs : Nat
  restartCount : Nat
  runtimeSteps : Nat
  /-- Stage-local grinding budgets are intentionally separate. -/
  batchGrindingQueries : Nat
  foldGrindingQueries : Nat
  finalGrindingQueries : Nat
  queryCandidateBranches : Nat

structure ResourceUse where
  adversaryOracleCalls : Nat
  simulatorOracleCalls : Nat
  verifierOracleCalls : Nat
  extractorOracleCalls : Nat
  freshOracleAnswers : Nat
  programmedPoints : Nat
  simulatedProofs : Nat
  restartCount : Nat
  runtimeSteps : Nat
  batchGrindingQueries : Nat
  foldGrindingQueries : Nat
  finalGrindingQueries : Nat
  queryCandidateBranches : Nat

def WithinBudget (use : ResourceUse) (budget : ResourceBudget) : Prop :=
  use.adversaryOracleCalls ≤ budget.adversaryOracleCalls ∧
  use.simulatorOracleCalls ≤ budget.simulatorOracleCalls ∧
  use.verifierOracleCalls ≤ budget.verifierOracleCalls ∧
  use.extractorOracleCalls ≤ budget.extractorOracleCalls ∧
  use.freshOracleAnswers ≤ budget.freshOracleAnswers ∧
  use.programmedPoints ≤ budget.programmedPoints ∧
  use.simulatedProofs ≤ budget.simulatedProofs ∧
  use.restartCount ≤ budget.restartCount ∧
  use.runtimeSteps ≤ budget.runtimeSteps ∧
  use.batchGrindingQueries ≤ budget.batchGrindingQueries ∧
  use.foldGrindingQueries ≤ budget.foldGrindingQueries ∧
  use.finalGrindingQueries ≤ budget.finalGrindingQueries ∧
  use.queryCandidateBranches ≤ budget.queryCandidateBranches

inductive ExtractionAbort where
  | oracle (reason : OracleAbort)
  | runtimeBudget
  | restartBudget
  | protocolAbort
  deriving DecidableEq, Repr

structure ExtractionRun (Witness : Type*) where
  output : Option Witness
  abort : Option ExtractionAbort
  use : ResourceUse

/-- An algorithm only.  There is deliberately no `extract_sound` or
`extractionBound` field. -/
structure ClassicalBlackBoxExtractor
    (Statement Proof Witness ExtractorCoins RestartResult : Type*) where
  /-- The frozen first-run adversary history `Q1`; verifier calls are not
  silently appended. -/
  run : ExtractorCoins → RestartCapability RestartResult →
    List QueryRecord → List (SimulatedProof Statement Proof) →
      PublicProof Statement Proof → ExtractionRun Witness

structure FirstRun (RandomTape Statement Proof : Type*) where
  /-- An opaque identity token for the tape fixed by the experiment. -/
  tapeIdentity : RandomTape
  forgery : Option (PublicProof Statement Proof)
  stateAtAdversaryHalt : OracleState

def FirstRun.q1 {RandomTape Statement Proof : Type*}
    (run : FirstRun RandomTape Statement Proof) : List QueryRecord :=
  freezeAdversaryQ1 run.stateAtAdversaryHalt

structure ExperimentOutcome
    (RandomTape Statement Proof Witness : Type*) where
  simulations : List (SimulatedProof Statement Proof)
  programmingAbort : Option OracleAbort
  firstRun : FirstRun RandomTape Statement Proof
  verifierAccepted : Bool
  extraction : ExtractionRun Witness
  use : ResourceUse
  /-- Raw event used by the Ganesh FS-WUR reduction. -/
  weakUniqueResponseBad : Bool
  /-- Raw exact-transcript coupling failure, including bounded samplers and
  the first-cap-203 branch scan. -/
  transcriptCouplingAbort : Bool

/-- One finite master law.  It determines first-run, simulator, verifier and
extractor coins, but acceptance and extraction remain different events. -/
structure ObservedProofExperiment
    (Sample RandomTape Statement Proof Witness : Type*)
    [Fintype Sample] [MeasurableSpace Sample] where
  law : PMF Sample
  outcome : Sample → ExperimentOutcome RandomTape Statement Proof Witness
  relation : PublicInstance Statement → Witness → Prop
  budget : ResourceBudget

def FreshAcceptanceEvent
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    Set Sample :=
  {sample | ∃ forgery,
    (experiment.outcome sample).firstRun.forgery = some forgery ∧
    PairFresh (experiment.outcome sample).simulations forgery ∧
    (experiment.outcome sample).verifierAccepted = true}

def ValidExtractionEvent
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    Set Sample :=
  {sample | ∃ forgery witness,
    (experiment.outcome sample).firstRun.forgery = some forgery ∧
    (experiment.outcome sample).extraction.output = some witness ∧
    experiment.relation forgery.publicInstance witness}

def ProgrammingAbortEvent
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    Set Sample :=
  {sample | (experiment.outcome sample).programmingAbort.isSome}

def ResourceAbortEvent
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    Set Sample :=
  {sample | ¬ WithinBudget (experiment.outcome sample).use experiment.budget}

noncomputable def ObservedProofExperiment.probability
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (event : Set Sample) : Real :=
  experiment.law.toMeasure.real event

noncomputable def freshAcceptanceProbability
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) : Real :=
  experiment.probability (FreshAcceptanceEvent experiment)

noncomputable def validExtractionProbability
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) : Real :=
  experiment.probability (ValidExtractionEvent experiment)

/-- Expected-cost accounting remains separate from a hard fuel cap. -/
noncomputable def expectedNatCost {Sample : Type*} (law : PMF Sample)
    (cost : Sample → Nat) : ENNReal := by
  letI : MeasurableSpace Sample := ⊤
  exact ∫⁻ sample, (cost sample : ENNReal) ∂law.toMeasure

noncomputable def outerEventProbability {Sample : Type*} (law : PMF Sample)
    (event : Set Sample) : ENNReal :=
  law.toOuterMeasure event

/-- Markov's inequality turns an expected extractor-runtime proof into an
explicit timeout event at the selected hard cutoff. -/
theorem timeout_probability_le_expected_div {Sample : Type*}
    (law : PMF Sample) (cost : Sample → Nat) (cutoff : Nat)
    (cutoffNonzero : cutoff ≠ 0) :
    outerEventProbability law {sample | cutoff ≤ cost sample} ≤
      expectedNatCost law cost / (cutoff : ENNReal) := by
  letI : MeasurableSpace Sample := ⊤
  rw [outerEventProbability, ← PMF.toMeasure_apply_eq_toOuterMeasure_apply]
  · simpa [expectedNatCost] using
      (MeasureTheory.meas_ge_le_lintegral_div
        (μ := law.toMeasure) (f := fun sample => (cost sample : ENNReal))
        measurable_from_top.aemeasurable
        (by exact_mod_cast cutoffNonzero) (ENNReal.natCast_ne_top cutoff))
  · trivial

theorem acceptance_and_extraction_are_distinct_events
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    freshAcceptanceProbability experiment =
        experiment.probability (FreshAcceptanceEvent experiment) ∧
    validExtractionProbability experiment =
        experiment.probability (ValidExtractionEvent experiment) := by
  exact ⟨rfl, rfl⟩

#print axioms programming_an_existing_point_aborts
#print axioms frozen_q1_contains_only_adversary_calls
#print axioms restart_preserves_random_tape
#print axioms attempt_fresh_implies_pair_fresh
#print axioms acceptance_and_extraction_are_distinct_events
#print axioms timeout_probability_le_expected_div

end AspisK1.V7FsAokExperiment
