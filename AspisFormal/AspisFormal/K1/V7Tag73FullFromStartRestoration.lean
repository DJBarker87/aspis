import AspisFormal.K1.V7Tag73RawStrictReplacementSuffix

/-!
# Full-from-start same-tape restoration for raw Tag-73

A strict fork cannot continue from a parent verifier's stale final oracle.  It
must first replay the literal prefix before the selected pair, program the two
scheduled squeeze coordinates there, and then invoke the prover's one fixed
start closure again.  This module implements exactly that low-level operation.

Unlike the older residual-continuation constructor, a successful replay below
is again a homogeneous `OperationalReturnedSegment`: its entry program is the
literal start closure and its provenance is `SameStartProgramProvenance.start`.
Consequently the same executable pair scan can be applied at every finite
depth.  The adaptive controller remains operational data at this layer; the
finite scheduler later constructs it from its projected `.machineFresh`
coordinates.

No restore function, verifier acceptance fact, trace-cover premise, witness,
or extraction conclusion is a field of any object below.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FullFromStartRestoration

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73PausedRecursiveReplay
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73ScheduledStrictReplacement
open AspisK1.V7Tag73SharedOracleVerifierRunner

noncomputable section

/-! ## Literal start replay after prefix-local pair programming -/

inductive FullFromStartReplayFailure where
  | programming (reason : OracleAbort)
  | replayAbort (reason : OracleAbort)
  | timeout
  deriving DecidableEq, Repr

/-- One normally returned replay of the literal same-hidden-tape start closure.
The programming base is definitionally the oracle obtained by replaying the
actual prefix before `location`'s first pair occurrence. -/
structure FullFromStartReturnedReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair parent outputInput advanceInput)
    (configuration : AtomicPairReplayConfiguration) where
  programming : ExactScheduledPairProgramming outputInput advanceInput
    (locatedReplayPrefix location).oracle configuration
  replayRun : MachineRun
    (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
  returnedValue : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  runExact : replayRun = runMachine configuration.postForkController
    configuration.oracleLimits .extractorReplay configuration.replayFuel
    programming.operations.afterBoth
    (source.capability.start source.observation)
  normallyReturned : replayRun.halt = .returned returnedValue

/-- Execute the exact two programming calls and then restart from the one
literal start closure.  All failure branches are returned as data. -/
noncomputable def constructFullFromStartReturnedReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    (location : LocatedOperationalPair parent outputInput advanceInput)
    (configuration : AtomicPairReplayConfiguration) :
    Except FullFromStartReplayFailure
      (FullFromStartReturnedReplay location configuration) :=
  match programmed : executeScheduledPairProgramming outputInput advanceInput
      (locatedReplayPrefix location).oracle configuration with
  | .error reason => .error (.programming reason)
  | .ok programming =>
      let replay := runMachine configuration.postForkController
        configuration.oracleLimits .extractorReplay configuration.replayFuel
        programming.operations.afterBoth
        (source.capability.start source.observation)
      match returned : replay.halt with
      | .oracleAbort reason => .error (.replayAbort reason)
      | .outOfFuel => .error .timeout
      | .returned value => .ok
          { programming := programming
            replayRun := replay
            returnedValue := value
            runExact := rfl
            normallyReturned := returned }

/-- A successful restart is again a complete, homogeneous, scan-capable
segment whose program provenance is the literal fixed start constructor. -/
def FullFromStartReturnedReplay.toOperationalSegment
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay location configuration) :
    OperationalReturnedSegment
      (source.capability.start source.observation) where
  entryOracle := replay.programming.operations.afterBoth
  entryProgram := source.capability.start source.observation
  programProvenance := .start
  controller := configuration.postForkController
  limits := configuration.oracleLimits
  actor := .extractorReplay
  proverActor := Or.inr rfl
  fuel := configuration.replayFuel
  run := replay.replayRun
  returnedValue := replay.returnedValue
  exactRun := replay.runExact
  normallyReturned := replay.normallyReturned

/-- Pair programming changes the table and programming ledger but leaves the
literal replay-prefix query history untouched. -/
theorem full_from_start_entry_history_is_exact_prefix
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay location configuration) :
    replay.toOperationalSegment.entryOracle.history =
      (locatedReplayPrefix location).oracle.history := by
  exact scheduled_pair_programming_preserves_query_history outputInput
    advanceInput (locatedReplayPrefix location).oracle configuration
    replay.programming

/-- The replay invokes exactly the source closure containing the original
hidden tape; no public tape token or caller-supplied resume program is used. -/
theorem full_from_start_replay_uses_exact_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay location configuration) :
    replay.toOperationalSegment.entryProgram =
      source.blackBox.start source.hiddenTape source.observation := by
  exact raw_source_capability_uses_same_hidden_tape source

/-- Both pair coordinates in the restarted branch are the two values supplied
by the surrounding scheduler. -/
theorem full_from_start_replay_installs_exact_coordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay location configuration) :
    (lookupEntry replay.toOperationalSegment.entryOracle outputInput).map
          TableEntry.output = some configuration.forkOutput ∧
      (lookupEntry replay.toOperationalSegment.entryOracle advanceInput).map
          TableEntry.output = some configuration.forkAdvance := by
  exact scheduled_pair_programming_installs_both_coordinates outputInput
    advanceInput (locatedReplayPrefix location).oracle configuration
    replay.programming

/-- The frozen first-run Q1 is not recomputed from a replay branch. -/
def FullFromStartReturnedReplay.frozenQ1
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (_replay : FullFromStartReturnedReplay location configuration) :
    List QueryRecord :=
  freezeAdversaryQ1 source.firstExecution.oracle

@[simp] theorem full_from_start_replay_q1_is_source_q1
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {location : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay location configuration) :
    replay.frozenQ1 = freezeAdversaryQ1 source.firstExecution.oracle := by
  rfl

/-! ## The exact no-pair branch -/

/-- Executable classification of the prover segment for one verifier squeeze.
The `absent` branch carries the literal `none` equation, not a promise that a
convenient checkpoint exists. -/
inductive OperationalPairSite {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput) : Type where
  | occurs (location : LocatedOperationalPair segment outputInput advanceInput)
  | absent (noneExact : firstEitherInputOccurrence outputInput advanceInput
      segment.records = none)

def locateOperationalPair {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput) :
    OperationalPairSite segment outputInput advanceInput := by
  cases found : firstEitherInputOccurrence outputInput advanceInput
      segment.records with
  | none => exact .absent found
  | some occurrence =>
      exact .occurs { occurrence := occurrence, found := found }

/-- In the no-pair branch the programming base is the actual end of the
complete parent prover segment.  This state contains no discarded verifier
suffix: verifier execution is stored separately from prover execution. -/
structure AbsentPairFullFromStartReturnedReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (parent : OperationalReturnedSegment
      (source.capability.start source.observation))
    (outputInput advanceInput : ShaInput)
    (configuration : AtomicPairReplayConfiguration) where
  noneExact : firstEitherInputOccurrence outputInput advanceInput
    parent.records = none
  programming : ExactScheduledPairProgramming outputInput advanceInput
    parent.run.oracle configuration
  replayRun : MachineRun
    (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
  returnedValue : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  runExact : replayRun = runMachine configuration.postForkController
    configuration.oracleLimits .extractorReplay configuration.replayFuel
    programming.operations.afterBoth
    (source.capability.start source.observation)
  normallyReturned : replayRun.halt = .returned returnedValue

noncomputable def constructAbsentPairFullFromStartReturnedReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (parent : OperationalReturnedSegment
      (source.capability.start source.observation))
    (outputInput advanceInput : ShaInput)
    (configuration : AtomicPairReplayConfiguration)
    (noneExact : firstEitherInputOccurrence outputInput advanceInput
      parent.records = none) :
    Except FullFromStartReplayFailure
      (AbsentPairFullFromStartReturnedReplay parent outputInput advanceInput
        configuration) :=
  match programmed : executeScheduledPairProgramming outputInput advanceInput
      parent.run.oracle configuration with
  | .error reason => .error (.programming reason)
  | .ok programming =>
      let replay := runMachine configuration.postForkController
        configuration.oracleLimits .extractorReplay configuration.replayFuel
        programming.operations.afterBoth
        (source.capability.start source.observation)
      match returned : replay.halt with
      | .oracleAbort reason => .error (.replayAbort reason)
      | .outOfFuel => .error .timeout
      | .returned value => .ok
          { noneExact := noneExact
            programming := programming
            replayRun := replay
            returnedValue := value
            runExact := rfl
            normallyReturned := returned }

def AbsentPairFullFromStartReturnedReplay.toOperationalSegment
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : AbsentPairFullFromStartReturnedReplay parent outputInput
      advanceInput configuration) :
    OperationalReturnedSegment
      (source.capability.start source.observation) where
  entryOracle := replay.programming.operations.afterBoth
  entryProgram := source.capability.start source.observation
  programProvenance := .start
  controller := configuration.postForkController
  limits := configuration.oracleLimits
  actor := .extractorReplay
  proverActor := Or.inr rfl
  fuel := configuration.replayFuel
  run := replay.replayRun
  returnedValue := replay.returnedValue
  exactRun := replay.runExact
  normallyReturned := replay.normallyReturned

theorem absent_pair_full_from_start_entry_history_is_parent_final
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : AbsentPairFullFromStartReturnedReplay parent outputInput
      advanceInput configuration) :
    replay.toOperationalSegment.entryOracle.history =
      parent.run.oracle.history := by
  exact scheduled_pair_programming_preserves_query_history outputInput
    advanceInput parent.run.oracle configuration replay.programming

theorem absent_pair_full_from_start_uses_exact_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : AbsentPairFullFromStartReturnedReplay parent outputInput
      advanceInput configuration) :
    replay.toOperationalSegment.entryProgram =
      source.blackBox.start source.hiddenTape source.observation := by
  exact raw_source_capability_uses_same_hidden_tape source

theorem absent_pair_full_from_start_installs_exact_coordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : AbsentPairFullFromStartReturnedReplay parent outputInput
      advanceInput configuration) :
    (lookupEntry replay.toOperationalSegment.entryOracle outputInput).map
          TableEntry.output = some configuration.forkOutput ∧
      (lookupEntry replay.toOperationalSegment.entryOracle advanceInput).map
          TableEntry.output = some configuration.forkAdvance := by
  exact scheduled_pair_programming_installs_both_coordinates outputInput
    advanceInput parent.run.oracle configuration replay.programming

/-- Homogeneous successful result of the executable occurs/absent scan.  Both
constructors restart the same literal start closure and therefore project to
the same operational segment type. -/
inductive FullFromStartReturnedBranch
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (parent : OperationalReturnedSegment
      (source.capability.start source.observation))
    (outputInput advanceInput : ShaInput)
    (configuration : AtomicPairReplayConfiguration) : Type _ where
  | occurs
      (location : LocatedOperationalPair parent outputInput advanceInput)
      (replay : FullFromStartReturnedReplay location configuration)
  | absent
      (replay : AbsentPairFullFromStartReturnedReplay parent outputInput
        advanceInput configuration)

def FullFromStartReturnedBranch.returnedValue
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration} :
    FullFromStartReturnedBranch source parent outputInput advanceInput
      configuration →
      CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  | .occurs _ replay => replay.returnedValue
  | .absent replay => replay.returnedValue

def FullFromStartReturnedBranch.finalOracle
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration} :
    FullFromStartReturnedBranch source parent outputInput advanceInput
      configuration → OracleState
  | .occurs _ replay => replay.replayRun.oracle
  | .absent replay => replay.replayRun.oracle

def FullFromStartReturnedBranch.toOperationalSegment
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration} :
    FullFromStartReturnedBranch source parent outputInput advanceInput
      configuration →
      OperationalReturnedSegment
        (source.capability.start source.observation)
  | .occurs _ replay => replay.toOperationalSegment
  | .absent replay => replay.toOperationalSegment

/-- Total executable scan followed by the appropriate concrete full-start
replay constructor. -/
noncomputable def constructFullFromStartReturnedBranch
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (parent : OperationalReturnedSegment
      (source.capability.start source.observation))
    (outputInput advanceInput : ShaInput)
    (configuration : AtomicPairReplayConfiguration) :
    Except FullFromStartReplayFailure
      (FullFromStartReturnedBranch source parent outputInput advanceInput
        configuration) :=
  match locateOperationalPair parent outputInput advanceInput with
  | .occurs location =>
      match constructFullFromStartReturnedReplay location configuration with
      | .error reason => .error reason
      | .ok replay => .ok (.occurs location replay)
  | .absent noneExact =>
      match constructAbsentPairFullFromStartReturnedReplay parent outputInput
          advanceInput configuration noneExact with
      | .error reason => .error reason
      | .ok replay => .ok (.absent replay)

theorem full_from_start_branch_uses_exact_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (branch : FullFromStartReturnedBranch source parent outputInput
      advanceInput configuration) :
    branch.toOperationalSegment.entryProgram =
      source.blackBox.start source.hiddenTape source.observation := by
  cases branch with
  | occurs location replay =>
      exact full_from_start_replay_uses_exact_hidden_tape replay
  | absent replay =>
      exact absent_pair_full_from_start_uses_exact_hidden_tape replay

/-! ## Generic complete-state restoration at an actual squeeze transition -/

/-- A pair is located by executable search in one concrete future-free state.
This generalizes the root-only location to child states produced recursively. -/
structure LocatedFutureFreeSqueeze
    (state : FutureFreeVerifierState)
    (outputInput advanceInput : ShaInput) where
  transition : FutureFreeTransition
  found : firstMatchingSqueezeTransition outputInput advanceInput state =
    some transition

theorem located_future_free_squeeze_is_transition_member
    {state : FutureFreeVerifierState} {outputInput advanceInput : ShaInput}
    (location : LocatedFutureFreeSqueeze state outputInput advanceInput) :
    location.transition ∈ state.transitions := by
  have found := location.found
  unfold firstMatchingSqueezeTransition at found
  exact List.mem_of_find?_eq_some found

theorem located_future_free_squeeze_inputs_are_exact
    {state : FutureFreeVerifierState} {outputInput advanceInput : ShaInput}
    (location : LocatedFutureFreeSqueeze state outputInput advanceInput) :
    squeezePairInputsOfTransition location.transition =
      some (outputInput, advanceInput) := by
  have found := location.found
  unfold firstMatchingSqueezeTransition at found
  exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1

private theorem squeeze_pair_inputs_some_has_literal_pair_state_generic
    (transition : FutureFreeTransition)
    (outputInput advanceInput : ShaInput)
    (exactInputs : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput)) :
    ∃ owner block reply,
      transition.event = .verifier (.squeezePair owner block) reply ∧
        outputInput = bytes transition.before.core.digest ++ [domSqueeze] ∧
        advanceInput = bytes transition.before.core.digest ++ [domAdvance] := by
  rcases transition with ⟨before, event, after⟩
  cases event with
  | proverC1 root => simp [squeezePairInputsOfTransition] at exactInputs
  | proverC2 lambda chi commitment =>
      simp [squeezePairInputsOfTransition] at exactInputs
  | proverPayload payload =>
      simp [squeezePairInputsOfTransition] at exactInputs
  | proverWorkNonce stage nonce =>
      simp [squeezePairInputsOfTransition] at exactInputs
  | verifier action reply =>
      cases action with
      | squeezePair owner block =>
          simp only [squeezePairInputsOfTransition, Option.some.injEq,
            Prod.mk.injEq] at exactInputs
          exact ⟨owner, block, reply, rfl, exactInputs.1.symm,
            exactInputs.2.symm⟩
      | absorb payload => simp [squeezePairInputsOfTransition] at exactInputs
      | requestRootSalt tree =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | absorbC1 root => simp [squeezePairInputsOfTransition] at exactInputs
      | absorbC2 lambda chi commitment =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | workProbe stage nonce kind =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | checkpoint checkpoint =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | markQ16Base => simp [squeezePairInputsOfTransition] at exactInputs
      | q16CandidateAbsorb counter outcome selected =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16Restore counter =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16Selected counter =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16SamplerAbortReject counter =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16AllNoncompactReject =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | terminal => simp [squeezePairInputsOfTransition] at exactInputs

/-- The two calls are the deployed `S || 0x01` and `S || 0x02` inputs for
one and the same complete preceding verifier snapshot. -/
theorem located_future_free_squeeze_has_literal_pair_state
    {state : FutureFreeVerifierState} {outputInput advanceInput : ShaInput}
    (location : LocatedFutureFreeSqueeze state outputInput advanceInput) :
    ∃ owner block reply,
      location.transition.event =
          .verifier (.squeezePair owner block) reply ∧
        outputInput = bytes location.transition.before.core.digest ++
          [domSqueeze] ∧
        advanceInput = bytes location.transition.before.core.digest ++
          [domAdvance] := by
  exact squeeze_pair_inputs_some_has_literal_pair_state_generic
    location.transition outputInput advanceInput
    (located_future_free_squeeze_inputs_are_exact location)

/-- Concrete restoration retains only the actual complete snapshot immediately
before the selected squeeze; no stale child suffix survives. -/
def restoreLocatedFutureFreeSqueeze
    {state : FutureFreeVerifierState} {outputInput advanceInput : ShaInput}
    (location : LocatedFutureFreeSqueeze state outputInput advanceInput) :
    FutureFreeVerifierState where
  current := location.transition.before
  seen := [location.transition.before]
  transitions := []

theorem located_future_free_squeeze_was_previously_seen
    {bindings : FixedBindings} {state : FutureFreeVerifierState}
    {outputInput advanceInput : ShaInput}
    (invariant : FutureFreeRunInvariant bindings state)
    (location : LocatedFutureFreeSqueeze state outputInput advanceInput) :
    location.transition.before ∈ state.seen := by
  exact (invariant.1.2.2 location.transition
    (located_future_free_squeeze_is_transition_member location)).1

/-- Restoration targets a nonempty complete state previously seen in the
actual parent execution and preserves the one fixed public instance. -/
theorem restored_located_squeeze_is_complete_nonempty_and_fixed
    {bindings : FixedBindings} {state : FutureFreeVerifierState}
    {outputInput advanceInput : ShaInput}
    (invariant : FutureFreeRunInvariant bindings state)
    (location : LocatedFutureFreeSqueeze state outputInput advanceInput) :
    FutureFreeRunInvariant bindings
      (restoreLocatedFutureFreeSqueeze location) := by
  have seen := located_future_free_squeeze_was_previously_seen invariant
    location
  have fixed := invariant.2.2 location.transition.before seen
  constructor
  · simp [FutureFreeHistoryClosed, restoreLocatedFutureFreeSqueeze]
  · simp [FutureFreeBindingsFixed, restoreLocatedFutureFreeSqueeze, fixed]

/-! ## Run the raw replay result from the exact restored verifier state -/

inductive FullFromStartChildFailure where
  | bindingMismatch
  | oracleAbort (reason : OracleAbort)
  | timeout
  deriving DecidableEq, Repr

def fullFromStartChildVerifierRun
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {parentState : FutureFreeVerifierState}
    {outputInput advanceInput : ShaInput}
    {proverLocation : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay proverLocation configuration)
    (verifierLocation : LocatedFutureFreeSqueeze parentState outputInput
      advanceInput)
    (environment : FutureFreeEnvironment)
    (driverFuel verifierFuel : Nat) : MachineRun FutureFreeVerifierState :=
  runMachine configuration.postForkController configuration.oracleLimits
    .verifier verifierFuel replay.replayRun.oracle
    (driveRawFutureFree environment replay.returnedValue.rawMessages driverFuel
      (restoreLocatedFutureFreeSqueeze verifierLocation))

structure ReturnedFullFromStartChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {parentState : FutureFreeVerifierState}
    {outputInput advanceInput : ShaInput}
    {proverLocation : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay proverLocation configuration)
    (verifierLocation : LocatedFutureFreeSqueeze parentState outputInput
      advanceInput)
    (environment : FutureFreeEnvironment)
    (driverFuel verifierFuel : Nat) where
  childBindingExact :
    FixedBindings.ofContext replay.returnedValue.rawMessages.context =
      verifierLocation.transition.before.bindings
  finalState : FutureFreeVerifierState
  normallyReturned :
    (fullFromStartChildVerifierRun replay verifierLocation environment
      driverFuel verifierFuel).halt = .returned finalState

noncomputable def constructReturnedFullFromStartChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {parentState : FutureFreeVerifierState}
    {outputInput advanceInput : ShaInput}
    {proverLocation : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    (replay : FullFromStartReturnedReplay proverLocation configuration)
    (verifierLocation : LocatedFutureFreeSqueeze parentState outputInput
      advanceInput)
    (environment : FutureFreeEnvironment)
    (driverFuel verifierFuel : Nat) :
    Except FullFromStartChildFailure
      (ReturnedFullFromStartChild replay verifierLocation environment
        driverFuel verifierFuel) := by
  classical
  exact if bindingExact :
      FixedBindings.ofContext replay.returnedValue.rawMessages.context =
        verifierLocation.transition.before.bindings then
    match returned : (fullFromStartChildVerifierRun replay verifierLocation
      environment driverFuel verifierFuel).halt with
    | .oracleAbort reason => .error (.oracleAbort reason)
    | .outOfFuel => .error .timeout
    | .returned finalState => .ok
        { childBindingExact := bindingExact
          finalState := finalState
          normallyReturned := returned }
  else
    .error .bindingMismatch

theorem returned_full_from_start_child_has_complete_nonempty_fixed_state
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {parent : OperationalReturnedSegment
      (source.capability.start source.observation)}
    {parentState : FutureFreeVerifierState}
    {outputInput advanceInput : ShaInput}
    {proverLocation : LocatedOperationalPair parent outputInput advanceInput}
    {configuration : AtomicPairReplayConfiguration}
    {replay : FullFromStartReturnedReplay proverLocation configuration}
    {verifierLocation : LocatedFutureFreeSqueeze parentState outputInput
      advanceInput}
    {environment : FutureFreeEnvironment}
    {driverFuel verifierFuel : Nat}
    (parentInvariant : FutureFreeRunInvariant
      verifierLocation.transition.before.bindings parentState)
    (child : ReturnedFullFromStartChild replay verifierLocation environment
      driverFuel verifierFuel) :
    FutureFreeRunInvariant
      (FixedBindings.ofContext replay.returnedValue.rawMessages.context)
      child.finalState := by
  have restoredParent :=
    restored_located_squeeze_is_complete_nonempty_and_fixed parentInvariant
      verifierLocation
  have restoredChild : FutureFreeRunInvariant
      (FixedBindings.ofContext replay.returnedValue.rawMessages.context)
      (restoreLocatedFutureFreeSqueeze verifierLocation) := by
    refine ⟨restoredParent.1, ?_, ?_⟩
    · simpa [restoreLocatedFutureFreeSqueeze] using child.childBindingExact.symm
    · intro snapshot member
      have snapshotEq := restoredParent.2.2 snapshot member
      exact snapshotEq.trans child.childBindingExact.symm
  obtain ⟨pairs, path, _history, _actors, _answers⟩ :=
    run_machine_returned_has_exact_query_path
      configuration.postForkController configuration.oracleLimits .verifier
      verifierFuel replay.replayRun.oracle
      (driveRawFutureFree environment replay.returnedValue.rawMessages
        driverFuel (restoreLocatedFutureFreeSqueeze verifierLocation))
      child.finalState child.normallyReturned
  exact ⟨
    drive_raw_future_free_path_preserves_history_closed environment
      replay.returnedValue.rawMessages driverFuel
      (restoreLocatedFutureFreeSqueeze verifierLocation) pairs child.finalState
      restoredChild.1 path,
    drive_raw_future_free_path_preserves_fixed_bindings
      (FixedBindings.ofContext replay.returnedValue.rawMessages.context)
      environment replay.returnedValue.rawMessages driverFuel
      (restoreLocatedFutureFreeSqueeze verifierLocation) pairs child.finalState
      restoredChild.2 path⟩

#print axioms full_from_start_entry_history_is_exact_prefix
#print axioms full_from_start_replay_uses_exact_hidden_tape
#print axioms full_from_start_replay_installs_exact_coordinates
#print axioms full_from_start_replay_q1_is_source_q1
#print axioms absent_pair_full_from_start_entry_history_is_parent_final
#print axioms absent_pair_full_from_start_uses_exact_hidden_tape
#print axioms absent_pair_full_from_start_installs_exact_coordinates
#print axioms full_from_start_branch_uses_exact_hidden_tape
#print axioms located_future_free_squeeze_is_transition_member
#print axioms located_future_free_squeeze_inputs_are_exact
#print axioms located_future_free_squeeze_has_literal_pair_state
#print axioms located_future_free_squeeze_was_previously_seen
#print axioms restored_located_squeeze_is_complete_nonempty_and_fixed
#print axioms returned_full_from_start_child_has_complete_nonempty_fixed_state

end

end AspisK1.V7Tag73FullFromStartRestoration
