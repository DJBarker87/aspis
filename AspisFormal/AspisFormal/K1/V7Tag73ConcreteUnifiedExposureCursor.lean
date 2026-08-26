import AspisFormal.K1.V7Tag73AtomicForkUniformScheduler
import AspisFormal.K1.V7Tag73ResumeDerivedReplayNode

/-!
# Concrete root-fork cursor and the recursive-dispatch boundary

This module connects the adaptive full-256 scheduler to the replay machinery
that actually exists today.  The existing `RestrictedReplayForest` has one
operational root and independently dispatched depth-one children.  It is not
a recursive adaptive dispatcher.

Accordingly, the positive construction below is exact but deliberately
limited: it exposes the two programmed coins for one concrete root-generated
pair, runs the actual depth-one dispatcher as a pure returned value after the
pair, and proves the strict resource cap contains both adjacent coordinates.
It does not count the already-completed replay hidden inside that dispatcher
result as scheduler-driven fresh queries.

The final sections kernel-check the precise obstruction.  Every existing
`RestrictedReplayNode` has depth at most one; a continuation-local suffix can
miss a pair in an ancestor segment; and `SegmentedRootToNodeHistory` forgets
the entry program needed to resume that segment.  A minimal replay-capable
segment type is defined and constructed for one actual returned continuation.
What remains missing is an operational constructor that accumulates those
segments while producing each next returned proof and future-free verifier
state.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ConcreteUnifiedExposureCursor

set_option maxRecDepth 8192

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73ReplayBranchDispatcher
open AspisK1.V7Tag73RestrictedReplayForest
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73OperationalKnowledgeInput
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## One concrete root-fork plan -/

/-- Concrete data needed to schedule one actual root-generated fork under a
strict resource envelope.  The numerical fields are ordinary resource facts:
they do not contain a cursor, trace cover, probability conclusion, or replay
success premise. -/
structure ConcreteRootForkPlan
    (HiddenTape TapeIdentity Observation Statement Proof Payload : Type*) where
  root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
    Proof Payload
  generated : GeneratedReplayPrefix root.dag
  template : AtomicPairReplayConfiguration
  envelope : StrictTag73ResourceEnvelope
  q1Bound : root.source.origin.firstRun.q1.length ≤ envelope.q1Calls
  restorationSlot : 0 < envelope.restorationCount
  pairCallsFit : 2 ≤ envelope.oracleCallsPerRestoration

def ConcreteRootForkPlan.frozenHistory
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) : List QueryRecord :=
  plan.root.source.origin.firstRun.q1

def ConcreteRootForkPlan.outputInput
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) : ShaInput :=
  generatedPairInput plan.root.execution plan.generated .output

def ConcreteRootForkPlan.advanceInput
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) : ShaInput :=
  generatedPairInput plan.root.execution plan.generated .advance

theorem concrete_root_pair_calls_fit_global_cap
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    plan.frozenHistory.length + 2 ≤
      strictGlobalOracleCallCap plan.envelope := by
  have oneRestoration : 1 ≤ plan.envelope.restorationCount :=
    plan.restorationSlot
  have twoWithinRestorationProduct :
      2 ≤ plan.envelope.restorationCount *
        plan.envelope.oracleCallsPerRestoration := by
    calc
      2 ≤ 1 * plan.envelope.oracleCallsPerRestoration := by
        simpa using plan.pairCallsFit
      _ ≤ plan.envelope.restorationCount *
          plan.envelope.oracleCallsPerRestoration :=
        Nat.mul_le_mul_right plan.envelope.oracleCallsPerRestoration
          oneRestoration
  unfold ConcreteRootForkPlan.frozenHistory strictGlobalOracleCallCap
  calc
    plan.root.source.origin.firstRun.q1.length + 2 ≤
        plan.envelope.q1Calls + 2 :=
      Nat.add_le_add_right plan.q1Bound 2
    _ ≤ plan.envelope.q1Calls + plan.envelope.verifierOracleCalls +
        plan.envelope.restorationCount *
          plan.envelope.oracleCallsPerRestoration := by
      omega

/-- Limits for the inert machine that returns the actual depth-one dispatcher
result.  This machine makes no oracle call. -/
def inertDispatchResultLimits : OracleLimits where
  totalCalls := 0
  freshCalls := 0
  programmedPoints := 0

/-- After both scheduled coins are known, evaluate the existing concrete
depth-one dispatcher and expose its `Except` value through a zero-query pure
machine.  Any replay contained in that value has already been evaluated by
the old dispatcher and is therefore not falsely counted as a scheduler-driven
fresh-answer continuation. -/
noncomputable def concreteRootDispatchResultCursor
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (configuration : AtomicPairReplayConfiguration) :
    UnifiedExposureCursor (strictGlobalOracleCallCap plan.envelope) :=
  .machine inertDispatchResultLimits (by simp [inertDispatchResultLimits])
    .extractorReplay emptyOracle
    (.pure (dispatchRestrictedReplayChild plan.root plan.generated
      configuration)) 0 empty_oracle_history_total_coherent
    (fun _result _state => .halted)

/-- Exact scheduler shell for one actual root-generated pair.  Neither the
history nor the two inputs is caller-invented: all three are computed from the
root and generated replay prefix. -/
noncomputable def concreteRootUnifiedExposureCursor
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    UnifiedExposureCursor (strictGlobalOracleCallCap plan.envelope) :=
  .forkPair plan.frozenHistory
    (concrete_root_pair_calls_fit_global_cap plan)
    plan.outputInput plan.advanceInput plan.template
    (concreteRootDispatchResultCursor plan)

theorem concrete_root_cursor_uses_exact_generated_inputs
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    plan.outputInput =
        generatedPairInput plan.root.execution plan.generated .output ∧
      plan.advanceInput =
        generatedPairInput plan.root.execution plan.generated .advance := by
  exact ⟨rfl, rfl⟩

theorem concrete_root_cursor_first_pair_is_exactly_two_coordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (transitionFuel : Nat) (forkOutput forkAdvance : Digest256) :
    runUnifiedExposureSchedule (transitionFuel + 1) 2
      (concreteRootUnifiedExposureCursor plan)
      (forkOutput, (forkAdvance, PUnit.unit)) =
        [{ frozenHistory := plan.frozenHistory
           outputInput := plan.outputInput
           advanceInput := plan.advanceInput
           template := plan.template
           forkOutput := forkOutput
           forkAdvance := forkAdvance }] := by
  exact run_unified_exposure_schedule_direct_fork_exactly_two transitionFuel
    plan.frozenHistory (concrete_root_pair_calls_fit_global_cap plan)
    plan.outputInput plan.advanceInput plan.template
    (concreteRootDispatchResultCursor plan) forkOutput forkAdvance

theorem concrete_root_cursor_trace_starts_with_adjacent_pair
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload)
    (transitionFuel : Nat) (forkOutput forkAdvance : Digest256) :
    runUnifiedExposureTrace (transitionFuel + 1) 2
      (concreteRootUnifiedExposureCursor plan)
      (forkOutput, (forkAdvance, PUnit.unit)) =
        [.forkOutput plan.frozenHistory plan.outputInput plan.advanceInput
            plan.template forkOutput,
          .forkAdvance
            { frozenHistory := plan.frozenHistory
              outputInput := plan.outputInput
              advanceInput := plan.advanceInput
              template := plan.template
              forkOutput := forkOutput
              forkAdvance := forkAdvance }] := by
  exact run_unified_exposure_trace_direct_fork_is_adjacent_pair transitionFuel
    plan.frozenHistory (concrete_root_pair_calls_fit_global_cap plan)
    plan.outputInput plan.advanceInput plan.template
    (concreteRootDispatchResultCursor plan) forkOutput forkAdvance

theorem concrete_root_strict_cap_cannot_cut_first_pair
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    2 ≤ strictUnifiedFull256ExposureCap plan.envelope := by
  unfold strictUnifiedFull256ExposureCap
  have oneRestoration : 1 ≤ plan.envelope.restorationCount :=
    plan.restorationSlot
  omega

theorem concrete_root_shell_fresh_and_fork_use_within_cap
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (plan : ConcreteRootForkPlan HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    unifiedFull256ExposureUse 0 1 ≤
      strictUnifiedFull256ExposureCap plan.envelope := by
  apply unified_full256_actual_use_le_strict_cap plan.envelope 0 1
  · exact Nat.zero_le _
  · exact plan.restorationSlot

/-! ## Exact depth-one obstruction -/

def restrictedReplayNodeDepth
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload} : RestrictedReplayNode root → Nat
  | .root => 0
  | .child _ => 1

theorem every_existing_restricted_replay_node_has_depth_at_most_one
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : RestrictedReplayNode root) : restrictedReplayNodeDepth node ≤ 1 := by
  cases node <;> simp [restrictedReplayNodeDepth]

def ExistingRestrictedForestHasGrandchild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) : Prop :=
  ∃ node : RestrictedReplayNode root, 2 ≤ restrictedReplayNodeDepth node

theorem existing_restricted_forest_has_no_grandchild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    ¬ ExistingRestrictedForestHasGrandchild root := by
  rintro ⟨node, depthTwo⟩
  have depthOne := every_existing_restricted_replay_node_has_depth_at_most_one
    node
  omega

/-- A current continuation suffix cannot replace a cumulative root-to-node
history: the exact same empty suffix can report no pair while an ancestor
record contains that pair. -/
theorem continuation_suffix_alone_is_not_a_complete_recursive_scan
    (outputInput advanceInput : ShaInput) (ancestor : QueryRecord)
    (hit : ancestor.input = outputInput ∨
      ancestor.input = advanceInput) :
    firstEitherInputOccurrence outputInput advanceInput [] = none ∧
      firstEitherInputOccurrence outputInput advanceInput [ancestor] ≠ none :=
  suffix_only_scan_can_miss_an_ancestor_pair outputInput advanceInput ancestor
    hit

/-! ## The program projection missing from segmented history -/

/-- Minimal operational decoration of one history segment.  It retains the
same-tape entry program and an actual normal-return equation; neither appears
in `ActualProverHistorySegment`. -/
structure ReplayCapableHistorySegment
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload) where
  history : ActualProverHistorySegment
  entryProgram : OracleMachine
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  programProvenance : SameTapeProgramProvenance source entryProgram
  controller : AdaptiveController
  limits : OracleLimits
  fuel : Nat
  run : MachineRun
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof Payload
  exactRun : run = runMachine controller limits .extractorReplay fuel
    history.entryOracle entryProgram
  normallyReturned : run.halt = .returned returnedValue
  finalOracleExact : run.oracle = history.finalOracle

/-- Every actual returned child continuation supplies one replay-capable
segment.  This is the strongest recursive building block present in the
current dispatcher stack. -/
def replayCapableSegmentOfContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (continuation : ResumeDerivedContinuation source) :
    ReplayCapableHistorySegment source :=
  let history : ActualProverHistorySegment :=
    { entryOracle := continuation.entryOracle
      finalOracle := continuation.run.oracle
      historyPrefix := by
        rw [continuation.exactRun]
        exact postfork_run_history_is_preserved continuation.controller
          continuation.limits .extractorReplay continuation.fuel
          continuation.entryOracle continuation.entryProgram
      records := continuation.proverTrace
      recordsExact := rfl
      proverActors := by
        intro record member
        apply Or.inr
        rw [ResumeDerivedContinuation.proverTrace,
          continuation.exactRun] at member
        exact run_machine_history_since_has_actor continuation.controller
          continuation.limits .extractorReplay continuation.fuel
          continuation.entryOracle continuation.entryProgram record member }
  { history := history
    entryProgram := continuation.entryProgram
    programProvenance := continuation.programProvenance
    controller := continuation.controller
    limits := continuation.limits
    fuel := continuation.fuel
    run := continuation.run
    returnedValue := continuation.returnedValue
    exactRun := continuation.exactRun
    normallyReturned := continuation.normallyReturned
    finalOracleExact := rfl }

/-- A replay-capable path is what recursive dispatch actually needs in
addition to the segmented query projection. -/
structure ReplayCapableRootToNodePath
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload) where
  segments : List (ReplayCapableHistorySegment source)
  linked : HistoryLinkedSegments (segments.map
    ReplayCapableHistorySegment.history)

def ReplayCapableRootToNodePath.toSegmentedHistory
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (path : ReplayCapableRootToNodePath source) :
    SegmentedRootToNodeHistory where
  segments := path.segments.map ReplayCapableHistorySegment.history
  linked := path.linked

def singletonReplayCapablePathOfContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (continuation : ResumeDerivedContinuation source) :
    ReplayCapableRootToNodePath source where
  segments := [replayCapableSegmentOfContinuation continuation]
  linked := by simp [HistoryLinkedSegments]

/-! The projection really forgets operational information. -/

def emptyActualProverHistorySegment : ActualProverHistorySegment where
  entryOracle := emptyOracle
  finalOracle := emptyOracle
  historyPrefix := List.prefix_refl []
  records := []
  recordsExact := rfl
  proverActors := by simp

structure BooleanProgramDecoratedSegment where
  history : ActualProverHistorySegment
  entryProgram : OracleMachine Bool

def BooleanProgramDecoratedSegment.forget
    (segment : BooleanProgramDecoratedSegment) : ActualProverHistorySegment :=
  segment.history

def falseProgramDecoration : BooleanProgramDecoratedSegment where
  history := emptyActualProverHistorySegment
  entryProgram := .pure false

def trueProgramDecoration : BooleanProgramDecoratedSegment where
  history := emptyActualProverHistorySegment
  entryProgram := .pure true

theorem segmented_history_projection_forgets_entry_program :
    falseProgramDecoration.forget = trueProgramDecoration.forget ∧
      falseProgramDecoration ≠ trueProgramDecoration := by
  constructor
  · rfl
  · intro equal
    have programsEqual := congrArg BooleanProgramDecoratedSegment.entryProgram
      equal
    simp [falseProgramDecoration, trueProgramDecoration] at programsEqual

/-!
The remaining constructor is now precise: after a child verifier returns, an
operational recursive dispatcher must append a `ReplayCapableHistorySegment`
to a linked `ReplayCapableRootToNodePath`, retain the new future-free verifier
state, and expose the next replay as a machine continuation before running it.
`ActualReturnedChildNode` provides one segment; no existing function builds
the linked arbitrary-depth path or the future-free post-checkpoint prover
tail.  Therefore this file does not claim a complete recursive cursor.
-/

#print axioms concrete_root_pair_calls_fit_global_cap
#print axioms concrete_root_cursor_uses_exact_generated_inputs
#print axioms concrete_root_cursor_first_pair_is_exactly_two_coordinates
#print axioms concrete_root_cursor_trace_starts_with_adjacent_pair
#print axioms concrete_root_strict_cap_cannot_cut_first_pair
#print axioms concrete_root_shell_fresh_and_fork_use_within_cap
#print axioms every_existing_restricted_replay_node_has_depth_at_most_one
#print axioms existing_restricted_forest_has_no_grandchild
#print axioms continuation_suffix_alone_is_not_a_complete_recursive_scan
#print axioms replayCapableSegmentOfContinuation
#print axioms segmented_history_projection_forgets_entry_program

end

end AspisK1.V7Tag73ConcreteUnifiedExposureCursor
