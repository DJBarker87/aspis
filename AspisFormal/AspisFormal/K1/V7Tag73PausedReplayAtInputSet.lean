import AspisFormal.K1.V7Tag73PausedRecursiveReplay

/-!
# A future-free pause at the first input from a fixed finite target set

This module generalizes the two-input scan used by
`V7Tag73PausedRecursiveReplay` to an arbitrary finite list of SHA inputs.  The
list is fixed before the scan.  A successful scan exposes the literal first
target query and constructs the exact `runPrefix` pause immediately before
that query.  A failed scan certifies that no record in the returned segment
has an input in the target list.

No target is synthesized from a completed proof, and this file makes no
claim about challenge families, source projections, or probabilities.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PausedReplayAtInputSet

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73PausedRecursiveReplay

noncomputable section

/-! ## Executable first occurrence in a fixed finite list -/

/-- Exact chronological split at the first record whose input belongs to the
fixed finite target list. -/
structure InputSetOccurrenceSplit where
  before : List QueryRecord
  chosen : QueryRecord
  after : List QueryRecord

/-- Executable chronological scan for the first query whose input belongs to
`targets`.  Repetitions in `targets` are observationally irrelevant. -/
def firstInputSetOccurrence (targets : List ShaInput) :
    List QueryRecord -> Option InputSetOccurrenceSplit
  | [] => none
  | record :: rest =>
      if record.input ∈ targets then
        some { before := [], chosen := record, after := rest }
      else
        match firstInputSetOccurrence targets rest with
        | none => none
        | some occurrence => some
            { before := record :: occurrence.before
              chosen := occurrence.chosen
              after := occurrence.after }

/-- A successful executable scan gives the exact decomposition, proves every
earlier record is outside the target list, and proves the chosen input is in
the list. -/
theorem first_input_set_occurrence_spec
    (targets : List ShaInput) (records : List QueryRecord)
    (occurrence : InputSetOccurrenceSplit)
    (found : firstInputSetOccurrence targets records = some occurrence) :
    records = occurrence.before ++ occurrence.chosen :: occurrence.after ∧
      (∀ prior ∈ occurrence.before, prior.input ∉ targets) ∧
      occurrence.chosen.input ∈ targets := by
  induction records generalizing occurrence with
  | nil => simp [firstInputSetOccurrence] at found
  | cons record rest ih =>
      by_cases hit : record.input ∈ targets
      · simp only [firstInputSetOccurrence, hit, if_true,
          Option.some.injEq] at found
        cases found
        exact ⟨rfl, by simp, hit⟩
      · cases recursive : firstInputSetOccurrence targets rest with
        | none =>
            simp [firstInputSetOccurrence, hit, recursive] at found
        | some tailOccurrence =>
            simp only [firstInputSetOccurrence, hit, if_false, recursive,
              Option.some.injEq] at found
            cases found
            obtain ⟨decomposition, beforeFresh, chosen⟩ :=
              ih tailOccurrence recursive
            refine ⟨by simp [decomposition], ?_, chosen⟩
            intro prior member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact hit
            · exact beforeFresh prior member

/-- The executable absent branch is equivalent to literal absence of every
target input from every record. -/
theorem first_input_set_occurrence_none_iff
    (targets : List ShaInput) (records : List QueryRecord) :
    firstInputSetOccurrence targets records = none ↔
      ∀ record ∈ records, record.input ∉ targets := by
  induction records with
  | nil => simp [firstInputSetOccurrence]
  | cons record rest ih =>
      by_cases hit : record.input ∈ targets
      · constructor
        · intro impossible
          simp only [firstInputSetOccurrence, hit, if_true] at impossible
          cases impossible
        · intro allRecords
          exact (allRecords record (by simp) hit).elim
      · constructor
        · intro noOccurrence queried member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact hit
          · have tailNone : firstInputSetOccurrence targets rest = none := by
              cases recursive : firstInputSetOccurrence targets rest with
              | none => rfl
              | some occurrence =>
                  simp only [firstInputSetOccurrence, hit, if_false,
                    recursive] at noOccurrence
                  cases noOccurrence
            exact (ih.mp tailNone) queried member
        · intro allRecords
          have tailAll : ∀ queried ∈ rest, queried.input ∉ targets := by
            intro queried member
            exact allRecords queried (by simp [member])
          have tailNone : firstInputSetOccurrence targets rest = none :=
            ih.mpr tailAll
          simp only [firstInputSetOccurrence, hit, if_false, tailNone]

/-! ## Located operational occurrence and exact pause -/

/-- A successful scan over one actual, normally returned machine segment. -/
structure LocatedOperationalInputSet {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (targets : List ShaInput) where
  occurrence : InputSetOccurrenceSplit
  found : firstInputSetOccurrence targets segment.records = some occurrence

/-- Replay of exactly the records preceding the selected target query. -/
def locatedInputSetReplayPrefix {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    (location : LocatedOperationalInputSet segment targets) : PrefixRun Result :=
  runPrefix
    (recordedPrefixController segment.entryOracle.history.length
      location.occurrence.before)
    segment.limits segment.actor location.occurrence.before.length
    segment.entryOracle segment.entryProgram

/-- Operational pause immediately before the first query in the target list.
The residual and pending continuation come from replaying the actual returned
run, not from a caller-supplied restore operation. -/
structure PausedReplayAtInputSet {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    (location : LocatedOperationalInputSet segment targets) where
  residualProgram : OracleMachine Result
  pendingInput : ShaInput
  pendingContinuation : ShaOutput -> OracleMachine Result
  pauseExact : (locatedInputSetReplayPrefix location).halt =
    .paused residualProgram
  residualIsQuery : residualProgram =
    .query pendingInput pendingContinuation
  pendingIsChosen : pendingInput = location.occurrence.chosen.input
  traceExact : queryAnswerTrace
      (historySince segment.entryOracle
        (locatedInputSetReplayPrefix location).oracle) =
    queryAnswerTrace location.occurrence.before

/-- A normal returned run and the successful executable set scan construct
the exact pause immediately before the selected query. -/
theorem paused_replay_at_input_set_exists {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    (location : LocatedOperationalInputSet segment targets) :
    Nonempty (PausedReplayAtInputSet location) := by
  have occurrenceSpec := first_input_set_occurrence_spec targets
    segment.records location.occurrence location.found
  have returnedRun :
      (runMachine segment.controller segment.limits segment.actor segment.fuel
        segment.entryOracle segment.entryProgram).halt =
          .returned segment.returnedValue := by
    rw [← segment.exactRun]
    exact segment.normallyReturned
  have decomposition :
      historySince segment.entryOracle
          (runMachine segment.controller segment.limits segment.actor
            segment.fuel segment.entryOracle segment.entryProgram).oracle =
        location.occurrence.before ++
          location.occurrence.chosen :: location.occurrence.after := by
    rw [← segment.exactRun]
    rw [← OperationalReturnedSegment.records]
    exact occurrenceSpec.1
  let pairOccurrence : PairOccurrenceSplit :=
    { before := location.occurrence.before
      chosen := location.occurrence.chosen
      after := location.occurrence.after }
  obtain ⟨residual, pendingInput, pendingContinuation, paused, residualQuery,
      pendingChosen, trace⟩ :=
    returned_run_first_occurrence_replays_to_exact_pause segment.controller
      segment.limits segment.actor segment.fuel segment.entryOracle
      segment.entryProgram segment.returnedValue pairOccurrence returnedRun
      decomposition
  exact Nonempty.intro
    { residualProgram := residual
      pendingInput := pendingInput
      pendingContinuation := pendingContinuation
      pauseExact := by simpa [locatedInputSetReplayPrefix] using paused
      residualIsQuery := residualQuery
      pendingIsChosen := pendingChosen
      traceExact := by simpa [locatedInputSetReplayPrefix] using trace }

/-- Canonical choice of the operational pause proved above. -/
noncomputable def pauseReplayAtInputSet {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    (location : LocatedOperationalInputSet segment targets) :
    PausedReplayAtInputSet location :=
  Classical.choice (paused_replay_at_input_set_exists location)

/-- The pending residual query is one of the fixed targets, derived from the
scan specification rather than stored as a field. -/
theorem PausedReplayAtInputSet.pending_input_mem_targets {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    {location : LocatedOperationalInputSet segment targets}
    (paused : PausedReplayAtInputSet location) :
    paused.pendingInput ∈ targets := by
  have spec := first_input_set_occurrence_spec targets segment.records
    location.occurrence location.found
  rw [paused.pendingIsChosen]
  exact spec.2.2

/-- The residual carries the same-start provenance induced by this actual
prefix pause. -/
theorem PausedReplayAtInputSet.programProvenance {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    {location : LocatedOperationalInputSet segment targets}
    (paused : PausedReplayAtInputSet location) :
    SameStartProgramProvenance start paused.residualProgram :=
  SameStartProgramProvenance.paused segment.programProvenance
    (recordedPrefixController segment.entryOracle.history.length
      location.occurrence.before)
    segment.limits segment.actor location.occurrence.before.length
    segment.entryOracle
    (by simpa [locatedInputSetReplayPrefix] using paused.pauseExact)

/-- The set-indexed pause retains the literal ancestor replay parameters and
the same-start provenance of its residual program. -/
theorem paused_input_set_retains_exact_ancestor_program_and_controller
    {Result : Type*} {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    {location : LocatedOperationalInputSet segment targets}
    (paused : PausedReplayAtInputSet location) :
    (locatedInputSetReplayPrefix location =
      runPrefix
        (recordedPrefixController segment.entryOracle.history.length
          location.occurrence.before)
        segment.limits segment.actor location.occurrence.before.length
        segment.entryOracle segment.entryProgram) ∧
      SameStartProgramProvenance start paused.residualProgram := by
  exact And.intro rfl paused.programProvenance

/-- Replaying the literal prefix before the first target preserves the whole
ancestor oracle history as an exact prefix. -/
theorem paused_input_set_prefix_history_is_cumulative
    {Result : Type*} {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    (location : LocatedOperationalInputSet segment targets) :
    segment.entryOracle.history <+:
      (locatedInputSetReplayPrefix location).oracle.history := by
  unfold locatedInputSetReplayPrefix
  exact prefix_run_history_is_preserved
    (recordedPrefixController segment.entryOracle.history.length
      location.occurrence.before)
    segment.limits segment.actor location.occurrence.before.length
    segment.entryOracle segment.entryProgram

/-- Resuming an exact set-indexed pause with the original controller and the
unused fuel returns the literal result of the original production segment.
This is a source equality obtained from machine execution, not a replay
assumption stored in the pause. -/
theorem paused_input_set_resume_returns_actual
    {Result : Type*} {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    {location : LocatedOperationalInputSet segment targets}
    (paused : PausedReplayAtInputSet location) :
    (runMachine segment.controller segment.limits segment.actor
      (segment.fuel - location.occurrence.before.length)
      (locatedInputSetReplayPrefix location).oracle
      paused.residualProgram).halt = .returned segment.returnedValue := by
  have occurrenceSpec := first_input_set_occurrence_spec targets
    segment.records location.occurrence location.found
  have returnedRun :
      (runMachine segment.controller segment.limits segment.actor segment.fuel
        segment.entryOracle segment.entryProgram).halt =
          .returned segment.returnedValue := by
    rw [← segment.exactRun]
    exact segment.normallyReturned
  have decomposition :
      historySince segment.entryOracle
          (runMachine segment.controller segment.limits segment.actor
            segment.fuel segment.entryOracle segment.entryProgram).oracle =
        location.occurrence.before ++
          location.occurrence.chosen :: location.occurrence.after := by
    rw [← segment.exactRun]
    rw [← OperationalReturnedSegment.records]
    exact occurrenceSpec.1
  let occurrence : PairOccurrenceSplit :=
    { before := location.occurrence.before
      chosen := location.occurrence.chosen
      after := location.occurrence.after }
  obtain ⟨pendingContinuation, exactPause, _trace, resumes⟩ :=
    returned_run_first_occurrence_replays_to_exact_pause_and_resume
      segment.controller segment.limits segment.actor segment.fuel
      segment.entryOracle segment.entryProgram segment.returnedValue occurrence
      returnedRun decomposition
  have residualExact :
      paused.residualProgram =
        .query location.occurrence.chosen.input pendingContinuation := by
    have haltExact :
        PrefixHalt.paused paused.residualProgram =
          .paused (.query location.occurrence.chosen.input
            pendingContinuation) := by
      rw [← paused.pauseExact]
      simpa [locatedInputSetReplayPrefix, occurrence] using exactPause
    exact PrefixHalt.paused.inj haltExact
  rw [residualExact]
  simpa [locatedInputSetReplayPrefix, occurrence] using resumes

/-! ## Total executable occurrence/absence classification -/

/-- The result of the executable scan over an operational segment.  The
absence constructor retains the literal equality computed by the scan. -/
inductive OperationalInputSetSearch {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (targets : List ShaInput) where
  | located (location : LocatedOperationalInputSet segment targets)
  | absent (notFound : firstInputSetOccurrence targets segment.records = none)

/-- Execute the occurrence/absence split for one returned segment. -/
def searchOperationalInputSet {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (targets : List ShaInput) : OperationalInputSetSearch segment targets := by
  cases found : firstInputSetOccurrence targets segment.records with
  | none => exact .absent found
  | some occurrence => exact .located { occurrence := occurrence, found := found }

/-- An executable absent result certifies every actual record input is outside
the entire target list. -/
theorem operational_input_set_absent_records_are_not_targets {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    (notFound : firstInputSetOccurrence targets segment.records = none) :
    ∀ record ∈ segment.records, record.input ∉ targets :=
  (first_input_set_occurrence_none_iff targets segment.records).mp notFound

/-- The executable classifier is complete: it either yields a real exact
pause, or certifies literal absence of all target inputs. -/
theorem operational_input_set_pause_or_absent {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (targets : List ShaInput) :
    (∃ location : LocatedOperationalInputSet segment targets,
      Nonempty (PausedReplayAtInputSet location)) ∨
      (∀ record ∈ segment.records, record.input ∉ targets) := by
  cases search : searchOperationalInputSet segment targets with
  | located location =>
      exact Or.inl ⟨location, paused_replay_at_input_set_exists location⟩
  | absent notFound =>
      exact Or.inr
        (operational_input_set_absent_records_are_not_targets notFound)

/-! ## Executable frozen replay states -/

/-- Minimal machine state retained after a real target pause.  It contains
neither the completed segment nor its returned result. -/
structure FrozenTargetPause (Result : Type*) where
  startProgram : OracleMachine Result
  prefixOracle : OracleState
  residualProgram : OracleMachine Result
  pendingInput : ShaInput
  pendingContinuation : ShaOutput → OracleMachine Result
  residualIsQuery : residualProgram =
    .query pendingInput pendingContinuation
  controller : AdaptiveController
  limits : OracleLimits
  actor : QueryActor
  remainingFuel : Nat
  provenance : SameStartProgramProvenance startProgram residualProgram

/-- Freeze exactly the pre-query machine data produced by an input-set pause.
The completed return value and all post-pause records are intentionally
discarded. -/
def freezePausedInputSet {Result : Type*}
    {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    {location : LocatedOperationalInputSet segment targets}
    (paused : PausedReplayAtInputSet location) : FrozenTargetPause Result where
  startProgram := start
  prefixOracle := (locatedInputSetReplayPrefix location).oracle
  residualProgram := paused.residualProgram
  pendingInput := paused.pendingInput
  pendingContinuation := paused.pendingContinuation
  residualIsQuery := paused.residualIsQuery
  controller := segment.controller
  limits := segment.limits
  actor := segment.actor
  remainingFuel := segment.fuel - location.occurrence.before.length
  provenance := paused.programProvenance

/-- Literal executable continuation of a frozen target pause.  A production
gamma replay supplies a causal controller; no oracle entry is preprogrammed
by this definition. -/
def runFrozenTargetContinuation {Result : Type*}
    (frozen : FrozenTargetPause Result)
    (controller : AdaptiveController) : MachineRun Result :=
  runMachine controller frozen.limits frozen.actor frozen.remainingFuel
    frozen.prefixOracle frozen.residualProgram

/-- Minimal state for the exhaustive no-target branch.  Rerunning this state
does not inspect a challenge argument. -/
structure FrozenNoTarget (Result : Type*) where
  startProgram : OracleMachine Result
  entryOracle : OracleState
  entryProgram : OracleMachine Result
  controller : AdaptiveController
  limits : OracleLimits
  actor : QueryActor
  fuel : Nat
  provenance : SameStartProgramProvenance startProgram entryProgram

def freezeNoTargetSegment {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start) : FrozenNoTarget Result where
  startProgram := start
  entryOracle := segment.entryOracle
  entryProgram := segment.entryProgram
  controller := segment.controller
  limits := segment.limits
  actor := segment.actor
  fuel := segment.fuel
  provenance := segment.programProvenance

def runFrozenNoTarget {Result : Type*}
    (frozen : FrozenNoTarget Result) : MachineRun Result :=
  runMachine frozen.controller frozen.limits frozen.actor frozen.fuel
    frozen.entryOracle frozen.entryProgram

/-- The no-target frozen state is an exact executable rerun of the actual
segment. -/
theorem run_frozen_no_target_returns_actual {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start) :
    (runFrozenNoTarget (freezeNoTargetSegment segment)).halt =
      .returned segment.returnedValue := by
  change (runMachine segment.controller segment.limits segment.actor
    segment.fuel segment.entryOracle segment.entryProgram).halt =
      .returned segment.returnedValue
  rw [← segment.exactRun]
  exact segment.normallyReturned

/-- The occurrence frozen state also preserves the actual continuation
equality when supplied the original controller. -/
theorem run_frozen_target_with_actual_controller_returns_actual
    {Result : Type*} {start : OracleMachine Result}
    {segment : OperationalReturnedSegment start}
    {targets : List ShaInput}
    {location : LocatedOperationalInputSet segment targets}
    (paused : PausedReplayAtInputSet location) :
    (runFrozenTargetContinuation (freezePausedInputSet paused)
      segment.controller).halt = .returned segment.returnedValue := by
  exact paused_input_set_resume_returns_actual paused

/-- Exhaustive machine-level pre-gamma replay state.  The occurrence branch
starts at a real pending target query; the no-target branch retains the fixed
entry program for a gamma-independent rerun. -/
inductive FrozenPreGammaState (Result : Type*) where
  | occurrence (state : FrozenTargetPause Result)
  | noTarget (state : FrozenNoTarget Result)

/-- Execute the fixed-target scan and freeze the corresponding replay state.
The only noncomputable choice selects the pause already proved to exist for
the literal first occurrence. -/
noncomputable def freezeOperationalPreGammaState {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (targets : List ShaInput) : FrozenPreGammaState Result :=
  match searchOperationalInputSet segment targets with
  | .located location =>
      .occurrence (freezePausedInputSet (pauseReplayAtInputSet location))
  | .absent _ => .noTarget (freezeNoTargetSegment segment)

/-- Complete source specification of the executable frozen state.  In the
occurrence branch the pending query is a literal target and resumption under
the actual controller returns the actual value.  In the absence branch every
actual input misses the target set and the fixed rerun returns the same
value. -/
theorem freeze_operational_pre_gamma_state_source_spec {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (targets : List ShaInput) :
    (∃ location : LocatedOperationalInputSet segment targets,
      freezeOperationalPreGammaState segment targets =
          .occurrence
            (freezePausedInputSet (pauseReplayAtInputSet location)) ∧
        (pauseReplayAtInputSet location).pendingInput ∈ targets ∧
        (runFrozenTargetContinuation
          (freezePausedInputSet (pauseReplayAtInputSet location))
          segment.controller).halt = .returned segment.returnedValue) ∨
    (freezeOperationalPreGammaState segment targets =
        .noTarget (freezeNoTargetSegment segment) ∧
      (∀ record ∈ segment.records, record.input ∉ targets) ∧
      (runFrozenNoTarget (freezeNoTargetSegment segment)).halt =
        .returned segment.returnedValue) := by
  cases search : searchOperationalInputSet segment targets with
  | located location =>
      left
      refine ⟨location, ?_, ?_, ?_⟩
      · simp [freezeOperationalPreGammaState, search]
      · exact (pauseReplayAtInputSet location).pending_input_mem_targets
      · exact run_frozen_target_with_actual_controller_returns_actual
          (pauseReplayAtInputSet location)
  | absent notFound =>
      right
      refine ⟨?_, ?_, run_frozen_no_target_returns_actual segment⟩
      · simp [freezeOperationalPreGammaState, search]
      · exact operational_input_set_absent_records_are_not_targets notFound

/-- The exhaustive input-set scan constructs either a genuine frozen pause
or a literal absence certificate paired with the fixed no-target rerun state.
-/
theorem freeze_input_set_pause_or_absent {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (targets : List ShaInput) :
    (∃ location : LocatedOperationalInputSet segment targets,
      ∃ paused : PausedReplayAtInputSet location,
        freezePausedInputSet paused =
          FrozenTargetPause.mk start
            (locatedInputSetReplayPrefix location).oracle
            paused.residualProgram paused.pendingInput
            paused.pendingContinuation paused.residualIsQuery
            segment.controller segment.limits segment.actor
            (segment.fuel - location.occurrence.before.length)
            paused.programProvenance) ∨
      ((∀ record ∈ segment.records, record.input ∉ targets) ∧
        (runFrozenNoTarget (freezeNoTargetSegment segment)).halt =
          .returned segment.returnedValue) := by
  cases operational_input_set_pause_or_absent segment targets with
  | inl found =>
      obtain ⟨location, nonemptyPaused⟩ := found
      let paused := Classical.choice nonemptyPaused
      exact Or.inl ⟨location, paused, rfl⟩
  | inr absent =>
      exact Or.inr ⟨absent, run_frozen_no_target_returns_actual segment⟩

#print axioms first_input_set_occurrence_spec
#print axioms first_input_set_occurrence_none_iff
#print axioms paused_replay_at_input_set_exists
#print axioms PausedReplayAtInputSet.pending_input_mem_targets
#print axioms PausedReplayAtInputSet.programProvenance
#print axioms paused_input_set_retains_exact_ancestor_program_and_controller
#print axioms paused_input_set_prefix_history_is_cumulative
#print axioms paused_input_set_resume_returns_actual
#print axioms operational_input_set_absent_records_are_not_targets
#print axioms operational_input_set_pause_or_absent
#print axioms run_frozen_no_target_returns_actual
#print axioms run_frozen_target_with_actual_controller_returns_actual
#print axioms freeze_operational_pre_gamma_state_source_spec
#print axioms freeze_input_set_pause_or_absent

end

end AspisK1.V7Tag73PausedReplayAtInputSet
