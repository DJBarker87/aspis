import AspisFormal.K1.V7Tag73RawSameTapeSource
import AspisFormal.K1.V7Tag73ScheduledReplacementAccounting

/-!
# Raw-result specialization of scheduled strict replacement

This module connects the raw same-hidden-tape prover result to the operational
strict-replacement constructor.  The result type contains only prover-owned
raw messages; no parsed child DAG or future verifier tape is introduced.

The executable operational-history scan selects a concrete ancestor query,
the adaptive scheduler supplies the two programmed coordinates, and a normal
residual return is retained literally.  Interpreting that raw return with the
future-free verifier is the next layer and is intentionally not assumed here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawScheduledStrictReplacement

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73PausedRecursiveReplay
open AspisK1.V7Tag73StrictAncestorReplacementLineage
open AspisK1.V7Tag73ScheduledStrictReplacement
open AspisK1.V7Tag73ScheduledReplacementAccounting

noncomputable section

/-! ## The actually returned raw root -/

/-- A normal return of the concrete raw same-tape source.  This is an outcome
of the operational machine, not an acceptance or extraction premise. -/
structure NormallyReturnedRawExecution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) where
  returnedValue : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  normallyReturned : source.firstExecution.halt = .returned returnedValue

/-- Package the raw first execution as the generic operational segment used by
the ancestor scanner.  Its start program is the literal same-tape closure. -/
def NormallyReturnedRawExecution.toOperationalSegment
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : NormallyReturnedRawExecution source) :
    OperationalReturnedSegment
      (source.capability.start source.observation) where
  entryOracle := source.initialOracle
  entryProgram := source.capability.start source.observation
  programProvenance := .start
  controller := source.controller
  limits := source.oracleLimits
  actor := .adversary
  proverActor := Or.inl rfl
  fuel := source.firstRunFuel
  run := source.firstExecution
  returnedValue := execution.returnedValue
  exactRun := rfl
  normallyReturned := execution.normallyReturned

@[simp] theorem raw_root_segment_start_is_exact_same_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (_execution : NormallyReturnedRawExecution source) :
    source.capability.start source.observation =
      source.blackBox.start source.hiddenTape source.observation := by
  exact raw_source_capability_uses_same_hidden_tape source

def rawRootReplayPath
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : NormallyReturnedRawExecution source) :
    SequentialReplayPath (source.capability.start source.observation)
      execution.toOperationalSegment :=
  .root execution.toOperationalSegment

/-! ## Strengthened executable location -/

/-- The generic scan theorem can be strengthened to retain equality with the
literal scan output.  This avoids choosing an unrelated convenient restore
location from a bare `Nonempty` proposition. -/
theorem strict_replacement_location_for_exact_scan_exists
    {Result : Type*} {start : OracleMachine Result}
    {final : OperationalReturnedSegment start}
    (outputInput advanceInput : ShaInput)
    (path : SequentialReplayPath start final)
    (scanLocation : SegmentedPairOccurrence)
    (found : firstPairInOperationalPath outputInput advanceInput path =
      some scanLocation) :
    ∃ location : StrictReplacementLocation outputInput advanceInput path,
      location.scanLocation = scanLocation := by
  obtain ⟨earlier, selected, later, split, index, selectedFound,
      earlierNone⟩ :=
    first_pair_in_operational_segments_spec outputInput advanceInput
      path.segments scanLocation
      (by simpa [firstPairInOperationalPath] using found)
  let location : StrictReplacementLocation outputInput advanceInput path :=
    { scanLocation := scanLocation
      earlier := earlier
      selected := selected
      later := later
      pathExact := split
      indexExact := index
      selectedLocation :=
        { occurrence := scanLocation.withinSegment
          found := selectedFound }
      occurrenceExact := rfl
      earlierHaveNoPair := earlierNone }
  exact ⟨location, rfl⟩

/-! ## Scheduled raw strict replacement -/

/-- The complete successful root replacement.  `scheduled` contains the two
real programming calls and the actual normally returned raw residual; the
scan equality ties its ancestor location to the executable root-history scan.
-/
structure RawScheduledRootReplacement
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : NormallyReturnedRawExecution source)
    (outputInput advanceInput : ShaInput)
    (configuration : AtomicPairReplayConfiguration) where
  scanLocation : SegmentedPairOccurrence
  scanExact : firstPairInOperationalPath outputInput advanceInput
    (rawRootReplayPath execution) = some scanLocation
  location : StrictReplacementLocation outputInput advanceInput
    (rawRootReplayPath execution)
  locationExact : location.scanLocation = scanLocation
  scheduled : ScheduledStrictReplacementLineage location configuration

/-- Execute the strengthened scan-selected raw root replacement.  All failure
branches are the concrete programming/replay aborts of the underlying
constructor. -/
noncomputable def constructRawScheduledRootReplacement
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : NormallyReturnedRawExecution source)
    (outputInput advanceInput : ShaInput)
    (configuration : AtomicPairReplayConfiguration)
    (scanLocation : SegmentedPairOccurrence)
    (found : firstPairInOperationalPath outputInput advanceInput
      (rawRootReplayPath execution) = some scanLocation) :
    Except ScheduledStrictReplacementFailure
      (RawScheduledRootReplacement execution outputInput advanceInput
        configuration) :=
  let located := Classical.choose
    (strict_replacement_location_for_exact_scan_exists outputInput
      advanceInput (rawRootReplayPath execution) scanLocation found)
  let locatedExact := Classical.choose_spec
    (strict_replacement_location_for_exact_scan_exists outputInput
      advanceInput (rawRootReplayPath execution) scanLocation found)
  match constructScheduledReplacementLineage located configuration with
  | .error reason => .error reason
  | .ok scheduled => .ok
      { scanLocation := scanLocation
        scanExact := found
        location := located
        locationExact := locatedExact
        scheduled := scheduled }

/-- The programmed table contains exactly the two coordinates supplied by
the adaptive uniform scheduler. -/
theorem raw_scheduled_replacement_installs_exact_coordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {execution : NormallyReturnedRawExecution source}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replacement : RawScheduledRootReplacement execution outputInput
      advanceInput configuration) :
    (lookupEntry replacement.scheduled.scheduled.completed.programming.afterBoth
        outputInput).map TableEntry.output = some configuration.forkOutput ∧
      (lookupEntry
        replacement.scheduled.scheduled.completed.programming.afterBoth
        advanceInput).map TableEntry.output = some configuration.forkAdvance :=
  constructed_scheduled_replacement_uses_exact_coordinates
    replacement.location.selectedLocation configuration
      replacement.scheduled.scheduled

/-- The residual value is not parsed or synthesized: it is exactly the value
returned by the real replay machine. -/
theorem raw_scheduled_replacement_return_is_literal_machine_return
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {execution : NormallyReturnedRawExecution source}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replacement : RawScheduledRootReplacement execution outputInput
      advanceInput configuration) :
    replacement.scheduled.scheduled.completed.continuationRun.halt =
      .returned
        replacement.scheduled.scheduled.completed.returnedValue :=
  replacement.scheduled.scheduled.completed.normallyReturned

def RawScheduledRootReplacement.rawResidualMessages
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {execution : NormallyReturnedRawExecution source}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replacement : RawScheduledRootReplacement execution outputInput
      advanceInput configuration) : RawTag73ProverMessages :=
  replacement.scheduled.scheduled.completed.returnedValue.rawMessages

/-- The raw residual retains all public bindings fixed by its parser-side
context check.  This theorem still says nothing about verifier acceptance. -/
theorem raw_scheduled_replacement_preserves_public_bindings
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {execution : NormallyReturnedRawExecution source}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replacement : RawScheduledRootReplacement execution outputInput
      advanceInput configuration) :
    let value := replacement.scheduled.scheduled.completed.returnedValue
    let bindings := FixedBindings.ofContext value.rawMessages.context
    bindings.programId = value.1.publicProof.publicInstance.context.programId ∧
      bindings.releaseBinding =
        value.1.publicProof.publicInstance.context.releaseBinding ∧
      bindings.statementDigest =
        value.1.publicProof.publicInstance.context.statementDigest ∧
      bindings.attemptId = value.1.publicProof.publicInstance.context.attemptId ∧
      bindings.proofAccountId =
        value.1.publicProof.publicInstance.context.attemptId := by
  exact checked_raw_return_preserves_public_bindings
    replacement.scheduled.scheduled.completed.returnedValue

/-- The resulting history is a strict replacement, not an append after the
stale root suffix. -/
theorem raw_scheduled_replacement_has_linked_strict_lineage
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {execution : NormallyReturnedRawExecution source}
    {outputInput advanceInput : ShaInput}
    {configuration : AtomicPairReplayConfiguration}
    (replacement : RawScheduledRootReplacement execution outputInput
      advanceInput configuration) :
    replacement.scheduled.lineage.oldSegments =
        replacement.scheduled.lineage.location.earlier ++
          replacement.scheduled.lineage.staleHistorySegments ∧
      replacement.scheduled.lineage.staleHistorySegments ≠ [] ∧
      HistoryLinkedSegments replacement.scheduled.lineage.newHistorySegments :=
  constructed_scheduled_lineage_replaces_nonempty_stale_suffix
    replacement.location configuration replacement.scheduled

#print axioms raw_root_segment_start_is_exact_same_hidden_tape
#print axioms strict_replacement_location_for_exact_scan_exists
#print axioms raw_scheduled_replacement_installs_exact_coordinates
#print axioms raw_scheduled_replacement_return_is_literal_machine_return
#print axioms raw_scheduled_replacement_preserves_public_bindings
#print axioms raw_scheduled_replacement_has_linked_strict_lineage

end

end AspisK1.V7Tag73RawScheduledStrictReplacement
