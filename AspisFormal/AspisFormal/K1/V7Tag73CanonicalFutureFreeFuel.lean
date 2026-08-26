import AspisFormal.K1.V7Tag73CheckedPathActualRunAlignment

/-!
# A canonical protocol cap for complete future-free Tag-73 paths

`CompleteCheckedFutureFreePath` intentionally admits harmless post-halt fuel
padding, so it has no representation-wide upper bound.  This module instead
constructs the particular path obtained from the strict checked refinement and
proves that its unpadded driver fuel is at most 1442 microsteps.

The accounting is protocol-local and keeps unlike resources separate:

* 6 fixed-prefix verifier actions;
* at most 14 C1/lambda/chi/C2 microsteps;
* at most 12 microsteps per supported linear slot;
* at most 641 q16 microsteps, preserving 64 separate cloned candidates and
  each candidate's eight-block cap; and
* one terminal marker step.

This is not a SHA-query cap: paired squeezes issue two queries, while prover
submissions, restores, checkpoints and the terminal marker may issue none.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CanonicalFutureFreeFuel

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73CheckedRefinementFutureFreePath
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73CheckedPathActualRunAlignment

noncomputable section

/-! ## Protocol-local component caps -/

def tag73CanonicalDriverFuelCap : Nat := 1442

theorem sampler_block_cap_le_twelve (id : ChallengeId) :
    samplerBlockCap (samplerMode id) ≤ 12 := by
  cases id <;> simp [samplerMode, samplerBlockCap]

theorem fixed_tape_linear_fuel_le_twelve
    (tape : DeployedFixedTape) (slot : FutureFreeSlot) :
    fixedTapeLinearFuel tape slot ≤ 12 := by
  cases slot with
  | fixed action => simp [fixedTapeLinearFuel]
  | challenge id =>
      exact (tape.messages.challengeUse id).withinDeployedCap.trans
        (sampler_block_cap_le_twelve id)
  | payload site => simp [fixedTapeLinearFuel]
  | work stage => simp [fixedTapeLinearFuel]
  | beginQ16 => simp [fixedTapeLinearFuel]

theorem fixed_tape_linear_fuels_le_twelve_mul_length
    (tape : DeployedFixedTape) : ∀ slots,
    fixedTapeLinearFuels tape slots ≤ 12 * slots.length := by
  intro slots
  induction slots with
  | nil => simp [fixedTapeLinearFuels]
  | cons slot rest ih =>
      rw [fixed_tape_linear_fuels_cons]
      have head := fixed_tape_linear_fuel_le_twelve tape slot
      simp only [List.length_cons]
      omega

theorem candidate_outcome_blocks_used_le_eight (outcome : CandidateOutcome) :
    outcome.blocksUsed ≤ 8 := by
  cases outcome with
  | samplerAbort => simp [CandidateOutcome.blocksUsed]
  | schedule schedule => exact schedule.withinSixtyFourDraws

theorem discarded_q16_fuel_le_ten_mul_length : ∀ specs,
    discardedQ16Fuel specs ≤ 10 * specs.length := by
  intro specs
  induction specs with
  | nil => simp [discardedQ16Fuel]
  | cons spec rest ih =>
      have blockCap := candidate_outcome_blocks_used_le_eight spec.outcome
      simp only [discardedQ16Fuel, List.length_cons]
      omega

theorem accepting_q16_driver_fuel_le_641 (tape : DeployedFixedTape) :
    2 + discardedQ16Fuel (q16TapeOfSearch tape.search).earlier +
        (1 + (q16TapeOfSearch tape.search).selected.outcome.blocksUsed) ≤
      641 := by
  change 2 + discardedQ16Fuel (earlierSpecs tape.search) +
      (1 + tape.search.selectedSchedule.blocksUsed) ≤ 641
  have earlierCap := discarded_q16_fuel_le_ten_mul_length
    (earlierSpecs tape.search)
  have earlierLength : (earlierSpecs tape.search).length =
      tape.search.selectedCounter.val := by
    simp [earlierSpecs]
  rw [earlierLength] at earlierCap
  have counterCap := tape.search.selectedCounter.isLt
  have selectedCap := tape.search.selectedSchedule.withinSixtyFourDraws
  omega

theorem before_q16_slot_count : beforeQ16Slots.length = 53 := by
  decide

theorem after_q16_preterminal_slot_count :
    afterQ16PreterminalSlots.length = 12 := by
  decide

/-- Exact arithmetic aggregation used by the canonical constructor. -/
theorem complete_component_fuel_le_canonical_cap
    (tape : DeployedFixedTape)
    (adaptiveSteps beforeSteps q16Steps afterSteps : Nat)
    (adaptiveFuel : adaptiveSteps = 6 +
      (tape.messages.challengeUse .lambda).blocksUsed +
      (tape.messages.challengeUse .chi).blocksUsed)
    (beforeFuel : beforeSteps = fixedTapeLinearFuels tape beforeQ16Slots)
    (q16Fuel : q16Steps = 2 + discardedQ16Fuel
        (q16TapeOfSearch tape.search).earlier +
      (1 + (q16TapeOfSearch tape.search).selected.outcome.blocksUsed))
    (afterFuel : afterSteps =
      fixedTapeLinearFuels tape afterQ16PreterminalSlots) :
    ((((6 + adaptiveSteps) + beforeSteps) + q16Steps) + afterSteps) + 1 ≤
      tag73CanonicalDriverFuelCap := by
  have lambdaCap :=
    (tape.messages.challengeUse ChallengeId.lambda).withinDeployedCap
  have chiCap :=
    (tape.messages.challengeUse ChallengeId.chi).withinDeployedCap
  have beforeCap := fixed_tape_linear_fuels_le_twelve_mul_length tape
    beforeQ16Slots
  have afterCap := fixed_tape_linear_fuels_le_twelve_mul_length tape
    afterQ16PreterminalSlots
  have q16Cap := accepting_q16_driver_fuel_le_641 tape
  simp only [samplerMode, samplerBlockCap] at lambdaCap chiCap
  rw [before_q16_slot_count] at beforeCap
  rw [after_q16_preterminal_slot_count] at afterCap
  unfold tag73CanonicalDriverFuelCap
  omega

/-! ## Canonical checked paths and actual-run alignment -/

/-- The exact unpadded construction, now carrying its proved protocol-wide
fuel cap.  The underlying complete path still exposes the external semantic,
authentication, and terminal obligations without asserting them. -/
structure CanonicalCappedCheckedFutureFreePath
    (table : FixedOracleTable) (tape : DeployedFixedTape) where
  construction : CanonicalCheckedFutureFreeConstruction table tape
  fuelWithinProtocolCap :
    construction.complete.fuel ≤ tag73CanonicalDriverFuelCap

theorem canonical_construction_fuel_le_protocol_cap
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (construction : CanonicalCheckedFutureFreeConstruction table tape) :
    construction.complete.fuel ≤ tag73CanonicalDriverFuelCap := by
  rw [construction.completeFuel]
  exact complete_component_fuel_le_canonical_cap tape
    construction.adaptiveSteps construction.beforeQ16Steps
    construction.q16Steps construction.afterQ16Steps
    construction.adaptiveFuel construction.beforeQ16Fuel
    construction.q16Fuel construction.afterQ16Fuel

/-- Work-erased checked refinement constructs the canonical, unpadded path;
the cap is derived from its exact schedule decomposition. -/
theorem checked_work_erased_refinement_constructs_canonical_capped_path
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : checkedRefineWorkErased table exactDeterministicDecoders tape =
      some rawTrace) :
    Nonempty (CanonicalCappedCheckedFutureFreePath table tape) := by
  obtain ⟨construction⟩ :=
    checked_work_erased_refinement_constructs_canonical_future_free_path
      table tape rawTrace run
  exact ⟨
    { construction := construction
      fuelWithinProtocolCap :=
        canonical_construction_fuel_le_protocol_cap table tape construction }⟩

/-- Strict deployed refinement supplies the selected-work/probe provenance;
the legal state-restoration path itself uses only the monotone work-erased
verifier. -/
theorem strict_checked_refinement_constructs_canonical_capped_path
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : checkedRefine table exactDeterministicDecoders tape =
      some rawTrace) :
    Nonempty (CanonicalCappedCheckedFutureFreePath table tape) := by
  exact checked_work_erased_refinement_constructs_canonical_capped_path
    table tape rawTrace
      (checked_refinement_success_survives_work_erasure table
        exactDeterministicDecoders tape rawTrace run)

/-- If an actual raw verifier is provisioned with at least the protocol cap,
the strict checked refinement's canonical path is literally that verifier's
ordered history and final schedule-exhausted state. -/
theorem strict_checked_refinement_aligns_with_cap_covered_actual_run
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (environmentExact : execution.environment =
      fixedTapeFutureFreeEnvironment tape)
    (rawExact : execution.adversaryValue.rawMessages =
      fixedTapeRawMessages tape)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ execution.driverFuel)
    (run : checkedRefine execution.finalTable exactDeterministicDecoders tape =
      some rawTrace) :
    ∃ canonical : CanonicalCappedCheckedFutureFreePath
        execution.finalTable tape,
      CheckedPathActualRunAlignment execution tape
        canonical.construction.complete := by
  obtain ⟨canonical⟩ :=
    strict_checked_refinement_constructs_canonical_capped_path
      execution.finalTable tape rawTrace run
  let path := canonical.construction.complete
  have covered : path.fuel ≤ execution.driverFuel :=
    canonical.fuelWithinProtocolCap.trans driverCoversProtocol
  exact ⟨canonical,
    align_complete_checked_path_with_actual_run execution tape path
      environmentExact rawExact covered⟩

#print axioms fixed_tape_linear_fuels_le_twelve_mul_length
#print axioms accepting_q16_driver_fuel_le_641
#print axioms complete_component_fuel_le_canonical_cap
#print axioms checked_work_erased_refinement_constructs_canonical_capped_path
#print axioms strict_checked_refinement_constructs_canonical_capped_path
#print axioms strict_checked_refinement_aligns_with_cap_covered_actual_run

end


end AspisK1.V7Tag73CanonicalFutureFreeFuel
