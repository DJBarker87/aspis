import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment
import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkControllerAnchor

/-!
# Exact root-coordinate alignment for the q16 controller

Every lookup used by the accepted evaluator has an adversary-or-verifier
fresh position.  This file identifies the same position in the literal full
scheduler trace and replays its strict prefix through the concrete indexed
final-work/q16 controller.  The reached cursor sees the exact SHA input before
the selected answer is consumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootControllerCoordinateAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Canonical initial state of one exposure-indexed candidate controller. -/
def exactCandidateControllerInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      FinalWorkQ16CandidateMemory :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory := inactiveCandidateMemory }

/-- Any exact final-table lookup is reached at its literal root record by the
same indexed controller compiled into the causal router.  The selected answer
has not yet influenced `reached`. -/
theorem exact_final_lookup_aligns_candidate_controller
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
    (anchor : Nat) (target : ShaInput) (answer : Digest256)
    (found : tableLookup (exactOperationalTable input) target = some answer) :
    ∃ priorRecords laterRecords actor reached,
      (runExactPlainRom transitionFuel configuration sample).trace =
        priorRecords ++
          (.machineFresh actor target answer : UnifiedExposureRecord) ::
            laterRecords ∧
      reached = indexedStateAfterRecords transitionFuel
        (finalWorkQ16CandidateController
          (globalFull256OracleCallCap parameters) transitionFuel anchor)
        priorRecords (exactCandidateControllerInitialState input) ∧
      reached.exposureIndex = priorRecords.length ∧
      unifiedInputBeforeAnswer? transitionFuel reached.cursor = some target := by
  let controller := finalWorkQ16CandidateController
    (globalFull256OracleCallCap parameters) transitionFuel anchor
  let initial := exactCandidateControllerInitialState input
  let rootTape := operationalTapeCoordinates
    (globalFull256OracleCallCap parameters) 1
    (unifiedFull256ExposureCap parameters)
    (exactCompilerOperationalIndexedTape parameters sample.2)
  have traceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase rootTape =
        (runExactPlainRom transitionFuel configuration sample).trace := by
    simpa [rootTape, exactCompilerUnifiedExposureTrace] using
      exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
        transitionFuel configuration sample
  rcases exact_compiler_final_lookup_has_root_position input target answer found
      with ⟨prior, later, position⟩ | ⟨prior, later, position⟩
  · let priorRecords := projectedMachineFreshRecords .adversary prior
    let laterRecords :=
      projectedMachineFreshRecords .adversary later ++
        projectedMachineFreshRecords .verifier
          input.package.root.full.projection.rootPrefixes.verifier.freshQueries ++
        (exactFixedComputedClientTailRun transitionFuel configuration sample
          input.package.root).trace
    have fullDecomposition :
        (runExactPlainRom transitionFuel configuration sample).trace =
          priorRecords ++
            (.machineFresh .adversary target answer : UnifiedExposureRecord) ::
              laterRecords := by
      rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
      unfold exactFixedOperationalStateMapTrace exactFixedRootRecords
        fullProjectedRootRecords priorRecords laterRecords
      rw [position]
      simp only [projected_machine_fresh_records_append,
        projectedMachineFreshRecords, List.cons_append, List.append_assoc]
    let reached := indexedStateAfterRecords transitionFuel controller
      priorRecords initial
    have selectedAligned :
        unifiedRecordAtAnswer transitionFuel reached.cursor answer =
          (.machineFresh .adversary target answer : UnifiedExposureRecord) := by
      exact trace_prefix_aligns_indexed_state transitionFuel controller
        priorRecords laterRecords
        (.machineFresh .adversary target answer) _ initial rootTape
        (traceExact.trans fullDecomposition)
    have inputExact :
        unifiedInputBeforeAnswer? transitionFuel reached.cursor = some target :=
      aligned_machine_record_has_exact_input transitionFuel reached.cursor
        .adversary target answer selectedAligned
    have indexExact : reached.exposureIndex = priorRecords.length := by
      simpa [reached, initial, exactCandidateControllerInitialState] using
        indexed_state_after_records_exposure_index transitionFuel controller
          priorRecords initial
    exact ⟨priorRecords, laterRecords, .adversary, reached,
      fullDecomposition, rfl, indexExact, inputExact⟩
  · let priorRecords :=
      projectedMachineFreshRecords .adversary
          input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
        projectedMachineFreshRecords .verifier prior
    let laterRecords :=
      projectedMachineFreshRecords .verifier later ++
        (exactFixedComputedClientTailRun transitionFuel configuration sample
          input.package.root).trace
    have fullDecomposition :
        (runExactPlainRom transitionFuel configuration sample).trace =
          priorRecords ++
            (.machineFresh .verifier target answer : UnifiedExposureRecord) ::
              laterRecords := by
      rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
      unfold exactFixedOperationalStateMapTrace exactFixedRootRecords
        fullProjectedRootRecords priorRecords laterRecords
      rw [position]
      simp only [projected_machine_fresh_records_append,
        projectedMachineFreshRecords, List.cons_append, List.append_assoc]
    let reached := indexedStateAfterRecords transitionFuel controller
      priorRecords initial
    have selectedAligned :
        unifiedRecordAtAnswer transitionFuel reached.cursor answer =
          (.machineFresh .verifier target answer : UnifiedExposureRecord) := by
      exact trace_prefix_aligns_indexed_state transitionFuel controller
        priorRecords laterRecords
        (.machineFresh .verifier target answer) _ initial rootTape
        (traceExact.trans fullDecomposition)
    have inputExact :
        unifiedInputBeforeAnswer? transitionFuel reached.cursor = some target :=
      aligned_machine_record_has_exact_input transitionFuel reached.cursor
        .verifier target answer selectedAligned
    have indexExact : reached.exposureIndex = priorRecords.length := by
      simpa [reached, initial, exactCandidateControllerInitialState] using
        indexed_state_after_records_exposure_index transitionFuel controller
          priorRecords initial
    exact ⟨priorRecords, laterRecords, .verifier, reached,
      fullDecomposition, rfl, indexExact, inputExact⟩

#print axioms exactCandidateControllerInitialState
#print axioms exact_final_lookup_aligns_candidate_controller

end

end AspisK1.V7Tag73ExactRootControllerCoordinateAlignment
