import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16ControllerProjection
import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16LabelsNodup
import AspisFormal.K1.V7Tag73ExactAlphaZeroChainRouting
import AspisFormal.K1.V7Tag73ExactAlphaQ16ProducerSeparation

/-!
# Accepted-root alpha labels in the composed 517-slot controller

This module lifts the exact alpha-zero source labels into the product
controller that also carries the established final-work/q16 causal DAG.  The
two components replay the same literal cursor; no separately simulated trace
is joined.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerProjection
open AspisK1.V7Tag73AlphaFinalWorkQ16LabelsNodup
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAlphaZeroChainRouting
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Align the exact compiler tape with `517 + residual`. -/
def exactCompilerAlphaFinalWorkQ16InputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      (517 + ((exactCompilerTargetCaps parameters).length - 517)) :=
  castFreshAnswerTape (by
    have enough :=
      exact_compiler_tape_has_alpha_final_work_q16_capacity parameters
    omega) tape

/-- Align the public `517` count with the finite cardinality of the composed
slot type. -/
def alphaFinalWorkQ16NamedSlotInputTape
    {residual : Nat}
    (tape : FreshAnswerTape Digest256 (517 + residual)) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset AlphaFinalWorkQ16DigestSlot).card + residual) :=
  castFreshAnswerTape (by
    rw [Finset.card_univ, alpha_final_work_q16_digest_slot_card]) tape

def exactAlphaFinalWorkQ16InitialState
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
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory) :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory := (inactiveAlphaZeroMemory, inactiveDagMemory) }

@[simp] theorem exact_combined_initial_alpha_projection
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    alphaIndexedState (exactAlphaFinalWorkQ16InitialState input) =
      exactAlphaZeroInitialState input := by
  rfl

@[simp] theorem exact_combined_initial_dag_projection
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    finalWorkQ16IndexedState (exactAlphaFinalWorkQ16InitialState input) =
      exactDagCandidateInitialState input := by
  rfl

/-- A literal alpha label is preserved as the left summand of the composed
controller at the identical accepted-root prefix. -/
theorem exact_alpha_preferred_lifts_to_composed_controller
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) (prior : List UnifiedExposureRecord)
    (slot : Fin 4)
    (preferred : alphaZeroPreferredSlot transitionFuel
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) prior
        (exactAlphaZeroInitialState input)) = some slot) :
    (alphaFinalWorkQ16DagController transitionFuel trial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (alphaFinalWorkQ16DagController transitionFuel trial.val
            (alphaZeroCausalController transitionFuel boundaryIndex)) prior
          (exactAlphaFinalWorkQ16InitialState input)) =
      some (Sum.inl slot) := by
  apply alpha_final_work_q16_preferred_of_alpha
  rw [alpha_indexed_state_after_composed_records]
  simpa using preferred

/-- Every alpha block consumed by the deployed decoder is now labeled in the
actual composed 517-slot controller, not only in its alpha projection. -/
theorem exact_compiler_consumed_alpha_outputs_have_517_preferred_slots
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters) :
    ∃ boundaryIndex producer outputs advances,
      producer.block = (0 : Fin 4) ∧
      ExactRootOrderedQ16Chain input producer.sourceInput producer.digest
        outputs advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse (.alpha 0)).blocksUsed ∧
      ExactAlphaZeroProducerInstalled input boundaryIndex producer ∧
      ∃ lengthCap : producer.block.val + outputs.length ≤ 4,
        ∀ index (inOutputs : index < outputs.length),
          ∃ outputPrefix later outputActor outputInput,
            exactFixedRootRecords input.package.root =
              outputPrefix ++
                (.machineFresh outputActor outputInput outputs[index] :
                  UnifiedExposureRecord) :: later ∧
            (alphaFinalWorkQ16DagController transitionFuel trial.val
              (alphaZeroCausalController transitionFuel boundaryIndex)
              ).preferredSlot
                (indexedStateAfterRecords transitionFuel
                  (alphaFinalWorkQ16DagController transitionFuel trial.val
                    (alphaZeroCausalController transitionFuel boundaryIndex))
                  outputPrefix (exactAlphaFinalWorkQ16InitialState input)) =
              some (Sum.inl
                ⟨producer.block.val + index,
                  (Nat.add_lt_add_left inOutputs producer.block.val).trans_le
                    lengthCap⟩) := by
  obtain ⟨boundaryIndex, producer, outputs, advances, blockZero, chain,
      outputsLength, installed, lengthCap, routed⟩ :=
    exact_compiler_alpha_zero_consumed_outputs_have_preferred_slots
      transitionRoom input
  refine ⟨boundaryIndex, producer, outputs, advances, blockZero, chain,
    outputsLength, installed, lengthCap, ?_⟩
  intro index inOutputs
  obtain ⟨outputPrefix, later, outputActor, outputInput, decomposition,
      preferred⟩ := routed index inOutputs
  exact ⟨outputPrefix, later, outputActor, outputInput, decomposition,
    exact_alpha_preferred_lifts_to_composed_controller input trial boundaryIndex
      outputPrefix _ preferred⟩

def exactAlphaFinalWorkQ16RootLabels
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    List (Option AlphaFinalWorkQ16DigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (alphaFinalWorkQ16DagController transitionFuel trial.val
      (alphaZeroCausalController transitionFuel boundaryIndex))
    (exactAlphaFinalWorkQ16InitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_alpha_final_work_q16_root_labels_form_trace
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    MachineLabeledTrace
      ((alphaFinalWorkQ16DagController transitionFuel trial.val
        (alphaZeroCausalController transitionFuel boundaryIndex)).machine
          transitionFuel)
      (exactAlphaFinalWorkQ16InitialState input)
      (exactAlphaFinalWorkQ16RootLabels input trial boundaryIndex)
      (indexedStateAfterRecords transitionFuel
        (alphaFinalWorkQ16DagController transitionFuel trial.val
          (alphaZeroCausalController transitionFuel boundaryIndex))
        (exactFixedRootRecords input.package.root)
        (exactAlphaFinalWorkQ16InitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (alphaFinalWorkQ16DagController transitionFuel trial.val
      (alphaZeroCausalController transitionFuel boundaryIndex))
    (exactAlphaFinalWorkQ16InitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_alpha_final_work_q16_root_named_slots_nodup
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    (namedTraceSlots
      (exactAlphaFinalWorkQ16RootLabels input trial boundaryIndex)).Nodup := by
  exact alpha_final_work_q16_labeled_records_named_slots_nodup transitionFuel
    trial.val boundaryIndex (exactFixedRootRecords input.package.root)
      (exactAlphaFinalWorkQ16InitialState input)

theorem exact_alpha_final_work_q16_root_labels_tape_prefix
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    freshAnswerTapeToList
        (alphaFinalWorkQ16NamedSlotInputTape
          (exactCompilerAlphaFinalWorkQ16InputTape parameters sample.2)) =
      (exactAlphaFinalWorkQ16RootLabels input trial boundaryIndex).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold alphaFinalWorkQ16NamedSlotInputTape
    exactCompilerAlphaFinalWorkQ16InputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]
  unfold exactAlphaFinalWorkQ16RootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  have base := exact_causal_router_tape_has_literal_root_prefix input
  unfold finalWorkQ16NamedSlotInputTape
    exactCompilerFinalWorkQ16InputTape at base
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast] at base
  exact base

theorem exact_alpha_final_work_q16_root_residual_enough_of_programmed_cover
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat)
    (programmedCover : 517 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps
        (exactAlphaFinalWorkQ16RootLabels input trial boundaryIndex) ≤
      (exactCompilerTargetCaps parameters).length - 517 := by
  let rootRecords := exactFixedRootRecords input.package.root
  let labels := exactAlphaFinalWorkQ16RootLabels input trial boundaryIndex
  have labelsLength : labels.length = rootRecords.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (alphaFinalWorkQ16DagController transitionFuel trial.val
          (alphaZeroCausalController transitionFuel boundaryIndex))
        (exactAlphaFinalWorkQ16InitialState input) rootRecords)
    simpa [labels, exactAlphaFinalWorkQ16RootLabels, rootRecords] using answers
  have residualLeLabels : residualTraceSteps labels ≤ labels.length := by
    have split := labeled_trace_length_split labels
    omega
  have projectedLength (actor : QueryActor) :
      ∀ queries : List (ShaInput × Digest256),
        (projectedMachineFreshRecords actor queries).length = queries.length := by
    intro queries
    induction queries with
    | nil => rfl
    | cons query queries ih =>
        rcases query with ⟨queryInput, answer⟩
        simp [projectedMachineFreshRecords, ih]
  have rootCountExact : rootRecords.length =
      machineFreshCoordinateCount rootRecords := by
    unfold rootRecords exactFixedRootRecords fullProjectedRootRecords
    simp [projectedLength]
  have rootMachineLe : machineFreshCoordinateCount rootRecords ≤
      machineFreshCoordinateCount
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp [rootRecords]
  have rootLengthLe : rootRecords.length ≤
      full256MachineFreshCap parameters := by
    rw [rootCountExact]
    exact rootMachineLe.trans input.package.root.traceCaps.1
  have fullCapLe : full256MachineFreshCap parameters ≤
      (exactCompilerTargetCaps parameters).length - 517 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLeLabels.trans
    (labelsLength.le.trans (rootLengthLe.trans fullCapLe))

/-- Any literal accepted-root answer labeled by the composed controller is
recovered from the corresponding coordinate of the actual 517-slot causal
router. -/
theorem exact_alpha_final_work_q16_router_routes_selected_root_answer
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (target : AlphaFinalWorkQ16DigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (residualEnough : residualTraceSteps
        (exactAlphaFinalWorkQ16RootLabels input trial boundaryIndex) ≤
      (exactCompilerTargetCaps parameters).length - 517)
    (preferred :
      (alphaFinalWorkQ16DagController transitionFuel trial.val
        (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (alphaFinalWorkQ16DagController transitionFuel trial.val
            (alphaZeroCausalController transitionFuel boundaryIndex)) prior
          (exactAlphaFinalWorkQ16InitialState input)) = some target) :
    causalRoutedAnswer? target
        (exactCompilerConcreteAlphaFinalWorkQ16Router parameters transitionFuel
          boundaryIndex trial.val
          (exactPlainRomCursor configuration sample.1).erase)
      (alphaFinalWorkQ16NamedSlotInputTape
          (exactCompilerAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some answer := by
  let controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      AlphaFinalWorkQ16DigestSlot
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory) :=
    alphaFinalWorkQ16DagController transitionFuel trial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)
  let initial := exactAlphaFinalWorkQ16InitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition :
      exactAlphaFinalWorkQ16RootLabels input trial boundaryIndex =
        priorLabels ++ (some target, answer) :: laterLabels := by
    unfold exactAlphaFinalWorkQ16RootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_alpha_final_work_q16_root_labels_form_trace input trial boundaryIndex)
    (exact_alpha_final_work_q16_root_named_slots_nodup input trial boundaryIndex)
    (fun slot _member => Finset.mem_univ slot) residualEnough
    (alphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerAlphaFinalWorkQ16InputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_alpha_final_work_q16_root_labels_tape_prefix input trial boundaryIndex)
    priorLabels laterLabels target answer labelsDecomposition

/-- Operational accepted-source endpoint for the added alpha coordinates.
Every alpha-zero output block consumed by the deployed bounded decoder is the
answer returned at its exact left-summand coordinate of the concrete 517-slot
router.  The unused portion of the four-block cap remains ordinary padding. -/
theorem exact_compiler_consumed_alpha_outputs_are_routed_by_517_router
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 517 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters) :
    ∃ boundaryIndex producer outputs advances,
      producer.block = (0 : Fin 4) ∧
      ExactRootOrderedQ16Chain input producer.sourceInput producer.digest
        outputs advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse (.alpha 0)).blocksUsed ∧
      ExactAlphaZeroProducerInstalled input boundaryIndex producer ∧
      ∃ lengthCap : producer.block.val + outputs.length ≤ 4,
        ∀ index (inOutputs : index < outputs.length),
          causalRoutedAnswer?
              (Sum.inl
                ⟨producer.block.val + index,
                  (Nat.add_lt_add_left inOutputs producer.block.val).trans_le
                    lengthCap⟩)
              (exactCompilerConcreteAlphaFinalWorkQ16Router parameters
                transitionFuel boundaryIndex trial.val
                (exactPlainRomCursor configuration sample.1).erase)
              (alphaFinalWorkQ16NamedSlotInputTape
                (exactCompilerAlphaFinalWorkQ16InputTape parameters sample.2)) =
            some outputs[index] := by
  obtain ⟨boundaryIndex, producer, outputs, advances, blockZero, chain,
      outputsLength, installed, lengthCap, preferred⟩ :=
    exact_compiler_consumed_alpha_outputs_have_517_preferred_slots
      transitionRoom input trial
  have residualEnough :=
    exact_alpha_final_work_q16_root_residual_enough_of_programmed_cover
      input trial boundaryIndex programmedCover
  refine ⟨boundaryIndex, producer, outputs, advances, blockZero, chain,
    outputsLength, installed, lengthCap, ?_⟩
  intro index inOutputs
  obtain ⟨prior, later, actor, queryInput, decomposition, selected⟩ :=
    preferred index inOutputs
  exact exact_alpha_final_work_q16_router_routes_selected_root_answer
    input trial boundaryIndex prior later actor queryInput outputs[index]
      (Sum.inl
        ⟨producer.block.val + index,
          (Nat.add_lt_add_left inOutputs producer.block.val).trans_le lengthCap⟩)
      decomposition residualEnough selected

#print axioms exactAlphaFinalWorkQ16InitialState
#print axioms exactCompilerAlphaFinalWorkQ16InputTape
#print axioms alphaFinalWorkQ16NamedSlotInputTape
#print axioms exact_combined_initial_alpha_projection
#print axioms exact_combined_initial_dag_projection
#print axioms exact_alpha_preferred_lifts_to_composed_controller
#print axioms exact_compiler_consumed_alpha_outputs_have_517_preferred_slots
#print axioms exactAlphaFinalWorkQ16RootLabels
#print axioms exact_alpha_final_work_q16_root_labels_form_trace
#print axioms exact_alpha_final_work_q16_root_named_slots_nodup
#print axioms exact_alpha_final_work_q16_root_labels_tape_prefix
#print axioms exact_alpha_final_work_q16_root_residual_enough_of_programmed_cover
#print axioms exact_alpha_final_work_q16_router_routes_selected_root_answer
#print axioms exact_compiler_consumed_alpha_outputs_are_routed_by_517_router

end


end AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
