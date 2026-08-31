import AspisFormal.K1.V7Tag73DagFinalWorkPairCompletion
import AspisFormal.K1.V7Tag73ExactDagQ16OutputLabel
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder
import AspisFormal.K1.V7Tag73ExactRootRecordOrderLift
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-!
# Exact recursive routing of the causal q16 DAG

This module composes the exact root-order certificate with the causal-DAG
controller. Its first layer records two generic facts needed by the recursive
fold: a selected position is unique in a list whose projected keys are
duplicate-free, and a tracked q16 base is monotone under arbitrary later
controller inputs.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactDagQ16ChainRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ActualQ16InitialDigest
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73DagFinalWorkPairCompletion
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16OutputLabel
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFinalWorkPairRootOrder
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Two decompositions selecting the same projected key in a projected-nodup
list have the same strict prefix. -/
theorem mapped_nodup_selected_prefix_eq
    {A B : Type} [BEq B] [LawfulBEq B]
    (f : A → B) (values firstPrefix firstSuffix secondPrefix secondSuffix :
      List A)
    (first second : A)
    (nodup : (values.map f).Nodup)
    (firstExact : values = firstPrefix ++ first :: firstSuffix)
    (secondExact : values = secondPrefix ++ second :: secondSuffix)
    (selectedExact : f first = f second) :
    firstPrefix = secondPrefix := by
  have firstFresh : f first ∉ firstPrefix.map f := by
    rw [firstExact, List.map_append, List.map_cons] at nodup
    have separated := (List.nodup_append.mp nodup).2.2
    intro member
    exact separated (f first) member (f first) (by simp) rfl
  have secondFresh : f second ∉ secondPrefix.map f := by
    rw [secondExact, List.map_append, List.map_cons] at nodup
    have separated := (List.nodup_append.mp nodup).2.2
    intro member
    exact separated (f second) member (f second) (by simp) rfl
  have firstIndex : (values.map f).idxOf (f first) = firstPrefix.length := by
    rw [firstExact, List.map_append, List.map_cons,
      List.idxOf_append_of_notMem firstFresh, List.idxOf_cons_self,
      List.length_map]
    omega
  have secondIndex : (values.map f).idxOf (f second) =
      secondPrefix.length := by
    rw [secondExact, List.map_append, List.map_cons,
      List.idxOf_append_of_notMem secondFresh, List.idxOf_cons_self,
      List.length_map]
    omega
  have lengthsExact : firstPrefix.length = secondPrefix.length := by
    rw [selectedExact] at firstIndex
    omega
  have firstPrefixOf : firstPrefix <+: values := by
    exact ⟨first :: firstSuffix, firstExact.symm⟩
  have secondPrefixOf : secondPrefix <+: values := by
    exact ⟨second :: secondSuffix, secondExact.symm⟩
  rw [List.prefix_iff_eq_take] at firstPrefixOf secondPrefixOf
  rw [firstPrefixOf, secondPrefixOf, lengthsExact]

/-- The final-work key may update its work flag, but once the causal-DAG
controller retains a q16 base, no later input can replace or erase it. -/
def Q16DagTracksBase (memory : FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (base : Digest256) : Prop :=
  ∃ workSeen, memory.anchor = .tracked key workSeen ∧
    memory.q16Base = some base

/-- The exact state after the nonce-absorb coordinate but before the matching
final-work coordinate. The q16 base is available while the work flag remains
false. -/
def Q16DagTracksBaseBeforeWork (memory : FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (base : Digest256) : Prop :=
  memory.anchor = .tracked key false ∧ memory.q16Base = some base

/-- Consuming the final-work slot implies that the tracked anchor has seen its
work input. This invariant is independent of q16 producer progress. -/
def Q16DagWorkSlotSound (memory : FinalWorkQ16DagMemory) : Prop :=
  match memory.anchor with
  | .inactive =>
      (none : FinalWorkQ16DigestSlot) ∉ memory.usedSlots
  | .tracked _ workSeen =>
      (none : FinalWorkQ16DigestSlot) ∈ memory.usedSlots → workSeen = true

theorem inactive_dag_memory_work_slot_sound :
    Q16DagWorkSlotSound inactiveDagMemory := by
  simp [Q16DagWorkSlotSound, inactiveDagMemory]

theorem dag_memory_after_input_preserves_work_slot_sound
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256)
    (sound : Q16DagWorkSlotSound memory) :
    Q16DagWorkSlotSound
      (dagMemoryAfterInput anchorIndex exposureIndex memory input answer) := by
  rcases memory with ⟨anchor, q16Base, producers, usedSlots⟩
  cases anchor with
  | inactive =>
      by_cases atAnchor : exposureIndex = anchorIndex
      · cases work : rawFinalWorkKeyOfWorkInput? input with
        | some key =>
            simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
              dagCoreMemoryAfterInput, dagPreferredSlotForInput,
              dagRawPreferredSlot, atAnchor, work]
        | none =>
            cases absorb : rawFinalWorkKeyOfAbsorbInput? input with
            | some key =>
                simpa [Q16DagWorkSlotSound, dagMemoryAfterInput,
                  dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                  dagRawPreferredSlot, atAnchor, work, absorb] using sound
            | none =>
                simpa [Q16DagWorkSlotSound, dagMemoryAfterInput,
                  dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                  dagRawPreferredSlot, atAnchor, work, absorb] using sound
      · simpa [Q16DagWorkSlotSound, dagMemoryAfterInput,
          dagCoreMemoryAfterInput, dagPreferredSlotForInput,
          dagRawPreferredSlot, atAnchor] using sound
  | tracked key workSeen =>
      cases workSeen with
      | false =>
          have noneFresh : (none : FinalWorkQ16DigestSlot) ∉ usedSlots := by
            intro used
            have sound' : (none : FinalWorkQ16DigestSlot) ∈ usedSlots →
                false = true := by
              simpa [Q16DagWorkSlotSound] using sound
            exact Bool.noConfusion (sound' used)
          by_cases isWork : input = key.workInput
          · subst input
            cases q16Base with
            | none =>
                by_cases isAbsorb : key.workInput = key.absorbInput <;>
                  simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                    dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                    dagRawPreferredSlot, isAbsorb, noneFresh]
            | some base =>
                simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                  dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                  dagRawPreferredSlot, noneFresh]
          · cases q16Base with
            | none =>
                by_cases isAbsorb : input = key.absorbInput
                · subst input
                  have absorbNeWork : key.absorbInput ≠ key.workInput :=
                    isWork
                  cases output : q16DagOutputSlot? producers
                      key.absorbInput with
                  | none =>
                      simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                        dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                        dagRawPreferredSlot, absorbNeWork,
                        noneFresh, output]
                  | some slot =>
                      by_cases outputUsed :
                        (some slot : FinalWorkQ16DigestSlot) ∈ usedSlots <;>
                        simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                          dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                          dagRawPreferredSlot, absorbNeWork,
                          noneFresh, output, outputUsed]
                · cases output : q16DagOutputSlot? producers input with
                  | none =>
                      simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                        dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                        dagRawPreferredSlot, isWork, isAbsorb, noneFresh,
                        output]
                  | some slot =>
                      by_cases outputUsed :
                        (some slot : FinalWorkQ16DigestSlot) ∈ usedSlots <;>
                        simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                          dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                          dagRawPreferredSlot, isWork, isAbsorb, noneFresh,
                          output, outputUsed]
            | some base =>
                cases output : q16DagOutputSlot? producers input with
                | none =>
                    simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                      dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                      dagRawPreferredSlot, isWork, noneFresh, output]
                | some slot =>
                    by_cases outputUsed :
                      (some slot : FinalWorkQ16DigestSlot) ∈ usedSlots <;>
                      simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                        dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                        dagRawPreferredSlot, isWork, noneFresh, output,
                        outputUsed]
      | true =>
          cases q16Base with
          | none =>
              by_cases isAbsorb : input = key.absorbInput <;>
                simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                  dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                  dagRawPreferredSlot, isAbsorb]
          | some base =>
              simp [Q16DagWorkSlotSound, dagMemoryAfterInput,
                dagCoreMemoryAfterInput, dagPreferredSlotForInput,
                dagRawPreferredSlot]

theorem dag_memory_after_input_preserves_tracks_base
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (base : Digest256)
    (input : ShaInput) (answer : Digest256)
    (tracked : Q16DagTracksBase memory key base) :
    Q16DagTracksBase
      (dagMemoryAfterInput anchorIndex exposureIndex memory input answer)
      key base := by
  obtain ⟨workSeen, anchorExact, baseExact⟩ := tracked
  refine ⟨workSeen || decide (input = key.workInput), ?_, ?_⟩
  · simp [dagMemoryAfterInput, dagCoreMemoryAfterInput, anchorExact,
      baseExact]
  · exact dag_memory_after_input_preserves_tracked_base anchorIndex
      exposureIndex memory key workSeen base input answer anchorExact baseExact

theorem dag_candidate_after_memory_preserves_tracks_base
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (base answer : Digest256)
    (tracked : Q16DagTracksBase state.memory key base) :
    Q16DagTracksBase
      (dagCandidateAfterMemory transitionFuel anchorIndex state answer)
      key base := by
  unfold dagCandidateAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simpa [inputExact] using tracked
  | some input =>
      simpa [inputExact] using
        dag_memory_after_input_preserves_tracks_base anchorIndex
          state.exposureIndex state.memory key base input answer tracked

theorem dag_candidate_after_memory_preserves_work_slot_sound
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256)
    (sound : Q16DagWorkSlotSound state.memory) :
    Q16DagWorkSlotSound
      (dagCandidateAfterMemory transitionFuel anchorIndex state answer) := by
  unfold dagCandidateAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simpa [inputExact] using sound
  | some input =>
      simpa [inputExact] using
        dag_memory_after_input_preserves_work_slot_sound anchorIndex
          state.exposureIndex state.memory input answer sound

/-- Prefix-independent monotonicity used between a producer coordinate and
either of its two children. -/
theorem dag_indexed_state_preserves_tracks_base
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory)
      (key : RawFinalWorkKey) (base : Digest256),
      Q16DagTracksBase state.memory key base →
      Q16DagTracksBase
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) records state).memory key base := by
  intro records
  induction records with
  | nil =>
      intro state key base tracked
      simpa only [indexed_state_after_records_nil] using tracked
  | cons record records ih =>
      intro state key base tracked
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextTracked : Q16DagTracksBase next.memory key base := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          dag_candidate_after_memory_preserves_tracks_base transitionFuel
            anchorIndex state key base record.answer tracked
      rw [indexed_state_after_records_cons]
      exact ih next key base nextTracked

theorem dag_indexed_state_preserves_work_slot_sound
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      Q16DagWorkSlotSound state.memory →
      Q16DagWorkSlotSound
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) records state).memory := by
  intro records
  induction records with
  | nil =>
      intro state sound
      simpa only [indexed_state_after_records_nil] using sound
  | cons record records ih =>
      intro state sound
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextSound : Q16DagWorkSlotSound next.memory := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          dag_candidate_after_memory_preserves_work_slot_sound transitionFuel
            anchorIndex state record.answer sound
      rw [indexed_state_after_records_cons]
      exact ih next nextSound

theorem dag_memory_after_nonwork_preserves_base_before_work
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (base : Digest256)
    (input : ShaInput) (answer : Digest256)
    (inputNe : input ≠ key.workInput)
    (tracked : Q16DagTracksBaseBeforeWork memory key base) :
    Q16DagTracksBaseBeforeWork
      (dagMemoryAfterInput anchorIndex exposureIndex memory input answer)
      key base := by
  obtain ⟨anchorExact, baseExact⟩ := tracked
  rcases memory with ⟨anchor, q16Base, producers, usedSlots⟩
  simp only at anchorExact baseExact
  subst anchor
  subst q16Base
  constructor <;>
    simp [dagMemoryAfterInput, dagCoreMemoryAfterInput, inputNe]

theorem dag_candidate_after_nonwork_preserves_base_before_work
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (base answer : Digest256)
    (input : ShaInput)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (inputNe : input ≠ key.workInput)
    (tracked : Q16DagTracksBaseBeforeWork state.memory key base) :
    Q16DagTracksBaseBeforeWork
      (dagCandidateAfterMemory transitionFuel anchorIndex state answer)
      key base := by
  unfold dagCandidateAfterMemory
  rw [inputExact]
  exact dag_memory_after_nonwork_preserves_base_before_work anchorIndex
    state.exposureIndex state.memory key base input answer inputNe tracked

/-- Aligned machine-fresh records that avoid the literal work coordinate keep
the absorb-first anchor at `workSeen = false`. Q16 producers may still evolve
under adversarial prequeries. -/
theorem aligned_machine_records_preserve_dag_base_before_work
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (key : RawFinalWorkKey) (base : Digest256) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      IndexedRecordsAligned transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) state records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records,
        causalInput? record ≠ some key.workInput) →
      Q16DagTracksBaseBeforeWork state.memory key base →
      Q16DagTracksBaseBeforeWork
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) records state).memory key base := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _onlyMachine _avoids tracked
      simpa only [indexed_state_after_records_nil] using tracked
  | cons head tail ih =>
      intro state aligned onlyMachine avoids tracked
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have inputNe : input ≠ key.workInput := by
        intro equal
        apply avoids (.machineFresh actor input answer) (by simp)
        simp [causalInput?, equal]
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state answer
      have nextTracked : Q16DagTracksBaseBeforeWork next.memory key base := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          dag_candidate_after_nonwork_preserves_base_before_work transitionFuel
            anchorIndex state key base answer input inputExact inputNe tracked
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have tailAvoids : ∀ record ∈ tail,
          causalInput? record ≠ some key.workInput := by
        intro record member
        exact avoids record (by simp [member])
      rw [indexed_state_after_records_cons]
      exact ih next tailAligned tailOnly tailAvoids nextTracked

/-- Before its fixed ordinal the causal-DAG controller remains completely
inactive, just like the older branch controller. -/
theorem dag_memory_stays_inactive_before_anchor
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      state.exposureIndex + records.length = anchor →
      state.memory = inactiveDagMemory →
      (indexedStateAfterRecords transitionFuel
        (finalWorkQ16DagController globalOracleCalls transitionFuel anchor)
        records state).memory = inactiveDagMemory := by
  intro records
  induction records with
  | nil =>
      intro state _anchorExact inactive
      simpa only [indexed_state_after_records_nil] using inactive
  | cons record records ih =>
      intro state anchorExact inactive
      have beforeAnchor : state.exposureIndex ≠ anchor := by
        intro equal
        rw [equal] at anchorExact
        simp only [List.length_cons] at anchorExact
        omega
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchor
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextInactive : next.memory = inactiveDagMemory := by
        simp only [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer]
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor <;>
          simp [dagCandidateAfterMemory, inputExact, inactive, beforeAnchor,
            inactiveDagMemory, dagMemoryAfterInput, dagCoreMemoryAfterInput,
            dagPreferredSlotForInput, dagRawPreferredSlot]
      have nextAnchor : next.exposureIndex + records.length = anchor := by
        simp only [next, indexed_after_answer_exposure_index,
          List.length_cons] at anchorExact ⊢
        omega
      rw [indexed_state_after_records_cons]
      exact ih next nextAnchor nextInactive

/-- Before the selected final-work anchor, the causal-DAG controller cannot
reserve any final-work or q16 destination.  The labelled prefix is therefore
entirely residual.  This is intentionally a controller fact, independent of
whether a source coordinate was first queried by the adversary or verifier. -/
theorem dag_labeled_records_before_anchor_all_residual
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      state.exposureIndex + records.length = anchor →
      state.memory = inactiveDagMemory →
      namedTraceSlots
        (indexedControllerLabeledRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel anchor)
          state records) = [] := by
  intro records
  induction records with
  | nil =>
      intro state _anchorExact _inactive
      rfl
  | cons record records ih =>
      intro state anchorExact inactive
      have beforeAnchor : state.exposureIndex ≠ anchor := by
        intro equal
        rw [equal] at anchorExact
        simp only [List.length_cons] at anchorExact
        omega
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchor
      let next := controller.afterAnswer transitionFuel state record.answer
      have preferredNone : controller.preferredSlot state = none := by
        unfold controller finalWorkQ16DagController
        unfold dagCandidatePreferredSlot
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor
        · rfl
        · simp [dagPreferredSlotForInput, dagRawPreferredSlot, inactive,
            beforeAnchor, inactiveDagMemory]
      have nextInactive : next.memory = inactiveDagMemory := by
        simp only [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer]
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor <;>
          simp [dagCandidateAfterMemory, inputExact, inactive, beforeAnchor,
            inactiveDagMemory, dagMemoryAfterInput, dagCoreMemoryAfterInput,
            dagPreferredSlotForInput, dagRawPreferredSlot]
      have nextAnchor : next.exposureIndex + records.length = anchor := by
        simp only [next, indexed_after_answer_exposure_index,
          List.length_cons] at anchorExact ⊢
        omega
      have tailResidual := ih next nextAnchor nextInactive
      change namedTraceSlots
        ((controller.preferredSlot state, record.answer) ::
          indexedControllerLabeledRecords transitionFuel controller next
            records) = []
      rw [preferredNone]
      exact tailResidual

/-- If the exact nonce-absorb record is the selected trial anchor, consuming
it installs the literal q16 base in the causal-DAG state. -/
theorem exact_dag_absorb_anchor_tracks_base
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
    (digest base : Digest256) (nonce : NonceBytes)
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord) (actor : QueryActor)
    (trialExact : trial.val = prior.length)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor
          (literalFinalWorkKey digest nonce).absorbInput base :
          UnifiedExposureRecord) :: later) :
    Q16DagTracksBase
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (prior ++
          [(.machineFresh actor
            (literalFinalWorkKey digest nonce).absorbInput base :
            UnifiedExposureRecord)])
        (exactDagCandidateInitialState input)).memory
      (literalFinalWorkKey digest nonce) base := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let beforeAbsorb := indexedStateAfterRecords transitionFuel controller prior
    initial
  have beforeIndex : beforeAbsorb.exposureIndex = trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller prior initial
    simpa [beforeAbsorb, initial, exactDagCandidateInitialState, trialExact]
      using count
  have beforeInactive : beforeAbsorb.memory = inactiveDagMemory := by
    apply dag_memory_stays_inactive_before_anchor transitionFuel trial.val prior
      initial
    · simp [initial, exactDagCandidateInitialState, trialExact]
    · simp [initial, exactDagCandidateInitialState]
  have aligned : unifiedRecordAtAnswer transitionFuel beforeAbsorb.cursor base =
      .machineFresh actor (literalFinalWorkKey digest nonce).absorbInput base := by
    have rootAligned := exact_root_records_aligned_for_dag_controller input
      trial.val prior
        (.machineFresh actor
          (literalFinalWorkKey digest nonce).absorbInput base)
        later decomposition
    simpa [beforeAbsorb, controller, exactDagTrialController, initial,
      UnifiedExposureRecord.answer] using rootAligned
  have inputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeAbsorb.cursor =
        some (literalFinalWorkKey digest nonce).absorbInput :=
    aligned_machine_record_has_exact_input transitionFuel beforeAbsorb.cursor
      actor (literalFinalWorkKey digest nonce).absorbInput base aligned
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil]
  change Q16DagTracksBase
    (dagCandidateAfterMemory transitionFuel trial.val beforeAbsorb base)
      (literalFinalWorkKey digest nonce) base
  unfold dagCandidateAfterMemory
  rw [inputExact]
  refine ⟨false, ?_, ?_⟩
  · simp [dagMemoryAfterInput, dagCoreMemoryAfterInput, beforeIndex,
      beforeInactive, inactiveDagMemory]
  · simp [dagMemoryAfterInput, dagCoreMemoryAfterInput, beforeIndex,
      beforeInactive, inactiveDagMemory]

/-- Strong absorb-first form: immediately after the selected anchor the q16
base is installed and the matching final-work input has not yet been seen. -/
theorem exact_dag_absorb_anchor_tracks_base_before_work
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
    (digest base : Digest256) (nonce : NonceBytes)
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord) (actor : QueryActor)
    (trialExact : trial.val = prior.length)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor
          (literalFinalWorkKey digest nonce).absorbInput base :
          UnifiedExposureRecord) :: later) :
    Q16DagTracksBaseBeforeWork
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (prior ++
          [(.machineFresh actor
            (literalFinalWorkKey digest nonce).absorbInput base :
            UnifiedExposureRecord)])
        (exactDagCandidateInitialState input)).memory
      (literalFinalWorkKey digest nonce) base := by
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState input
  let beforeAbsorb := indexedStateAfterRecords transitionFuel controller prior
    initial
  have beforeIndex : beforeAbsorb.exposureIndex = trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller prior initial
    simpa [beforeAbsorb, initial, exactDagCandidateInitialState, trialExact]
      using count
  have beforeInactive : beforeAbsorb.memory = inactiveDagMemory := by
    apply dag_memory_stays_inactive_before_anchor transitionFuel trial.val prior
      initial
    · simp [initial, exactDagCandidateInitialState, trialExact]
    · simp [initial, exactDagCandidateInitialState]
  have aligned : unifiedRecordAtAnswer transitionFuel beforeAbsorb.cursor base =
      .machineFresh actor (literalFinalWorkKey digest nonce).absorbInput base := by
    have rootAligned := exact_root_records_aligned_for_dag_controller input
      trial.val prior
        (.machineFresh actor
          (literalFinalWorkKey digest nonce).absorbInput base)
        later decomposition
    simpa [beforeAbsorb, controller, exactDagTrialController, initial,
      UnifiedExposureRecord.answer] using rootAligned
  have inputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeAbsorb.cursor =
        some (literalFinalWorkKey digest nonce).absorbInput :=
    aligned_machine_record_has_exact_input transitionFuel beforeAbsorb.cursor
      actor (literalFinalWorkKey digest nonce).absorbInput base aligned
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil]
  change Q16DagTracksBaseBeforeWork
    (dagCandidateAfterMemory transitionFuel trial.val beforeAbsorb base)
      (literalFinalWorkKey digest nonce) base
  unfold dagCandidateAfterMemory
  rw [inputExact]
  constructor
  · simp [dagMemoryAfterInput, dagCoreMemoryAfterInput, beforeIndex,
      beforeInactive, inactiveDagMemory]
  · simp [dagMemoryAfterInput, dagCoreMemoryAfterInput, beforeIndex,
      beforeInactive, inactiveDagMemory]

/-- In the opposite pair order, the work anchor followed by the exact absorb
record also installs and retains the literal q16 base in the DAG controller. -/
theorem exact_dag_work_then_absorb_tracks_base
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
    (digest workAnswer base : Digest256) (nonce : NonceBytes)
    (trial : ExactCompilerExposureTrial parameters)
    (prior middle later : List UnifiedExposureRecord)
    (workActor absorbActor : QueryActor)
    (trialExact : trial.val = prior.length)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh workActor
          (literalFinalWorkKey digest nonce).workInput workAnswer :
          UnifiedExposureRecord) :: middle ++
        (.machineFresh absorbActor
          (literalFinalWorkKey digest nonce).absorbInput base :
          UnifiedExposureRecord) :: later) :
    let completedPrefix :=
      prior ++
        (.machineFresh workActor
          (literalFinalWorkKey digest nonce).workInput workAnswer :
          UnifiedExposureRecord) :: middle ++
        [(.machineFresh absorbActor
          (literalFinalWorkKey digest nonce).absorbInput base :
          UnifiedExposureRecord)]
    Q16DagTracksBase
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) completedPrefix
        (exactDagCandidateInitialState input)).memory
      (literalFinalWorkKey digest nonce) base := by
  dsimp only
  let key := literalFinalWorkKey digest nonce
  let workRecord : UnifiedExposureRecord :=
    .machineFresh workActor key.workInput workAnswer
  let absorbRecord : UnifiedExposureRecord :=
    .machineFresh absorbActor key.absorbInput base
  let completedPrefix := prior ++ workRecord :: middle ++ [absorbRecord]
  have aligned := exact_root_records_aligned_for_candidate_controller input
    prior.length
  have completed := aligned_work_then_absorb_completes_pair transitionFuel
    (exactPlainRomCursor configuration sample.1).erase
    (exactFixedRootRecords input.package.root) prior middle later digest nonce
      workAnswer base workActor absorbActor decomposition aligned
      (exact_root_records_only_machine_fresh input)
      (exact_root_record_causal_inputs_nodup input)
  have candidateMemoryExact :
      (indexedStateAfterRecords transitionFuel
        (finalWorkQ16CandidateController
          (globalFull256OracleCallCap parameters) transitionFuel prior.length)
        completedPrefix (exactPairControllerInitialState input)).memory =
        .tracked key true (some base) emptyRawQ16Branches := by
    simpa [completedPrefix, workRecord, absorbRecord, key,
      exactPairControllerInitialState, UnifiedExposureRecord.answer,
      indexed_state_after_records_append] using completed
  have initialAgree := exact_pair_and_dag_initial_core_agree input
  have replayCore := candidate_dag_replay_core_eq transitionFuel prior.length
    completedPrefix (exactPairControllerInitialState input)
      (exactDagCandidateInitialState input) initialAgree.1 initialAgree.2.1
      initialAgree.2.2
  rw [candidateMemoryExact] at replayCore
  simp only [candidateMemoryCore] at replayCore
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) completedPrefix
    (exactDagCandidateInitialState input)
  have dagCoreExact : dagMemoryCore reached.memory =
      .tracked key true (some base) := by
    simpa [reached, exactDagTrialController, trialExact] using replayCore.symm
  rcases reachedExact : reached.memory with
    ⟨anchor, q16Base, producers, usedSlots⟩
  cases anchor with
  | inactive =>
      simp [dagMemoryCore, reachedExact] at dagCoreExact
  | tracked reachedKey workSeen =>
      simp only [dagMemoryCore, reachedExact,
        FinalWorkQ16Core.tracked.injEq] at dagCoreExact
      rcases dagCoreExact with ⟨keyExact, workExact, baseExact⟩
      subst reachedKey
      subst workSeen
      refine ⟨true, ?_, ?_⟩
      · simpa [reached, reachedExact, key]
      · simpa [reached, reachedExact] using baseExact

/-- A reachable nonempty producer inventory certifies that the controller is
already tracked and retains some q16 base. -/
theorem producer_member_implies_tracks_some_base
    (memory : FinalWorkQ16DagMemory) (producer : Q16DagProducer)
    (invariant : Q16DagMemoryProducerInvariant memory)
    (member : producer ∈ memory.producers) :
    ∃ key base, Q16DagTracksBase memory key base := by
  cases baseExact : memory.q16Base with
  | none =>
      have empty := invariant.noBaseHasNoProducers baseExact
      rw [empty] at member
      simp at member
  | some base =>
      cases anchorExact : memory.anchor with
      | inactive =>
          have noBase := invariant.inactiveHasNoBase anchorExact
          rw [baseExact] at noBase
          contradiction
      | tracked key workSeen =>
          exact ⟨key, base, workSeen, anchorExact, baseExact⟩

/-- A source coordinate has installed its literal producer after any exact
actor-tagged decomposition selecting that coordinate. -/
def ExactDagProducerInstalled
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
    (producer : Q16DagProducer) : Prop :=
  ∀ prior later actor,
    exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) :: later →
    producer ∈
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (prior ++
          [(.machineFresh actor producer.sourceInput producer.digest :
            UnifiedExposureRecord)])
        (exactDagCandidateInitialState input)).memory.producers

/-- The exact source positions of the two final-work inputs selected by one
causal-DAG trial.  The trial anchor is the earlier of the work and nonce-
absorb records, rather than an abstract tape index.  Keeping both actors and
the strict order proof-relevant is necessary for the later cached-versus-fresh
source analysis: either input may already have been first queried by the
adversary. -/
def ExactDagFinalWorkPairLabeled
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
    (key : RawFinalWorkKey) (workAnswer base : Digest256) : Prop :=
  (∃ prior middle later workActor absorbActor,
      exactFixedRootRecords input.package.root =
        prior ++ (.machineFresh workActor key.workInput workAnswer :
          UnifiedExposureRecord) :: middle ++
          (.machineFresh absorbActor key.absorbInput base :
            UnifiedExposureRecord) :: later ∧
      trial.val = prior.length) ∨
  (∃ prior middle later workActor absorbActor,
      exactFixedRootRecords input.package.root =
        prior ++ (.machineFresh absorbActor key.absorbInput base :
          UnifiedExposureRecord) :: middle ++
          (.machineFresh workActor key.workInput workAnswer :
            UnifiedExposureRecord) :: later ∧
      trial.val = prior.length)

/-- The proof-relevant final-work pair anchor exposes an entirely residual
literal prefix.  The result is deliberately about the controller labels only:
it does not claim that this prefix was verifier-owned, since either selected
pair input may have been prequeried by the adversary. -/
theorem exact_dag_final_work_pair_labeled_prefix_all_residual
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
    (key : RawFinalWorkKey) (workAnswer base : Digest256)
    (labeled : ExactDagFinalWorkPairLabeled input trial key workAnswer base) :
    (∃ prior middle later workActor absorbActor,
      exactFixedRootRecords input.package.root =
        prior ++ (.machineFresh workActor key.workInput workAnswer :
          UnifiedExposureRecord) :: middle ++
          (.machineFresh absorbActor key.absorbInput base :
          UnifiedExposureRecord) :: later ∧
      trial.val = prior.length ∧
      namedTraceSlots (List.take prior.length
        (exactDagCandidateRootLabels input trial)) = []) ∨
    (∃ prior middle later workActor absorbActor,
      exactFixedRootRecords input.package.root =
        prior ++ (.machineFresh absorbActor key.absorbInput base :
          UnifiedExposureRecord) :: middle ++
          (.machineFresh workActor key.workInput workAnswer :
          UnifiedExposureRecord) :: later ∧
      trial.val = prior.length ∧
      namedTraceSlots (List.take prior.length
        (exactDagCandidateRootLabels input trial)) = []) := by
  rcases labeled with
      ⟨prior, middle, later, workActor, absorbActor, recordsExact, trialExact⟩ |
      ⟨prior, middle, later, workActor, absorbActor, recordsExact, trialExact⟩
  · refine Or.inl ⟨prior, middle, later, workActor, absorbActor, recordsExact,
      trialExact, ?_⟩
    have prefixLabels : List.take prior.length
        (exactDagCandidateRootLabels input trial) = indexedControllerLabeledRecords transitionFuel
          (exactDagTrialController transitionFuel trial)
          (exactDagCandidateInitialState input) prior := by
      unfold exactDagCandidateRootLabels
      let suffix :=
        (.machineFresh workActor key.workInput workAnswer :
          UnifiedExposureRecord) :: middle ++
          (.machineFresh absorbActor key.absorbInput base :
            UnifiedExposureRecord) :: later
      have rootSplit : exactFixedRootRecords input.package.root =
          prior ++ suffix := by
        simpa [suffix, List.append_assoc] using recordsExact
      rw [rootSplit]
      rw [indexed_controller_labeled_records_append transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactDagCandidateInitialState input) prior suffix]
      have prefixLength :
          (indexedControllerLabeledRecords transitionFuel
            (exactDagTrialController transitionFuel trial)
            (exactDagCandidateInitialState input) prior).length =
            prior.length := by
        have answers := congrArg List.length
          (indexed_controller_labeled_records_answers transitionFuel
            (exactDagTrialController transitionFuel trial)
            (exactDagCandidateInitialState input) prior)
        simpa using answers
      rw [List.take_append_of_le_length (by omega : prior.length ≤
        (indexedControllerLabeledRecords transitionFuel
          (exactDagTrialController transitionFuel trial)
          (exactDagCandidateInitialState input) prior).length)]
      simp [prefixLength]
    rw [prefixLabels]
    apply dag_labeled_records_before_anchor_all_residual transitionFuel trial.val
      prior (exactDagCandidateInitialState input)
    · simp [exactDagCandidateInitialState, trialExact]
    · rfl
  · refine Or.inr ⟨prior, middle, later, workActor, absorbActor, recordsExact,
      trialExact, ?_⟩
    have prefixLabels : List.take prior.length
        (exactDagCandidateRootLabels input trial) = indexedControllerLabeledRecords transitionFuel
          (exactDagTrialController transitionFuel trial)
          (exactDagCandidateInitialState input) prior := by
      unfold exactDagCandidateRootLabels
      let suffix :=
        (.machineFresh absorbActor key.absorbInput base :
          UnifiedExposureRecord) :: middle ++
          (.machineFresh workActor key.workInput workAnswer :
            UnifiedExposureRecord) :: later
      have rootSplit : exactFixedRootRecords input.package.root =
          prior ++ suffix := by
        simpa [suffix, List.append_assoc] using recordsExact
      rw [rootSplit]
      rw [indexed_controller_labeled_records_append transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactDagCandidateInitialState input) prior suffix]
      have prefixLength :
          (indexedControllerLabeledRecords transitionFuel
            (exactDagTrialController transitionFuel trial)
            (exactDagCandidateInitialState input) prior).length =
            prior.length := by
        have answers := congrArg List.length
          (indexed_controller_labeled_records_answers transitionFuel
            (exactDagTrialController transitionFuel trial)
            (exactDagCandidateInitialState input) prior)
        simpa using answers
      rw [List.take_append_of_le_length (by omega : prior.length ≤
        (indexedControllerLabeledRecords transitionFuel
          (exactDagTrialController transitionFuel trial)
          (exactDagCandidateInitialState input) prior).length)]
      simp [prefixLength]
    rw [prefixLabels]
    apply dag_labeled_records_before_anchor_all_residual transitionFuel trial.val
      prior (exactDagCandidateInitialState input)
    · simp [exactDagCandidateInitialState, trialExact]
    · rfl

/-- The selected final-work answer is named by the `none` slot in the same
exact causal-DAG trial used for q16 routing. -/
def ExactDagFinalWorkLabeled
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
    (key : RawFinalWorkKey) (answer : Digest256) : Prop :=
  ∃ prior later actor,
    exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor key.workInput answer :
        UnifiedExposureRecord) :: later ∧
    (exactDagTrialController transitionFuel trial).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)) = some none

/-- A candidate record after any already-tracked base prefix installs the
exact block-zero producer; projected-input uniqueness makes the conclusion
independent of which actor-tagged decomposition selects that record. -/
theorem exact_dag_candidate_installed_after_tracked_prefix
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
    (key : RawFinalWorkKey) (base initialDigest : Digest256)
    (counter : Fin 64)
    (basePrefix between later : List UnifiedExposureRecord)
    (candidateActor : QueryActor)
    (tracked : Q16DagTracksBase
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) basePrefix
        (exactDagCandidateInitialState input)).memory key base)
    (decomposition : exactFixedRootRecords input.package.root =
      basePrefix ++ between ++
        (.machineFresh candidateActor
          (bytes base ++ [domAbsorb, queryCandidateLabel,
            UInt8.ofNat counter.val]) initialDigest :
          UnifiedExposureRecord) :: later) :
    ExactDagProducerInstalled input trial
      (Q16DagProducer.mk initialDigest (counter, ⟨0, by omega⟩)
        (bytes base ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val])) := by
  let candidateInput := bytes base ++
    [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]
  let producer := Q16DagProducer.mk initialDigest (counter, ⟨0, by omega⟩)
    candidateInput
  let candidatePrefix := basePrefix ++ between
  let baseState := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) basePrefix
    (exactDagCandidateInitialState input)
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) candidatePrefix
    (exactDagCandidateInitialState input)
  have reachedTracked : Q16DagTracksBase reached.memory key base := by
    have preserved := dag_indexed_state_preserves_tracks_base transitionFuel
      trial.val between baseState key base (by simpa [baseState] using tracked)
    simpa [reached, baseState, candidatePrefix, exactDagTrialController,
      indexed_state_after_records_append] using preserved
  obtain ⟨workSeen, anchorExact, baseExact⟩ := reachedTracked
  have canonicalExact : exactFixedRootRecords input.package.root =
      candidatePrefix ++
        (.machineFresh candidateActor candidateInput initialDigest :
          UnifiedExposureRecord) :: later := by
    simpa only [candidatePrefix, candidateInput, List.append_assoc] using
      decomposition
  have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      initialDigest =
        .machineFresh candidateActor candidateInput initialDigest := by
    have rootAligned := exact_root_records_aligned_for_dag_controller input
      trial.val candidatePrefix
        (.machineFresh candidateActor candidateInput initialDigest)
        later canonicalExact
    simpa [reached, exactDagTrialController,
      UnifiedExposureRecord.answer] using rootAligned
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some candidateInput :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor
      candidateActor candidateInput initialDigest aligned
  have installedMemory := dag_memory_after_candidate_contains_producer
    trial.val reached.exposureIndex reached.memory key workSeen base
      initialDigest counter anchorExact baseExact
  have canonicalInstalled : producer ∈
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (candidatePrefix ++
          [(.machineFresh candidateActor candidateInput initialDigest :
            UnifiedExposureRecord)])
        (exactDagCandidateInitialState input)).memory.producers := by
    rw [indexed_state_after_records_append,
      indexed_state_after_records_cons, indexed_state_after_records_nil]
    change producer ∈
      (dagCandidateAfterMemory transitionFuel trial.val reached
        initialDigest).producers
    unfold dagCandidateAfterMemory
    rw [inputExact]
    simpa [producer, candidateInput] using installedMemory
  intro arbitraryPrior arbitraryLater arbitraryActor arbitraryExact
  have prefixExact : candidatePrefix = arbitraryPrior := by
    apply mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root) candidatePrefix later
        arbitraryPrior arbitraryLater
        (.machineFresh candidateActor candidateInput initialDigest)
        (.machineFresh arbitraryActor producer.sourceInput producer.digest)
      (exact_root_record_causal_inputs_nodup input) canonicalExact
      (by simpa [producer, candidateInput] using arbitraryExact)
    simp [producer, candidateInput, causalInput?]
  subst arbitraryPrior
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil]
  change producer ∈
    (dagCandidateAfterMemory transitionFuel trial.val reached
      initialDigest).producers
  unfold dagCandidateAfterMemory
  rw [inputExact]
  simpa [producer, candidateInput] using installedMemory

/-- The exact nonce-absorb answer is strictly earlier than every candidate
through the selected counter, lifted to the actor-tagged root record list. -/
theorem exact_q16_absorb_before_candidate_records
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
    (digest base : Digest256) (nonce : NonceBytes)
    (absorbLookup : tableLookup (exactOperationalTable input)
      (literalFinalWorkKey digest nonce).absorbInput = some base)
    (baseExact : base = (exactOperationalRawTrace input).q16BaseDigest)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    ∃ prior middle later absorbActor candidateActor,
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh absorbActor
            (literalFinalWorkKey digest nonce).absorbInput base :
            UnifiedExposureRecord) :: middle ++
          (.machineFresh candidateActor
            (bytes base ++ [domAbsorb, queryCandidateLabel,
              UInt8.ofNat counter.val])
            (exactOperationalQ16InitialDigest input counter) :
            UnifiedExposureRecord) :: later := by
  let candidateInput := bytes base ++
    [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]
  have candidateLookup : tableLookup (exactOperationalTable input)
      candidateInput = some (exactOperationalQ16InitialDigest input counter) := by
    change tableLookup (exactOperationalTable input)
      (bytes base ++ [domAbsorb, queryCandidateLabel,
        UInt8.ofNat counter.val]) =
        some (exactOperationalQ16InitialDigest input counter)
    rw [baseExact]
    exact exact_operational_q16_candidate_absorb_lookup input counter
      beforeSelected
  have dependency : HasLiteralStatePrefix base candidateInput := by
    simp [HasLiteralStatePrefix, candidateInput]
  obtain ⟨before, middle, after, ordered⟩ :=
    exact_compiler_literal_dependency_has_strict_root_order transitionRoom
      input (literalFinalWorkKey digest nonce).absorbInput candidateInput base
      (exactOperationalQ16InitialDigest input counter) absorbLookup
      candidateLookup dependency
  obtain ⟨prior, between, later, absorbActor, candidateActor, recordsExact⟩ :=
    exact_root_pair_order_lifts_to_records input
      (literalFinalWorkKey digest nonce).absorbInput candidateInput base
      (exactOperationalQ16InitialDigest input counter) before middle after
      ordered
  exact ⟨prior, between, later, absorbActor, candidateActor, by
    simpa [candidateInput] using recordsExact⟩

/-- Strict accepted execution selects one genuine work-qualified trial whose
causal-DAG controller installs block zero for every candidate consumed through
the first-cap-203 result. -/
theorem exact_compiler_accepted_dag_trial_installs_all_candidates
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
      fixedInstance sample) :
    ∃ (digest workAnswer base : Digest256)
        (trial : ExactCompilerExposureTrial parameters),
      FinalWork34Accepted workAnswer ∧
      base = (exactOperationalRawTrace input).q16BaseDigest ∧
      ExactDagFinalWorkPairLabeled input trial
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer base ∧
      ExactDagFinalWorkLabeled input trial
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer ∧
      ∀ (counter : Fin 64)
        (beforeSelected : counter.val ≤
          (exactOperationalTape input).search.selectedCounter.val),
        ExactDagProducerInstalled input trial
          (Q16DagProducer.mk (exactOperationalQ16InitialDigest input counter)
            (counter, ⟨0, by omega⟩)
            (bytes base ++ [domAbsorb, queryCandidateLabel,
              UInt8.ofNat counter.val])) := by
  obtain ⟨digest, workAnswer, base, workLookup, workAccepted, absorbLookup,
      baseExact⟩ := exact_operational_final_work_pair_lookups input
  let nonce := (exactOperationalTape input).messages.finalGrinding.selected
  let key := literalFinalWorkKey digest nonce
  obtain ⟨workActor, workMember⟩ :=
    exact_final_table_lookup_has_root_record input key.workInput workAnswer
      (by simpa [key, nonce] using workLookup)
  obtain ⟨absorbActor, absorbMember⟩ :=
    exact_final_table_lookup_has_root_record input key.absorbInput base
      (by simpa [key, nonce] using absorbLookup)
  let workRecord : UnifiedExposureRecord :=
    .machineFresh workActor key.workInput workAnswer
  let absorbRecord : UnifiedExposureRecord :=
    .machineFresh absorbActor key.absorbInput base
  have recordsDifferent : workRecord ≠ absorbRecord := by
    intro equal
    have optionalInputsEqual : some key.workInput = some key.absorbInput := by
      simpa [workRecord, absorbRecord, causalInput?] using
        congrArg causalInput? equal
    have inputsEqual : key.workInput = key.absorbInput :=
      Option.some.inj optionalInputsEqual
    exact key.absorbInput_ne_workInput inputsEqual.symm
  have pairOrder := distinct_members_have_strict_list_order
    (exactFixedRootRecords input.package.root) workRecord absorbRecord
    recordsDifferent (by simpa [workRecord] using workMember)
      (by simpa [absorbRecord] using absorbMember)
  rcases pairOrder with
      ⟨prior, middle, later, workFirst⟩ |
      ⟨prior, middle, later, absorbFirst⟩
  · have trialBound : prior.length <
        unifiedFull256ExposureCap parameters :=
      exact_root_strict_prefix_lt_exposure_cap input prior
        (middle ++ absorbRecord :: later) workRecord (by
          simpa only [List.cons_append, List.append_assoc] using workFirst)
    let trial : ExactCompilerExposureTrial parameters :=
      ⟨prior.length, trialBound⟩
    have pairLabeled : ExactDagFinalWorkPairLabeled input trial key
        workAnswer base := by
      refine Or.inl ⟨prior, middle, later, workActor, absorbActor, ?_, rfl⟩
      simpa [workRecord, absorbRecord, key] using workFirst
    let basePrefix := prior ++ workRecord :: middle ++ [absorbRecord]
    have pairExact : exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh workActor
            (literalFinalWorkKey digest nonce).workInput workAnswer :
            UnifiedExposureRecord) :: middle ++
          (.machineFresh absorbActor
            (literalFinalWorkKey digest nonce).absorbInput base :
            UnifiedExposureRecord) :: later := by
      simpa [workRecord, absorbRecord, key] using workFirst
    have tracked : Q16DagTracksBase
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial) basePrefix
          (exactDagCandidateInitialState input)).memory key base := by
      have ready := exact_dag_work_then_absorb_tracks_base input digest
        workAnswer base nonce trial prior middle later workActor absorbActor
        (by rfl) pairExact
      simpa [basePrefix, workRecord, absorbRecord, key] using ready
    have workLabeled : ExactDagFinalWorkLabeled input trial
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer := by
      refine ⟨prior, middle ++ absorbRecord :: later, workActor, ?_, ?_⟩
      · simpa [workRecord, key, nonce, List.cons_append,
          List.append_assoc] using workFirst
      · let beforeWork := indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial) prior
          (exactDagCandidateInitialState input)
        have beforeIndex : beforeWork.exposureIndex = trial.val := by
          have count := indexed_state_after_records_exposure_index
            transitionFuel (exactDagTrialController transitionFuel trial) prior
              (exactDagCandidateInitialState input)
          simpa [beforeWork, exactDagCandidateInitialState, trial] using count
        have beforeInactive : beforeWork.memory = inactiveDagMemory := by
          apply dag_memory_stays_inactive_before_anchor transitionFuel
            trial.val prior (exactDagCandidateInitialState input)
          · simp [exactDagCandidateInitialState, trial]
          · simp [exactDagCandidateInitialState]
        have pairAtWork : exactFixedRootRecords input.package.root =
            prior ++ workRecord :: (middle ++ absorbRecord :: later) := by
          simpa only [List.cons_append, List.append_assoc] using workFirst
        have aligned : unifiedRecordAtAnswer transitionFuel beforeWork.cursor
            workAnswer = workRecord := by
          have rootAligned := exact_root_records_aligned_for_dag_controller
            input trial.val prior workRecord
              (middle ++ absorbRecord :: later) pairAtWork
          simpa [beforeWork, workRecord, UnifiedExposureRecord.answer,
            exactDagTrialController] using rootAligned
        have inputExact : unifiedInputBeforeAnswer? transitionFuel
            beforeWork.cursor = some key.workInput :=
          aligned_machine_record_has_exact_input transitionFuel
            beforeWork.cursor workActor key.workInput workAnswer (by
              simpa [workRecord] using aligned)
        change dagCandidatePreferredSlot transitionFuel trial.val beforeWork =
          some none
        simp [dagCandidatePreferredSlot, inputExact, dagPreferredSlotForInput,
          dagRawPreferredSlot, beforeIndex, beforeInactive, inactiveDagMemory,
          key, nonce]
    refine ⟨digest, workAnswer, base, trial, workAccepted, baseExact,
      pairLabeled, workLabeled, ?_⟩
    intro counter beforeSelected
    obtain ⟨absorbPrior, candidateMiddle, candidateLater,
        firstAbsorbActor, candidateActor, absorbBeforeCandidate⟩ :=
      exact_q16_absorb_before_candidate_records transitionRoom input digest
        base nonce (by simpa [key, nonce] using absorbLookup) baseExact counter
        beforeSelected
    let prefixBeforeAbsorb := prior ++ workRecord :: middle
    have pairAtAbsorb : exactFixedRootRecords input.package.root =
        prefixBeforeAbsorb ++ absorbRecord :: later := by
      simpa only [prefixBeforeAbsorb, List.cons_append,
        List.append_assoc] using workFirst
    have prefixExact : prefixBeforeAbsorb = absorbPrior := by
      apply mapped_nodup_selected_prefix_eq causalInput?
        (exactFixedRootRecords input.package.root) prefixBeforeAbsorb later
          absorbPrior (candidateMiddle ++
            (.machineFresh candidateActor
              (bytes base ++ [domAbsorb, queryCandidateLabel,
                UInt8.ofNat counter.val])
              (exactOperationalQ16InitialDigest input counter) :
              UnifiedExposureRecord) :: candidateLater)
          absorbRecord
          (.machineFresh firstAbsorbActor
            (literalFinalWorkKey digest nonce).absorbInput base)
        (exact_root_record_causal_inputs_nodup input) pairAtAbsorb
        (by simpa only [List.cons_append, List.append_assoc] using
          absorbBeforeCandidate)
      simp [absorbRecord, key, causalInput?]
    subst absorbPrior
    have absorbRecordExact : absorbRecord =
        (.machineFresh firstAbsorbActor
          (literalFinalWorkKey digest nonce).absorbInput base :
          UnifiedExposureRecord) := by
      have suffixExact : absorbRecord :: later =
          (.machineFresh firstAbsorbActor
            (literalFinalWorkKey digest nonce).absorbInput base :
            UnifiedExposureRecord) ::
            (candidateMiddle ++
              (.machineFresh candidateActor
                (bytes base ++ [domAbsorb, queryCandidateLabel,
                  UInt8.ofNat counter.val])
                (exactOperationalQ16InitialDigest input counter) :
                UnifiedExposureRecord) :: candidateLater) := by
        exact List.append_cancel_left (pairAtAbsorb.symm.trans (by
          simpa only [List.cons_append, List.append_assoc] using
            absorbBeforeCandidate))
      exact (List.cons.inj suffixExact).1
    rw [← absorbRecordExact] at absorbBeforeCandidate
    apply exact_dag_candidate_installed_after_tracked_prefix input trial key
      base (exactOperationalQ16InitialDigest input counter) counter basePrefix
      candidateMiddle candidateLater candidateActor tracked
    simpa [basePrefix, prefixBeforeAbsorb, absorbRecord, key,
      List.append_assoc] using absorbBeforeCandidate
  · have trialBound : prior.length <
        unifiedFull256ExposureCap parameters :=
      exact_root_strict_prefix_lt_exposure_cap input prior
        (middle ++ workRecord :: later) absorbRecord (by
          simpa only [List.cons_append, List.append_assoc] using absorbFirst)
    let trial : ExactCompilerExposureTrial parameters :=
      ⟨prior.length, trialBound⟩
    have pairLabeled : ExactDagFinalWorkPairLabeled input trial key
        workAnswer base := by
      refine Or.inr ⟨prior, middle, later, workActor, absorbActor, ?_, rfl⟩
      simpa [workRecord, absorbRecord, key] using absorbFirst
    let basePrefix := prior ++ [absorbRecord]
    have absorbExact : exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh absorbActor
            (literalFinalWorkKey digest nonce).absorbInput base :
            UnifiedExposureRecord) :: (middle ++ workRecord :: later) := by
      simpa [absorbRecord, key, List.cons_append, List.append_assoc] using
        absorbFirst
    have tracked : Q16DagTracksBase
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial) basePrefix
          (exactDagCandidateInitialState input)).memory key base := by
      have ready := exact_dag_absorb_anchor_tracks_base input digest base nonce
        trial prior (middle ++ workRecord :: later) absorbActor (by rfl)
        absorbExact
      simpa [basePrefix, absorbRecord, key] using ready
    let workPrior := prior ++ absorbRecord :: middle
    let beforeWork := indexedStateAfterRecords transitionFuel
      (exactDagTrialController transitionFuel trial) workPrior
      (exactDagCandidateInitialState input)
    have beforeWorkTracked : Q16DagTracksBaseBeforeWork beforeWork.memory
        key base := by
      let afterAbsorb := indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) basePrefix
        (exactDagCandidateInitialState input)
      have afterAbsorbTracked : Q16DagTracksBaseBeforeWork afterAbsorb.memory
          key base := by
        have ready := exact_dag_absorb_anchor_tracks_base_before_work input
          digest base nonce trial prior (middle ++ workRecord :: later)
            absorbActor (by rfl) absorbExact
        simpa [afterAbsorb, basePrefix, absorbRecord, key] using ready
      have segmentDecomposition : exactFixedRootRecords input.package.root =
          basePrefix ++ middle ++ (workRecord :: later) := by
        simpa [basePrefix, List.cons_append, List.append_assoc] using
          absorbFirst
      have fullAligned := exact_root_records_aligned_for_dag_controller input
        trial.val
      have middleAlignedRaw := indexed_records_aligned_segment transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactDagCandidateInitialState input)
        (exactFixedRootRecords input.package.root) basePrefix middle
          (workRecord :: later) fullAligned segmentDecomposition
      have middleAligned : IndexedRecordsAligned transitionFuel
          (exactDagTrialController transitionFuel trial) afterAbsorb middle := by
        simpa [afterAbsorb] using middleAlignedRaw
      have middleOnly := only_machine_fresh_records_segment
        (exactFixedRootRecords input.package.root) basePrefix middle
          (workRecord :: later) (exact_root_records_only_machine_fresh input)
            segmentDecomposition
      have middleAvoidsRaw := strict_record_middle_avoids_second_input
        (exactFixedRootRecords input.package.root) prior middle later
          absorbRecord workRecord (exact_root_record_causal_inputs_nodup input)
            absorbFirst
      have middleAvoids : ∀ record ∈ middle,
          causalInput? record ≠ some key.workInput := by
        intro record member
        simpa [workRecord, causalInput?] using
          middleAvoidsRaw record member
      have preserved := aligned_machine_records_preserve_dag_base_before_work
        transitionFuel trial.val key base middle afterAbsorb middleAligned
          middleOnly middleAvoids afterAbsorbTracked
      simpa [beforeWork, workPrior, afterAbsorb, basePrefix,
        indexed_state_after_records_append, exactDagTrialController] using
          preserved
    have workLabeled : ExactDagFinalWorkLabeled input trial
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer := by
      refine ⟨workPrior, later, workActor, ?_, ?_⟩
      · simpa [workPrior, workRecord, key, nonce, List.cons_append,
          List.append_assoc] using absorbFirst
      · have pairAtWork : exactFixedRootRecords input.package.root =
            workPrior ++ workRecord :: later := by
          simpa [workPrior, List.cons_append, List.append_assoc] using
            absorbFirst
        have aligned : unifiedRecordAtAnswer transitionFuel beforeWork.cursor
            workAnswer = workRecord := by
          have rootAligned := exact_root_records_aligned_for_dag_controller
            input trial.val workPrior workRecord later pairAtWork
          simpa [beforeWork, workRecord, UnifiedExposureRecord.answer,
            exactDagTrialController] using rootAligned
        have inputExact : unifiedInputBeforeAnswer? transitionFuel
            beforeWork.cursor = some key.workInput :=
          aligned_machine_record_has_exact_input transitionFuel
            beforeWork.cursor workActor key.workInput workAnswer (by
              simpa [workRecord] using aligned)
        have workSlotSound : Q16DagWorkSlotSound beforeWork.memory := by
          have preserved := dag_indexed_state_preserves_work_slot_sound
            transitionFuel trial.val workPrior
              (exactDagCandidateInitialState input)
                inactive_dag_memory_work_slot_sound
          simpa [beforeWork, exactDagTrialController] using preserved
        have noneFresh : (none : FinalWorkQ16DigestSlot) ∉
            beforeWork.memory.usedSlots := by
          simpa [Q16DagWorkSlotSound, beforeWorkTracked.1] using workSlotSound
        change dagCandidatePreferredSlot transitionFuel trial.val beforeWork =
          some none
        simp [dagCandidatePreferredSlot, inputExact, dagPreferredSlotForInput,
          dagRawPreferredSlot, beforeWorkTracked.1, noneFresh]
    refine ⟨digest, workAnswer, base, trial, workAccepted, baseExact,
      pairLabeled, workLabeled, ?_⟩
    intro counter beforeSelected
    obtain ⟨absorbPrior, candidateMiddle, candidateLater,
        firstAbsorbActor, candidateActor, absorbBeforeCandidate⟩ :=
      exact_q16_absorb_before_candidate_records transitionRoom input digest
        base nonce (by simpa [key, nonce] using absorbLookup) baseExact counter
        beforeSelected
    have pairAtAbsorb : exactFixedRootRecords input.package.root =
        prior ++ absorbRecord :: (middle ++ workRecord :: later) := by
      simpa only [List.cons_append, List.append_assoc] using absorbFirst
    have prefixExact : prior = absorbPrior := by
      apply mapped_nodup_selected_prefix_eq causalInput?
        (exactFixedRootRecords input.package.root) prior
          (middle ++ workRecord :: later) absorbPrior
          (candidateMiddle ++
            (.machineFresh candidateActor
              (bytes base ++ [domAbsorb, queryCandidateLabel,
                UInt8.ofNat counter.val])
              (exactOperationalQ16InitialDigest input counter) :
              UnifiedExposureRecord) :: candidateLater)
          absorbRecord
          (.machineFresh firstAbsorbActor
            (literalFinalWorkKey digest nonce).absorbInput base)
        (exact_root_record_causal_inputs_nodup input) pairAtAbsorb
        (by simpa only [List.cons_append, List.append_assoc] using
          absorbBeforeCandidate)
      simp [absorbRecord, key, causalInput?]
    subst absorbPrior
    have absorbRecordExact : absorbRecord =
        (.machineFresh firstAbsorbActor
          (literalFinalWorkKey digest nonce).absorbInput base :
          UnifiedExposureRecord) := by
      have suffixExact : absorbRecord :: (middle ++ workRecord :: later) =
          (.machineFresh firstAbsorbActor
            (literalFinalWorkKey digest nonce).absorbInput base :
            UnifiedExposureRecord) ::
            (candidateMiddle ++
              (.machineFresh candidateActor
                (bytes base ++ [domAbsorb, queryCandidateLabel,
                  UInt8.ofNat counter.val])
                (exactOperationalQ16InitialDigest input counter) :
                UnifiedExposureRecord) :: candidateLater) := by
        exact List.append_cancel_left (pairAtAbsorb.symm.trans (by
          simpa only [List.cons_append, List.append_assoc] using
            absorbBeforeCandidate))
      exact (List.cons.inj suffixExact).1
    rw [← absorbRecordExact] at absorbBeforeCandidate
    apply exact_dag_candidate_installed_after_tracked_prefix input trial key
      base (exactOperationalQ16InitialDigest input counter) counter basePrefix
      candidateMiddle candidateLater candidateActor tracked
    simpa [basePrefix, absorbRecord, key, List.append_assoc] using
      absorbBeforeCandidate

/-- If an installed producer is strictly earlier than a dependent fresh
coordinate, it is present in the exact pre-answer state of that coordinate. -/
theorem exact_dag_installed_producer_available_before_ordered_child
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
    (producer : Q16DagProducer)
    (childInput : ShaInput) (childAnswer : Digest256)
    (installed : ExactDagProducerInstalled input trial producer)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producer.sourceInput, producer.digest) :: middle ++
          (childInput, childAnswer) :: after) :
    ∃ prior middle later producerActor childActor,
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh producerActor producer.sourceInput producer.digest :
            UnifiedExposureRecord) :: middle ++
          (.machineFresh childActor childInput childAnswer :
            UnifiedExposureRecord) :: later ∧
      producer ∈
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial)
          (prior ++
            (.machineFresh producerActor producer.sourceInput producer.digest :
              UnifiedExposureRecord) :: middle)
          (exactDagCandidateInitialState input)).memory.producers := by
  obtain ⟨before, middle, after, pairExact⟩ := ordered
  obtain ⟨prior, between, later, producerActor, childActor, recordsExact⟩ :=
    exact_root_pair_order_lifts_to_records input producer.sourceInput
      childInput producer.digest childAnswer before middle after pairExact
  let producerRecord : UnifiedExposureRecord :=
    .machineFresh producerActor producer.sourceInput producer.digest
  let childRecord : UnifiedExposureRecord :=
    .machineFresh childActor childInput childAnswer
  have installedAfter : producer ∈
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (prior ++ [producerRecord])
        (exactDagCandidateInitialState input)).memory.producers := by
    apply installed prior (between ++ childRecord :: later) producerActor
    simpa only [producerRecord, childRecord, List.cons_append,
      List.append_assoc] using recordsExact
  let afterProducer := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial)
    (prior ++ [producerRecord]) (exactDagCandidateInitialState input)
  have growth : afterProducer.memory.producers <+:
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) between
        afterProducer).memory.producers := by
    simpa [exactDagTrialController] using
      dag_indexed_state_producers_prefix transitionFuel trial.val between
        afterProducer
  have available : producer ∈
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (prior ++ producerRecord :: between)
        (exactDagCandidateInitialState input)).memory.producers := by
    have member := growth.subset (by
      simpa [afterProducer] using installedAfter)
    simpa [afterProducer, indexed_state_after_records_append] using member
  exact ⟨prior, between, later, producerActor, childActor, by
    simpa only [producerRecord, childRecord] using recordsExact, available⟩

/-- An advance child strictly below an installed parent is itself installed
at its unique exact root record. This is the recursive edge of the causal DAG. -/
theorem exact_dag_advance_installs_next_producer
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
    (parent : Q16DagProducer) (advanced : Digest256)
    (bounded : parent.slot.2.val + 1 < 8)
    (installed : ExactDagProducerInstalled input trial parent)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (parent.sourceInput, parent.digest) :: middle ++
          (gammaAdvanceInput parent.digest, advanced) :: after) :
    ExactDagProducerInstalled input trial
      (Q16DagProducer.mk advanced
        (parent.slot.1, ⟨parent.slot.2.val + 1, bounded⟩)
        (gammaAdvanceInput parent.digest)) := by
  let nextProducer := Q16DagProducer.mk advanced
    (parent.slot.1, ⟨parent.slot.2.val + 1, bounded⟩)
    (gammaAdvanceInput parent.digest)
  intro arbitraryPrior arbitraryLater arbitraryActor arbitraryExact
  obtain ⟨prior, between, later, producerActor, childActor,
      recordsExact, parentMember⟩ :=
    exact_dag_installed_producer_available_before_ordered_child input trial
      parent (gammaAdvanceInput parent.digest) advanced installed ordered
  let producerRecord : UnifiedExposureRecord :=
    .machineFresh producerActor parent.sourceInput parent.digest
  let childRecord : UnifiedExposureRecord :=
    .machineFresh childActor (gammaAdvanceInput parent.digest) advanced
  let childPrefix := prior ++ producerRecord :: between
  have canonicalChildExact : exactFixedRootRecords input.package.root =
      childPrefix ++ childRecord :: later := by
    simpa only [childPrefix, producerRecord, childRecord, List.cons_append,
      List.append_assoc] using recordsExact
  have prefixExact : childPrefix = arbitraryPrior := by
    apply mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root) childPrefix later
        arbitraryPrior arbitraryLater childRecord
        (.machineFresh arbitraryActor nextProducer.sourceInput
          nextProducer.digest)
      (exact_root_record_causal_inputs_nodup input) canonicalChildExact
      (by simpa only [nextProducer] using arbitraryExact)
    simp [childRecord, nextProducer, causalInput?]
  subst arbitraryPrior
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) childPrefix
    (exactDagCandidateInitialState input)
  have reachedMember : parent ∈ reached.memory.producers := by
    simpa [reached, childPrefix, producerRecord, childRecord] using parentMember
  have invariant : Q16DagMemoryProducerInvariant reached.memory := by
    simpa [reached] using
      exact_dag_candidate_prefix_producer_invariant input trial childPrefix
        (childRecord :: later) canonicalChildExact
  have digestNodup :
      (reached.memory.producers.map Q16DagProducer.digest).Nodup := by
    simpa [reached] using
      exact_dag_candidate_prefix_producer_digests_nodup input trial childPrefix
        (childRecord :: later) canonicalChildExact
  obtain ⟨key, base, workSeen, anchorExact, baseExact⟩ :=
    producer_member_implies_tracks_some_base reached.memory parent invariant
      reachedMember
  have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor advanced =
      .machineFresh arbitraryActor nextProducer.sourceInput
        nextProducer.digest := by
    have rootAligned := exact_root_records_aligned_for_dag_controller input
      trial.val childPrefix
        (.machineFresh arbitraryActor nextProducer.sourceInput
          nextProducer.digest)
        arbitraryLater (by simpa only [nextProducer] using arbitraryExact)
    simpa [reached, exactDagTrialController, nextProducer,
      UnifiedExposureRecord.answer] using rootAligned
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaAdvanceInput parent.digest) := by
    have exact := aligned_machine_record_has_exact_input transitionFuel
      reached.cursor arbitraryActor nextProducer.sourceInput
        nextProducer.digest aligned
    simpa [nextProducer] using exact
  have installedMemory := dag_memory_after_advance_contains_producer trial.val
    reached.exposureIndex reached.memory key workSeen base advanced parent
      bounded anchorExact baseExact digestNodup reachedMember
  change nextProducer ∈
    (indexedStateAfterRecords transitionFuel
      (exactDagTrialController transitionFuel trial)
      (childPrefix ++
        [(.machineFresh arbitraryActor nextProducer.sourceInput
          nextProducer.digest : UnifiedExposureRecord)])
      (exactDagCandidateInitialState input)).memory.producers
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil]
  change nextProducer ∈
    (dagCandidateAfterMemory transitionFuel trial.val reached advanced).producers
  unfold dagCandidateAfterMemory
  rw [inputExact]
  simpa [nextProducer, gammaAdvanceInput] using installedMemory

/-- The output child of an installed producer receives that producer's exact
slot and therefore routes to its literal root answer. -/
theorem exact_dag_installed_producer_routes_ordered_output
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
    (producer : Q16DagProducer) (output : Digest256)
    (installed : ExactDagProducerInstalled input trial producer)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producer.sourceInput, producer.digest) :: middle ++
          (gammaOutputInput producer.digest, output) :: after)
    (residualEnough :
      residualTraceSteps (exactDagCandidateRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 513) :
    causalRoutedAnswer? (some producer.slot)
        (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
          (exactPlainRomCursor configuration sample.1).erase)
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      some output := by
  obtain ⟨prior, between, later, producerActor, outputActor,
      recordsExact, producerMember⟩ :=
    exact_dag_installed_producer_available_before_ordered_child input trial
      producer (gammaOutputInput producer.digest) output installed ordered
  let producerRecord : UnifiedExposureRecord :=
    .machineFresh producerActor producer.sourceInput producer.digest
  let outputRecord : UnifiedExposureRecord :=
    .machineFresh outputActor (gammaOutputInput producer.digest) output
  let outputPrefix := prior ++ producerRecord :: between
  have decomposition : exactFixedRootRecords input.package.root =
      outputPrefix ++ outputRecord :: later := by
    simpa only [outputPrefix, producerRecord, outputRecord, List.cons_append,
      List.append_assoc] using recordsExact
  have preferred := exact_dag_q16_output_has_preferred_slot input trial
    outputPrefix later outputActor output producer (by
      simpa [outputRecord, gammaOutputInput] using decomposition) (by
      simpa [outputPrefix, producerRecord, outputRecord] using producerMember)
  exact exact_dag_candidate_router_routes_selected_root_answer input trial
    outputPrefix later outputActor (gammaOutputInput producer.digest) output
      (some producer.slot) (by simpa [outputRecord] using decomposition)
      residualEnough preferred

/-- Recursive exact-root fold. Every consumed output in an ordered duplex
chain is routed at the slot determined by its counter and block offset. -/
theorem exact_ordered_q16_chain_routes
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
    (counter : Fin 64) :
    ∀ {producerInput : ShaInput} {digest : Digest256}
      {outputs advances : List Digest256}
      (block : Fin 8)
      (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
        advances)
      (lengthCap : block.val + outputs.length ≤ 8)
      (installed : ExactDagProducerInstalled input trial
        (Q16DagProducer.mk digest (counter, block) producerInput))
      (residualEnough :
        residualTraceSteps (exactDagCandidateRootLabels input trial) ≤
          (exactCompilerTargetCaps parameters).length - 513),
      ∀ index (inOutputs : index < outputs.length),
        causalRoutedAnswer?
            (some (counter,
              ⟨block.val + index,
                (Nat.add_lt_add_left inOutputs block.val).trans_le
                  lengthCap⟩))
            (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
              (exactPlainRomCursor configuration sample.1).erase)
            (finalWorkQ16NamedSlotInputTape
              (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
          some outputs[index] := by
  intro producerInput digest outputs advances block chain lengthCap installed
    residualEnough
  induction chain generalizing block with
  | done producerInput digest producerFound =>
      intro index inOutputs
      simp at inOutputs
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail ih =>
      intro index inOutputs
      let producer := Q16DagProducer.mk digest (counter, block) producerInput
      have headRouted :=
        exact_dag_installed_producer_routes_ordered_output input trial producer
          output installed (by
            simpa [producer, gammaOutputInput] using producerBeforeOutput)
          residualEnough
      cases index with
      | zero =>
          change causalRoutedAnswer? (some (counter, block))
              (exactCompilerExposureTrialDagRouter parameters transitionFuel
                trial (exactPlainRomCursor configuration sample.1).erase)
              (finalWorkQ16NamedSlotInputTape
                (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
            some output
          exact headRouted
      | succ index =>
          have indexInTail : index < outputs.length := by
            simpa using inOutputs
          have nextBound : block.val + 1 < 8 := by
            have positive : 0 < outputs.length := Nat.zero_lt_of_lt indexInTail
            simp only [List.length_cons] at lengthCap
            omega
          let nextBlock : Fin 8 := ⟨block.val + 1, nextBound⟩
          let nextProducer := Q16DagProducer.mk advanced
            (counter, nextBlock) (gammaAdvanceInput digest)
          have nextInstalled : ExactDagProducerInstalled input trial
              nextProducer := by
            have installedRaw := exact_dag_advance_installs_next_producer input
              trial producer advanced nextBound installed (by
                simpa [producer, gammaAdvanceInput] using
                  producerBeforeAdvance)
            simpa [producer, nextProducer, nextBlock] using installedRaw
          have tailLengthCap : nextBlock.val + outputs.length ≤ 8 := by
            simp [nextBlock]
            simp only [List.length_cons] at lengthCap
            omega
          have tailRouted := ih nextBlock tailLengthCap nextInstalled
            index indexInTail
          let goalBlock : Fin 8 :=
            ⟨block.val + (index + 1),
              (Nat.add_lt_add_left inOutputs block.val).trans_le lengthCap⟩
          let tailBlock : Fin 8 :=
            ⟨nextBlock.val + index,
              (Nat.add_lt_add_left indexInTail nextBlock.val).trans_le
                tailLengthCap⟩
          have blockExact : goalBlock = tailBlock := by
            apply Fin.ext
            simp only [goalBlock, tailBlock, nextBlock]
            omega
          have outputExact : (output :: outputs)[index + 1] =
              outputs[index] := by
            rfl
          change causalRoutedAnswer? (some (counter, goalBlock))
              (exactCompilerExposureTrialDagRouter parameters transitionFuel
                trial (exactPlainRomCursor configuration sample.1).erase)
              (finalWorkQ16NamedSlotInputTape
                (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
            some (output :: outputs)[index + 1]
          rw [blockExact, outputExact]
          exact tailRouted

/-! ## Accepted-source operational forest closure -/

/-- The exact branch-coordinate witness chosen from the accepted source run,
restricted to the candidates actually scanned by first-cap-203. -/
noncomputable def exactDagOperationalQ16CandidateBlocks
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Fin 64 → List Digest256 := fun counter =>
  if beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val then
    (exactOperationalQ16BranchCoordinates input counter
      beforeSelected).outputs
  else
    []

theorem exact_dag_operational_q16_candidate_blocks_length
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
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    (exactDagOperationalQ16CandidateBlocks input counter).length =
      ((exactOperationalTape input).search.outcome counter).blocksUsed := by
  rw [exactDagOperationalQ16CandidateBlocks, dif_pos beforeSelected]
  exact (exactOperationalQ16BranchCoordinates input counter
    beforeSelected).outputsLength

theorem exact_dag_operational_q16_candidate_blocks_decode
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
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    decodeCandidateOutcome counter
        (exactDagOperationalQ16CandidateBlocks input counter) =
      some ((exactOperationalTape input).search.outcome counter) := by
  rw [exactDagOperationalQ16CandidateBlocks, dif_pos beforeSelected]
  exact (exactOperationalQ16BranchCoordinates input counter
    beforeSelected).decoded

/-- The selected final-work component of the joint factorization is exactly
the `none` named slot of the causal router. -/
theorem exact_compiler_final_work_apply_eq_named_slot_coordinate
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    (exactCompilerCausalFinalWorkQ16Coordinates parameters router tape).2.1 =
      (router.coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters tape))).1
        ⟨none, Finset.mem_univ _⟩ := by
  rfl

theorem exact_compiler_final_work_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (answer : Digest256)
    (routed : causalRoutedAnswer? none router
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters tape)) = some answer) :
    (exactCompilerCausalFinalWorkQ16Coordinates parameters router tape).2.1 =
      answer := by
  rw [exact_compiler_final_work_apply_eq_named_slot_coordinate]
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (finalWorkQ16NamedSlotInputTape
      (exactCompilerFinalWorkQ16InputTape parameters tape))
    none (Finset.mem_univ _) answer routed

/-- Accepted production execution supplies one concrete restoration trial in
which every consumed q16 block is routed to its literal source answer. Thus
the online causal router realizes the same first-cap-203 search consumed by
the checked source execution. -/
theorem exact_compiler_accepted_dag_q16_operational_realization
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    ∃ (digest workAnswer base : Digest256)
        (trial : ExactCompilerExposureTrial parameters),
      FinalWork34Accepted workAnswer ∧
      base = (exactOperationalRawTrace input).q16BaseDigest ∧
      ExactDagFinalWorkPairLabeled input trial
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer base ∧
      ExactDagFinalWorkLabeled input trial
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        workAnswer ∧
      (exactCompilerCausalFinalWorkQ16Coordinates parameters
        (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
          (exactPlainRomCursor configuration sample.1).erase)
        sample.2).2.1 = workAnswer ∧
      OperationalQ16ForestRealization
        (exactOperationalTape input).frontierNodes
        (exactOperationalTape input).search
        (exactCompilerCausalFinalWorkQ16Coordinates parameters
          (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
            (exactPlainRomCursor configuration sample.1).erase)
          sample.2).2.2 := by
  obtain ⟨digest, workAnswer, base, trial, workAccepted, baseExact,
      pairLabeled, workLabeled, installed⟩ :=
    exact_compiler_accepted_dag_trial_installs_all_candidates transitionRoom
      input
  have residualEnough :
      residualTraceSteps (exactDagCandidateRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 513 :=
    exact_dag_candidate_root_residual_enough_of_programmed_cover input trial
      programmedCover
  have workLabeledExact := workLabeled
  obtain ⟨workPrior, workLater, workActor, workDecomposition,
      workPreferred⟩ := workLabeled
  have workRouted :
      causalRoutedAnswer? none
          (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
            (exactPlainRomCursor configuration sample.1).erase)
          (finalWorkQ16NamedSlotInputTape
            (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
        some workAnswer :=
    exact_dag_candidate_router_routes_selected_root_answer input trial
      workPrior workLater workActor
      (literalFinalWorkKey digest
        (exactOperationalTape input).messages.finalGrinding.selected).workInput
      workAnswer none workDecomposition residualEnough workPreferred
  have workCoordinate :
      (exactCompilerCausalFinalWorkQ16Coordinates parameters
        (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
          (exactPlainRomCursor configuration sample.1).erase)
        sample.2).2.1 = workAnswer :=
    exact_compiler_final_work_coordinate_eq_of_routed_lookup parameters
      (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase)
      sample.2 workAnswer workRouted
  have candidateLengthCap : ∀ counter,
      counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
      (exactDagOperationalQ16CandidateBlocks input counter).length ≤ 8 := by
    intro counter beforeSelected
    exact
      (exact_dag_operational_q16_candidate_blocks_length input counter
        beforeSelected).le.trans
        (candidate_outcome_blocks_cap
          ((exactOperationalTape input).search.outcome counter))
  have routedAll : ∀ counter
      (beforeSelected : counter.val ≤
        (exactOperationalTape input).search.selectedCounter.val),
      ∀ index
        (inBlocks : index <
          (exactDagOperationalQ16CandidateBlocks input counter).length),
        causalRoutedAnswer?
            (some (counter,
              ⟨index, Nat.lt_of_lt_of_le inBlocks
                (candidateLengthCap counter beforeSelected)⟩))
            (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
              (exactPlainRomCursor configuration sample.1).erase)
            (finalWorkQ16NamedSlotInputTape
              (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
          some ((exactDagOperationalQ16CandidateBlocks input counter)[index]) := by
    intro counter beforeSelected index inBlocks
    let coordinates := exactOperationalQ16BranchCoordinates input counter
      beforeSelected
    have chain : ExactRootOrderedQ16Chain input
        (bytes (exactOperationalRawTrace input).q16BaseDigest ++
          [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val])
        (exactOperationalQ16InitialDigest input counter)
        coordinates.outputs coordinates.advances := by
      simpa [coordinates] using
        exact_operational_q16_branch_has_exact_root_order transitionRoom input
          counter beforeSelected
    have firstInstalled : ExactDagProducerInstalled input trial
        (Q16DagProducer.mk
          (exactOperationalQ16InitialDigest input counter)
          (counter, ⟨0, by omega⟩)
          (bytes (exactOperationalRawTrace input).q16BaseDigest ++
            [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val])) := by
      simpa [baseExact] using installed counter beforeSelected
    have lengthCap : coordinates.outputs.length ≤ 8 := by
      rw [coordinates.outputsLength]
      exact candidate_outcome_blocks_cap
        ((exactOperationalTape input).search.outcome counter)
    have inCoordinates : index < coordinates.outputs.length := by
      simpa [coordinates, exactDagOperationalQ16CandidateBlocks,
        beforeSelected] using inBlocks
    have routed := exact_ordered_q16_chain_routes input trial counter
      (block := ⟨0, by omega⟩) chain (by simpa using lengthCap)
      firstInstalled residualEnough index inCoordinates
    have candidateBlocksExact :
        exactDagOperationalQ16CandidateBlocks input counter =
          coordinates.outputs := by
      simp only [exactDagOperationalQ16CandidateBlocks,
        dif_pos beforeSelected]
      rfl
    have valueExact :
        (exactDagOperationalQ16CandidateBlocks input counter)[index] =
          coordinates.outputs[index] := by
      simpa only [candidateBlocksExact]
    rw [valueExact]
    convert routed using 1
    congr 1
    congr 1
    congr 1
    apply Fin.ext
    simp
  have outcomeDecoded : ∀ counter,
      counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
      decodeCandidateOutcome counter
          (exactDagOperationalQ16CandidateBlocks input counter) =
        some ((exactOperationalTape input).search.outcome counter) := by
    intro counter beforeSelected
    exact exact_dag_operational_q16_candidate_blocks_decode input counter
      beforeSelected
  have frontierRealized : ∀ counter schedule,
      counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
      (exactOperationalTape input).search.outcome counter = .schedule schedule →
      semanticFrontierNodes (semanticScheduleOfOperational schedule) =
        (exactOperationalTape input).frontierNodes schedule := by
    intro counter schedule _beforeSelected _outcomeExact
    exact (frontierExact schedule).symm
  refine ⟨digest, workAnswer, base, trial, workAccepted, baseExact,
    pairLabeled, workLabeledExact, workCoordinate, ?_⟩
  exact exact_compiler_final_work_q16_operational_realization_of_used_lookups
    parameters
    (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration sample.1).erase)
    sample.2 (exactOperationalTape input).search
    (exactDagOperationalQ16CandidateBlocks input) candidateLengthCap routedAll
      outcomeDecoded frontierRealized

#print axioms mapped_nodup_selected_prefix_eq
#print axioms Q16DagTracksBase
#print axioms Q16DagTracksBaseBeforeWork
#print axioms Q16DagWorkSlotSound
#print axioms dag_memory_after_input_preserves_work_slot_sound
#print axioms dag_candidate_after_memory_preserves_work_slot_sound
#print axioms dag_indexed_state_preserves_work_slot_sound
#print axioms dag_memory_after_nonwork_preserves_base_before_work
#print axioms dag_candidate_after_nonwork_preserves_base_before_work
#print axioms aligned_machine_records_preserve_dag_base_before_work
#print axioms dag_memory_after_input_preserves_tracks_base
#print axioms dag_candidate_after_memory_preserves_tracks_base
#print axioms dag_indexed_state_preserves_tracks_base
#print axioms dag_memory_stays_inactive_before_anchor
#print axioms dag_labeled_records_before_anchor_all_residual
#print axioms exact_dag_absorb_anchor_tracks_base
#print axioms exact_dag_absorb_anchor_tracks_base_before_work
#print axioms exact_dag_work_then_absorb_tracks_base
#print axioms producer_member_implies_tracks_some_base
#print axioms ExactDagProducerInstalled
#print axioms ExactDagFinalWorkPairLabeled
#print axioms exact_dag_final_work_pair_labeled_prefix_all_residual
#print axioms ExactDagFinalWorkLabeled
#print axioms exact_dag_candidate_installed_after_tracked_prefix
#print axioms exact_compiler_accepted_dag_trial_installs_all_candidates
#print axioms exact_dag_installed_producer_available_before_ordered_child
#print axioms exact_dag_advance_installs_next_producer
#print axioms exact_dag_installed_producer_routes_ordered_output
#print axioms exact_ordered_q16_chain_routes
#print axioms exactDagOperationalQ16CandidateBlocks
#print axioms exact_dag_operational_q16_candidate_blocks_length
#print axioms exact_dag_operational_q16_candidate_blocks_decode
#print axioms exact_compiler_final_work_apply_eq_named_slot_coordinate
#print axioms exact_compiler_final_work_coordinate_eq_of_routed_lookup
#print axioms exact_compiler_accepted_dag_q16_operational_realization

end

end AspisK1.V7Tag73ExactDagQ16ChainRouting
