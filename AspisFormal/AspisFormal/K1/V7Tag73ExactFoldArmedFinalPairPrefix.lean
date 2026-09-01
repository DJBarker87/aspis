import AspisFormal.K1.V7Tag73ExactDagQ16ChainRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedFinalWorkRouting
import AspisFormal.K1.V7Tag73FoldArmedWorkConditionedPrefix

/-!
# No-q16 fold-armed prefix through the final nonce absorb

The final-work pair may first be exposed in either order.  In the absorb-first
case the useful prefix stops at that anchor.  In the work-first case it runs
through the later absorb record; every strict prefix is either still before
the anchor or tracks the selected work key without a q16 base.  Consequently
the complete fold-armed controller emits no q16 label on either prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73ExactFoldArmedFinalPairPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldArmedFinalWorkRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Every pre-answer state of the work-first prefix ending at the selected
nonce absorb has an empty q16 producer inventory. -/
theorem exact_work_first_prefix_has_no_q16_producers
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
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh workActor
          (literalFinalWorkKey digest nonce).workInput workAnswer :
          UnifiedExposureRecord) :: middle ++
        (.machineFresh absorbActor
          (literalFinalWorkKey digest nonce).absorbInput base :
          UnifiedExposureRecord) :: later) :
    let workRecord : UnifiedExposureRecord :=
      .machineFresh workActor
        (literalFinalWorkKey digest nonce).workInput workAnswer
    let absorbRecord : UnifiedExposureRecord :=
      .machineFresh absorbActor
        (literalFinalWorkKey digest nonce).absorbInput base
    let completed := prior ++ workRecord :: middle ++ [absorbRecord]
    ∀ before current after,
      completed = before ++ current :: after →
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) before
        (exactDagCandidateInitialState input)).memory.producers = [] := by
  dsimp
  intro before current after completedExact
  let key := literalFinalWorkKey digest nonce
  let workRecord : UnifiedExposureRecord :=
    .machineFresh workActor key.workInput workAnswer
  let absorbRecord : UnifiedExposureRecord :=
    .machineFresh absorbActor key.absorbInput base
  let dagState : IndexedUnifiedExposureState
      (globalFull256OracleCallCap parameters) FinalWorkQ16DagMemory :=
    indexedStateAfterRecords transitionFuel
      (exactDagTrialController transitionFuel trial) before
        (exactDagCandidateInitialState input)
  change dagState.memory.producers = []
  have beforeLt : before.length <
      (prior ++ workRecord :: middle ++ [absorbRecord]).length := by
    have lengths := congrArg List.length completedExact
    simp only [List.length_append, List.length_cons]
      at lengths ⊢
    omega
  have beforePrefix : before <+:
      (prior ++ workRecord :: middle ++ [absorbRecord]) := by
    refine ⟨current :: after, ?_⟩
    simpa only [List.cons_append, List.append_assoc] using completedExact.symm
  have rootBefore : exactFixedRootRecords input.package.root =
      before ++ current :: (after ++ later) := by
    rw [rootExact]
    simpa [key, workRecord, absorbRecord, List.append_assoc] using
      congrArg (fun records => records ++ later) completedExact
  have invariant : Q16DagMemoryProducerInvariant dagState.memory := by
    simpa [dagState] using exact_dag_candidate_prefix_producer_invariant input
      trial before (current :: after ++ later) (by
        simpa only [List.cons_append, List.append_assoc] using rootBefore)
  by_cases beforeAnchor : before.length ≤ prior.length
  · have inactive : dagState.memory = inactiveDagMemory := by
      apply dag_memory_stays_inactive_through_anchor_prefix transitionFuel
        trial.val before (exactDagCandidateInitialState input)
      · simp [exactDagCandidateInitialState, trialExact, beforeAnchor]
      · simp [exactDagCandidateInitialState]
    exact invariant.noBaseHasNoProducers (by simp [inactive, inactiveDagMemory])
  · have priorPrefixWhole : prior <+:
        (prior ++ workRecord :: middle ++ [absorbRecord]) := by
      simpa only [List.cons_append, List.append_assoc] using
        (List.prefix_append prior (workRecord :: middle ++ [absorbRecord]))
    have priorPrefixBefore : prior <+: before := by
      apply List.prefix_iff_eq_take.mpr
      have priorTake := List.prefix_iff_eq_take.mp priorPrefixWhole
      have beforeTake := List.prefix_iff_eq_take.mp beforePrefix
      rw [beforeTake, List.take_take, Nat.min_eq_left (by omega)]
      exact priorTake
    obtain ⟨rest, beforeEq⟩ := priorPrefixBefore
    cases rest with
    | nil =>
        have lengths := congrArg List.length beforeEq
        simp at lengths
        omega
    | cons first tail =>
        have tailPrefix : first :: tail <+:
            workRecord :: middle ++ [absorbRecord] := by
          have dropped := beforePrefix.drop prior.length
          rw [← beforeEq] at dropped
          simpa using dropped
        obtain ⟨remainder, prefixEq⟩ := tailPrefix
        have firstEq : first = workRecord := by
          have heads := congrArg List.head? prefixEq
          simpa using heads
        have tailOnly : tail <+: middle ++ [absorbRecord] := by
          refine ⟨remainder, ?_⟩
          have tails := congrArg List.tail prefixEq
          simpa using tails
        subst first
        have tailBound : tail.length ≤ middle.length := by
          have beforeLength := congrArg List.length beforeEq
          simp only [List.length_append, List.length_cons] at beforeLength
          simp only [List.length_append, List.length_cons,
            List.length_nil] at beforeLt
          omega
        have tailPrefixMiddle : tail <+: middle :=
          (List.isPrefix_append_of_length tailBound).mp tailOnly
        obtain ⟨suffix, middleEq⟩ := tailPrefixMiddle
        have tracked : Q16DagTracksWithoutBase dagState.memory key := by
          have source :=
            exact_dag_work_then_absorb_middle_prefix_without_base input digest
              workAnswer base nonce trial prior middle later tail suffix
                workActor absorbActor trialExact rootExact (by
                  simpa using middleEq.symm)
          change Q16DagTracksWithoutBase
            (indexedStateAfterRecords transitionFuel
              (exactDagTrialController transitionFuel trial) before
              (exactDagCandidateInitialState input)).memory key
          rw [← beforeEq]
          simpa [dagState, key, workRecord] using source
        obtain ⟨_workSeen, _anchorExact, baseNone⟩ := tracked
        exact invariant.noBaseHasNoProducers baseNone

/-- In the absorb-first order the useful prefix ends at the anchor itself,
so every pre-answer state is still the inactive DAG state. -/
theorem exact_absorb_first_prefix_has_no_q16_producers
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
    (key : RawFinalWorkKey) (base : Digest256)
    (trial : ExactCompilerExposureTrial parameters)
    (prior : List UnifiedExposureRecord) (absorbActor : QueryActor)
    (trialExact : trial.val = prior.length) :
    let absorbRecord : UnifiedExposureRecord :=
      .machineFresh absorbActor key.absorbInput base
    let completed := prior ++ [absorbRecord]
    ∀ before current after,
      completed = before ++ current :: after →
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) before
        (exactDagCandidateInitialState input)).memory.producers = [] := by
  dsimp
  intro before current after completedExact
  let dagState : IndexedUnifiedExposureState
      (globalFull256OracleCallCap parameters) FinalWorkQ16DagMemory :=
    indexedStateAfterRecords transitionFuel
      (exactDagTrialController transitionFuel trial) before
        (exactDagCandidateInitialState input)
  change dagState.memory.producers = []
  have beforeAnchor : before.length ≤ prior.length := by
    have lengths : prior.length + 1 =
        before.length + (after.length + 1) := by
      simpa only [List.length_append, List.length_cons,
        List.length_nil, Nat.add_zero] using
          congrArg List.length completedExact
    omega
  have inactive : dagState.memory = inactiveDagMemory := by
    apply dag_memory_stays_inactive_through_anchor_prefix transitionFuel
      trial.val before (exactDagCandidateInitialState input)
    · simp [exactDagCandidateInitialState, trialExact, beforeAnchor]
    · simp [exactDagCandidateInitialState]
  simp [inactive, inactiveDagMemory]

/-- Either chronological order of the selected final-work pair exposes a
literal root prefix through the nonce absorb on which the complete fold-armed
controller uses only residual, fold, alpha, or final-work coordinates. -/
theorem exact_fold_armed_final_pair_has_work_conditioned_prefix
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (digest workAnswer base : Digest256) (nonce : NonceBytes)
    (pairLabeled : ExactDagFinalWorkPairLabeled input finalTrial
      (literalFinalWorkKey digest nonce) workAnswer base) :
    ∃ completed remaining,
      exactFixedRootRecords input.package.root = completed ++ remaining ∧
      (∀ slot ∈ namedTraceSlots
        (indexedControllerLabeledRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldTrial.val
            finalTrial.val)
          (foldArmedInitialState
            (exactPlainRomCursor configuration sample.1).erase)
          completed),
        slot = none ∨ (∃ alpha : Fin 4, slot = some (Sum.inl alpha)) ∨
          slot = some (Sum.inr none)) := by
  let key := literalFinalWorkKey digest nonce
  rcases pairLabeled with
      ⟨prior, middle, later, workActor, absorbActor, rootExact, trialExact⟩ |
      ⟨prior, middle, later, workActor, absorbActor, rootExact, trialExact⟩
  · let workRecord : UnifiedExposureRecord :=
      .machineFresh workActor key.workInput workAnswer
    let absorbRecord : UnifiedExposureRecord :=
      .machineFresh absorbActor key.absorbInput base
    let completed := prior ++ workRecord :: middle ++ [absorbRecord]
    refine ⟨completed, later, ?_, ?_⟩
    · simpa [completed, workRecord, absorbRecord, key, List.append_assoc]
        using rootExact
    · apply fold_armed_named_slots_without_q16_producers transitionFuel
        foldTrial.val finalTrial.val completed
          (foldArmedInitialState
            (exactPlainRomCursor configuration sample.1).erase)
      intro before current after completedExact
      rw [fold_armed_dag_state_after_records]
      have source := exact_work_first_prefix_has_no_q16_producers input digest
        workAnswer base nonce finalTrial prior middle later workActor absorbActor
          trialExact rootExact before current after (by
            simpa [completed, workRecord, absorbRecord, key] using
              completedExact)
      simpa [exactDagTrialController, foldArmedPreFinalDagState,
        foldArmedInitialState, foldArmedUnderlyingState,
        finalWorkQ16IndexedState, exactDagCandidateInitialState] using source
  · let workRecord : UnifiedExposureRecord :=
      .machineFresh workActor key.workInput workAnswer
    let absorbRecord : UnifiedExposureRecord :=
      .machineFresh absorbActor key.absorbInput base
    let completed := prior ++ [absorbRecord]
    refine ⟨completed, middle ++ workRecord :: later, ?_, ?_⟩
    · simpa [completed, workRecord, absorbRecord, key, List.append_assoc]
        using rootExact
    · apply fold_armed_named_slots_without_q16_producers transitionFuel
        foldTrial.val finalTrial.val completed
          (foldArmedInitialState
            (exactPlainRomCursor configuration sample.1).erase)
      intro before current after completedExact
      rw [fold_armed_dag_state_after_records]
      have source := exact_absorb_first_prefix_has_no_q16_producers input key
        base finalTrial prior absorbActor trialExact before current after (by
          simpa [completed, absorbRecord] using completedExact)
      simpa [exactDagTrialController, foldArmedPreFinalDagState,
        foldArmedInitialState, foldArmedUnderlyingState,
        finalWorkQ16IndexedState, exactDagCandidateInitialState] using source

#print axioms exact_work_first_prefix_has_no_q16_producers
#print axioms exact_absorb_first_prefix_has_no_q16_producers
#print axioms exact_fold_armed_final_pair_has_work_conditioned_prefix

end

end AspisK1.V7Tag73ExactFoldArmedFinalPairPrefix
