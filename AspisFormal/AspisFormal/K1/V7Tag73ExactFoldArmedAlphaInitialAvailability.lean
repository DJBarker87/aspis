import AspisFormal.K1.V7Tag73ExactAcceptedFoldAlphaChainOrder
import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaProducerAvailability

/-!
# Availability of the deployed alpha block-zero producer

The selected fold record either installs a previously cached boundary answer
or arms that literal boundary until its future first exposure.  This leaf
shows that, in both cases, the deployed block-zero producer is live before an
ordered post-fold alpha output child.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaInitialAvailability

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldArmedAlphaProducerAvailability
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A nonempty duplex certificate exposes its literal first output, advance,
and remaining source chain. -/
theorem gamma_table_coordinate_chain_nonempty_head
    (table : FixedOracleTable) (digest : Digest256)
    (outputs advances : List Digest256)
    (chain : GammaTableCoordinateChain table digest outputs advances)
    (positive : 0 < outputs.length) :
    ∃ output advanced tailOutputs tailAdvances,
      outputs = output :: tailOutputs ∧
      advances = advanced :: tailAdvances ∧
      tableLookup table (gammaOutputInput digest) = some output ∧
      tableLookup table (gammaAdvanceInput digest) = some advanced ∧
      GammaTableCoordinateChain table advanced tailOutputs tailAdvances := by
  cases chain with
  | done => simp at positive
  | next outputLookup advanceLookup tail =>
      exact ⟨_, _, _, _, rfl, rfl, outputLookup, advanceLookup, tail⟩

/-- If the deployed block-zero output is first exposed in the literal root
suffix after the selected fold record, its source producer is live at that
exact pre-answer state. -/
theorem exact_fold_armed_initial_producer_available_before_post_fold_output
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
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (before later : List UnifiedExposureRecord)
    (outputActor : QueryActor) (output : Digest256)
    (laterExact : fold.later = before ++
      (.machineFresh outputActor (gammaOutputInput fold.boundaryAnswer) output :
        UnifiedExposureRecord) :: later)
    (ordered : ∃ rootBefore rootMiddle rootAfter,
      exactRootFreshQueries input =
        rootBefore ++
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected,
            fold.boundaryAnswer) :: rootMiddle ++
          (gammaOutputInput fold.boundaryAnswer, output) :: rootAfter) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let reached := indexedStateAfterRecords transitionFuel controller before
      afterFold
    ({ digest := fold.boundaryAnswer, block := 0,
        sourceInput := bytes fold.digest ++
          [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected } :
      AlphaZeroProducer) ∈ reached.memory.2.1.alpha.producers := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let producer : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0,
      sourceInput := bytes fold.digest ++
        [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected }
  let outputRecord : UnifiedExposureRecord := .machineFresh outputActor
    (gammaOutputInput fold.boundaryAnswer) output
  dsimp only
  obtain ⟨boundaryActor, cached | future⟩ :=
    exact_fold_step_cached_or_future_armed input fold finalTrial
  · have initialMember : producer ∈ afterFold.memory.2.1.alpha.producers := by
      have cached' :
          (controller.afterMemory reachedFold fold.answer).2.1.alpha.producers =
            [producer] := by
        simpa [controller, reachedFold, initial, producer] using cached
      change producer ∈
        (controller.afterMemory reachedFold fold.answer).2.1.alpha.producers
      rw [cached']
      simp
    have persisted :=
      exact_fold_armed_live_producer_persists_over_post_fold_segment input fold
        finalTrial [] before (outputRecord :: later) (by
          simpa [outputRecord] using laterExact) producer
    have persisted' := persisted (by simpa [afterFold] using initialMember)
    simpa [producer, controller, initial, reachedFold, afterFold] using
      persisted'
  · obtain ⟨rootBefore, rootMiddle, rootAfter, pairOrder⟩ := ordered
    obtain ⟨producerPrior, producerMiddle, producerLater, producerActor,
        childActor, recordsOrder⟩ :=
      exact_root_pair_order_lifts_to_records input producer.sourceInput
        (gammaOutputInput producer.digest) producer.digest output rootBefore
          rootMiddle rootAfter (by simpa [producer] using pairOrder)
    let producerRecord : UnifiedExposureRecord := .machineFresh producerActor
      producer.sourceInput producer.digest
    have outputRecordExact :
        (.machineFresh childActor (gammaOutputInput producer.digest) output :
          UnifiedExposureRecord) = outputRecord := by
      apply List.inj_on_of_nodup_map
        (exact_root_record_causal_inputs_nodup input)
      · rw [recordsOrder]
        simp
      · rw [fold.rootDecomposition, laterExact]
        simp [outputRecord]
      · simp [causalInput?, outputRecord, producer]
    change (.machineFresh childActor (gammaOutputInput producer.digest) output :
      UnifiedExposureRecord) =
        .machineFresh outputActor (gammaOutputInput fold.boundaryAnswer) output
          at outputRecordExact
    have childActorExact : childActor = outputActor := by
      injection outputRecordExact
    subst childActor
    have orderedPrefix : producerRecord ∈
        fold.prior ++
          (.machineFresh fold.actor
            (bytes fold.digest ++ [domGrind] ++
              bytes (exactOperationalTape input).messages.foldGrinding.selected)
            fold.answer : UnifiedExposureRecord) :: before := by
      have prefixExact :=
        alpha_mapped_nodup_selected_prefix_eq causalInput?
          (exactFixedRootRecords input.package.root)
          (producerPrior ++ producerRecord :: producerMiddle) producerLater
          (fold.prior ++
            [(.machineFresh fold.actor
              (bytes fold.digest ++ [domGrind] ++
                bytes (exactOperationalTape input).messages.foldGrinding.selected)
              fold.answer : UnifiedExposureRecord)] ++ before) later
          outputRecord outputRecord
          (exact_root_record_causal_inputs_nodup input)
          (by simpa [producerRecord, outputRecord, outputRecordExact,
              List.append_assoc] using recordsOrder)
          (by rw [fold.rootDecomposition, laterExact]
              simp [outputRecord, List.append_assoc]) rfl
      have member : producerRecord ∈
          producerPrior ++ producerRecord :: producerMiddle := by simp
      rw [prefixExact] at member
      simpa using member
    have producerRecordExact :
        producerRecord =
          (.machineFresh boundaryActor producer.sourceInput producer.digest :
            UnifiedExposureRecord) := by
      apply List.inj_on_of_nodup_map
        (exact_root_record_causal_inputs_nodup input)
      · rw [recordsOrder]
        simp [producerRecord]
      · rw [fold.rootDecomposition]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (by
          simpa [producer] using future.2.2))
      · simp [producerRecord, causalInput?]
    have boundaryInBefore :
        (.machineFresh boundaryActor producer.sourceInput producer.digest :
          UnifiedExposureRecord) ∈ before := by
      rw [← producerRecordExact]
      rw [List.mem_append] at orderedPrefix
      rcases orderedPrefix with inPrior | inRest
      · have rootNodup := exact_root_record_causal_inputs_nodup input
        rw [fold.rootDecomposition, List.map_append] at rootNodup
        have disjoint := rootNodup.disjoint
        have rightMember : causalInput? producerRecord ∈
            ((.machineFresh fold.actor
              (bytes fold.digest ++ [domGrind] ++
                bytes (exactOperationalTape input).messages.foldGrinding.selected)
              fold.answer : UnifiedExposureRecord) :: fold.later).map
                causalInput? := by
          rw [List.mem_map]
          refine ⟨(.machineFresh boundaryActor producer.sourceInput
            producer.digest : UnifiedExposureRecord), ?_, ?_⟩
          · exact List.mem_cons_of_mem _ (by
              simpa [producer] using future.2.2)
          · simp [producerRecordExact, causalInput?]
        have forbidden := List.disjoint_left.mp disjoint
          (by exact List.mem_map.mpr ⟨producerRecord, inPrior, rfl⟩)
          rightMember
        exact forbidden.elim
      · simp only [List.mem_cons] at inRest
        rcases inRest with selectedExact | inBefore
        · have inputExact := congrArg causalInput? selectedExact
          norm_num [producerRecord, producer, causalInput?, domAbsorb,
            domGrind] at inputExact
          exact (four_transcript_domains_are_pairwise_distinct.2.2.1
            inputExact.1).elim
        · simpa using inBefore
    obtain ⟨beforeBoundary, afterBoundary, beforeExact⟩ :=
      (List.mem_iff_append).mp boundaryInBefore
    obtain ⟨canonicalBefore, canonicalAfter, canonicalExact,
        canonicalInstalled⟩ :=
      exact_future_fold_boundary_installs_block_zero input fold finalTrial
        boundaryActor (by simpa [producer] using future.2.2)
    have beforeBoundaryExact : canonicalBefore = beforeBoundary := by
      apply alpha_mapped_nodup_selected_prefix_eq causalInput? fold.later
        canonicalBefore canonicalAfter beforeBoundary
          (afterBoundary ++ outputRecord :: later)
        (.machineFresh boundaryActor producer.sourceInput producer.digest :
          UnifiedExposureRecord)
        (.machineFresh boundaryActor producer.sourceInput producer.digest :
          UnifiedExposureRecord)
      · have rootNodup := exact_root_record_causal_inputs_nodup input
        rw [fold.rootDecomposition, List.map_append] at rootNodup
        exact (List.nodup_append.mp rootNodup).2.1.tail
      · simpa [producer] using canonicalExact
      · rw [laterExact, beforeExact]
        simp [outputRecord, List.append_assoc]
      · rfl
    subst canonicalBefore
    have installedMember : producer ∈
        (indexedStateAfterRecords transitionFuel controller
          (beforeBoundary ++
            [(.machineFresh boundaryActor producer.sourceInput producer.digest :
              UnifiedExposureRecord)]) afterFold).memory.2.1.alpha.producers := by
      rw [indexed_state_after_records_append,
        indexed_state_after_records_cons, indexed_state_after_records_nil]
      change producer ∈
        (controller.afterMemory
          (indexedStateAfterRecords transitionFuel controller beforeBoundary
            afterFold) producer.digest).2.1.alpha.producers
      rw [canonicalInstalled]
      simp [producer]
    have persisted :=
      exact_fold_armed_live_producer_persists_over_post_fold_segment input fold
        finalTrial
        (beforeBoundary ++
          [(.machineFresh boundaryActor producer.sourceInput producer.digest :
            UnifiedExposureRecord)]) afterBoundary (outputRecord :: later)
        (by rw [laterExact, beforeExact]
            simp [outputRecord, List.append_assoc]) producer
    have persisted' := persisted installedMember
    simpa [producer, beforeExact, controller, initial, reachedFold, afterFold,
      indexed_state_after_records_append] using persisted'

/-- Consequently, a deployed block-zero output first exposed after the fold
is carried by the literal alpha-zero named coordinate of the complete router. -/
theorem exact_fold_armed_post_fold_block_zero_output_is_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (before later : List UnifiedExposureRecord)
    (outputActor : QueryActor) (output : Digest256)
    (laterExact : fold.later = before ++
      (.machineFresh outputActor (gammaOutputInput fold.boundaryAnswer) output :
        UnifiedExposureRecord) :: later)
    (ordered : ∃ rootBefore rootMiddle rootAfter,
      exactRootFreshQueries input =
        rootBefore ++
          (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected,
            fold.boundaryAnswer) :: rootMiddle ++
          (gammaOutputInput fold.boundaryAnswer, output) :: rootAfter) :
    causalRoutedAnswer? (some (Sum.inl (0 : Fin 4)))
      (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
        fold.trial.val finalTrial.val
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some output := by
  let producer : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0,
      sourceInput := bytes fold.digest ++
        [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected }
  have member :=
    exact_fold_armed_initial_producer_available_before_post_fold_output input
      fold finalTrial before later outputActor output laterExact ordered
  have routed := exact_fold_armed_live_producer_output_is_routed
    programmedCover input fold finalTrial before later outputActor producer output
      (by simpa [producer] using laterExact) (by simpa [producer] using member)
  exact routed

/-- Exhaustive causal classification of the deployed first alpha block.  It
is either an adversary/verifier first-creation record strictly before the fold,
or the named post-fold alpha-zero coordinate.  The selected fold record itself
cannot alias the 33-byte duplex output input. -/
theorem exact_accepted_fold_alpha_block_zero_residual_or_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters) :
    ∃ output advanced tailOutputs tailAdvances,
      fold.alphaOutputs = output :: tailOutputs ∧
      fold.alphaAdvances = advanced :: tailAdvances ∧
      ((∃ actor,
          (.machineFresh actor (gammaOutputInput fold.boundaryAnswer) output :
            UnifiedExposureRecord) ∈ fold.prior) ∨
        causalRoutedAnswer? (some (Sum.inl (0 : Fin 4)))
          (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
            transitionFuel fold.trial.val finalTrial.val
            (exactPlainRomCursor configuration sample.1).erase)
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
          some output) := by
  have positive : 0 < fold.alphaOutputs.length := by
    rw [fold.alphaOutputsLength]
    exact ((exactOperationalTape input).messages.challengeUse
      (.alpha 0)).consumesBlock
  obtain ⟨output, advanced, tailOutputs, tailAdvances, outputsExact,
      advancesExact, outputLookup, _advanceLookup, _tail⟩ :=
    gamma_table_coordinate_chain_nonempty_head (exactOperationalTable input)
      fold.boundaryAnswer fold.alphaOutputs fold.alphaAdvances
      fold.alphaCoordinates positive
  obtain ⟨outputActor, outputMember⟩ :=
    exact_final_table_lookup_has_root_record input
      (gammaOutputInput fold.boundaryAnswer) output outputLookup
  have dependency : HasLiteralStatePrefix fold.boundaryAnswer
      (gammaOutputInput fold.boundaryAnswer) := by
    simp [HasLiteralStatePrefix, gammaOutputInput]
  have ordered :=
    exact_compiler_literal_dependency_has_strict_root_order transitionRoom input
      (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected)
      (gammaOutputInput fold.boundaryAnswer) fold.boundaryAnswer output
      fold.boundaryLookup outputLookup dependency
  rw [fold.rootDecomposition, List.mem_append] at outputMember
  rcases outputMember with beforeFold | atOrAfterFold
  · exact ⟨output, advanced, tailOutputs, tailAdvances, outputsExact,
      advancesExact, Or.inl ⟨outputActor, beforeFold⟩⟩
  · simp only [List.mem_cons] at atOrAfterFold
    rcases atOrAfterFold with atFold | afterFold
    · have inputExact := congrArg causalInput? atFold
      have lengthExact := congrArg (fun value => (value.getD []).length)
        inputExact
      simp [causalInput?, gammaOutputInput, bytes_length] at lengthExact
    · obtain ⟨before, later, laterExact⟩ :=
        (List.mem_iff_append).mp afterFold
      have routed := exact_fold_armed_post_fold_block_zero_output_is_routed
        programmedCover input fold finalTrial before later outputActor output
          laterExact ordered
      exact ⟨output, advanced, tailOutputs, tailAdvances, outputsExact,
        advancesExact, Or.inr routed⟩

#print axioms
  exact_fold_armed_initial_producer_available_before_post_fold_output
#print axioms exact_fold_armed_post_fold_block_zero_output_is_routed
#print axioms exact_accepted_fold_alpha_block_zero_residual_or_routed

end

end AspisK1.V7Tag73ExactFoldArmedAlphaInitialAvailability
