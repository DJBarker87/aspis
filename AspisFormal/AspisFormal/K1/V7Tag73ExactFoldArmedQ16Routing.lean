import AspisFormal.K1.V7Tag73ExactFoldArmedFinalWorkRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaQ16Disjoint

/-!
# Accepted q16 routing through the fold-armed controller

The exact installed q16 producer and ordered output lemmas are unchanged.  The
new ingredient is the fold-armed alpha/q16 priority theorem, which rules out
alpha shadowing before, at, and after the selected fold exposure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactFoldArmedQ16Routing

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactDagQ16OutputLabel
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactFoldArmedAlphaQ16Disjoint
open AspisK1.V7Tag73ExactFoldArmedFinalWorkRouting
open AspisK1.V7Tag73ExactFoldArmedRootRouting
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- One ordered output of an exact installed q16 producer is routed by its
literal `(counter, block)` slot through the fold-armed 518-slot controller. -/
theorem exact_fold_armed_dag_installed_producer_routes_ordered_output
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
    (producer : Q16DagProducer) (output : Digest256)
    (installed : ExactDagProducerInstalled input finalTrial producer)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producer.sourceInput, producer.digest) :: middle ++
          (gammaOutputInput producer.digest, output) :: after) :
    causalRoutedAnswer? (some (Sum.inr (some producer.slot)))
        (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
          fold.trial.val finalTrial.val
          (exactPlainRomCursor configuration sample.1).erase)
        (foldAlphaFinalWorkQ16NamedSlotInputTape
          (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some output := by
  obtain ⟨prior, between, later, producerActor, outputActor,
      recordsExact, producerMember⟩ :=
    exact_dag_installed_producer_available_before_ordered_child input finalTrial
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
  have dagPreferred := exact_dag_q16_output_has_preferred_slot input finalTrial
    outputPrefix later outputActor output producer (by
      simpa [outputRecord, gammaOutputInput] using decomposition) (by
      simpa [outputPrefix, producerRecord, outputRecord] using producerMember)
  have alphaNone :=
    exact_fold_armed_alpha_preferred_none_of_q16_preferred input fold finalTrial
      outputPrefix later outputActor (gammaOutputInput producer.digest) output
        producer.slot (by simpa [outputRecord] using decomposition) dagPreferred
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller outputPrefix
    initial
  have dagProjection : foldArmedPreFinalDagState reached =
      indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel finalTrial) outputPrefix
        (exactDagCandidateInitialState input) := by
    rw [show foldArmedPreFinalDagState reached =
        indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
            transitionFuel finalTrial.val) outputPrefix
          (foldArmedPreFinalDagState initial) by
      exact fold_armed_dag_state_after_records transitionFuel fold.trial.val
        finalTrial.val outputPrefix initial]
    rw [fold_armed_initial_dag_state_eq input]
    rfl
  have dagPreferredProjected :
      (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
        transitionFuel finalTrial.val).preferredSlot
          (foldArmedPreFinalDagState reached) = some (some producer.slot) := by
    rw [dagProjection]
    simpa [exactDagTrialController] using dagPreferred
  have underlyingPreferred :
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (foldArmedAlphaZeroController transitionFuel)).preferredSlot
          (foldArmedUnderlyingState reached) =
        some (Sum.inr (some producer.slot)) := by
    apply alpha_final_work_q16_preferred_of_dag
    · simpa [reached, foldArmedAlphaZeroController, foldArmedAlphaState] using
        alphaNone
    · simpa [foldArmedPreFinalDagState] using dagPreferredProjected
  have distinct : outputPrefix.length ≠ fold.trial.val := by
    symm
    apply exact_accepted_fold_trial_ne_root_record_of_input_length input fold
      outputPrefix later outputActor (gammaOutputInput producer.digest) output
      (by simpa [outputRecord] using decomposition)
    simp [gammaOutputInput, bytes_length]
  have reachedIndex : reached.exposureIndex = outputPrefix.length := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller outputPrefix initial
    simpa [reached, initial, foldArmedInitialState] using count
  have notFold : reached.exposureIndex ≠ fold.trial.val := by
    simpa [reachedIndex] using distinct
  have preferred : controller.preferredSlot reached =
      some (some (Sum.inr (some producer.slot))) := by
    simp [controller, foldArmedCompleteController, notFold,
      underlyingPreferred]
  exact exact_fold_armed_root_answer_is_routed programmedCover input fold.trial
    finalTrial outputPrefix later outputActor
      (gammaOutputInput producer.digest) output
      (some (Sum.inr (some producer.slot)))
      (by simpa [outputRecord] using decomposition) (by
        simpa [controller, initial, reached] using preferred)

/-- Recursive accepted q16 chain routed through the fold-armed controller. -/
theorem exact_fold_armed_ordered_q16_chain_routes
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
    (counter : Fin 64) :
    ∀ {producerInput : ShaInput} {digest : Digest256}
      {outputs advances : List Digest256}
      (block : Fin 8)
      (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
        advances)
      (lengthCap : block.val + outputs.length ≤ 8)
      (installed : ExactDagProducerInstalled input finalTrial
        (Q16DagProducer.mk digest (counter, block) producerInput)),
      ∀ index (inOutputs : index < outputs.length),
        causalRoutedAnswer?
            (some (Sum.inr (some (counter,
              ⟨block.val + index,
                (Nat.add_lt_add_left inOutputs block.val).trans_le
                  lengthCap⟩))))
            (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
              transitionFuel fold.trial.val finalTrial.val
              (exactPlainRomCursor configuration sample.1).erase)
            (foldAlphaFinalWorkQ16NamedSlotInputTape
              (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
          some outputs[index] := by
  intro producerInput digest outputs advances block chain lengthCap installed
  induction chain generalizing block with
  | done producerInput digest producerFound =>
      intro index inOutputs
      simp at inOutputs
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail ih =>
      intro index inOutputs
      let producer := Q16DagProducer.mk digest (counter, block) producerInput
      have headRouted :=
        exact_fold_armed_dag_installed_producer_routes_ordered_output
          programmedCover input fold finalTrial producer output installed (by
            simpa [producer, gammaOutputInput] using producerBeforeOutput)
      cases index with
      | zero =>
          change causalRoutedAnswer? (some (Sum.inr (some (counter, block))))
              _ _ = some output
          exact headRouted
      | succ index =>
          have indexInTail : index < outputs.length := by simpa using inOutputs
          have nextBound : block.val + 1 < 8 := by
            have positive : 0 < outputs.length := Nat.zero_lt_of_lt indexInTail
            simp only [List.length_cons] at lengthCap
            omega
          let nextBlock : Fin 8 := ⟨block.val + 1, nextBound⟩
          let nextProducer := Q16DagProducer.mk advanced
            (counter, nextBlock) (gammaAdvanceInput digest)
          have nextInstalled : ExactDagProducerInstalled input finalTrial
              nextProducer := by
            have installedRaw := exact_dag_advance_installs_next_producer input
              finalTrial producer advanced nextBound installed (by
                simpa [producer, gammaAdvanceInput] using producerBeforeAdvance)
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
          have outputExact : (output :: outputs)[index + 1] = outputs[index] :=
            rfl
          change causalRoutedAnswer?
              (some (Sum.inr (some (counter, goalBlock)))) _ _ =
            some (output :: outputs)[index + 1]
          rw [blockExact, outputExact]
          exact tailRouted

/-- The exact accepted q16 forest is realized by the fold-armed routed
coordinates through the selected counter. -/
theorem exact_compiler_fold_armed_q16_forest_realization
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (base : Digest256)
    (baseExact : base = (exactOperationalRawTrace input).q16BaseDigest)
    (installed : ∀ counter,
      counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
      ExactDagProducerInstalled input finalTrial
        (Q16DagProducer.mk
          (exactOperationalQ16InitialDigest input counter)
          (counter, ⟨0, by omega⟩)
          (bytes base ++
            [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val])))
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel fold.trial.val finalTrial.val
      (exactPlainRomCursor configuration sample.1).erase
    OperationalQ16ForestRealization
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        sample.2).2.2.2 := by
  let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
    transitionFuel fold.trial.val finalTrial.val
    (exactPlainRomCursor configuration sample.1).erase
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
            (some (Sum.inr (some (counter,
              ⟨index, Nat.lt_of_lt_of_le inBlocks
                (candidateLengthCap counter beforeSelected)⟩))))
            router
            (foldAlphaFinalWorkQ16NamedSlotInputTape
              (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
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
    have firstInstalled : ExactDagProducerInstalled input finalTrial
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
    have routed := exact_fold_armed_ordered_q16_chain_routes programmedCover
      input fold finalTrial counter (block := ⟨0, by omega⟩) chain
        (by simpa using lengthCap) firstInstalled index inCoordinates
    have candidateBlocksExact :
        exactDagOperationalQ16CandidateBlocks input counter =
          coordinates.outputs := by
      simp only [exactDagOperationalQ16CandidateBlocks, dif_pos beforeSelected]
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
  exact exact_compiler_fold_q16_operational_realization_of_used_lookups
    parameters router sample.2 (exactOperationalTape input).search
      (exactDagOperationalQ16CandidateBlocks input) candidateLengthCap routedAll
        outcomeDecoded frontierRealized

noncomputable def exactAcceptedFoldArmedRouter
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
    ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters :=
  exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
    (exactAcceptedFoldTrial input).trial.val
    (exactAcceptedDagInstallation transitionRoom input).finalTrial.val
    (exactPlainRomCursor configuration sample.1).erase

theorem exact_accepted_fold_armed_coordinate
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
      fixedInstance sample) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
      (exactAcceptedFoldArmedRouter transitionRoom input) sample.2).2.1 =
        (exactAcceptedFoldTrial input).answer := by
  apply exact_compiler_fold_coordinate_eq_of_routed_lookup
  exact exact_fold_armed_accepted_fold_is_routed programmedCover input
    (exactAcceptedFoldTrial input)
    (exactAcceptedDagInstallation transitionRoom input).finalTrial

theorem exact_accepted_fold_armed_final_work_coordinate
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
      fixedInstance sample) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
      (exactAcceptedFoldArmedRouter transitionRoom input) sample.2).2.2.1 =
        (exactAcceptedDagInstallation transitionRoom input).workAnswer := by
  apply exact_compiler_fold_final_work_coordinate_eq_of_routed_lookup
  exact exact_fold_armed_final_work_is_routed programmedCover input
    (exactAcceptedFoldTrial input)
    (exactAcceptedDagInstallation transitionRoom input)

structure ExactAcceptedFoldArmedQ16Anchor
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) where
  fold : ExactAcceptedFoldTrial input
  source : ExactAcceptedDagInstallation input
  router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters
  routerExact : router = exactCompilerFoldArmedAlphaFinalWorkQ16Router
    parameters transitionFuel fold.trial.val source.finalTrial.val
    (exactPlainRomCursor configuration sample.1).erase
  foldCoordinate :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      sample.2).2.1 = fold.answer
  workCoordinate :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      sample.2).2.2.1 = source.workAnswer

noncomputable def exactAcceptedFoldArmedQ16Anchor
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
      fixedInstance sample) : ExactAcceptedFoldArmedQ16Anchor input :=
  { fold := exactAcceptedFoldTrial input
    source := exactAcceptedDagInstallation transitionRoom input
    router := exactAcceptedFoldArmedRouter transitionRoom input
    routerExact := rfl
    foldCoordinate := exact_accepted_fold_armed_coordinate transitionRoom
      programmedCover input
    workCoordinate := exact_accepted_fold_armed_final_work_coordinate
      transitionRoom programmedCover input }

structure ExactAcceptedFoldArmedQ16Realization
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) where
  anchor : ExactAcceptedFoldArmedQ16Anchor input
  forestRealized : OperationalQ16ForestRealization
    (exactOperationalTape input).frontierNodes
    (exactOperationalTape input).search
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters anchor.router
      sample.2).2.2.2

theorem exact_compiler_accepted_fold_armed_q16_operational_realization
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
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    Nonempty (ExactAcceptedFoldArmedQ16Realization input) := by
  let anchor := exactAcceptedFoldArmedQ16Anchor transitionRoom programmedCover
    input
  have forestRealized : OperationalQ16ForestRealization
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        anchor.router sample.2).2.2.2 := by
    rw [anchor.routerExact]
    exact exact_compiler_fold_armed_q16_forest_realization transitionRoom
      programmedCover input anchor.fold anchor.source.finalTrial
        anchor.source.base anchor.source.baseExact anchor.source.installed
          frontierExact
  exact ⟨{ anchor := anchor, forestRealized := forestRealized }⟩

#print axioms exact_fold_armed_dag_installed_producer_routes_ordered_output
#print axioms exact_fold_armed_ordered_q16_chain_routes
#print axioms exact_compiler_fold_armed_q16_forest_realization
#print axioms exact_accepted_fold_armed_coordinate
#print axioms exact_accepted_fold_armed_final_work_coordinate
#print axioms exact_compiler_accepted_fold_armed_q16_operational_realization

end

end AspisK1.V7Tag73ExactFoldArmedQ16Routing
