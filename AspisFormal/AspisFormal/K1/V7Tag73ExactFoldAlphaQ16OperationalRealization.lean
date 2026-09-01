import AspisFormal.K1.V7Tag73ExactAcceptedFoldTrialPackage
import AspisFormal.K1.V7Tag73CausalFinalWorkQ16UsedForest

/-!
# Exact 518-slot operational coordinates

These lemmas connect recursive lookups in the complete fold/alpha/final/q16
router to the three deployed coordinate components used by K1.3.  They are
pure consequences of the selected product/reindexing equivalence.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactDagQ16OutputLabel
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem exact_compiler_fold_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (answer : Digest256)
    (routed : causalRoutedAnswer? none router
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.1 = answer := by
  change
    (router.coordinateEquiv
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))).1
        ⟨none, Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))
    none (Finset.mem_univ _) answer routed

theorem exact_compiler_fold_final_work_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (answer : Digest256)
    (routed : causalRoutedAnswer? (some (Sum.inr none)) router
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.2.1 = answer := by
  change
    (router.coordinateEquiv
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))).1
        ⟨some (Sum.inr none), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))
    (some (Sum.inr none)) (Finset.mem_univ _) answer routed

theorem exact_compiler_fold_q16_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (counter : Fin 64) (block : Fin 8) (answer : Digest256)
    (routed : causalRoutedAnswer?
      (some (Sum.inr (some (counter, block)))) router
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.2.2 counter block = answer := by
  change
    (router.coordinateEquiv
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))).1
        ⟨some (Sum.inr (some (counter, block))), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))
    (some (Sum.inr (some (counter, block)))) (Finset.mem_univ _) answer routed

/-- The production decoder only consumes the prefix through its selected
counter, so routed equations for that prefix suffice for exact realization. -/
theorem exact_compiler_fold_q16_operational_realization_of_used_lookups
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (candidateBlocks : Fin 64 → List Digest256)
    (candidateLengthCap : ∀ counter,
      counter.val ≤ search.selectedCounter.val →
      (candidateBlocks counter).length ≤ 8)
    (routed : ∀ counter
      (beforeSelected : counter.val ≤ search.selectedCounter.val),
      ∀ index (inBlocks : index < (candidateBlocks counter).length),
        causalRoutedAnswer?
            (some (Sum.inr (some (counter,
              ⟨index, Nat.lt_of_lt_of_le inBlocks
                (candidateLengthCap counter beforeSelected)⟩))))
            router
            (foldAlphaFinalWorkQ16NamedSlotInputTape
              (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
          some ((candidateBlocks counter)[index]))
    (outcomeDecoded : ∀ counter,
      counter.val ≤ search.selectedCounter.val →
      decodeCandidateOutcome counter (candidateBlocks counter) =
        some (search.outcome counter))
    (frontierExact : ∀ counter schedule,
      counter.val ≤ search.selectedCounter.val →
      search.outcome counter = .schedule schedule →
      semanticFrontierNodes (semanticScheduleOfOperational schedule) =
        frontierNodes schedule) :
    OperationalQ16ForestRealization frontierNodes search
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        tape).2.2.2 := by
  apply operationalQ16ForestRealizationOfDigestPointwise
  refine
    { candidateBlocks := candidateBlocks
      candidateLengthCap := candidateLengthCap
      candidateBlockExact := ?_
      outcomeDecoded := outcomeDecoded
      frontierExact := frontierExact }
  intro counter beforeSelected index inBlocks
  symm
  exact exact_compiler_fold_q16_coordinate_eq_of_routed_lookup parameters
    router tape counter
      ⟨index, Nat.lt_of_lt_of_le inBlocks
        (candidateLengthCap counter beforeSelected)⟩
      ((candidateBlocks counter)[index])
      (routed counter beforeSelected index inBlocks)

/-! ## Accepted-source routing through the complete controller -/

/-- One output child of an installed q16 producer is routed through the
complete controller.  Its 33-byte duplex input cannot collide with the
retained 41-byte fold-work input. -/
theorem exact_fold_dag_installed_producer_routes_ordered_output
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
    (boundaryIndex : Nat)
    (producer : Q16DagProducer) (output : Digest256)
    (installed : ExactDagProducerInstalled input finalTrial producer)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producer.sourceInput, producer.digest) :: middle ++
          (gammaOutputInput producer.digest, output) :: after) :
    causalRoutedAnswer? (some (Sum.inr (some producer.slot)))
        (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
          fold.trial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))
          (inactiveAlphaZeroMemory, inactiveDagMemory)
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
  have preferred := exact_dag_preferred_lifts_to_composed_controller input
    finalTrial boundaryIndex outputPrefix later outputActor
      (gammaOutputInput producer.digest) output (some producer.slot)
      (by simpa [outputRecord] using decomposition) dagPreferred
  have distinct : outputPrefix.length ≠ fold.trial.val := by
    symm
    apply exact_accepted_fold_trial_ne_root_record_of_input_length input fold
      outputPrefix later outputActor (gammaOutputInput producer.digest) output
      (by simpa [outputRecord] using decomposition)
    simp [gammaOutputInput, bytes_length]
  exact exact_underlying_root_answer_is_routed_by_518_router programmedCover
    input fold.trial finalTrial boundaryIndex outputPrefix later outputActor
    (gammaOutputInput producer.digest) output
    (Sum.inr (some producer.slot)) (by simpa [outputRecord] using decomposition)
    distinct preferred

/-- Recursive accepted q16 chain routed through the complete 518-slot
controller. -/
theorem exact_fold_ordered_q16_chain_routes
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
    (boundaryIndex : Nat)
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
            (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
              fold.trial.val
              (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
                (alphaZeroCausalController transitionFuel boundaryIndex))
              (inactiveAlphaZeroMemory, inactiveDagMemory)
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
        exact_fold_dag_installed_producer_routes_ordered_output programmedCover
          input fold finalTrial boundaryIndex producer output installed (by
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

/-- The accepted q16 chain alone realizes the consumed forest in the complete
router.  Factoring this from the fold/final anchor keeps kernel elaboration
bounded. -/
theorem exact_compiler_fold_alpha_q16_forest_realization
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
    (boundaryIndex : Nat)
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
    let router := exactCompilerFoldAlphaFinalWorkQ16Router parameters
      transitionFuel fold.trial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex))
      (inactiveAlphaZeroMemory, inactiveDagMemory)
      (exactPlainRomCursor configuration sample.1).erase
    OperationalQ16ForestRealization
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        sample.2).2.2.2 := by
  let router := exactCompilerFoldAlphaFinalWorkQ16Router parameters
    transitionFuel fold.trial.val
    (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
      (alphaZeroCausalController transitionFuel boundaryIndex))
    (inactiveAlphaZeroMemory, inactiveDagMemory)
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
    have routed := exact_fold_ordered_q16_chain_routes programmedCover input
      fold finalTrial boundaryIndex counter (block := ⟨0, by omega⟩) chain
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

/-- The exact accepted DAG installation, retained once so later bridge lemmas
do not repeatedly elaborate its existential source theorem. -/
structure ExactAcceptedDagInstallation
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
  digest : Digest256
  workAnswer : Digest256
  base : Digest256
  finalTrial : ExactCompilerExposureTrial parameters
  workAccepted : FinalWork34Accepted workAnswer
  prefinal : ExactOperationalPrefinalDigest input digest
  baseExact : base = (exactOperationalRawTrace input).q16BaseDigest
  pairLabeled : ExactDagFinalWorkPairLabeled input finalTrial
    (literalFinalWorkKey digest
      (exactOperationalTape input).messages.finalGrinding.selected)
    workAnswer base
  workLabeled : ExactDagFinalWorkLabeled input finalTrial
    (literalFinalWorkKey digest
      (exactOperationalTape input).messages.finalGrinding.selected)
    workAnswer
  installed : ∀ counter,
    counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
    ExactDagProducerInstalled input finalTrial
      (Q16DagProducer.mk
        (exactOperationalQ16InitialDigest input counter)
        (counter, ⟨0, by omega⟩)
        (bytes base ++
          [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]))

theorem exact_accepted_dag_installation_exists
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
    Nonempty (ExactAcceptedDagInstallation input) := by
  obtain ⟨digest, workAnswer, base, finalTrial, workAccepted, prefinal,
      baseExact, pairLabeled, workLabeled, installed⟩ :=
    exact_compiler_accepted_dag_trial_installs_all_candidates transitionRoom
      input
  exact ⟨
    { digest := digest
      workAnswer := workAnswer
      base := base
      finalTrial := finalTrial
      workAccepted := workAccepted
      prefinal := prefinal
      baseExact := baseExact
      pairLabeled := pairLabeled
      workLabeled := workLabeled
      installed := installed }⟩

noncomputable def exactAcceptedDagInstallation
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
      fixedInstance sample) : ExactAcceptedDagInstallation input :=
  Classical.choice (exact_accepted_dag_installation_exists transitionRoom input)

noncomputable def exactAcceptedFoldAlphaQ16Router
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
  exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
    (exactAcceptedFoldTrial input).trial.val
    (alphaFinalWorkQ16DagController transitionFuel
      (exactAcceptedDagInstallation transitionRoom input).finalTrial.val
      (alphaZeroCausalController transitionFuel 0))
    (inactiveAlphaZeroMemory, inactiveDagMemory)
    (exactPlainRomCursor configuration sample.1).erase

theorem exact_accepted_fold_coordinate
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
      (exactAcceptedFoldAlphaQ16Router transitionRoom input) sample.2).2.1 =
        (exactAcceptedFoldTrial input).answer := by
  apply exact_compiler_fold_coordinate_eq_of_routed_lookup
  exact exact_accepted_fold_trial_is_routed programmedCover input
    (exactAcceptedFoldTrial input)
    (exactAcceptedDagInstallation transitionRoom input).finalTrial 0

theorem exact_accepted_final_work_coordinate
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
      (exactAcceptedFoldAlphaQ16Router transitionRoom input) sample.2).2.2.1 =
        (exactAcceptedDagInstallation transitionRoom input).workAnswer := by
  let source := exactAcceptedDagInstallation transitionRoom input
  obtain ⟨workPrior, workLater, workActor, workDecomposition,
      workDagPreferred⟩ := source.workLabeled
  have workPreferred := exact_dag_preferred_lifts_to_composed_controller input
    source.finalTrial 0 workPrior workLater workActor
      (literalFinalWorkKey source.digest
        (exactOperationalTape input).messages.finalGrinding.selected).workInput
      source.workAnswer none workDecomposition workDagPreferred
  have workDistinct : workPrior.length ≠
      (exactAcceptedFoldTrial input).trial.val := by
    symm
    exact exact_accepted_fold_trial_ne_final_work_record input
      (exactAcceptedFoldTrial input) source.digest source.workAnswer
      source.prefinal workPrior workLater workActor workDecomposition
  apply exact_compiler_fold_final_work_coordinate_eq_of_routed_lookup
  exact exact_underlying_root_answer_is_routed_by_518_router programmedCover
    input (exactAcceptedFoldTrial input).trial source.finalTrial 0 workPrior
    workLater workActor
    (literalFinalWorkKey source.digest
      (exactOperationalTape input).messages.finalGrinding.selected).workInput
    source.workAnswer (Sum.inr none) workDecomposition workDistinct workPreferred

/-- Accepted fold/final anchor, retained separately from the q16 forest proof. -/
structure ExactAcceptedFoldAlphaQ16Anchor
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
  digest : Digest256
  workAnswer : Digest256
  base : Digest256
  finalTrial : ExactCompilerExposureTrial parameters
  boundaryIndex : Nat
  router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters
  foldAccepted : FoldWork31Accepted fold.answer
  workAccepted : FinalWork34Accepted workAnswer
  prefinal : ExactOperationalPrefinalDigest input digest
  baseExact : base = (exactOperationalRawTrace input).q16BaseDigest
  pairLabeled : ExactDagFinalWorkPairLabeled input finalTrial
    (literalFinalWorkKey digest
      (exactOperationalTape input).messages.finalGrinding.selected)
    workAnswer base
  routerExact : router = exactCompilerFoldAlphaFinalWorkQ16Router parameters
    transitionFuel fold.trial.val
    (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
      (alphaZeroCausalController transitionFuel boundaryIndex))
    (inactiveAlphaZeroMemory, inactiveDagMemory)
    (exactPlainRomCursor configuration sample.1).erase
  foldCoordinate :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      sample.2).2.1 = fold.answer
  workCoordinate :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      sample.2).2.2.1 = workAnswer
  installed : ∀ counter,
    counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
    ExactDagProducerInstalled input finalTrial
      (Q16DagProducer.mk
        (exactOperationalQ16InitialDigest input counter)
        (counter, ⟨0, by omega⟩)
        (bytes base ++
          [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]))

noncomputable def exactAcceptedFoldAlphaQ16Anchor
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
      fixedInstance sample) : ExactAcceptedFoldAlphaQ16Anchor input :=
  let source := exactAcceptedDagInstallation transitionRoom input
  { fold := exactAcceptedFoldTrial input
    digest := source.digest
    workAnswer := source.workAnswer
    base := source.base
    finalTrial := source.finalTrial
    boundaryIndex := 0
    router := exactAcceptedFoldAlphaQ16Router transitionRoom input
    foldAccepted := (exactAcceptedFoldTrial input).accepted
    workAccepted := source.workAccepted
    prefinal := source.prefinal
    baseExact := source.baseExact
    pairLabeled := source.pairLabeled
    routerExact := rfl
    foldCoordinate := exact_accepted_fold_coordinate transitionRoom
      programmedCover input
    workCoordinate := exact_accepted_final_work_coordinate transitionRoom
      programmedCover input
    installed := source.installed }

/-- Proof-relevant complete accepted coordinate package. -/
structure ExactAcceptedFoldAlphaQ16Realization
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
  anchor : ExactAcceptedFoldAlphaQ16Anchor input
  forestRealized : OperationalQ16ForestRealization
    (exactOperationalTape input).frontierNodes
    (exactOperationalTape input).search
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters anchor.router
      sample.2).2.2.2

/-- Accepted-source fold/final anchor in the complete router. -/
theorem exact_compiler_accepted_fold_alpha_q16_anchor
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
    Nonempty (ExactAcceptedFoldAlphaQ16Anchor input) :=
  ⟨exactAcceptedFoldAlphaQ16Anchor transitionRoom programmedCover input⟩

/-- Complete accepted-source realization obtained by composing the small
anchor theorem with the separately checked forest theorem. -/
theorem exact_compiler_accepted_fold_alpha_q16_operational_realization
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
    Nonempty (ExactAcceptedFoldAlphaQ16Realization input) := by
  let anchor := Classical.choice
    (exact_compiler_accepted_fold_alpha_q16_anchor transitionRoom
      programmedCover input frontierExact)
  have forestRealized : OperationalQ16ForestRealization
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        anchor.router sample.2).2.2.2 := by
    rw [anchor.routerExact]
    exact exact_compiler_fold_alpha_q16_forest_realization transitionRoom
      programmedCover input anchor.fold anchor.finalTrial anchor.boundaryIndex
      anchor.base anchor.baseExact anchor.installed frontierExact
  exact ⟨{ anchor := anchor, forestRealized := forestRealized }⟩

#print axioms exact_compiler_fold_coordinate_eq_of_routed_lookup
#print axioms exact_compiler_fold_final_work_coordinate_eq_of_routed_lookup
#print axioms exact_compiler_fold_q16_coordinate_eq_of_routed_lookup
#print axioms exact_compiler_fold_q16_operational_realization_of_used_lookups
#print axioms exact_fold_dag_installed_producer_routes_ordered_output
#print axioms exact_fold_ordered_q16_chain_routes
#print axioms exact_compiler_accepted_fold_alpha_q16_anchor
#print axioms exact_compiler_accepted_fold_alpha_q16_operational_realization

end

end AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
