import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaInitialAvailability

/-!
# Exact cached alpha successors at the selected fold

When an adversary exposes the fold boundary before the selected fold-work
record, the controller reconstructs the bounded alpha producer chain from the
remembered machine-query list.  This leaf exposes that reconstruction and
proves that every chronologically ordered advance found in the first replay
pass is already live immediately after the fold.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaCachedSuccessor

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroBoundaryInvariant
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldArmedAlphaDigestNodup
open AspisK1.V7Tag73ExactFoldArmedAlphaInitialAvailability
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A cached producer is placed immediately after its literal source pair in
one chronological replay pass.  This is the induction currency for walking
the at-most-four-block alpha chain. -/
def ReplaySeenAlphaProducerPlacement
    (seen : List (ShaInput × Digest256))
    (seed producer : AlphaZeroProducer) : Prop :=
  ∃ before after,
    seen = before ++ (producer.sourceInput, producer.digest) :: after ∧
    producer ∈ replaySeenAlphaPass
      (before ++ [(producer.sourceInput, producer.digest)]) [seed]

/-- Advance one cached producer placement along a strictly later remembered
advance pair.  The proof uses first-input uniqueness to align the two list
cuts, then replays only through the advance itself. -/
theorem replay_seen_alpha_producer_placement_advance
    (seen : List (ShaInput × Digest256))
    (seed parent : AlphaZeroProducer) (advanced : Digest256)
    (bounded : parent.block.val + 1 < 4)
    (seenInputsNodup : (seen.map Prod.fst).Nodup)
    (seedLength : seed.sourceInput.length = 43)
    (seedInvariant : AlphaZeroMemoryProducerInvariant
      { producers := [seed], usedSlots := (∅ : Finset (Fin 4)) })
    (seedBoundary : AlphaZeroBlockZeroBoundaryValid [seed])
    (fullDigestNodup :
      ((replaySeenAlphaPass seen [seed]).map
        AlphaZeroProducer.digest).Nodup)
    (parentPlacement : ReplaySeenAlphaProducerPlacement seen seed parent)
    (advanceOrdered : ∃ advanceBefore advanceAfter,
      seen = advanceBefore ++
        (bytes parent.digest ++ [domAdvance], advanced) :: advanceAfter ∧
      (parent.sourceInput, parent.digest) ∈ advanceBefore) :
    ReplaySeenAlphaProducerPlacement seen seed
      { digest := advanced,
        block := ⟨parent.block.val + 1, bounded⟩,
        sourceInput := bytes parent.digest ++ [domAdvance] } := by
  let advancePair : ShaInput × Digest256 :=
    (bytes parent.digest ++ [domAdvance], advanced)
  let parentPair : ShaInput × Digest256 :=
    (parent.sourceInput, parent.digest)
  let next : AlphaZeroProducer :=
    { digest := advanced,
      block := ⟨parent.block.val + 1, bounded⟩,
      sourceInput := bytes parent.digest ++ [domAdvance] }
  obtain ⟨parentBefore, parentAfter, parentSeenExact, parentMember⟩ :=
    parentPlacement
  obtain ⟨advanceBefore, advanceAfter, advanceSeenExact,
      parentInAdvanceBefore⟩ := advanceOrdered
  obtain ⟨betweenBefore, betweenAfter, advanceBeforeExact⟩ :=
    (List.mem_iff_append).mp parentInAdvanceBefore
  have seenFromAdvance : seen =
      betweenBefore ++ parentPair ::
        (betweenAfter ++ advancePair :: advanceAfter) := by
    rw [advanceSeenExact, advanceBeforeExact]
    simp [parentPair, advancePair, List.append_assoc]
  have parentPrefixExact : parentBefore = betweenBefore := by
    apply alpha_mapped_nodup_selected_prefix_eq Prod.fst seen
      parentBefore parentAfter betweenBefore
      (betweenAfter ++ advancePair :: advanceAfter)
      (parent.sourceInput, parent.digest) parentPair seenInputsNodup
    · simpa [parentPair] using parentSeenExact
    · exact seenFromAdvance
    · simp [parentPair]
  have parentBeforeAdvance : parent ∈
      replaySeenAlphaPass advanceBefore [seed] := by
    have passPrefix := replay_seen_alpha_pass_prefix_of_append
      (betweenBefore ++ [parentPair]) betweenAfter [seed]
    rw [advanceBeforeExact]
    have retained := passPrefix.subset (by
      simpa [parentPrefixExact, parentPair] using parentMember)
    simpa [parentPair, List.append_assoc] using retained
  let throughAdvance := advanceBefore ++ [advancePair]
  have throughPrefix : replaySeenAlphaPass throughAdvance [seed] <+:
      replaySeenAlphaPass seen [seed] := by
    have seenExact : seen = throughAdvance ++ advanceAfter := by
      simpa [throughAdvance, advancePair, List.append_assoc] using
        advanceSeenExact
    rw [seenExact]
    exact replay_seen_alpha_pass_prefix_of_append throughAdvance advanceAfter
      [seed]
  have throughInputsNodup : (throughAdvance.map Prod.fst).Nodup := by
    have listPrefix : throughAdvance <+: seen := by
      refine ⟨advanceAfter, ?_⟩
      simpa [throughAdvance, advancePair, List.append_assoc] using
        advanceSeenExact.symm
    exact (listPrefix.map Prod.fst).nodup seenInputsNodup
  have throughInvariant := replay_seen_alpha_pass_preserves_producer_invariant
    throughAdvance [seed] (∅ : Finset (Fin 4)) seedInvariant
  have throughBoundary := replay_seen_alpha_pass_preserves_block_zero_boundary
    throughAdvance [seed] seedBoundary
  have throughDigestNodup :
      ((replaySeenAlphaPass throughAdvance [seed]).map
        AlphaZeroProducer.digest).Nodup :=
    (throughPrefix.map AlphaZeroProducer.digest).nodup fullDigestNodup
  have throughProvenance : ∀ producer,
      producer ∈ replaySeenAlphaPass throughAdvance [seed] →
        producer = seed ∨
          (producer.sourceInput, producer.digest) ∈ throughAdvance := by
    intro producer member
    rcases replay_seen_alpha_pass_member_old_or_seen throughAdvance [seed]
        producer member with old | remembered
    · left
      simpa using old
    · exact Or.inr remembered
  have nextMember := replay_seen_alpha_pass_contains_ordered_advance_successor
    throughAdvance [seed] (∅ : Finset (Fin 4)) seed parent advanced bounded
      throughInputsNodup seedLength throughInvariant throughBoundary
      throughDigestNodup throughProvenance
      (by simp [throughAdvance, advancePair])
      ⟨advanceBefore, [], by simp [throughAdvance, advancePair],
        parentBeforeAdvance⟩
  refine ⟨advanceBefore, advanceAfter, ?_, ?_⟩
  · simpa [next, advancePair] using advanceSeenExact
  · simpa [next, throughAdvance, advancePair] using nextMember

#print axioms ReplaySeenAlphaProducerPlacement
#print axioms replay_seen_alpha_producer_placement_advance

/-- Strict root order descends to the machine-pair memory before the selected
fold.  In particular, when the later coordinate is cached before the fold,
the earlier coordinate lies in the exact replay prefix preceding it. -/
theorem exact_fold_prior_strict_pair_order_seen_split
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
    (firstInput secondInput : ShaInput)
    (firstAnswer secondAnswer : Digest256)
    (rootBefore rootMiddle rootAfter : List (ShaInput × Digest256))
    (ordered : exactRootFreshQueries input =
      rootBefore ++ (firstInput, firstAnswer) :: rootMiddle ++
        (secondInput, secondAnswer) :: rootAfter)
    (secondActor : QueryActor)
    (secondBefore :
      (.machineFresh secondActor secondInput secondAnswer :
        UnifiedExposureRecord) ∈ fold.prior) :
    ∃ seenBefore seenAfter,
      fold.prior.filterMap machineFreshPair? =
        seenBefore ++ (secondInput, secondAnswer) :: seenAfter ∧
      (firstInput, firstAnswer) ∈ seenBefore := by
  obtain ⟨beforeRecords, middleRecords, afterRecords, firstActor,
      liftedSecondActor, rootRecordsExact⟩ :=
    AspisK1.V7Tag73ExactRootRecordOrderLift.exact_root_pair_order_lifts_to_records
      input firstInput secondInput
      firstAnswer secondAnswer rootBefore rootMiddle rootAfter ordered
  let firstRecord : UnifiedExposureRecord :=
    .machineFresh firstActor firstInput firstAnswer
  let liftedSecondRecord : UnifiedExposureRecord :=
    .machineFresh liftedSecondActor secondInput secondAnswer
  let secondRecord : UnifiedExposureRecord :=
    .machineFresh secondActor secondInput secondAnswer
  have liftedSecondMember : liftedSecondRecord ∈
      exactFixedRootRecords input.package.root := by
    rw [rootRecordsExact]
    simp [liftedSecondRecord]
  have secondRootMember : secondRecord ∈
      exactFixedRootRecords input.package.root := by
    rw [fold.rootDecomposition]
    exact List.mem_append_left _ (by simpa [secondRecord] using secondBefore)
  have secondRecordExact : liftedSecondRecord = secondRecord := by
    apply List.inj_on_of_nodup_map
      (exact_root_record_causal_inputs_nodup input)
      liftedSecondMember secondRootMember
    simp [liftedSecondRecord, secondRecord, causalInput?]
  obtain ⟨priorBefore, priorAfter, priorExact⟩ :=
    (List.mem_iff_append).mp secondBefore
  have secondRootExact : exactFixedRootRecords input.package.root =
      priorBefore ++ secondRecord ::
        (priorAfter ++
          (.machineFresh fold.actor
            (bytes fold.digest ++ [domGrind] ++
              bytes (exactOperationalTape input).messages.foldGrinding.selected)
            fold.answer : UnifiedExposureRecord) :: fold.later) := by
    rw [fold.rootDecomposition, priorExact]
    simp only [secondRecord, List.cons_append, List.append_assoc]
  have liftedRootExact : exactFixedRootRecords input.package.root =
      (beforeRecords ++ firstRecord :: middleRecords) ++
        liftedSecondRecord :: afterRecords := by
    simpa [firstRecord, liftedSecondRecord, List.append_assoc] using
      rootRecordsExact
  have prefixExact : beforeRecords ++ firstRecord :: middleRecords =
      priorBefore := by
    apply alpha_mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root)
      (beforeRecords ++ firstRecord :: middleRecords) afterRecords
      priorBefore
      (priorAfter ++
        (.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord) :: fold.later)
      liftedSecondRecord secondRecord
      (exact_root_record_causal_inputs_nodup input)
      liftedRootExact secondRootExact (by
        rw [secondRecordExact])
  refine ⟨beforeRecords.filterMap machineFreshPair? ++
      (firstInput, firstAnswer) :: middleRecords.filterMap machineFreshPair?,
    priorAfter.filterMap machineFreshPair?, ?_, ?_⟩
  · rw [priorExact, ← prefixExact]
    simp [firstRecord, machineFreshPair?, machineFreshInput?,
      UnifiedExposureRecord.answer, List.filterMap_append, List.append_assoc]
  · simp

/-- A cached fold boundary gives the base placement for the chronological
producer induction. -/
theorem exact_fold_cached_boundary_seed_placement
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
    (boundaryActor : QueryActor)
    (boundaryBefore :
      (.machineFresh boundaryActor
        (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.prior) :
    let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
    let seed : AlphaZeroProducer :=
      { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
    ReplaySeenAlphaProducerPlacement
      (fold.prior.filterMap machineFreshPair?) seed seed := by
  dsimp only
  let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected
  let seed : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
  obtain ⟨before, after, priorExact⟩ :=
    (List.mem_iff_append).mp boundaryBefore
  refine ⟨before.filterMap machineFreshPair?,
    after.filterMap machineFreshPair?, ?_, ?_⟩
  · rw [priorExact]
    simp [seed, target, machineFreshPair?, machineFreshInput?,
      UnifiedExposureRecord.answer, List.filterMap_append,
      List.append_assoc]
  · have seedMember : seed ∈ [seed] := by simp
    exact (replay_seen_alpha_pass_prefix
      (before.filterMap machineFreshPair? ++
        [(seed.sourceInput, seed.digest)]) [seed]).subset seedMember

/-- Exact accepted-root specialization of the cached placement step. -/
theorem exact_fold_cached_producer_placement_advance
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
    (boundaryActor : QueryActor)
    (boundaryBefore :
      (.machineFresh boundaryActor
        (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.prior)
    (parent : AlphaZeroProducer) (advanced : Digest256)
    (bounded : parent.block.val + 1 < 4)
    (parentPlacement :
      let target := bytes fold.digest ++
        [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected
      let seed : AlphaZeroProducer :=
        { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
      ReplaySeenAlphaProducerPlacement
        (fold.prior.filterMap machineFreshPair?) seed parent)
    (rootBefore rootMiddle rootAfter : List (ShaInput × Digest256))
    (advanceOrder : exactRootFreshQueries input =
      rootBefore ++ (parent.sourceInput, parent.digest) :: rootMiddle ++
        (bytes parent.digest ++ [domAdvance], advanced) :: rootAfter)
    (advanceActor : QueryActor)
    (advanceBefore :
      (.machineFresh advanceActor
        (bytes parent.digest ++ [domAdvance]) advanced :
        UnifiedExposureRecord) ∈ fold.prior) :
    let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
    let seed : AlphaZeroProducer :=
      { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
    ReplaySeenAlphaProducerPlacement (fold.prior.filterMap machineFreshPair?)
      seed
      { digest := advanced,
        block := ⟨parent.block.val + 1, bounded⟩,
        sourceInput := bytes parent.digest ++ [domAdvance] } := by
  dsimp only
  let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected
  let seed : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
  let seen := fold.prior.filterMap machineFreshPair?
  have seenNodup := exact_fold_reached_seen_machine_inputs_nodup input fold
    finalTrial
  have seenMemoryExact := exact_fold_reached_seen_machine_exact input fold
    finalTrial
  change
    ((indexedStateAfterRecords transitionFuel
      (foldArmedCompleteController transitionFuel fold.trial.val finalTrial.val)
      fold.prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
      ).memory.2.1.seenMachine.map Prod.fst).Nodup at seenNodup
  rw [seenMemoryExact] at seenNodup
  have targetLength : target.length = 43 := by
    simp [target, bytes_length]
  have seedInvariant : AlphaZeroMemoryProducerInvariant
      { producers := [seed], usedSlots := (∅ : Finset (Fin 4)) } := by
    constructor
    · intro producer member
      simp only [List.mem_singleton] at member
      subst producer
      exact Or.inl rfl
    · simp
    · simp
  have seedBoundary : AlphaZeroBlockZeroBoundaryValid [seed] := by
    intro producer member blockZero
    simp only [List.mem_singleton] at member
    subst producer
    simpa [seed] using targetLength
  have passInvariant := replay_seen_alpha_pass_preserves_producer_invariant
    seen [seed] (∅ : Finset (Fin 4)) seedInvariant
  have literalSource : ∀ producer,
      producer ∈ replaySeenAlphaPass seen [seed] →
        ∃ actor,
          (.machineFresh actor producer.sourceInput producer.digest :
            UnifiedExposureRecord) ∈ fold.prior := by
    intro producer member
    rcases replay_seen_alpha_pass_member_old_or_seen seen [seed] producer
        member with old | remembered
    · have producerExact : producer = seed := by simpa using old
      subst producer
      exact ⟨boundaryActor, by simpa [seed, target] using boundaryBefore⟩
    · rw [show seen = fold.prior.filterMap machineFreshPair? from rfl] at remembered
      obtain ⟨record, recordMember, recordExact⟩ :=
        List.mem_filterMap.mp remembered
      cases record with
      | machineFresh actor sourceInput sourceAnswer =>
          have pairExact : (sourceInput, sourceAnswer) =
              (producer.sourceInput, producer.digest) := by
            simpa [machineFreshPair?, machineFreshInput?,
              UnifiedExposureRecord.answer] using recordExact
          cases pairExact
          exact ⟨actor, recordMember⟩
      | padding value =>
          simp [machineFreshPair?, machineFreshInput?] at recordExact
      | forkOutput actor sourceInput output advance answer =>
          simp [machineFreshPair?, machineFreshInput?] at recordExact
      | forkAdvance answer =>
          simp [machineFreshPair?, machineFreshInput?] at recordExact
  have priorAnswerNodup :
      (fold.prior.map UnifiedExposureRecord.answer).Nodup := by
    have rootNodup := exact_root_record_answers_nodup input
    rw [fold.rootDecomposition, List.map_append] at rootNodup
    exact (List.nodup_append.mp rootNodup).1
  have passDigestNodup :
      ((replaySeenAlphaPass seen [seed]).map
        AlphaZeroProducer.digest).Nodup := by
    have producerNodup : (replaySeenAlphaPass seen [seed]).Nodup :=
      List.Nodup.of_map AlphaZeroProducer.block passInvariant.blocksNodup
    apply producerNodup.map_on
    intro left leftMember right rightMember digestExact
    obtain ⟨leftActor, leftRecord⟩ := literalSource left leftMember
    obtain ⟨rightActor, rightRecord⟩ := literalSource right rightMember
    have recordExact :
        (.machineFresh leftActor left.sourceInput left.digest :
            UnifiedExposureRecord) =
          .machineFresh rightActor right.sourceInput right.digest := by
      apply List.inj_on_of_nodup_map priorAnswerNodup leftRecord rightRecord
      simpa [UnifiedExposureRecord.answer] using digestExact
    have sourceExact : left.sourceInput = right.sourceInput := by
      injection recordExact
    exact List.inj_on_of_nodup_map passInvariant.sourceInputsNodup
      leftMember rightMember sourceExact
  obtain ⟨advanceSeenBefore, advanceSeenAfter, advanceSeenExact,
      parentSeenBefore⟩ :=
    exact_fold_prior_strict_pair_order_seen_split input fold
      parent.sourceInput (bytes parent.digest ++ [domAdvance]) parent.digest
      advanced rootBefore rootMiddle rootAfter advanceOrder advanceActor
      advanceBefore
  exact replay_seen_alpha_producer_placement_advance seen seed parent advanced
    bounded (by simpa [seen] using seenNodup) targetLength seedInvariant
      seedBoundary passDigestNodup (by simpa [seed, target] using parentPlacement)
      ⟨advanceSeenBefore, advanceSeenAfter, by
        simpa [seen] using advanceSeenExact, parentSeenBefore⟩

#print axioms exact_fold_cached_boundary_seed_placement
#print axioms exact_fold_cached_producer_placement_advance

/-- In the cached-boundary branch, the exact post-fold producer inventory is
the bounded replay closure over the literal pre-fold machine records. -/
theorem exact_fold_armed_cached_after_fold_producers_eq
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
    (boundaryActor : QueryActor)
    (boundaryBefore :
      (.machineFresh boundaryActor
        (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.prior) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
    afterFold.memory.2.1.alpha.producers =
      cachedAlphaProducerClosure (fold.prior.filterMap machineFreshPair?)
        target fold.boundaryAnswer := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected
  have rootAligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  have selectedAligned :
      unifiedRecordAtAnswer transitionFuel reachedFold.cursor fold.answer =
        (.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord) :=
    rootAligned fold.prior _ fold.later fold.rootDecomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reachedFold.cursor =
      some (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) :=
    aligned_machine_record_has_exact_input transitionFuel reachedFold.cursor
      fold.actor _ fold.answer selectedAligned
  have atFold : reachedFold.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    simpa [reachedFold, initial, foldArmedInitialState, fold.trialExact] using
      count
  have projectedInput : unifiedInputBeforeAnswer? transitionFuel
      (foldArmedAlphaState reachedFold).cursor =
        some (bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) := by
    simpa [foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]
      using inputExact
  have armedExact : armFoldAlphaBoundary transitionFuel
      (foldArmedAlphaState reachedFold) = some target := by
    simp only [armFoldAlphaBoundary, projectedInput, Option.bind_some]
    simpa [target] using literal_fold_work_arms_exact_alpha_boundary fold.digest
      (exactOperationalTape input).messages.foldGrinding.selected
  have cached := exact_fold_boundary_before_is_cached input fold finalTrial
    boundaryActor boundaryBefore
  have cached' : seenMachineAnswer? (foldArmedAlphaState reachedFold).memory
      target = some fold.boundaryAnswer := by
    change seenMachineAnswer? reachedFold.memory.2.1 target =
      some fold.boundaryAnswer
    simpa [reachedFold, controller, initial, target] using cached
  have seenExact := exact_fold_reached_seen_machine_exact input fold finalTrial
  have alphaMemoryExact : afterFold.memory.2.1 =
      armFoldAlphaMemory transitionFuel (foldArmedAlphaState reachedFold)
        fold.answer := by
    simp [afterFold, controller,
      IndexedUnifiedExposureController.afterAnswer,
      foldArmedCompleteController, atFold]
  dsimp only
  rw [alphaMemoryExact]
  simp only [armFoldAlphaMemory, armedExact, cached']
  change cachedAlphaProducerClosure reachedFold.memory.2.1.seenMachine target
      fold.boundaryAnswer = _
  rw [seenExact]

/-- A chronologically ordered cached advance is discovered in the first replay
pass and therefore remains in the full three-pass deployed closure. -/
theorem exact_fold_armed_cached_ordered_advance_successor_after_fold
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
    (boundaryActor : QueryActor)
    (boundaryBefore :
      (.machineFresh boundaryActor
        (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        fold.boundaryAnswer : UnifiedExposureRecord) ∈ fold.prior)
    (seenBefore seenAfter : List (ShaInput × Digest256))
    (parent : AlphaZeroProducer) (advanced : Digest256)
    (bounded : parent.block.val + 1 < 4)
    (seenExact : fold.prior.filterMap machineFreshPair? =
      seenBefore ++
        (bytes parent.digest ++ [domAdvance], advanced) :: seenAfter)
    (parentBefore : parent ∈ replaySeenAlphaPass seenBefore
      [⟨fold.boundaryAnswer, 0,
        bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected⟩]) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    ({ digest := advanced, block := ⟨parent.block.val + 1, bounded⟩,
        sourceInput := bytes parent.digest ++ [domAdvance] } :
        AlphaZeroProducer) ∈ afterFold.memory.2.1.alpha.producers := by
  dsimp only
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected
  let seed : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
  let seen := fold.prior.filterMap machineFreshPair?
  have targetLength : target.length = 43 := by
    simp [target, bytes_length]
  have seedInvariant : AlphaZeroMemoryProducerInvariant
      { producers := [seed], usedSlots := (∅ : Finset (Fin 4)) } := by
    constructor
    · intro producer member
      simp only [List.mem_singleton] at member
      subst producer
      exact Or.inl rfl
    · simp
    · simp
  have seedBoundary : AlphaZeroBlockZeroBoundaryValid [seed] := by
    intro producer member blockZero
    simp only [List.mem_singleton] at member
    subst producer
    simpa [seed] using targetLength
  have passInvariant := replay_seen_alpha_pass_preserves_producer_invariant
    seen [seed] (∅ : Finset (Fin 4)) seedInvariant
  have passBoundary := replay_seen_alpha_pass_preserves_block_zero_boundary
    seen [seed] seedBoundary
  have afterDigestNodup :=
    exact_fold_armed_post_fold_prefix_producer_digests_nodup input fold
      finalTrial [] fold.later (by simp)
  have afterExact := exact_fold_armed_cached_after_fold_producers_eq input fold
    finalTrial boundaryActor boundaryBefore
  have passPrefix : replaySeenAlphaPass seen [seed] <+:
      cachedAlphaProducerClosure seen target fold.boundaryAnswer := by
    unfold cachedAlphaProducerClosure
    simp only [replaySeenAlphaClosure]
    exact replay_seen_alpha_closure_prefix 2 seen
      (replaySeenAlphaPass seen [seed])
  have passDigestNodup :
      ((replaySeenAlphaPass seen [seed]).map
        AlphaZeroProducer.digest).Nodup := by
    apply (passPrefix.map AlphaZeroProducer.digest).nodup
    rw [← afterExact]
    exact afterDigestNodup
  have passProvenance : ∀ producer,
      producer ∈ replaySeenAlphaPass seen [seed] →
        producer = seed ∨ (producer.sourceInput, producer.digest) ∈ seen := by
    intro producer member
    rcases replay_seen_alpha_pass_member_old_or_seen seen [seed] producer
        member with old | remembered
    · left
      simpa [seed] using old
    · exact Or.inr remembered
  have seenInputsNodup := exact_fold_reached_seen_machine_inputs_nodup input
    fold finalTrial
  change (reachedFold.memory.2.1.seenMachine.map Prod.fst).Nodup at seenInputsNodup
  have seenMemoryExact : reachedFold.memory.2.1.seenMachine = seen := by
    simpa [seen, reachedFold, controller, initial] using
      exact_fold_reached_seen_machine_exact input fold finalTrial
  rw [seenMemoryExact] at seenInputsNodup
  have nextInPass := replay_seen_alpha_pass_contains_ordered_advance_successor
    seen [seed] (∅ : Finset (Fin 4)) seed parent advanced bounded
      seenInputsNodup
      targetLength passInvariant passBoundary passDigestNodup passProvenance
      (by simpa [seen, seenExact])
      ⟨seenBefore, seenAfter, by simpa [seen] using seenExact,
        by simpa [seed, target] using parentBefore⟩
  have nextInClosure := passPrefix.subset nextInPass
  rw [afterExact]
  simpa [seen, seed, target] using nextInClosure

#print axioms exact_fold_armed_cached_after_fold_producers_eq
#print axioms exact_fold_prior_strict_pair_order_seen_split
#print axioms
  exact_fold_armed_cached_ordered_advance_successor_after_fold

end

end AspisK1.V7Tag73ExactFoldArmedAlphaCachedSuccessor
