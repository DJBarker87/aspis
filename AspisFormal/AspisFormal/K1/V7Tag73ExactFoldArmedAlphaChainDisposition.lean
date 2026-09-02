import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaCachedSuccessor

/-!
# Exact cached-or-routed classification of every alpha block

The selected fold can occur after an adversary has already exposed an alpha
coordinate.  This leaf carries one producer certificate through the literal
at-most-four-block alpha chain.  A pre-fold producer is reconstructed by the
cached replay; a post-fold child sees the same producer live in the fold-armed
controller.  Consequently every consumed output is either a literal record in
the shared fold prefix or the exact named alpha coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaChainDisposition

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldArmedAlphaCachedSuccessor
open AspisK1.V7Tag73ExactFoldArmedAlphaInitialAvailability
open AspisK1.V7Tag73ExactFoldArmedAlphaProducerAvailability
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The induction currency for the exact alpha chain.  Its first component
handles a producer whose source is already in the selected-fold prefix.  Its
second component says the same producer is live immediately before every
strictly later post-fold child. -/
def ExactFoldAlphaProducerCertificate
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
    (seed producer : AlphaZeroProducer) : Prop :=
  (∀ actor,
      (.machineFresh actor producer.sourceInput producer.digest :
        UnifiedExposureRecord) ∈ fold.prior →
      ∃ boundaryActor,
        (.machineFresh boundaryActor seed.sourceInput seed.digest :
          UnifiedExposureRecord) ∈ fold.prior ∧
        ReplaySeenAlphaProducerPlacement
          (fold.prior.filterMap machineFreshPair?) seed producer) ∧
  (∀ before later childActor childInput childAnswer,
      fold.later = before ++
        (.machineFresh childActor childInput childAnswer :
          UnifiedExposureRecord) :: later →
      (∃ rootBefore rootMiddle rootAfter,
        exactRootFreshQueries input =
          rootBefore ++ (producer.sourceInput, producer.digest) ::
            rootMiddle ++ (childInput, childAnswer) :: rootAfter) →
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
      producer ∈ reached.memory.2.1.alpha.producers)

/-- The selected fold boundary is the base producer certificate. -/
theorem exact_fold_alpha_boundary_producer_certificate
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
    (finalTrial : ExactCompilerExposureTrial parameters) :
    let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected
    let seed : AlphaZeroProducer :=
      { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
    ExactFoldAlphaProducerCertificate input fold finalTrial seed seed := by
  dsimp only
  let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected
  let seed : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
  constructor
  · intro actor member
    refine ⟨actor, member, ?_⟩
    simpa [seed, target] using
      exact_fold_cached_boundary_seed_placement input fold actor (by
        simpa [seed, target] using member)
  · intro before later childActor childInput childAnswer laterExact ordered
    simpa [seed, target] using
      exact_fold_armed_initial_producer_available_before_post_fold_child
        input fold finalTrial before later childActor childInput childAnswer
          laterExact (by simpa [seed, target] using ordered)

/-- A certified producer classifies its literal output as either cached in the
selected-fold prefix or installed at its exact named alpha coordinate. -/
theorem exact_certified_fold_alpha_output_cached_or_routed
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
    (seed producer : AlphaZeroProducer) (output : Digest256)
    (certificate : ExactFoldAlphaProducerCertificate input fold finalTrial
      seed producer)
    (outputLookup : tableLookup (exactOperationalTable input)
      (gammaOutputInput producer.digest) = some output)
    (ordered : ∃ rootBefore rootMiddle rootAfter,
      exactRootFreshQueries input =
        rootBefore ++ (producer.sourceInput, producer.digest) :: rootMiddle ++
          (gammaOutputInput producer.digest, output) :: rootAfter) :
    (∃ actor,
      (.machineFresh actor (gammaOutputInput producer.digest) output :
        UnifiedExposureRecord) ∈ fold.prior) ∨
    causalRoutedAnswer? (some (Sum.inl producer.block))
      (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
        fold.trial.val finalTrial.val
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some output := by
  obtain ⟨outputActor, outputMember⟩ :=
    AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence.exact_final_table_lookup_has_root_record
      input (gammaOutputInput producer.digest) output outputLookup
  rw [fold.rootDecomposition, List.mem_append] at outputMember
  rcases outputMember with beforeFold | atOrAfterFold
  · exact Or.inl ⟨outputActor, beforeFold⟩
  · simp only [List.mem_cons] at atOrAfterFold
    rcases atOrAfterFold with atFold | afterFold
    · have inputExact := congrArg causalInput? atFold
      have lengthExact := congrArg (fun value => (value.getD []).length)
        inputExact
      simp [causalInput?, gammaOutputInput, bytes_length] at lengthExact
    · obtain ⟨before, later, laterExact⟩ :=
        (List.mem_iff_append).mp afterFold
      have producerMember := certificate.2 before later outputActor
        (gammaOutputInput producer.digest) output laterExact ordered
      exact Or.inr (exact_fold_armed_live_producer_output_is_routed
        programmedCover input fold finalTrial before later outputActor producer
          output laterExact producerMember)

/-- A certified producer whose literal source is in the fold prefix belongs to
the exact producer inventory immediately after the selected fold. -/
theorem exact_cached_certified_producer_member_after_fold
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
    (producer : AlphaZeroProducer)
    (cachedCertificate :
      let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected
      let seed : AlphaZeroProducer :=
        { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
      ∀ actor,
        (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) ∈ fold.prior →
        ∃ boundaryActor,
          (.machineFresh boundaryActor seed.sourceInput seed.digest :
            UnifiedExposureRecord) ∈ fold.prior ∧
          ReplaySeenAlphaProducerPlacement
            (fold.prior.filterMap machineFreshPair?) seed producer)
    (sourceActor : QueryActor)
    (sourceBefore :
      (.machineFresh sourceActor producer.sourceInput producer.digest :
        UnifiedExposureRecord) ∈ fold.prior) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    producer ∈ afterFold.memory.2.1.alpha.producers := by
  dsimp only at cachedCertificate ⊢
  let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected
  let seed : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
  let seen := fold.prior.filterMap machineFreshPair?
  obtain ⟨boundaryActor, boundaryBefore, placement⟩ :=
    cachedCertificate sourceActor sourceBefore
  obtain ⟨before, after, seenExact, producerInPrefix⟩ := placement
  have throughPrefix : replaySeenAlphaPass
      (before ++ [(producer.sourceInput, producer.digest)]) [seed] <+:
      replaySeenAlphaPass seen [seed] := by
    rw [show seen = fold.prior.filterMap machineFreshPair? from rfl,
      seenExact]
    simpa [List.append_assoc] using
      replay_seen_alpha_pass_prefix_of_append
        (before ++ [(producer.sourceInput, producer.digest)]) after [seed]
  have producerInPass : producer ∈ replaySeenAlphaPass seen [seed] :=
    throughPrefix.subset producerInPrefix
  have passPrefix : replaySeenAlphaPass seen [seed] <+:
      cachedAlphaProducerClosure seen target fold.boundaryAnswer := by
    unfold cachedAlphaProducerClosure
    simp only [replaySeenAlphaClosure]
    exact replay_seen_alpha_closure_prefix 2 seen
      (replaySeenAlphaPass seen [seed])
  have producerInClosure := passPrefix.subset producerInPass
  have afterExact := exact_fold_armed_cached_after_fold_producers_eq input fold
    finalTrial boundaryActor (by simpa [seed, target] using boundaryBefore)
  rw [afterExact]
  simpa [seen, seed, target] using producerInClosure

/-- Strict root order between two machine records already known to lie after
the selected fold descends to an exact decomposition of `fold.later`. -/
theorem exact_fold_later_strict_record_order_split
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
    (firstActor secondActor : QueryActor)
    (firstLater :
      (.machineFresh firstActor firstInput firstAnswer :
        UnifiedExposureRecord) ∈ fold.later)
    (secondLater :
      (.machineFresh secondActor secondInput secondAnswer :
        UnifiedExposureRecord) ∈ fold.later) :
    ∃ before middle after,
      fold.later = before ++
        (.machineFresh firstActor firstInput firstAnswer :
          UnifiedExposureRecord) :: middle ++
        (.machineFresh secondActor secondInput secondAnswer :
          UnifiedExposureRecord) :: after := by
  obtain ⟨rootRecordBefore, rootRecordMiddle, rootRecordAfter,
      liftedFirstActor, liftedSecondActor, liftedRootExact⟩ :=
    AspisK1.V7Tag73ExactRootRecordOrderLift.exact_root_pair_order_lifts_to_records
      input firstInput secondInput firstAnswer secondAnswer rootBefore
        rootMiddle rootAfter ordered
  let firstRecord : UnifiedExposureRecord :=
    .machineFresh firstActor firstInput firstAnswer
  let secondRecord : UnifiedExposureRecord :=
    .machineFresh secondActor secondInput secondAnswer
  let liftedFirst : UnifiedExposureRecord :=
    .machineFresh liftedFirstActor firstInput firstAnswer
  let liftedSecond : UnifiedExposureRecord :=
    .machineFresh liftedSecondActor secondInput secondAnswer
  have firstRootMember : firstRecord ∈
      exactFixedRootRecords input.package.root := by
    rw [fold.rootDecomposition]
    exact List.mem_append_right _ (by simp [firstRecord, firstLater])
  have secondRootMember : secondRecord ∈
      exactFixedRootRecords input.package.root := by
    rw [fold.rootDecomposition]
    exact List.mem_append_right _ (by simp [secondRecord, secondLater])
  have liftedFirstMember : liftedFirst ∈
      exactFixedRootRecords input.package.root := by
    rw [liftedRootExact]
    simp [liftedFirst]
  have liftedSecondMember : liftedSecond ∈
      exactFixedRootRecords input.package.root := by
    rw [liftedRootExact]
    simp [liftedSecond]
  have firstExact : liftedFirst = firstRecord := by
    apply List.inj_on_of_nodup_map
      (exact_root_record_causal_inputs_nodup input)
      liftedFirstMember firstRootMember
    simp [liftedFirst, firstRecord, causalInput?]
  have secondExact : liftedSecond = secondRecord := by
    apply List.inj_on_of_nodup_map
      (exact_root_record_causal_inputs_nodup input)
      liftedSecondMember secondRootMember
    simp [liftedSecond, secondRecord, causalInput?]
  obtain ⟨before, afterFirst, laterAtFirst⟩ :=
    (List.mem_iff_append).mp firstLater
  have foldRootAtFirst : exactFixedRootRecords input.package.root =
      (fold.prior ++
        [(.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord)] ++ before) ++
        firstRecord :: afterFirst := by
    rw [fold.rootDecomposition, laterAtFirst]
    simp [firstRecord, List.append_assoc]
  have liftedRootAtFirst : exactFixedRootRecords input.package.root =
      rootRecordBefore ++ firstRecord ::
        (rootRecordMiddle ++ secondRecord :: rootRecordAfter) := by
    simpa [liftedFirst, liftedSecond, firstExact, secondExact,
      List.append_assoc] using liftedRootExact
  have prefixExact : rootRecordBefore =
      fold.prior ++
        [(.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord)] ++ before := by
    apply alpha_mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root)
      rootRecordBefore
      (rootRecordMiddle ++ secondRecord :: rootRecordAfter)
      (fold.prior ++
        [(.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord)] ++ before)
      afterFirst firstRecord firstRecord
      (exact_root_record_causal_inputs_nodup input)
      liftedRootAtFirst foldRootAtFirst rfl
  have suffixExact : afterFirst =
      rootRecordMiddle ++ secondRecord :: rootRecordAfter := by
    rw [prefixExact] at liftedRootAtFirst
    exact (List.cons.inj
      (List.append_right_injective
        (fold.prior ++
          [(.machineFresh fold.actor
            (bytes fold.digest ++ [domGrind] ++
              bytes (exactOperationalTape input).messages.foldGrinding.selected)
            fold.answer : UnifiedExposureRecord)] ++ before)
        (foldRootAtFirst.symm.trans liftedRootAtFirst))).2
  refine ⟨before, rootRecordMiddle, rootRecordAfter, ?_⟩
  rw [laterAtFirst, suffixExact]
  simp [firstRecord, secondRecord, List.append_assoc]

/-- Membership in the remembered machine-pair projection retains a literal
machine record and its actor. -/
theorem machine_pair_mem_filterMap_has_record
    (records : List UnifiedExposureRecord)
    (queryInput : ShaInput) (answer : Digest256)
    (member : (queryInput, answer) ∈
      records.filterMap machineFreshPair?) :
    ∃ actor,
      (.machineFresh actor queryInput answer : UnifiedExposureRecord) ∈
        records := by
  obtain ⟨record, recordMember, recordExact⟩ :=
    List.mem_filterMap.mp member
  cases record with
  | machineFresh actor sourceInput sourceAnswer =>
      have pairExact : (sourceInput, sourceAnswer) =
          (queryInput, answer) := by
        simpa [machineFreshPair?, machineFreshInput?,
          UnifiedExposureRecord.answer] using recordExact
      cases pairExact
      exact ⟨actor, recordMember⟩
  | padding value =>
      simp [machineFreshPair?, machineFreshInput?] at recordExact
  | forkOutput actor sourceInput output advance sourceAnswer =>
      simp [machineFreshPair?, machineFreshInput?] at recordExact
  | forkAdvance sourceAnswer =>
      simp [machineFreshPair?, machineFreshInput?] at recordExact

/-- One exact advance preserves the producer certificate.  Cached advances
are reconstructed by the pre-fold replay.  Post-fold advances install the
successor in the live controller before every later child. -/
theorem exact_fold_alpha_producer_certificate_advance
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
    (seed parent : AlphaZeroProducer) (advanced : Digest256)
    (bounded : parent.block.val + 1 < 4)
    (parentCertificate : ExactFoldAlphaProducerCertificate input fold
      finalTrial seed parent)
    (advanceLookup : tableLookup (exactOperationalTable input)
      (gammaAdvanceInput parent.digest) = some advanced)
    (rootBefore rootMiddle rootAfter : List (ShaInput × Digest256))
    (advanceOrder : exactRootFreshQueries input =
      rootBefore ++ (parent.sourceInput, parent.digest) :: rootMiddle ++
        (gammaAdvanceInput parent.digest, advanced) :: rootAfter)
    (seedExact : seed =
      { digest := fold.boundaryAnswer, block := 0,
        sourceInput := bytes fold.digest ++
          [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected }) :
    ExactFoldAlphaProducerCertificate input fold finalTrial seed
      { digest := advanced,
        block := ⟨parent.block.val + 1, bounded⟩,
        sourceInput := gammaAdvanceInput parent.digest } := by
  let next : AlphaZeroProducer :=
    { digest := advanced,
      block := ⟨parent.block.val + 1, bounded⟩,
      sourceInput := gammaAdvanceInput parent.digest }
  have nextCached : ∀ actor,
      (.machineFresh actor next.sourceInput next.digest :
        UnifiedExposureRecord) ∈ fold.prior →
      ∃ boundaryActor,
        (.machineFresh boundaryActor seed.sourceInput seed.digest :
          UnifiedExposureRecord) ∈ fold.prior ∧
        ReplaySeenAlphaProducerPlacement
          (fold.prior.filterMap machineFreshPair?) seed next := by
    intro advanceActor advanceBefore
    obtain ⟨seenBefore, seenAfter, seenExact, parentBefore⟩ :=
      exact_fold_prior_strict_pair_order_seen_split input fold
        parent.sourceInput (gammaAdvanceInput parent.digest) parent.digest
        advanced rootBefore rootMiddle rootAfter advanceOrder advanceActor
        (by simpa [next] using advanceBefore)
    have parentPairMember : (parent.sourceInput, parent.digest) ∈
        fold.prior.filterMap machineFreshPair? := by
      rw [seenExact]
      exact List.mem_append_left _ parentBefore
    obtain ⟨parentActor, parentSourceBefore⟩ :=
      machine_pair_mem_filterMap_has_record fold.prior parent.sourceInput
        parent.digest parentPairMember
    obtain ⟨boundaryActor, boundaryBefore, parentPlacement⟩ :=
      parentCertificate.1 parentActor parentSourceBefore
    refine ⟨boundaryActor, boundaryBefore, ?_⟩
    have nextPlacement := exact_fold_cached_producer_placement_advance
      input fold finalTrial boundaryActor (by simpa [seedExact] using
        boundaryBefore) parent advanced bounded (by
          simpa [seedExact] using parentPlacement)
        rootBefore rootMiddle rootAfter advanceOrder advanceActor (by
          simpa [next, gammaAdvanceInput] using advanceBefore)
    simpa [next, seedExact, gammaAdvanceInput] using nextPlacement
  refine ⟨nextCached, ?_⟩
  intro childBefore childLater childActor childInput childAnswer childLaterExact
    nextBeforeChild
  obtain ⟨advanceActor, advanceMember⟩ :=
    AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence.exact_final_table_lookup_has_root_record
      input (gammaAdvanceInput parent.digest) advanced advanceLookup
  rw [fold.rootDecomposition, List.mem_append] at advanceMember
  rcases advanceMember with advanceBefore | advanceAtOrAfter
  · have nextAfterFold := exact_cached_certified_producer_member_after_fold
      input fold finalTrial next (by simpa [seedExact] using nextCached)
        advanceActor (by simpa [next] using advanceBefore)
    have persisted := exact_fold_armed_live_producer_persists_over_post_fold_segment
      input fold finalTrial [] childBefore
        ((.machineFresh childActor childInput childAnswer :
          UnifiedExposureRecord) :: childLater)
        (by simpa [List.append_assoc] using childLaterExact) next
    simpa [next] using persisted (by simpa using nextAfterFold)
  · simp only [List.mem_cons] at advanceAtOrAfter
    rcases advanceAtOrAfter with advanceAtFold | advanceLater
    · have inputExact := congrArg causalInput? advanceAtFold
      have lengthExact := congrArg (fun value => (value.getD []).length)
        inputExact
      simp [causalInput?, gammaAdvanceInput, bytes_length] at lengthExact
    · obtain ⟨childRootBefore, childRootMiddle, childRootAfter,
          childOrder⟩ := nextBeforeChild
      obtain ⟨beforeAdvance, between, afterChild, laterExact⟩ :=
        exact_fold_later_strict_record_order_split input fold
          (gammaAdvanceInput parent.digest) childInput advanced childAnswer
          childRootBefore childRootMiddle childRootAfter (by
            simpa [next] using childOrder) advanceActor childActor
          advanceLater (by simpa using
            (show (.machineFresh childActor childInput childAnswer :
              UnifiedExposureRecord) ∈ fold.later from by
                rw [childLaterExact]
                simp))
      have parentBeforeAdvance := parentCertificate.2 beforeAdvance
        (between ++
          (.machineFresh childActor childInput childAnswer :
            UnifiedExposureRecord) :: afterChild)
        advanceActor (gammaAdvanceInput parent.digest) advanced (by
          simpa [List.append_assoc] using laterExact)
        ⟨rootBefore, rootMiddle, rootAfter, advanceOrder⟩
      have nextBeforeChild :=
        exact_fold_armed_successor_available_after_post_fold_advance input fold
          finalTrial beforeAdvance between afterChild advanceActor childActor
          parent advanced bounded childInput childAnswer laterExact
            parentBeforeAdvance
      have laterNodup : (fold.later.map causalInput?).Nodup := by
        have rootNodup := exact_root_record_causal_inputs_nodup input
        rw [fold.rootDecomposition, List.map_append] at rootNodup
        exact (List.nodup_append.mp rootNodup).2.1.tail
      have childPrefixExact' : childBefore = beforeAdvance ++
          [(.machineFresh advanceActor (gammaAdvanceInput parent.digest)
            advanced : UnifiedExposureRecord)] ++ between := by
        apply alpha_mapped_nodup_selected_prefix_eq causalInput? fold.later
          childBefore childLater
          (beforeAdvance ++
            [(.machineFresh advanceActor (gammaAdvanceInput parent.digest)
              advanced : UnifiedExposureRecord)] ++ between)
          afterChild
          (.machineFresh childActor childInput childAnswer :
            UnifiedExposureRecord)
          (.machineFresh childActor childInput childAnswer :
            UnifiedExposureRecord)
          laterNodup childLaterExact (by
            simpa [List.append_assoc] using laterExact) rfl
      have childPrefixExact : childBefore = beforeAdvance ++
          (.machineFresh advanceActor (gammaAdvanceInput parent.digest)
            advanced : UnifiedExposureRecord) :: between := by
        simpa using childPrefixExact'
      rw [childPrefixExact]
      simpa [next] using nextBeforeChild

/-- The exact per-block disposition trace.  Its state and offset indices follow
the duplex chain directly, avoiding proof-term-heavy random-access indices. -/
inductive ExactFoldAlphaOutputDispositions
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
    (finalTrial : ExactCompilerExposureTrial parameters) :
    Nat → Digest256 → List Digest256 → List Digest256 → Prop where
  | done (offset : Nat) (state : Digest256) :
      ExactFoldAlphaOutputDispositions input fold finalTrial offset state [] []
  | next {offset : Nat} {state output advanced : Digest256}
      {outputs advances : List Digest256}
      (blockBound : offset < 4)
      (outputLookup : tableLookup (exactOperationalTable input)
        (gammaOutputInput state) = some output)
      (disposition :
        (∃ actor,
          (.machineFresh actor (gammaOutputInput state) output :
            UnifiedExposureRecord) ∈ fold.prior) ∨
        causalRoutedAnswer? (some (Sum.inl ⟨offset, blockBound⟩))
          (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
            transitionFuel fold.trial.val finalTrial.val
            (exactPlainRomCursor configuration sample.1).erase)
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
          some output)
      (tail : ExactFoldAlphaOutputDispositions input fold finalTrial
        (offset + 1) advanced outputs advances) :
      ExactFoldAlphaOutputDispositions input fold finalTrial offset state
        (output :: outputs) (advanced :: advances)

/-- Recursive fold over the literal accepted alpha chain.  Every consumed
output receives the exact cached-or-routed disposition trace. -/
theorem exact_certified_fold_alpha_chain_output_dispositions
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
    (seed : AlphaZeroProducer)
    (seedExact : seed =
      { digest := fold.boundaryAnswer, block := 0,
        sourceInput := bytes fold.digest ++
          [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected }) :
    ∀ {producerInput : ShaInput} {digest : Digest256}
      {outputs advances : List Digest256}
      (block : Fin 4)
      (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
        advances)
      (lengthCap : block.val + outputs.length ≤ 4)
      (certificate : ExactFoldAlphaProducerCertificate input fold finalTrial
        seed (AlphaZeroProducer.mk digest block producerInput)),
      ExactFoldAlphaOutputDispositions input fold finalTrial block.val digest
        outputs advances := by
  intro producerInput digest outputs advances block chain
  induction chain generalizing block with
  | done producerInput digest producerFound =>
      intro lengthCap certificate
      exact .done block.val digest
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail
      ih =>
      intro lengthCap certificate
      have blockBound : block.val < 4 := by
        simp only [List.length_cons] at lengthCap
        omega
      have headDisposition := exact_certified_fold_alpha_output_cached_or_routed
        programmedCover input fold finalTrial seed
          { digest := digest, block := block, sourceInput := producerInput }
          output certificate outputFound producerBeforeOutput
      cases outputs with
      | nil =>
          have advancesEmpty : advances = [] := by
            have lengths := exact_root_ordered_q16_chain_lengths tail
            exact List.length_eq_zero_iff.mp (by simpa using lengths)
          subst advances
          refine .next blockBound outputFound ?_
            (.done (block.val + 1) advanced)
          rw [show (⟨block.val, blockBound⟩ : Fin 4) = block by
            apply Fin.ext
            rfl]
          exact headDisposition
      | cons nextOutput tailOutputs =>
          have nextBound : block.val + 1 < 4 := by
            simp only [List.length_cons] at lengthCap
            omega
          let nextBlock : Fin 4 := ⟨block.val + 1, nextBound⟩
          let nextProducer : AlphaZeroProducer :=
            { digest := advanced, block := nextBlock,
              sourceInput := gammaAdvanceInput digest }
          obtain ⟨advanceRootBefore, advanceRootMiddle, advanceRootAfter,
              advanceOrder⟩ := producerBeforeAdvance
          have nextCertificate : ExactFoldAlphaProducerCertificate input fold
              finalTrial seed nextProducer := by
            have advancedCertificate :=
              exact_fold_alpha_producer_certificate_advance input fold
                finalTrial seed
                { digest := digest, block := block,
                  sourceInput := producerInput }
                advanced nextBound certificate advanceFound
                  advanceRootBefore advanceRootMiddle advanceRootAfter
                    advanceOrder seedExact
            simpa [nextProducer, nextBlock] using advancedCertificate
          have tailLengthCap : nextBlock.val +
              (nextOutput :: tailOutputs).length ≤ 4 := by
            simp only [List.length_cons] at lengthCap
            simp [nextBlock]
            omega
          have tailDispositions := ih nextBlock tailLengthCap nextCertificate
          refine .next blockBound outputFound ?_ ?_
          · rw [show (⟨block.val, blockBound⟩ : Fin 4) = block by
              apply Fin.ext
              rfl]
            exact headDisposition
          · change ExactFoldAlphaOutputDispositions input fold finalTrial
              (block.val + 1) advanced (nextOutput :: tailOutputs) advances
              at tailDispositions
            exact tailDispositions

/-- Exact accepted-source specialization: the complete consumed alpha chain
starts at block zero and carries a disposition for every deployed output. -/
theorem exact_accepted_fold_alpha_output_dispositions
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
    ExactFoldAlphaOutputDispositions input fold finalTrial 0
      fold.boundaryAnswer fold.alphaOutputs fold.alphaAdvances := by
  let target := bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected
  let seed : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0, sourceInput := target }
  have chain :=
    AspisK1.V7Tag73ExactAcceptedFoldAlphaChainOrder.exact_accepted_fold_alpha_chain_has_root_order
      transitionRoom input fold
  have certificate := exact_fold_alpha_boundary_producer_certificate input fold
    finalTrial
  have lengthCap : (0 : Fin 4).val + fold.alphaOutputs.length ≤ 4 := by
    rw [fold.alphaOutputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        (.alpha 0)).withinDeployedCap
  exact exact_certified_fold_alpha_chain_output_dispositions programmedCover
    input fold finalTrial seed (by rfl) 0 (by simpa [seed, target] using chain)
      lengthCap (by simpa [seed, target] using certificate)

#print axioms exact_fold_alpha_boundary_producer_certificate
#print axioms exact_certified_fold_alpha_output_cached_or_routed
#print axioms exact_cached_certified_producer_member_after_fold
#print axioms exact_fold_later_strict_record_order_split
#print axioms machine_pair_mem_filterMap_has_record
#print axioms exact_fold_alpha_producer_certificate_advance
#print axioms ExactFoldAlphaOutputDispositions
#print axioms exact_certified_fold_alpha_chain_output_dispositions
#print axioms exact_accepted_fold_alpha_output_dispositions

end

end AspisK1.V7Tag73ExactFoldArmedAlphaChainDisposition
