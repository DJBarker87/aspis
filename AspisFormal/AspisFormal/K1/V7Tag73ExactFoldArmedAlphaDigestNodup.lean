import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaPrefixInvariant

/-!
# Digest uniqueness for literal fold-armed alpha producers

The fold-armed prefix invariant already proves that every live alpha producer
has a literal machine-fresh source record in the consumed root prefix, and
that producer source inputs are unique.  Exact compiler roots additionally
have unique fresh answers.  Together these facts imply the missing executable
controller condition: live producer digests are duplicate-free.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaDigestNodup

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Literal source provenance and duplicate-free source answers force the
live alpha producer digest inventory to be duplicate-free. -/
theorem fold_armed_alpha_producer_digests_nodup_of_literal_sources
    (records : List UnifiedExposureRecord)
    (memory : FoldArmedAlphaZeroMemory)
    (invariant : FoldArmedAlphaPrefixInvariant records memory)
    (recordAnswersNodup :
      (records.map UnifiedExposureRecord.answer).Nodup) :
    (memory.alpha.producers.map AlphaZeroProducer.digest).Nodup := by
  have producerNodup : memory.alpha.producers.Nodup :=
    List.Nodup.of_map AlphaZeroProducer.block
      invariant.core.producer.blocksNodup
  apply producerNodup.map_on
  intro left leftMember right rightMember digestExact
  obtain ⟨leftActor, leftRecordMember⟩ :=
    invariant.sourcesLiteral left leftMember
  obtain ⟨rightActor, rightRecordMember⟩ :=
    invariant.sourcesLiteral right rightMember
  have recordExact :
      (.machineFresh leftActor left.sourceInput left.digest :
          UnifiedExposureRecord) =
        .machineFresh rightActor right.sourceInput right.digest := by
    apply List.inj_on_of_nodup_map recordAnswersNodup leftRecordMember
      rightRecordMember
    simpa [UnifiedExposureRecord.answer] using digestExact
  have sourceExact : left.sourceInput = right.sourceInput := by
    injection recordExact
  exact List.inj_on_of_nodup_map
    invariant.core.producer.sourceInputsNodup leftMember rightMember sourceExact

/-- Exact accepted-root form used by post-fold source routing. -/
theorem exact_fold_armed_post_fold_prefix_producer_digests_nodup
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
    (segment rest : List UnifiedExposureRecord)
    (laterExact : fold.later = segment ++ rest) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let reached := indexedStateAfterRecords transitionFuel controller segment
      afterFold
    (reached.memory.2.1.alpha.producers.map
      AlphaZeroProducer.digest).Nodup := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  let afterFold := controller.afterAnswer transitionFuel reachedFold
    fold.answer
  let consumed := fold.prior ++ [selected]
  let reached := indexedStateAfterRecords transitionFuel controller segment
    afterFold
  have invariant : FoldArmedAlphaPrefixInvariant (consumed ++ segment)
      reached.memory.2.1 := by
    simpa [controller, initial, reachedFold, selected, afterFold, consumed,
      reached] using exact_fold_armed_post_fold_prefix_invariant input fold
        finalTrial segment rest laterExact
  have rootNodup := exact_root_record_answers_nodup input
  have consumedNodup :
      ((consumed ++ segment).map UnifiedExposureRecord.answer).Nodup := by
    rw [fold.rootDecomposition, laterExact] at rootNodup
    have normalized :
        ((consumed ++ segment).map UnifiedExposureRecord.answer ++
          rest.map UnifiedExposureRecord.answer).Nodup := by
      simpa [consumed, selected, List.map_append, List.append_assoc] using
        rootNodup
    exact (List.nodup_append.mp normalized).1
  dsimp only
  exact fold_armed_alpha_producer_digests_nodup_of_literal_sources
    (consumed ++ segment) reached.memory.2.1 invariant consumedNodup

#print axioms
  fold_armed_alpha_producer_digests_nodup_of_literal_sources
#print axioms
  exact_fold_armed_post_fold_prefix_producer_digests_nodup

end

end AspisK1.V7Tag73ExactFoldArmedAlphaDigestNodup
