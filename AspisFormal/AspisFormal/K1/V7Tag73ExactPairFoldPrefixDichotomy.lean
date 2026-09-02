import AspisFormal.K1.V7Tag73ExactPairAlphaValueClosure

/-!
# Selected-fold prefix dichotomy on an adversary-first K1.3 fibre

The final-pair replay already fixes a literal source prefix without fixing any
q16 coordinate.  If the selected fold exposure lies inside that prefix, the
two accepted executions therefore have exactly the same fold prefix.  This
isolates the only remaining alpha-routing case honestly: a fold-work query
delayed until after the replayed final-pair prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactPairFoldPrefixDichotomy

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldArmedFinalPairPrefix
open AspisK1.V7Tag73ExactPairAlphaValueClosure
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The final-pair common prefix either already contains the selected fold
position, in which case both literal fold prefixes are equal, or it ends no
later than that position.  The second disjunct is the precise delayed-fold
case left for the causal alpha proof. -/
theorem exact_fixed_clean_pair_k13_fold_prefix_eq_or_after_final_pair_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1)
    (workExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.2.1) :
    let leftFold := exactAcceptedFoldTrial leftWitness.joint.input
    let rightFold := exactAcceptedFoldTrial rightWitness.joint.input
    leftFold.prior = rightFold.prior \/
      ∃ completed rootRemaining tapeRemaining,
        exactFixedRootRecords leftWitness.joint.input.package.root =
            completed ++ rootRemaining /\
          freshAnswerTapeToList right =
            completed.map UnifiedExposureRecord.answer ++ tapeRemaining /\
          completed.length ≤ foldTrial.val := by
  let leftFold := exactAcceptedFoldTrial leftWitness.joint.input
  let rightFold := exactAcceptedFoldTrial rightWitness.joint.input
  obtain ⟨completed, rootRemaining, tapeRemaining, rootExact, tapeExact⟩ :=
    exact_fixed_clean_pair_k13_has_common_final_absorb_tape_prefix foldTrial
      finalTrial hidden left right leftWitness programmedCover contextExact
        foldExact workExact
  by_cases inside : foldTrial.val < completed.length
  · left
    have priorLength : leftFold.prior.length = foldTrial.val := by
      have trialExact := leftFold.trialExact
      rw [leftWitness.foldExact] at trialExact
      exact trialExact.symm
    have priorLe : leftFold.prior.length <= completed.length := by omega
    have priorPrefixRoot : leftFold.prior <+:
        exactFixedRootRecords leftWitness.joint.input.package.root := by
      rw [leftFold.rootDecomposition]
      exact leftFold.prior.prefix_append _
    have priorPrefixCompleted : leftFold.prior <+: completed := by
      apply (List.isPrefix_append_of_length priorLe).mp
      simpa [rootExact] using priorPrefixRoot
    obtain ⟨suffix, completedExact⟩ := priorPrefixCompleted
    have rightTapeFromLeft : ∃ remaining,
        freshAnswerTapeToList right =
          leftFold.prior.map UnifiedExposureRecord.answer ++ remaining := by
      refine ⟨suffix.map UnifiedExposureRecord.answer ++ tapeRemaining, ?_⟩
      rw [tapeExact, ← completedExact, List.map_append, List.append_assoc]
    exact exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix foldTrial
      hidden left right leftWitness.joint.input rightWitness.joint.input
      leftFold.prior leftFold.later rightFold.prior rightFold.later
      leftFold.actor rightFold.actor
      (bytes leftFold.digest ++ [domGrind] ++
        bytes (exactOperationalTape leftWitness.joint.input).messages.foldGrinding.selected)
      (bytes rightFold.digest ++ [domGrind] ++
        bytes (exactOperationalTape rightWitness.joint.input).messages.foldGrinding.selected)
      leftFold.answer rightFold.answer leftFold.rootDecomposition
      rightFold.rootDecomposition
      (by
        have trialExact := leftFold.trialExact
        rwa [leftWitness.foldExact] at trialExact)
      (by
        have trialExact := rightFold.trialExact
        rwa [rightWitness.foldExact] at trialExact)
      rightTapeFromLeft
  · right
    exact ⟨completed, rootRemaining, tapeRemaining, rootExact, tapeExact,
      Nat.le_of_not_gt inside⟩

#print axioms
  exact_fixed_clean_pair_k13_fold_prefix_eq_or_after_final_pair_prefix

end

end AspisK1.V7Tag73ExactPairFoldPrefixDichotomy
