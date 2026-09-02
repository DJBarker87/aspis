import AspisFormal.K1.V7Tag73ExactPairAlphaValueClosure
import AspisFormal.K1.V7Tag73FoldArmedWorkConditionedPrefix

/-!
# Selected-fold prefix equality or an earlier q16 coordinate

Equal residual, alpha, fold-work, and final-work coordinates replay every
prefix which has not consumed a q16 named slot.  Applied at the selected fold
cut, this gives the exact remaining adversary-first dichotomy: either the two
accepted fold prefixes coincide, or the left prefix already contains a named
q16 exposure.  No ordering assumption is imposed on the adversary.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactPairFoldQ16Dichotomy

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedWorkConditionedPrefix
open AspisK1.V7Tag73FoldAlphaPreFinalPrefix
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- At the selected fold cut, fixed non-q16 coordinates either determine the
complete literal prefix or that prefix has already consumed a named q16 slot.
The latter is the only causal-order case left for the K1.3 fibre proof. -/
theorem exact_fixed_clean_pair_k13_fold_priors_eq_or_prior_q16
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
    leftFold.prior = rightFold.prior ∨
      ∃ slot ∈ namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel
            (foldArmedCompleteController
              (globalOracleCalls := globalFull256OracleCallCap parameters)
              transitionFuel foldTrial.val finalTrial.val)
            (foldArmedInitialState
              (exactPlainRomCursor configuration hidden).erase)
            leftFold.prior),
        ∃ query : Fin 64 × Fin 8, slot = some (Sum.inr (some query)) := by
  let leftFold := exactAcceptedFoldTrial leftWitness.joint.input
  let rightFold := exactAcceptedFoldTrial rightWitness.joint.input
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration hidden).erase
  let labels := namedTraceSlots
    (indexedControllerLabeledRecords transitionFuel controller initial
      leftFold.prior)
  by_cases noQ16 : ∀ slot ∈ labels,
      slot = none ∨
        (∃ alpha : Fin 4, slot = some (Sum.inl alpha)) ∨
        slot = some (Sum.inr none)
  · left
    obtain ⟨rightRemaining, rightTapePrefix⟩ :=
      exact_fold_armed_coordinates_force_work_conditioned_prefix
        leftWitness.joint.input foldTrial finalTrial leftFold.prior
          ((.machineFresh leftFold.actor
            (bytes leftFold.digest ++ [domGrind] ++
              bytes (exactOperationalTape leftWitness.joint.input).messages.foldGrinding.selected)
            leftFold.answer : UnifiedExposureRecord) :: leftFold.later)
          (by simpa only [List.cons_append] using leftFold.rootDecomposition)
          programmedCover right contextExact foldExact workExact (by
            simpa [labels, controller, initial] using noQ16)
    rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
      at rightTapePrefix
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
      ⟨rightRemaining, rightTapePrefix⟩
  · right
    push Not at noQ16
    obtain ⟨slot, slotMember, forbidden⟩ := noQ16
    refine ⟨slot, by simpa [labels, controller, initial] using slotMember, ?_⟩
    rcases slot with _ | slot
    · exact (forbidden.1 rfl).elim
    · rcases slot with alpha | workOrQ16
      · exact (forbidden.2.1 alpha rfl).elim
      · rcases workOrQ16 with _ | query
        · exact (forbidden.2.2 rfl).elim
        · exact ⟨query, rfl⟩

#print axioms exact_fixed_clean_pair_k13_fold_priors_eq_or_prior_q16

end

end AspisK1.V7Tag73ExactPairFoldQ16Dichotomy
