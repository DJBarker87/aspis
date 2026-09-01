import AspisFormal.K1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
import AspisFormal.K1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization
import AspisFormal.K1.V7Tag73ExactFoldAlphaQ16OperationalRealization

/-!
# Exact two-trial K1.3 probability closure

This module connects the accepted fold-work and final-work exposure records to
the separately indexed 31-bit/34-bit probability theorem.  The first small
step proves that the exposure selected by an exact final-work pair is unique;
this lets an existing K1.3 failure witness and the complete 518-coordinate
router use literally the same final trial.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactPairTrialProbabilityClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedCleanQ16ResidualFactorization
open AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- In a duplicate-free list, two decompositions selecting the same value have
the same prefix length. -/
theorem nodup_selected_prefix_length_unique
    {α : Type} {records priorLeft laterLeft priorRight laterRight : List α}
    {selected : α}
    (nodup : records.Nodup)
    (leftExact : records = priorLeft ++ selected :: laterLeft)
    (rightExact : records = priorRight ++ selected :: laterRight) :
    priorLeft.length = priorRight.length := by
  have leftAt : records[priorLeft.length]? = some selected := by
    rw [leftExact]
    simp
  have rightAt : records[priorRight.length]? = some selected := by
    rw [rightExact]
    simp
  have leftBound : priorLeft.length < records.length := by
    rw [leftExact]
    simp
  exact (List.getElem?_inj leftBound nodup).mp (leftAt.trans rightAt.symm)

/-- Point-index form of the same uniqueness fact. -/
theorem nodup_selected_index_unique
    {α : Type} {records : List α} {left right : Nat} {selected : α}
    (nodup : records.Nodup)
    (leftAt : records[left]? = some selected)
    (rightAt : records[right]? = some selected) : left = right := by
  have leftBound : left < records.length :=
    (List.getElem?_eq_some_iff.mp leftAt).1
  exact (List.getElem?_inj leftBound nodup).mp (leftAt.trans rightAt.symm)

/-- The causal-DAG final pair fixes one literal earliest exposure.  Therefore
two certificates for the same accepted input/key/answers select the same
compiler trial. -/
theorem exact_dag_final_work_pair_labeled_trial_unique
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
    (left right : ExactCompilerExposureTrial parameters)
    (key : RawFinalWorkKey) (workAnswer base : Digest256)
    (leftLabeled : ExactDagFinalWorkPairLabeled input left key workAnswer base)
    (rightLabeled : ExactDagFinalWorkPairLabeled input right key workAnswer base) :
    left = right := by
  have rootNodup := exact_root_record_causal_inputs_nodup input
  rcases leftLabeled with
      ⟨leftPrior, leftMiddle, leftLater, leftWorkActor, leftAbsorbActor,
        leftRoot, leftTrial⟩ |
      ⟨leftPrior, leftMiddle, leftLater, leftWorkActor, leftAbsorbActor,
        leftRoot, leftTrial⟩ <;>
    rcases rightLabeled with
      ⟨rightPrior, rightMiddle, rightLater, rightWorkActor, rightAbsorbActor,
        rightRoot, rightTrial⟩ |
      ⟨rightPrior, rightMiddle, rightLater, rightWorkActor, rightAbsorbActor,
        rightRoot, rightTrial⟩
  · apply Fin.ext
    rw [leftTrial, rightTrial]
    exact nodup_selected_index_unique rootNodup
      (selected := some key.workInput)
      (by rw [leftRoot]; simp [List.map_append, causalInput?])
      (by rw [rightRoot]; simp [List.map_append, causalInput?])
  · exfalso
    have workPosition : leftPrior.length =
        (rightPrior ++
          (.machineFresh rightAbsorbActor key.absorbInput base :
            UnifiedExposureRecord) :: rightMiddle).length := by
      exact nodup_selected_index_unique rootNodup
        (selected := some key.workInput)
        (by rw [leftRoot]; simp [List.map_append, causalInput?])
        (by rw [rightRoot]; simp [List.map_append, causalInput?])
    have absorbPosition :
        (leftPrior ++
          (.machineFresh leftWorkActor key.workInput workAnswer :
            UnifiedExposureRecord) :: leftMiddle).length = rightPrior.length := by
      exact nodup_selected_index_unique rootNodup
        (selected := some key.absorbInput)
        (by rw [leftRoot]; simp [List.map_append, causalInput?])
        (by rw [rightRoot]; simp [List.map_append, causalInput?])
    simp only [List.length_append, List.length_cons] at workPosition absorbPosition
    omega
  · exfalso
    have absorbPosition : leftPrior.length =
        (rightPrior ++
          (.machineFresh rightWorkActor key.workInput workAnswer :
            UnifiedExposureRecord) :: rightMiddle).length := by
      exact nodup_selected_index_unique rootNodup
        (selected := some key.absorbInput)
        (by rw [leftRoot]; simp [List.map_append, causalInput?])
        (by rw [rightRoot]; simp [List.map_append, causalInput?])
    have workPosition :
        (leftPrior ++
          (.machineFresh leftAbsorbActor key.absorbInput base :
            UnifiedExposureRecord) :: leftMiddle).length = rightPrior.length := by
      exact nodup_selected_index_unique rootNodup
        (selected := some key.workInput)
        (by rw [leftRoot]; simp [List.map_append, causalInput?])
        (by rw [rightRoot]; simp [List.map_append, causalInput?])
    simp only [List.length_append, List.length_cons] at absorbPosition workPosition
    omega
  · apply Fin.ext
    rw [leftTrial, rightTrial]
    exact nodup_selected_index_unique rootNodup
      (selected := some key.absorbInput)
      (by rw [leftRoot]; simp [List.map_append, causalInput?])
      (by rw [rightRoot]; simp [List.map_append, causalInput?])

/-- A pair-label certificate exposes both literal root records, independent of
which of them was encountered first. -/
theorem exact_dag_final_work_pair_labeled_members
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
    ∃ workActor absorbActor,
      (.machineFresh workActor key.workInput workAnswer :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root ∧
      (.machineFresh absorbActor key.absorbInput base :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
  rcases labeled with
      ⟨prior, middle, later, workActor, absorbActor, rootExact, _trialExact⟩ |
      ⟨prior, middle, later, workActor, absorbActor, rootExact, _trialExact⟩
  · refine ⟨workActor, absorbActor, ?_, ?_⟩ <;> rw [rootExact] <;> simp
  · refine ⟨workActor, absorbActor, ?_, ?_⟩ <;> rw [rootExact] <;> simp

/-- Two accepted pair certificates with the same final nonce and q16 base
must use the same pre-final digest, work answer, and exposure trial. -/
theorem exact_literal_final_work_pair_trial_unique_of_base
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
    (left right : ExactCompilerExposureTrial parameters)
    (leftDigest rightDigest leftWork rightWork base : Digest256)
    (nonce : NonceBytes)
    (leftLabeled : ExactDagFinalWorkPairLabeled input left
      (literalFinalWorkKey leftDigest nonce) leftWork base)
    (rightLabeled : ExactDagFinalWorkPairLabeled input right
      (literalFinalWorkKey rightDigest nonce) rightWork base) :
    left = right := by
  obtain ⟨leftWorkActor, leftAbsorbActor, leftWorkMember, leftAbsorbMember⟩ :=
    exact_dag_final_work_pair_labeled_members input left
      (literalFinalWorkKey leftDigest nonce) leftWork base leftLabeled
  obtain ⟨rightWorkActor, rightAbsorbActor, rightWorkMember,
      rightAbsorbMember⟩ :=
    exact_dag_final_work_pair_labeled_members input right
      (literalFinalWorkKey rightDigest nonce) rightWork base rightLabeled
  have absorbRecordExact :
      (.machineFresh leftAbsorbActor
          (literalFinalWorkKey leftDigest nonce).absorbInput base :
          UnifiedExposureRecord) =
        (.machineFresh rightAbsorbActor
          (literalFinalWorkKey rightDigest nonce).absorbInput base :
          UnifiedExposureRecord) :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      leftAbsorbMember rightAbsorbMember rfl
  have absorbInputExact :
      (literalFinalWorkKey leftDigest nonce).absorbInput =
        (literalFinalWorkKey rightDigest nonce).absorbInput := by
    injection absorbRecordExact
  have digestExact : leftDigest = rightDigest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) absorbInputExact
    simpa [RawFinalWorkKey.absorbInput, literalFinalWorkKey] using prefixExact
  subst rightDigest
  have workRecordExact :
      (.machineFresh leftWorkActor
          (literalFinalWorkKey leftDigest nonce).workInput leftWork :
          UnifiedExposureRecord) =
        (.machineFresh rightWorkActor
          (literalFinalWorkKey leftDigest nonce).workInput rightWork :
          UnifiedExposureRecord) :=
    List.inj_on_of_nodup_map (exact_root_record_causal_inputs_nodup input)
      leftWorkMember rightWorkMember rfl
  have workExact : leftWork = rightWork := by
    injection workRecordExact
  subst rightWork
  exact exact_dag_final_work_pair_labeled_trial_unique input left right
    (literalFinalWorkKey leftDigest nonce) leftWork base leftLabeled rightLabeled

/-- The final trial retained by every existing K1.3 joint witness is exactly
the final trial used by the canonical complete accepted router. -/
theorem exact_fixed_k13_actual_trial_eq_accepted_installation
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial) :
    trial = (exactAcceptedDagInstallation transitionRoom input).finalTrial := by
  obtain ⟨digest, workAnswer, base, _workAccepted, _prefinal, baseExact,
      pairLabeled, _workLabeled, _workCoordinate, _realized⟩ := actual
  let source := exactAcceptedDagInstallation transitionRoom input
  have baseSame : base = source.base := baseExact.trans source.baseExact.symm
  have sourcePair : ExactDagFinalWorkPairLabeled input source.finalTrial
      (literalFinalWorkKey source.digest
        (exactOperationalTape input).messages.finalGrinding.selected)
      source.workAnswer base := by
    simpa only [baseSame] using source.pairLabeled
  exact exact_literal_final_work_pair_trial_unique_of_base input trial
    source.finalTrial digest source.digest workAnswer source.workAnswer base
    (exactOperationalTape input).messages.finalGrinding.selected pairLabeled
    sourcePair

/-- The complete 518-coordinate realization can be retained with the exact
final trial already carried by a K1.3 joint witness. -/
theorem exact_fixed_k13_actual_fold_alpha_q16_realization
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    ∃ realization : ExactAcceptedFoldAlphaQ16Realization input,
      realization.anchor.finalTrial = trial ∧
      realization.anchor.boundaryIndex = 0 ∧
      realization.anchor.fold.trial = (exactAcceptedFoldTrial input).trial := by
  let anchor := exactAcceptedFoldAlphaQ16Anchor transitionRoom programmedCover
    input
  have forestRealized : OperationalQ16ForestRealization
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        anchor.router sample.2).2.2.2 := by
    rw [anchor.routerExact]
    exact exact_compiler_fold_alpha_q16_forest_realization transitionRoom
      programmedCover input anchor.fold anchor.finalTrial anchor.boundaryIndex
      anchor.base anchor.baseExact anchor.installed frontierExact
  refine ⟨{ anchor := anchor, forestRealized := forestRealized }, ?_, rfl, rfl⟩
  change (exactAcceptedDagInstallation transitionRoom input).finalTrial = trial
  exact (exact_fixed_k13_actual_trial_eq_accepted_installation transitionRoom
    input trial actual).symm

/-! ## Exact clean pair-indexed event -/

/-- One clean K1.3 failure indexed by both literal positioned work trials. -/
structure ExactFixedCleanK13PairTrialWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) : Type where
  joint : ExactFixedK13JointTrialWitness transitionFuel configuration
    projection fixedInstance decoder sample finalTrial
  legal : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
    configuration projection fixedInstance
  foldExact : (exactAcceptedFoldTrial joint.input).trial = foldTrial

def exactFixedCleanK13PairTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | Nonempty (ExactFixedCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder sample foldTrial finalTrial)}

/-- Every clean K1.3 query failure chooses its literal fold/final trial pair. -/
theorem exact_fixed_clean_k13_query_event_subset_pair_trial_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance ∩
      exactTag73K13QueryEvent transitionFuel configuration projection
        fixedInstance decoder) ⊆
      ⋃ foldTrial : ExactCompilerExposureTrial parameters,
        ⋃ finalTrial : ExactCompilerExposureTrial parameters,
          exactFixedCleanK13PairTrialEvent transitionFuel configuration
            projection fixedInstance decoder foldTrial finalTrial := by
  intro sample member
  obtain ⟨finalTrial, finalMember⟩ :=
    exact_fixed_k13_query_failure_has_joint_trial_witness transitionRoom
      (by omega) source (frontierExact sample) member.2
  let joint := Classical.choice finalMember
  let foldTrial := (exactAcceptedFoldTrial joint.input).trial
  apply Set.mem_iUnion.mpr
  refine ⟨foldTrial, Set.mem_iUnion.mpr ⟨finalTrial, ?_⟩⟩
  exact ⟨{ joint := joint, legal := member.1, foldExact := rfl }⟩

#print axioms nodup_selected_prefix_length_unique
#print axioms nodup_selected_index_unique
#print axioms exact_dag_final_work_pair_labeled_trial_unique
#print axioms exact_dag_final_work_pair_labeled_members
#print axioms exact_literal_final_work_pair_trial_unique_of_base
#print axioms exact_fixed_k13_actual_trial_eq_accepted_installation
#print axioms exact_fixed_k13_actual_fold_alpha_q16_realization
#print axioms ExactFixedCleanK13PairTrialWitness
#print axioms exact_fixed_clean_k13_query_event_subset_pair_trial_union

end

end AspisK1.V7Tag73ExactPairTrialProbabilityClosure
