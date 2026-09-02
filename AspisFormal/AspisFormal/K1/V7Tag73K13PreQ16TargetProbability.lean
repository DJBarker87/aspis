import AspisFormal.K1.V7Tag73K13PreQ16TargetActualBridge
import AspisFormal.K1.V7Tag73K12ExactFailureProbability

/-!
# Probability handoff for Tag-73 pre-q16 Merkle targets

The event in this file is on the exact compiler sample space.  For each fixed
hidden prover tape, its fresh-answer slice is transported by the canonical
length cast to the causal target tree proved in the preceding modules.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16TargetProbability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K12ExactFailureProbability
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16TargetActualBridge
open AspisK1.V7Tag73K13PreQ16TargetSchedulerTree
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerkleFirstUnresolvedBinding

noncomputable section

def canonicalPreQ16MerkleTargetHitEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    Set (FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :=
  {tape |
    (preQ16MerkleTargetTree
      (globalFull256OracleCallCap parameters)
      (unifiedFull256ExposureCap parameters) transitionFuel
      (exactPlainRomCursor configuration hidden).erase).everHits
        (castFreshAnswerTape (preQ16MasterLengthEq parameters) tape)}

theorem canonical_preQ16_merkle_target_hit_probability_le_exact_count
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    (uniformDigestFreshTape
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (canonicalPreQ16MerkleTargetHitEvent configuration transitionFuel
          hidden) ≤
      ((((preQ16MerkleTargetCapsFrom 0
            (unifiedFull256ExposureCap parameters)).sum) *
          (2 ^ 256) ^ (unifiedFull256ExposureCap parameters - 1) : Nat) :
          ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          unifiedFull256ExposureCap parameters) := by
  let tree := preQ16MerkleTargetTree
    (globalFull256OracleCallCap parameters)
    (unifiedFull256ExposureCap parameters) transitionFuel
    (exactPlainRomCursor configuration hidden).erase
  let equiv := castFreshAnswerTape (Output := Digest256)
    (preQ16MasterLengthEq parameters)
  have transported := uniform_of_fintype_equiv_preimage_probability_eq equiv
    (causalHitEvent tree)
  have eventExact : equiv ⁻¹' causalHitEvent tree =
      canonicalPreQ16MerkleTargetHitEvent configuration transitionFuel hidden :=
    rfl
  rw [eventExact] at transported
  have counted := pre_q16_merkle_target_tree_uniform_probability_le
    (globalFull256OracleCallCap parameters)
    (unifiedFull256ExposureCap parameters) transitionFuel
    (exactPlainRomCursor configuration hidden).erase
  rw [show
      (uniformDigestFreshTape
        (exactCompilerTargetCaps parameters).length).toOuterMeasure
          (canonicalPreQ16MerkleTargetHitEvent configuration transitionFuel
            hidden) =
        (uniformDigestFreshTape
          (preQ16MerkleTargetCapsFrom 0
            (unifiedFull256ExposureCap parameters)).length).toOuterMeasure
          (causalHitEvent tree) by
      simpa only [uniformDigestFreshTape] using transported]
  exact counted

def exactK13PreQ16MerkleTargetHitEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (transitionFuel : Nat) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | sample.2 ∈
    canonicalPreQ16MerkleTargetHitEvent configuration transitionFuel sample.1}

theorem exact_k13_preQ16_merkle_target_hit_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (transitionFuel : Nat) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactK13PreQ16MerkleTargetHitEvent configuration transitionFuel) ≤
      ((((preQ16MerkleTargetCapsFrom 0
            (unifiedFull256ExposureCap parameters)).sum) *
          (2 ^ 256) ^ (unifiedFull256ExposureCap parameters - 1) : Nat) :
          ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          unifiedFull256ExposureCap parameters) := by
  unfold exactCompilerJointLaw
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact canonical_preQ16_merkle_target_hit_probability_le_exact_count
    configuration transitionFuel hidden

/-- Operational event exposing exactly the accepted-trial late-target witness
needed by the deterministic actual-run bridge. -/
def exactK13PreQ16LateTargetEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (trial : ExactCompilerExposureTrial parameters)
      (prior later : List UnifiedExposureRecord)
      (pivotActor : QueryActor) (pivotInput : ShaInput) (pivotAnswer : Digest256),
    ExactFixedK13ActualJointTrial input trial ∧
    exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
        UnifiedExposureRecord) :: later ∧
    trial.val = prior.length ∧
    PrefixResolutionLateTargetHit (exactK12Truncate input)
      (exposurePrefixRawQueries prior) (exactK12OrderedQueries input)
      (exactK12Roots input) (exactK12Openings input)}

theorem exact_k13_preQ16_late_target_subset_hit_event
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 2 ≤ transitionFuel) :
    exactK13PreQ16LateTargetEvent transitionFuel configuration projection
        fixedInstance ⊆
      exactK13PreQ16MerkleTargetHitEvent configuration transitionFuel := by
  intro sample member
  rcases member with
    ⟨input, trial, prior, later, pivotActor, pivotInput, pivotAnswer, actual,
      rootExact, trialExact, lateHit⟩
  exact exact_actual_late_target_implies_master_scheduler_hit transitionRoom
    input trial actual prior later pivotActor pivotInput pivotAnswer rootExact
      trialExact lateHit

theorem exact_k13_preQ16_late_target_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 2 ≤ transitionFuel) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactK13PreQ16LateTargetEvent transitionFuel configuration projection
          fixedInstance) ≤
      ((((preQ16MerkleTargetCapsFrom 0
            (unifiedFull256ExposureCap parameters)).sum) *
          (2 ^ 256) ^ (unifiedFull256ExposureCap parameters - 1) : Nat) :
          ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          unifiedFull256ExposureCap parameters) := by
  exact ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
    (exact_k13_preQ16_late_target_subset_hit_event transitionFuel configuration
      projection fixedInstance transitionRoom)).trans
    (exact_k13_preQ16_merkle_target_hit_probability_le hiddenLaw configuration
      transitionFuel)

#print axioms canonical_preQ16_merkle_target_hit_probability_le_exact_count
#print axioms exact_k13_preQ16_merkle_target_hit_probability_le
#print axioms exact_k13_preQ16_late_target_subset_hit_event
#print axioms exact_k13_preQ16_late_target_probability_le

end

end AspisK1.V7Tag73K13PreQ16TargetProbability
