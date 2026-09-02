import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaInitialAvailability
import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant

/-!
# Hybrid cached/named alpha answer equality

The fold-armed alpha controller deliberately leaves an adversary-first split:
an alpha output already created before the selected fold is part of the shared
root prefix, while a genuinely post-fold output occupies its named alpha slot.
This leaf joins those cases across two clean fibres.  A cached answer is fixed
by first-input uniqueness in the other exact root; only the both-post-fold case
uses equality of the named coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactPairAlphaHybridEquality

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A machine record transported through a shared prefix has the same answer
as any record at the same SHA input in the other exact root.  The second record
need not itself be in the shared prefix; root-wide first-input uniqueness is
enough. -/
theorem exact_shared_prior_record_and_root_record_same_input_answer_eq
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
    (sourcePrior targetPrior : List UnifiedExposureRecord)
    (sourceActor targetActor : QueryActor) (queryInput : ShaInput)
    (sourceAnswer targetAnswer : Digest256)
    (priorExact : sourcePrior = targetPrior)
    (sourceMember :
      (.machineFresh sourceActor queryInput sourceAnswer :
        UnifiedExposureRecord) ∈ sourcePrior)
    (targetRootMember :
      (.machineFresh targetActor queryInput targetAnswer :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root)
    (targetPrefixMember : ∀ record, record ∈ targetPrior →
      record ∈ exactFixedRootRecords input.package.root) :
    sourceAnswer = targetAnswer := by
  have transported :
      (.machineFresh sourceActor queryInput sourceAnswer :
        UnifiedExposureRecord) ∈ targetPrior := by
    simpa [← priorExact] using sourceMember
  have sourceRootMember := targetPrefixMember _ transported
  have recordExact :
      (.machineFresh sourceActor queryInput sourceAnswer :
        UnifiedExposureRecord) =
      .machineFresh targetActor queryInput targetAnswer := by
    apply List.inj_on_of_nodup_map
      (exact_root_record_causal_inputs_nodup input)
      sourceRootMember targetRootMember
    rfl
  injection recordExact

/-- Exhaustive two-fibre join for one alpha block.  Each side may either
provide a cached shared-prefix record or the exact named routed lookup.  Mixed
cases are resolved by root-input uniqueness; the named coordinate is compared
only when both sides are post-fold. -/
theorem exact_pair_alpha_answer_eq_of_cached_or_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (leftInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance leftSample)
    (rightInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance rightSample)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (leftPrior rightPrior : List UnifiedExposureRecord)
    (block : Fin 4) (queryInput : ShaInput)
    (leftAnswer rightAnswer : Digest256)
    (leftLookup : tableLookup (exactOperationalTable leftInput) queryInput =
      some leftAnswer)
    (rightLookup : tableLookup (exactOperationalTable rightInput) queryInput =
      some rightAnswer)
    (priorExact : leftPrior = rightPrior)
    (leftPrefixMember : ∀ record, record ∈ leftPrior →
      record ∈ exactFixedRootRecords leftInput.package.root)
    (rightPrefixMember : ∀ record, record ∈ rightPrior →
      record ∈ exactFixedRootRecords rightInput.package.root)
    (leftDisposition :
      (∃ actor,
        (.machineFresh actor queryInput leftAnswer : UnifiedExposureRecord) ∈
          leftPrior) ∨
      causalRoutedAnswer? (some (Sum.inl block)) router
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters
              leftSample.2)) = some leftAnswer)
    (rightDisposition :
      (∃ actor,
        (.machineFresh actor queryInput rightAnswer : UnifiedExposureRecord) ∈
          rightPrior) ∨
      causalRoutedAnswer? (some (Sum.inl block)) router
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters
              rightSample.2)) = some rightAnswer)
    (alphaCoordinatesExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        leftSample.2).1.2 block =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        rightSample.2).1.2 block) :
    leftAnswer = rightAnswer := by
  obtain ⟨leftRootActor, leftRootMember⟩ :=
    AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence.exact_final_table_lookup_has_root_record
      leftInput queryInput leftAnswer leftLookup
  obtain ⟨rightRootActor, rightRootMember⟩ :=
    AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence.exact_final_table_lookup_has_root_record
      rightInput queryInput rightAnswer rightLookup
  rcases leftDisposition with leftCached | leftRouted
  · obtain ⟨leftActor, leftMember⟩ := leftCached
    exact exact_shared_prior_record_and_root_record_same_input_answer_eq
      rightInput leftPrior rightPrior leftActor rightRootActor queryInput
        leftAnswer rightAnswer priorExact leftMember rightRootMember
        rightPrefixMember
  · rcases rightDisposition with rightCached | rightRouted
    · obtain ⟨rightActor, rightMember⟩ := rightCached
      exact (exact_shared_prior_record_and_root_record_same_input_answer_eq
        leftInput rightPrior leftPrior rightActor leftRootActor queryInput
          rightAnswer leftAnswer priorExact.symm rightMember leftRootMember
          leftPrefixMember).symm
    · have leftCoordinate := exact_fold_alpha_coordinate_eq_of_routed_lookup
        parameters router leftSample.2 block leftAnswer leftRouted
      have rightCoordinate := exact_fold_alpha_coordinate_eq_of_routed_lookup
        parameters router rightSample.2 block rightAnswer rightRouted
      exact leftCoordinate.symm.trans
        (alphaCoordinatesExact.trans rightCoordinate)

#print axioms
  exact_shared_prior_record_and_root_record_same_input_answer_eq
#print axioms exact_pair_alpha_answer_eq_of_cached_or_routed

end

end AspisK1.V7Tag73ExactPairAlphaHybridEquality
