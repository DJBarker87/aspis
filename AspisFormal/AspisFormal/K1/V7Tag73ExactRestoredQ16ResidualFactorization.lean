import AspisFormal.K1.V7Tag73ExactFixedQ16JointEventHandoff
import AspisFormal.K1.V7Tag73ExactRestoredQ16JointEventHandoff

/-!
# Residual factorization endpoint for the restored Tag-73 q16 event

The causal final-work/q16 router removes exactly 513 fresh answers from the
compiler tape.  The semantic q16 theorem may be applied only when the
size-9,557 consistency set is a function of the remaining residual tape.

This file makes that last source obligation exact.  It packages each restored
root query failure into its literal exposure-indexed joint trial, chooses a
canonical representative in every nonempty residual fibre, and proves the
complete probability bound from one explicit fibre-invariance proposition.
No independence, trace cover, or probability estimate is placed in that
proposition: it says only that two genuine witnesses in one residual fibre
have the same source-derived consistency set.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactRestoredQ16JointEventHandoff
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness

noncomputable section

/-! ## Exact pointwise trial witness -/

/-- The source-derived consistency set on the literal completed root. -/
def exactRestoredRootK13IntrinsicBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (words : ExtractedWords) : Finset (Fin 262144) :=
  restoredOperationalK13ConsistencySet decoder words
    ((exact_restored_operational_k13_provider input).data
      input.package.root.fixedRoot.base.runtime.node
      (exact_restoration_accumulator_contains_root input)
      (exact_restoration_accumulator_root_is_done input))

/-- The exact 513-coordinate factor selected by one chronological exposure
trial on one compiler sample. -/
def exactRestoredRootK13TrialCoordinates
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    ExactCompilerFinalWorkQ16Residual parameters ×
      (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerCausalFinalWorkQ16Coordinates parameters
    (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration sample.1).erase) sample.2

/-- Proof-relevant membership in one genuine restored K1.3 joint trial.  The
bad set is not caller supplied: `badExact` pins it to the literal restored
root input and its extracted two-tree words. -/
structure ExactRestoredRootK13JointTrialWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters)
    (trial : ExactCompilerExposureTrial parameters) : Type where
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance sample
  k12 : RestoredNodeK12Certificate
    input.package.root.fixedRoot.base.runtime.node
  bad : Finset (Fin 262144)
  badExact : bad = exactRestoredRootK13IntrinsicBad decoder input k12.words
  badCard : bad.card ≤ 9557
  actualTrial : ExactFixedK13ActualJointTrial input trial
  coordinate :
    exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        sample ∈
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun _residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulBadEvent bad)

/-- The event assigned to one chronological trial is inhabitedness of the
exact source-derived witness above. -/
def exactRestoredRootK13JointTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | Nonempty
    (ExactRestoredRootK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder sample trial)}

/-- The pointwise joint-event theorem supplies a member of the exact trial
inventory, retaining its source-derived consistency set. -/
theorem exact_restored_root_query_failure_has_joint_trial_witness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (member : sample ∈
      exactTag73RestoredOperationalCanonicalRootK13QueryEvent transitionFuel
        configuration projection fixedInstance decoder) :
    ∃ trial : ExactCompilerExposureTrial parameters,
      sample ∈ exactRestoredRootK13JointTrialEvent transitionFuel configuration
        projection fixedInstance decoder trial := by
  obtain ⟨input, k12, bad, trial, badExact, badCard, actualTrial,
      coordinate⟩ :=
    exact_restored_root_query_failure_has_joint_trial_coordinate
      transitionRoom programmedCover frontierExact member
  refine ⟨trial, ⟨?_⟩⟩
  exact
    { input := input
      k12 := k12
      bad := bad
      badExact := by
        simpa [exactRestoredRootK13IntrinsicBad] using badExact
      badCard := badCard
      actualTrial := actualTrial
      coordinate := by
        simpa [exactRestoredRootK13TrialCoordinates] using coordinate }

/-! ## Canonical residual fibres -/

/-- Choose the source-derived bad set attached to one event member.  This is
totalized by the empty set off the event and is never trusted there. -/
noncomputable def exactRestoredRootK13PointwiseBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    Finset (Fin 262144) := by
  classical
  exact if member : Nonempty
        (ExactRestoredRootK13JointTrialWitness transitionFuel configuration
          projection fixedInstance decoder sample trial) then
      (Classical.choice member).bad
    else
      ∅

theorem exact_restored_root_k13_pointwise_bad_eq_choice
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : Nonempty
      (ExactRestoredRootK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder sample trial)) :
    exactRestoredRootK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial sample =
      (Classical.choice member).bad := by
  classical
  simp [exactRestoredRootK13PointwiseBad, member]

theorem exact_restored_root_k13_pointwise_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (exactRestoredRootK13PointwiseBad transitionFuel configuration projection
      fixedInstance decoder trial sample).card ≤ 9557 := by
  classical
  by_cases member : Nonempty
      (ExactRestoredRootK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder sample trial)
  · simpa [exactRestoredRootK13PointwiseBad, member] using
      (Classical.choice member).badCard
  · simp [exactRestoredRootK13PointwiseBad, member]

/-- The sole remaining source noninterference statement.  Inside one genuine
trial, changing only the 513 routed final-work/q16 answers while preserving
the residual cannot change the committed, source-derived consistency set.
The event hypotheses exclude the meaningless off-event totalization. -/
def ExactRestoredRootK13ResidualInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length),
    (hidden, left) ∈ exactRestoredRootK13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial →
    (hidden, right) ∈ exactRestoredRootK13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial →
    (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactRestoredRootK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, left) =
      exactRestoredRootK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, right)

/-- A residual fibre is nonempty exactly when it contains a genuine member of
the selected trial event. -/
def exactRestoredRootK13ResidualFibreNonempty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters) : Prop :=
  ∃ tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length,
    (hidden, tape) ∈ exactRestoredRootK13JointTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial ∧
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, tape)).1 = residual

/-- Canonicalize a bad set on every nonempty residual fibre. -/
noncomputable def exactRestoredRootK13ResidualBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters) :
    Finset (Fin 262144) := by
  classical
  exact if inhabitedFibre :
        exactRestoredRootK13ResidualFibreNonempty transitionFuel configuration
          projection fixedInstance decoder trial hidden residual then
      exactRestoredRootK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, Classical.choose inhabitedFibre)
    else
      ∅

theorem exact_restored_root_k13_residual_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters) :
    (exactRestoredRootK13ResidualBad transitionFuel configuration projection
      fixedInstance decoder trial hidden residual).card ≤ 9557 := by
  classical
  by_cases inhabitedFibre : exactRestoredRootK13ResidualFibreNonempty
      transitionFuel
      configuration projection fixedInstance decoder trial hidden residual
  · simpa [exactRestoredRootK13ResidualBad, inhabitedFibre] using
      exact_restored_root_k13_pointwise_bad_card
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, Classical.choose inhabitedFibre)
  · simp [exactRestoredRootK13ResidualBad, inhabitedFibre]

theorem exact_restored_root_k13_residual_bad_eq_pointwise
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (invariant : ExactRestoredRootK13ResidualInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (member : (hidden, tape) ∈
      exactRestoredRootK13JointTrialEvent transitionFuel configuration
        projection fixedInstance decoder trial) :
    exactRestoredRootK13ResidualBad transitionFuel configuration projection
        fixedInstance decoder trial hidden
          (exactRestoredRootK13TrialCoordinates transitionFuel configuration
            trial (hidden, tape)).1 =
      exactRestoredRootK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, tape) := by
  classical
  let residual := (exactRestoredRootK13TrialCoordinates transitionFuel
    configuration trial (hidden, tape)).1
  have inhabitedFibre : exactRestoredRootK13ResidualFibreNonempty transitionFuel
      configuration projection fixedInstance decoder trial hidden residual :=
    ⟨tape, member, rfl⟩
  let representative := Classical.choose inhabitedFibre
  have representativeFacts := Classical.choose_spec inhabitedFibre
  have sameResidual :
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, representative)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, tape)).1 := by
    exact representativeFacts.2
  have sameBad := invariant trial hidden representative tape
    representativeFacts.1 member sameResidual
  simpa [exactRestoredRootK13ResidualBad, inhabitedFibre, residual,
    representative]
    using sameBad

/-! ## Exact finite-trial package and probability consequence -/

/-- The residual invariant instantiates the existing exposure-indexed joint
work/q16 trial package. -/
noncomputable def exactRestoredRootK13ExposureTrials
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (invariant : ExactRestoredRootK13ResidualInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    ExactCompilerExposureIndexedFinalWorkQ16Trials
      (HiddenTape := HiddenTape) parameters where
  event := exactRestoredRootK13JointTrialEvent transitionFuel configuration
    projection fixedInstance decoder
  router := fun trial hidden =>
    exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase
  bad := exactRestoredRootK13ResidualBad transitionFuel configuration projection
    fixedInstance decoder
  badCard := exact_restored_root_k13_residual_bad_card
    (configuration := configuration) (projection := projection)
    (fixedInstance := fixedInstance) (decoder := decoder)
  reference := reference
  traceExists := traceExists
  covered := by
    intro trial hidden tape member
    change exactRestoredRootK13TrialCoordinates transitionFuel configuration
        trial (hidden, tape) ∈
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulBadEvent
            (exactRestoredRootK13ResidualBad transitionFuel configuration
              projection fixedInstance decoder trial hidden residual))
    let witness := Classical.choice member
    have residualEq := exact_restored_root_k13_residual_bad_eq_pointwise
      invariant trial hidden tape member
    have pointwiseEq :
        exactRestoredRootK13PointwiseBad transitionFuel configuration projection
            fixedInstance decoder trial (hidden, tape) = witness.bad := by
      simpa [witness] using
        (exact_restored_root_k13_pointwise_bad_eq_choice
          (configuration := configuration) (projection := projection)
          (fixedInstance := fixedInstance) (decoder := decoder) trial
          (hidden, tape) member)
    have badEq :
        exactRestoredRootK13ResidualBad transitionFuel configuration projection
            fixedInstance decoder trial hidden
              (exactRestoredRootK13TrialCoordinates transitionFuel configuration
                trial (hidden, tape)).1 = witness.bad :=
      residualEq.trans pointwiseEq
    rcases witness.coordinate with ⟨success, badMember⟩
    refine ⟨success, ?_⟩
    change successfulFinalWorkQ16TotalEquiv
        ⟨(exactRestoredRootK13TrialCoordinates transitionFuel configuration
          trial (hidden, tape)).2, success⟩ ∈
      finalWorkQ16SuccessfulBadEvent
        (exactRestoredRootK13ResidualBad transitionFuel configuration projection
          fixedInstance decoder trial hidden
            (exactRestoredRootK13TrialCoordinates transitionFuel configuration
              trial (hidden, tape)).1)
    rw [badEq]
    exact badMember

/-- Every restored-root K1.3 query failure belongs to the finite union of the
exact chronological joint trials. -/
theorem exact_restored_root_k13_query_event_subset_trial_union
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
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    exactTag73RestoredOperationalCanonicalRootK13QueryEvent transitionFuel configuration
        projection fixedInstance decoder ⊆
      ⋃ trial : ExactCompilerExposureTrial parameters,
        exactRestoredRootK13JointTrialEvent transitionFuel configuration
          projection fixedInstance decoder trial := by
  intro sample member
  obtain ⟨trial, trialMember⟩ :=
    exact_restored_root_query_failure_has_joint_trial_witness transitionRoom
      programmedCover (frontierExact sample) member
  exact Set.mem_iUnion.mpr ⟨trial, trialMember⟩

/-- Exact raw K1.3 query bound, conditional only on the explicit residual
fibre invariant.  The factor `F / 2^34` is retained honestly; the one-forest
form follows separately when the release exposure cap is at most `2^34`. -/
theorem exact_restored_root_k13_query_probability_le_exposure_mul
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactRestoredRootK13ResidualInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73RestoredOperationalCanonicalRootK13QueryEvent transitionFuel
          configuration projection fixedInstance decoder) ≤
      ((unifiedFull256ExposureCap parameters : ENNReal) *
        q16SemanticOneForestRawError) / (2 : ENNReal) ^ 34 := by
  let trials := exactRestoredRootK13ExposureTrials transitionFuel configuration
    projection fixedInstance decoder invariant reference traceExists
  calc
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) := by
      apply measure_mono
      exact exact_restored_root_k13_query_event_subset_trial_union
        transitionRoom programmedCover frontierExact
    _ ≤ ((unifiedFull256ExposureCap parameters : ENNReal) *
          q16SemanticOneForestRawError) / (2 : ENNReal) ^ 34 :=
      trials.failure_union_probability_le_exposure_mul

/-- Release-form K1.3 query bound.  When the complete compiler exposure budget
fits one deployed final-work unit, the same exact cover is bounded by the
original one-forest q16 error without any independence assumption or grinding
normalisation. -/
theorem exact_restored_root_k13_query_probability_le_one_forest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactRestoredRootK13ResidualInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (exposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73RestoredOperationalCanonicalRootK13QueryEvent transitionFuel
          configuration projection fixedInstance decoder) ≤
      q16SemanticOneForestRawError := by
  let trials := exactRestoredRootK13ExposureTrials transitionFuel configuration
    projection fixedInstance decoder invariant reference traceExists
  calc
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) := by
      apply measure_mono
      exact exact_restored_root_k13_query_event_subset_trial_union
        transitionRoom programmedCover frontierExact
    _ ≤ q16SemanticOneForestRawError :=
      trials.failure_union_probability_le_one_forest exposureCap

#print axioms exact_restored_root_query_failure_has_joint_trial_witness
#print axioms exact_restored_root_k13_pointwise_bad_card
#print axioms exact_restored_root_k13_residual_bad_card
#print axioms exact_restored_root_k13_residual_bad_eq_pointwise
#print axioms exactRestoredRootK13ExposureTrials
#print axioms exact_restored_root_k13_query_event_subset_trial_union
#print axioms exact_restored_root_k13_query_probability_le_exposure_mul
#print axioms exact_restored_root_k13_query_probability_le_one_forest

end

end AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
