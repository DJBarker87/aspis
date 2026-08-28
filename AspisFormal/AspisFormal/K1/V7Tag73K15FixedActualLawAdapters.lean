import AspisFormal.K1.V7Tag73ExactCompilerResources
import AspisFormal.K1.V7Tag73K15FixedSamplerProbabilityAdapters
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatProbability

/-!
# Actual-compiler-law adapters for the fixed Tag-73 K1.5 families

This file closes the probability transport that is common to the fixed K1.5
families once a source theorem has exposed their literal sampler coordinates.
It adds the two transports not already present in
`V7Tag73CompleteCausalOrdinaryProbability`:

* two sequential complete ordinary samplers, retaining both rejection and
  duplex-advance paths; and
* one production variable-prefix nonzero sampler, conditioning only on the
  prefix read before the first nonzero decode.

The specializations below conclude bounds under `exactCompilerJointLaw`, not
under an abstract replacement law.  Their remaining `coordinates` and
`covered` arguments are deterministic source-routing facts.  No probability
bound, independence assertion, fixed-event ledger, or aggregate K1.5 cover is
accepted as an input.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73K15FixedActualLawAdapters

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15FixedSamplerProbabilityAdapters
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaProbability
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyLogUpCollisionBounds
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15IndependentRootCertificates
open AspisPool.V7PointClaimBatchBinding
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## One complete ordinary challenge -/

/-- The existing one-call conditioning theorem, stated directly on
`exactCompilerJointLaw`. -/
theorem exact_compiler_joint_law_dependent_ordinary_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (target : HiddenTape → Residual →
      Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤ cap)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual ↦
          successfulCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (target hidden residual))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact exact_compiler_dependent_ordinary_event_probability_le hiddenLaw
    (exactCompilerTargetCaps parameters).length success coordinates
    successfulCoordinates target cap targetCap event covered

/-! ## Two sequential ordinary challenges -/

/-- Separate two complete sequential ordinary sampler calls from an arbitrary
residual tape.  The target may depend on the residual and on both complete
rejection/advance skeletons, but not on the isolated ordered pair of returned
field values. -/
theorem uniform_tape_dependent_ordinary_pair_event_probability_le
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryPair)
    (target : Residual → Tag73CompleteOrdinaryPairSkeleton →
      Finset (QM31Exact × QM31Exact))
    (cap : Nat)
    (targetCap : ∀ residual skeleton,
      (target residual skeleton).card ≤
        cap * Fintype.card QM31Exact)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual ↦
        successfulCoordinates ⁻¹'
          duplexOrdinaryPairDependentEvent (target residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_tape_dependent_successful_event_probability_le success
    coordinates successfulCoordinates
    (fun residual ↦ duplexOrdinaryPairDependentEvent (target residual))
    ((cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal))
  · intro residual
    exact duplex_ordinary_pair_dependent_probability_le
      (target residual) cap (targetCap residual)
  · exact covered

/-- Average the exact two-ordinary-call coordinate router over the arbitrary
hidden adversary tape. -/
theorem exact_compiler_dependent_ordinary_pair_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 freshExposures ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryPair)
    (target : HiddenTape → Residual →
      Tag73CompleteOrdinaryPairSkeleton →
        Finset (QM31Exact × QM31Exact))
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤
        cap * Fintype.card QM31Exact)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual ↦
          successfulCoordinates ⁻¹'
            duplexOrdinaryPairDependentEvent (target hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_ordinary_pair_event_probability_le success
    (coordinates hidden) successfulCoordinates (target hidden) cap
    (targetCap hidden) (jointEventSlice event hidden) (covered hidden)

/-- The same two-call transport stated directly on the production compiler
law. -/
theorem exact_compiler_joint_law_dependent_ordinary_pair_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryPair)
    (target : HiddenTape → Residual →
      Tag73CompleteOrdinaryPairSkeleton →
        Finset (QM31Exact × QM31Exact))
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤
        cap * Fintype.card QM31Exact)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual ↦
          successfulCoordinates ⁻¹'
            duplexOrdinaryPairDependentEvent (target hidden residual))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact exact_compiler_dependent_ordinary_pair_event_probability_le
    hiddenLaw (exactCompilerTargetCaps parameters).length success coordinates
    successfulCoordinates target cap targetCap event covered

/-- Concrete exact-compiler-law OOD-pair specialization. -/
theorem exact_compiler_joint_law_ood_mix_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryPair)
    (trace : HiddenTape → Residual →
      Tag73CompleteOrdinaryPairSkeleton →
        AspisV5RelationSumcheckSoundness.FourRoundDiscrepancyTrace QM31Exact)
    (round : Fin 4)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual ↦
          successfulCoordinates ⁻¹'
            duplexOrdinaryPairDependentEvent
              (fixedOodMixPairTarget (trace hidden residual) round))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (2 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply exact_compiler_joint_law_dependent_ordinary_pair_event_probability_le
    hiddenLaw parameters success coordinates successfulCoordinates
    (fun hidden residual ↦
      fixedOodMixPairTarget (trace hidden residual) round) 2
  · intro hidden residual skeleton
    exact oodMixCancellation_exact_pair_set_card_le
      (trace hidden residual skeleton) round
  · exact covered

/-! ## One variable-prefix nonzero challenge -/

/-- Transport a nuisance-dependent target through the literal total
variable-prefix tape.  Failed sampler executions contribute no event mass;
unread suffix streams remain arbitrary. -/
theorem uniform_tape_dependent_variable_prefix_nonzero_event_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Tape ≃ Residual × TotalGammaDuplexTape)
    (target : Residual → VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ residual skeleton,
      (target residual skeleton).card ≤ cap)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
        successfulGammaPrefixSkeletonDependentEvent (target residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply uniform_tape_dependent_successful_event_probability_le
    GammaPrefixSucceeds coordinates (Equiv.refl SuccessfulGammaPrefixTape)
    (fun residual ↦
      successfulGammaPrefixSkeletonDependentEvent (target residual))
    ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))
  · intro residual
    exact successful_gamma_prefix_skeleton_dependent_probability_le
      (target residual) cap (targetCap residual)
  · exact covered

/-- Average a variable-prefix target over the hidden adversary tape. -/
theorem exact_compiler_dependent_variable_prefix_nonzero_event_probability_le
    {HiddenTape Residual : Type} [Fintype HiddenTape]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 freshExposures ≃
        Residual × TotalGammaDuplexTape)
    (target : HiddenTape → Residual →
      VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤ cap)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
          successfulGammaPrefixSkeletonDependentEvent
            (target hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_variable_prefix_nonzero_event_probability_le
    (coordinates hidden) (target hidden) cap (targetCap hidden)
    (jointEventSlice event hidden) (covered hidden)

/-- The variable-prefix transport stated directly on the production compiler
law. -/
theorem exact_compiler_joint_law_dependent_variable_prefix_event_probability_le
    {HiddenTape Residual : Type} [Fintype HiddenTape]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × TotalGammaDuplexTape)
    (target : HiddenTape → Residual →
      VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤ cap)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
          successfulGammaPrefixSkeletonDependentEvent
            (target hidden residual))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact exact_compiler_dependent_variable_prefix_nonzero_event_probability_le
    hiddenLaw (exactCompilerTargetCaps parameters).length coordinates target
    cap targetCap event covered

/-! ## Exact fixed-family finite targets -/

/-- The fixed C1 family has the literal lambda cap used by the measure
ledger. -/
theorem fixed_c1_family_lambda_target_card_le_292800
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) :
    (familyLambdaBad (fixedC1CopySourceFamily decoder lanes)).card ≤
      292800 := by
  calc
    (familyLambdaBad (fixedC1CopySourceFamily decoder lanes)).card ≤
        2928 * Fintype.card (FixedC1TupleCandidate decoder lanes) :=
      familyLambdaBad_card_le (fixedC1CopySourceFamily decoder lanes)
    _ ≤ 2928 * 100 := Nat.mul_le_mul_left 2928
      (fixedC1TupleCandidate_card_le_100 decoder lanes)
    _ = 292800 := by norm_num

/-- The fixed C1 family has the literal conditional chi cap used by the
measure ledger. -/
theorem fixed_c1_family_chi_target_card_le_73100
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) (lambda : QM31Exact) :
    (familyChiBad (fixedC1CopySourceFamily decoder lanes) lambda).card ≤
      73100 := by
  calc
    (familyChiBad (fixedC1CopySourceFamily decoder lanes) lambda).card ≤
        731 * Fintype.card (FixedC1TupleCandidate decoder lanes) :=
      familyChiBad_card_le (fixedC1CopySourceFamily decoder lanes) lambda
    _ ≤ 731 * 100 := Nat.mul_le_mul_left 731
      (fixedC1TupleCandidate_card_le_100 decoder lanes)
    _ = 73100 := by norm_num

/-- A literal fixed-family lambda witness is already membership in the one
pre-lambda family target; no selected-extraction premise is needed. -/
theorem copy_lambda_category_mem_fixed_family_target
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) (lambda : QM31Exact)
    (failure : ∃ candidate : FixedC1TupleCandidate decoder lanes,
      CopyTupleCompressionCollision
        (fixedC1CopySourceFamily decoder lanes candidate).registry lambda) :
    lambda ∈ familyLambdaBad
      (fixedC1CopySourceFamily decoder lanes) := by
  classical
  rcases failure with ⟨candidate, collision⟩
  unfold familyLambdaBad
  rw [Finset.mem_biUnion]
  refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
  simpa [packedLambdaBad, copyLambdaCollisionSet]
    using collision

/-- Exact-compiler-law adapter for either literal singleton-zero category
(`muZero` or `inactiveChi`). -/
theorem exact_compiler_joint_law_zero_ordinary_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun _ ↦
          successfulCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (fun _ ↦ zeroChallengeSet))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (1 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  have bound :=
    exact_compiler_joint_law_dependent_ordinary_event_probability_le
      hiddenLaw parameters success coordinates successfulCoordinates
      (fun _ _ _ ↦ zeroChallengeSet) 1
      (fun _ _ _ ↦ Nat.le_of_eq zeroChallengeSet_card) event covered
  simpa using bound

/-- Actual-law adapter for the literal fixed-C1 lambda category.  Its only
remaining arguments are the source coordinate equivalence and pointwise
source inclusion. -/
theorem exact_compiler_joint_law_copy_lambda_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (lanes : HiddenTape → Residual → C1InitialWords)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual ↦
          successfulCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (fun _ ↦
              familyLambdaBad (fixedC1CopySourceFamily decoder
                (lanes hidden residual))))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (292800 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply exact_compiler_joint_law_dependent_ordinary_event_probability_le
    hiddenLaw parameters success coordinates successfulCoordinates
    (fun hidden residual _ ↦ familyLambdaBad
      (fixedC1CopySourceFamily decoder (lanes hidden residual))) 292800
  · intro hidden residual skeleton
    exact fixed_c1_family_lambda_target_card_le_292800 decoder
      (lanes hidden residual)
  · exact covered

/-- Actual-law adapter for the literal fixed-C1 chi category.  `lambda` is a
residual coordinate and is therefore fixed before the isolated chi value. -/
theorem exact_compiler_joint_law_copy_chi_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (lanes : HiddenTape → Residual → C1InitialWords)
    (lambda : HiddenTape → Residual → QM31Exact)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual ↦
          successfulCoordinates ⁻¹'
            fixedOrdinarySamplerTargetEvent (fun _ ↦
              familyChiBad (fixedC1CopySourceFamily decoder
                (lanes hidden residual)) (lambda hidden residual)))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (73100 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply exact_compiler_joint_law_dependent_ordinary_event_probability_le
    hiddenLaw parameters success coordinates successfulCoordinates
    (fun hidden residual _ ↦ familyChiBad
      (fixedC1CopySourceFamily decoder (lanes hidden residual))
      (lambda hidden residual)) 73100
  · intro hidden residual skeleton
    exact fixed_c1_family_chi_target_card_le_73100 decoder
      (lanes hidden residual) (lambda hidden residual)
  · exact covered

/-- Guard the degree-two kappa target by its genuine nonzero discrepancy
condition.  This avoids demanding a global nonzero premise on nuisance
skeletons that never contribute to the collision event. -/
noncomputable def guardedVariablePrefixKappaCollisionTarget
    (values : VariableGammaCompleteSkeleton → Fin 3 → QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) : Finset QM31Exact :=
  if values skeleton = 0 then ∅
  else threeRowNonzeroCollisionSet (values skeleton)

theorem guarded_variable_prefix_kappa_target_card_le_two
    (values : VariableGammaCompleteSkeleton → Fin 3 → QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) :
    (guardedVariablePrefixKappaCollisionTarget values skeleton).card ≤ 2 := by
  classical
  by_cases zero : values skeleton = 0
  · simp [guardedVariablePrefixKappaCollisionTarget, zero]
  · simp only [guardedVariablePrefixKappaCollisionTarget, if_neg zero]
    exact threeRow_nonzero_collision_card_le_two (values skeleton) zero

theorem mem_guarded_variable_prefix_kappa_target
    (values : VariableGammaCompleteSkeleton → Fin 3 → QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) (kappa : QM31Exact)
    (nonzero : values skeleton ≠ 0)
    (member : kappa ∈ threeRowNonzeroCollisionSet (values skeleton)) :
    kappa ∈ guardedVariablePrefixKappaCollisionTarget values skeleton := by
  simp [guardedVariablePrefixKappaCollisionTarget, nonzero, member]

theorem exact_compiler_joint_law_guarded_kappa_event_probability_le
    {HiddenTape Residual : Type} [Fintype HiddenTape]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × TotalGammaDuplexTape)
    (values : HiddenTape → Residual →
      VariableGammaCompleteSkeleton → Fin 3 → QM31Exact)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
          successfulGammaPrefixSkeletonDependentEvent
            (guardedVariablePrefixKappaCollisionTarget
              (values hidden residual)))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (2 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply exact_compiler_joint_law_dependent_variable_prefix_event_probability_le
    hiddenLaw parameters coordinates
    (fun hidden residual ↦
      guardedVariablePrefixKappaCollisionTarget (values hidden residual)) 2
  · intro hidden residual skeleton
    exact guarded_variable_prefix_kappa_target_card_le_two
      (values hidden residual) skeleton
  · exact covered

end

#print axioms uniform_tape_dependent_ordinary_pair_event_probability_le
#print axioms
  exact_compiler_joint_law_dependent_ordinary_event_probability_le
#print axioms exact_compiler_dependent_ordinary_pair_event_probability_le
#print axioms
  exact_compiler_joint_law_dependent_ordinary_pair_event_probability_le
#print axioms exact_compiler_joint_law_ood_mix_event_probability_le
#print axioms
  uniform_tape_dependent_variable_prefix_nonzero_event_probability_le
#print axioms
  exact_compiler_dependent_variable_prefix_nonzero_event_probability_le
#print axioms
  exact_compiler_joint_law_dependent_variable_prefix_event_probability_le
#print axioms fixed_c1_family_lambda_target_card_le_292800
#print axioms fixed_c1_family_chi_target_card_le_73100
#print axioms copy_lambda_category_mem_fixed_family_target
#print axioms exact_compiler_joint_law_zero_ordinary_event_probability_le
#print axioms exact_compiler_joint_law_copy_lambda_event_probability_le
#print axioms exact_compiler_joint_law_copy_chi_event_probability_le
#print axioms guarded_variable_prefix_kappa_target_card_le_two
#print axioms mem_guarded_variable_prefix_kappa_target
#print axioms exact_compiler_joint_law_guarded_kappa_event_probability_le

end AspisK1.V7Tag73K15FixedActualLawAdapters
