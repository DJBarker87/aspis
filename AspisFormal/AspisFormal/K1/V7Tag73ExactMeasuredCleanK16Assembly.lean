import AspisFormal.K1.V7Tag73ExactMeasuredK16Assembly
import AspisFormal.K1.V7Tag73ExactCleanK13MeasuredComposition
import AspisFormal.K1.V7Tag73ExactPairAdversaryProfileClosure

/-!
# Exact measured Tag-73 closure from the clean work-dependent q16 theorem

The compiler already charges its causal target event separately.  Therefore
the upstream K1.2--K1.5 stages need bounds only on the literal compiler-clean
event.  This module installs the work-dependent q16 theorem at precisely that
restricted seam and leaves the other published/source event bounds unchanged.

The sole Tag-73-specific q16 premise is the adversary-first semantic-profile
invariant at equal causal residual and equal already-exposed final-work answer.
No proof-of-work normalization or independence assumption is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

namespace AspisK1.V7Tag73ExactMeasuredCleanK16Assembly

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactConcreteK16Assembly
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization
open AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactMeasuredK16Assembly
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73ExactPairAdversaryProfileClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredConcreteK16Assembly
open AspisK1.V7Tag73ExactRestoredK15Events
open AspisK1.V7Tag73ExactRestoredK15MeasuredAssembly
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K13K14EventComposition
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73RestoredCausalErrorLedger
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Release-facing K1.2--K1.6 theorem with q16 discharged by the clean
one-forest factorization.  The old adversary-profile premise is replaced by
the canonical decoded-source certificate and the explicitly typed pre-final
semantic-binding boundary.  The latter still requires collision-event or
external-assumption discharge before release. -/
theorem exact_tag73_measured_clean_k16_aok_raw
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload)
    (fixedInstance : PublicInstance V5PublicStatement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (k12Source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (k13Source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (decodedSource : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (k12WordsInvariant :
      ExactFixedCleanK13PairWordsInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder)
    (k13TranscriptInvariant :
      ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34)
    (oneFoldBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13OneFoldEvent transitionFuel configuration projection
            fixedInstance decoder) ≤ exactOneFoldIdealRawError)
    (jointBatchBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13JointQueryBatchCollisionEvent transitionFuel
            configuration projection fixedInstance decoder k13Source) ≤
        exactJointQueryBatchIdealRawError)
    (laterAlphaBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
            projection fixedInstance decoder k13Source) ≤
        exactLaterRelationAlphaIdealRawError)
    (width29Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K14Width29Event transitionFuel configuration projection
            fixedInstance decoder) ≤ exactK14IdealRawError)
    (fixedK15Bounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters)
      (exactTag73RestoredFixedK15Events environment))
    (restoredK15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredK15ResidualEvent environment) ≤
        exactK14IdealRawError) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance
          (exactTag73SpendRelation (deployedOwner := deployedOwner)
            (deployedNote := deployedNote)
            (deployedNullifier := deployedNullifier)
            (deployedNode := deployedNode)) +
      exactFixedClosedK16RawError
          (exactTag73ConcreteUpstreamTerms configuration exactK13SemanticRawError
            exactK14IdealRawError exactK15RestoredCausalRawError) parameters := by
  let relation := exactTag73SpendRelation (deployedOwner := deployedOwner)
    (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
    (deployedNode := deployedNode)
  let k15 := exactTag73RestoredCausalK15Classifier transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon environment
  let stages := exactTag73RestoredCausalStages transitionFuel configuration
    projection fixedInstance decoder decoderBinding basis rc poseidon environment
  have q16TransitionRoom : 2 ≤ transitionFuel :=
    le_trans (by decide : 2 ≤ 3) transitionRoom
  have q16SemanticBound :=
    exact_fixed_clean_pair_k13_query_probability_le_one_forest_of_components
      (decoder := decoder) hiddenLaw q16TransitionRoom programmedCover
      decodedSource k12WordsInvariant k13TranscriptInvariant frontierExact reference
      traceExists foldExposureCap finalExposureCap
  have q16CleanBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73K13QueryEvent transitionFuel configuration projection
            fixedInstance decoder) ≤ q16SemanticOneForestRawError :=
    q16SemanticBound
  have k13Clean := exact_assembled_k13_clean_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance relation decoder
    decoderBinding k15 initialEncoderExact k13Source q16CleanBound oneFoldBound
    jointBatchBound laterAlphaBound
  have k14Measure := exact_assembled_k14_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance relation decoder
    decoderBinding k15 width29Bound
  have k15Measure := exact_restored_k15_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance decoder
    decoderBinding basis rc poseidon environment fixedK15Bounds
    restoredK15Bound
  have k12TransitionRoom : 2 ≤ transitionFuel := q16TransitionRoom
  have k12Measure := exact_tag73_assembled_k12_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance relation decoder
    decoderBinding k15 k12Source k12TransitionRoom
  exact exact_fixed_tag73_k16_classical_rom_aok_raw_restricted_stages
    hiddenLaw transitionFuel configuration projection fixedInstance relation
    transitionRoom driverCoversProtocol runtimeReserves cutoffBeyondCap stages
    (exactTag73ConcreteUpstreamTerms configuration exactK13SemanticRawError
      exactK14IdealRawError exactK15RestoredCausalRawError)
    (((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      Set.inter_subset_right).trans k12Measure)
    k13Clean
    (((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      Set.inter_subset_right).trans k14Measure)
    (((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      Set.inter_subset_right).trans k15Measure)

end

#print axioms exact_tag73_measured_clean_k16_aok_raw

end AspisK1.V7Tag73ExactMeasuredCleanK16Assembly
