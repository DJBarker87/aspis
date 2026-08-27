import AspisFormal.K1.V7Tag73ExactRestoredK15Events
import AspisFormal.K1.V7Tag73RestoredK15EventComposition

/-!
# Measured assembly of the exact restoration-aware Tag-73 K1.5 stage

This module discharges the generic event-cover premise of the K1.5 measure
ledger with the literal corrected classifier.  What remains for production is
only the eight component sampler bounds and the single restored-gamma bound on
the exact events defined by the source model.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactRestoredK15MeasuredAssembly

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73ExactRestoredK15Events
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73RestoredCausalErrorLedger
open AspisK1.V7Tag73RestoredK15EventComposition
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact measured K1.5 bound for the corrected operational classifier.  Its
deterministic cover is kernel-proved; only the nine actual source-event bounds
remain arguments. -/
theorem exact_restored_k15_error_measure_bound
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
    (fixedBounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters)
      (exactTag73RestoredFixedK15Events environment))
    (restoredBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredK15ResidualEvent environment) ≤
        exactK14IdealRawError) :
    K15SpendWitnessErrorMeasureBound hiddenLaw
      (exactTag73ProofRelevantStages transitionFuel configuration projection
        fixedInstance
        (exactTag73SpendRelation (deployedOwner := deployedOwner)
          (deployedNote := deployedNote)
          (deployedNullifier := deployedNullifier)
          (deployedNode := deployedNode)) decoder decoderBinding
        (exactTag73RestoredCausalK15Classifier transitionFuel configuration
          projection fixedInstance decoder decoderBinding basis rc poseidon
          environment))
      exactK15RestoredCausalRawError := by
  exact restored_k15_error_measure_bound_of_cover hiddenLaw
    (exactTag73ProofRelevantStages transitionFuel configuration projection
      fixedInstance
      (exactTag73SpendRelation (deployedOwner := deployedOwner)
        (deployedNote := deployedNote)
        (deployedNullifier := deployedNullifier)
        (deployedNode := deployedNode)) decoder decoderBinding
      (exactTag73RestoredCausalK15Classifier transitionFuel configuration
        projection fixedInstance decoder decoderBinding basis rc poseidon
        environment))
    (exactTag73RestoredFixedK15Events environment)
    (exactTag73RestoredK15ResidualEvent environment)
    (exact_restored_k15_error_event_subset_fixed_union_residual environment)
    fixedBounds restoredBound

end


#print axioms exact_restored_k15_error_measure_bound

end AspisK1.V7Tag73ExactRestoredK15MeasuredAssembly
