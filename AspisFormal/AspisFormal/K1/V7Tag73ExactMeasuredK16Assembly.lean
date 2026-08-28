import AspisFormal.K1.V7Tag73ExactRestoredConcreteK16Assembly
import AspisFormal.K1.V7Tag73ExactRestoredK15MeasuredAssembly
import AspisFormal.K1.V7Tag73K13K14EventComposition

/-!
# Exact measured Tag-73 K1.2--K1.6 assembly

This is the concrete event-level capstone.  It replaces the three abstract
K1.3--K1.5 measure-bound arguments of the restored K1.6 theorem by the exact
source events already defined for the deployed Tag-73 schedule:

* q16, one-fold, joint query batching, and later relation-alpha for K1.3;
* the single restoration-wide width-29 event for K1.4; and
* the eight fixed K1.5 families plus the restoration-aware gamma residual.

K1.2 remains fully discharged by its proved two-tree 208-bit classifier.  No
independence assumption or proof-of-work normalization is introduced here.
The remaining probability arguments are literal event inequalities on the
exact compiler law, ready for the scheduler/source coordinate adapters.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

namespace AspisK1.V7Tag73ExactMeasuredK16Assembly

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactConcreteK16Assembly
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactOperationalResourceCertificate
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
open AspisK1.V7Tag73RestoredCausalErrorLedger
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Final restored K1.2--K1.6 theorem with only literal source-event bounds.
The published circle-code theorem enters through the K1.3 one-fold/width
event inequalities; Poseidon remains the explicitly permitted faithful
primitive interface. -/
theorem exact_tag73_measured_k16_aok_raw
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
    {deployedOwner : Digest -> Digest}
    {deployedNote : Digest -> F -> F -> Digest -> Digest}
    {deployedNullifier : Digest -> Digest -> Digest}
    {deployedNode : Digest -> Digest -> Digest}
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
    (transitionRoom : 3 <= transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap <= configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (q16Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13QueryEvent transitionFuel configuration projection
            fixedInstance decoder) <= exactQ16IdealRawError)
    (oneFoldBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13OneFoldEvent transitionFuel configuration projection
            fixedInstance decoder) <= exactOneFoldIdealRawError)
    (jointBatchBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13JointQueryBatchCollisionEvent transitionFuel
            configuration projection fixedInstance decoder k13Source) <=
        exactJointQueryBatchIdealRawError)
    (laterAlphaBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
            projection fixedInstance decoder k13Source) <=
        exactLaterRelationAlphaIdealRawError)
    (width29Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K14Width29Event transitionFuel configuration projection
            fixedInstance decoder) <= exactK14IdealRawError)
    (fixedK15Bounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters)
      (exactTag73RestoredFixedK15Events environment))
    (restoredK15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredK15ResidualEvent environment) <=
        exactK14IdealRawError) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) <=
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance
          (exactTag73SpendRelation (deployedOwner := deployedOwner)
            (deployedNote := deployedNote)
            (deployedNullifier := deployedNullifier)
            (deployedNode := deployedNode)) +
        exactFixedClosedK16RawError
          (exactTag73ConcreteUpstreamTerms configuration exactK13IdealRawError
            exactK14IdealRawError exactK15RestoredCausalRawError) parameters := by
  let relation := exactTag73SpendRelation (deployedOwner := deployedOwner)
    (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
    (deployedNode := deployedNode)
  let k15 := exactTag73RestoredCausalK15Classifier transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon environment
  have k13Measure := exact_assembled_k13_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance relation decoder
    decoderBinding k15 initialEncoderExact k13Source q16Bound oneFoldBound
    jointBatchBound laterAlphaBound
  have k14Measure := exact_assembled_k14_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance relation decoder
    decoderBinding k15 width29Bound
  have k15Measure := exact_restored_k15_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance decoder
    decoderBinding basis rc poseidon environment fixedK15Bounds
    restoredK15Bound
  exact exact_tag73_restored_concrete_k16_aok_raw_with_all_stage_terms_fixed
    hiddenLaw transitionFuel configuration projection fixedInstance decoder
    decoderBinding basis rc poseidon environment k12Source transitionRoom
    driverCoversProtocol runtimeReserves cutoffBeyondCap k13Measure k14Measure
    k15Measure

end

#print axioms exact_tag73_measured_k16_aok_raw

end AspisK1.V7Tag73ExactMeasuredK16Assembly
