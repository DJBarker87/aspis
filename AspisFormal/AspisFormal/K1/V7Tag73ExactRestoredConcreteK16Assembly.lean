import AspisFormal.K1.V7Tag73ExactConcreteK16Assembly
import AspisFormal.K1.V7Tag73ExactOperationalK15Stage
import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73RestoredCausalK15Stage
import AspisFormal.K1.V7Tag73RestoredCausalErrorLedger

/-!
# Restoration-aware concrete Tag-73 K1.2--K1.6 assembly

The first concrete assembly used the local operational K1.5 classifier.  A
gamma/point-lane failure on that classifier can reveal a usable coherent trace
on a restored branch, so its fixed-family-only K1.5 term is not the final
operational accounting.

This module installs the corrected restoration-aware classifier.  A usable
point-compatible restored branch is returned as client extraction; the only
K1.5 errors are the eight fixed families or the constrained restored-gamma
event under absence of a usable restoration.  Accordingly the exact K1.5
term is

`initialBatchChallengeCap / (P^4 - 1) + 396430 / (P^4 - 1)`.

Together with the separate ordinary K1.4 width-29 term, this gives the honest
two-cap operational ledger proved in `V7Tag73RestoredCausalErrorLedger`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactRestoredConcreteK16Assembly

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactConcreteK16Assembly
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73RestoredCausalErrorLedger
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact four-stage package with restoration-aware K1.5 classification. -/
noncomputable abbrev exactTag73RestoredCausalStages
    {HiddenTape TapeIdentity Observation Payload : Type}
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
      poseidon) :=
  exactTag73ProofRelevantStages transitionFuel configuration projection
    fixedInstance
    (exactTag73SpendRelation (deployedOwner := deployedOwner)
      (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
      (deployedNode := deployedNode)) decoder decoderBinding
    (exactTag73RestoredCausalK15Classifier transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon
      environment)

/-- Final corrected concrete K1.2--K1.6 theorem.  K1.2 is discharged by its
proved exact two-tree bound.  K1.3, K1.4, and restoration-aware K1.5 retain
only their concrete event-measure bridges. -/
theorem exact_tag73_restored_concrete_k16_aok_raw_with_all_stage_terms_fixed
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
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw
      (exactTag73RestoredCausalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      exactK13IdealRawError)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw
      (exactTag73RestoredCausalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      exactK14IdealRawError)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw
      (exactTag73RestoredCausalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      exactK15RestoredCausalRawError) :
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
          (exactTag73ConcreteUpstreamTerms configuration exactK13IdealRawError
            exactK14IdealRawError exactK15RestoredCausalRawError) parameters := by
  let stages := exactTag73RestoredCausalStages transitionFuel configuration
    projection fixedInstance decoder decoderBinding basis rc poseidon environment
  have k12TransitionRoom : 2 ≤ transitionFuel :=
    le_trans (by decide : 2 ≤ 3) transitionRoom
  have k12Bound := exact_tag73_assembled_k12_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance
    (exactTag73SpendRelation (deployedOwner := deployedOwner)
      (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
      (deployedNode := deployedNode)) decoder decoderBinding
    (exactTag73RestoredCausalK15Classifier transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon
      environment) k12Source k12TransitionRoom
  exact exact_fixed_tag73_k16_classical_rom_aok_raw hiddenLaw transitionFuel
    configuration projection fixedInstance
    (exactTag73SpendRelation (deployedOwner := deployedOwner)
      (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
      (deployedNode := deployedNode)) transitionRoom driverCoversProtocol
    runtimeReserves cutoffBeyondCap stages
    (exactTag73ConcreteUpstreamTerms configuration exactK13IdealRawError
      exactK14IdealRawError exactK15RestoredCausalRawError)
    k12Bound k13Bound k14Bound k15Bound

end


#print axioms exactTag73RestoredCausalStages
#print axioms
  exact_tag73_restored_concrete_k16_aok_raw_with_all_stage_terms_fixed

end AspisK1.V7Tag73ExactRestoredConcreteK16Assembly
