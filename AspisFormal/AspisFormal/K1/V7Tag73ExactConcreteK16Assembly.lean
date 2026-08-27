import AspisFormal.K1.V7Tag73ExactConcreteK12Bound
import AspisFormal.K1.V7Tag73ExactOperationalK15Stage
import AspisFormal.K1.V7Tag73K14K15IdealErrorLedger

/-!
# Concrete Tag-73 K1.2--K1.6 assembly

This module installs the executable K1.2--K1.4 classifiers and the literal
operational K1.5 classifier in the exact fixed-instance K1.6 theorem.  It also
discharges the K1.2 numerical premise with the proved two-tree 208-bit
scheduler bound.  Consequently the only remaining numerical premises are the
actual K1.3, K1.4 and K1.5 error-event bounds.

The K1.5 environment is still an explicit source/restoration input: this file
does not manufacture evaluator material or a client handoff.  It only removes
the generic stage-package boundary and proves the exact composition theorem
that the final Rust/Aeneas and causal-probability bridges will instantiate.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactConcreteK16Assembly

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
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The literal operational four-stage package used by the final theorem. -/
noncomputable abbrev exactTag73OperationalStages
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
    (environment : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :=
  exactTag73ProofRelevantStages transitionFuel configuration projection
    fixedInstance
    (exactTag73SpendRelation (deployedOwner := deployedOwner)
      (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
      (deployedNode := deployedNode)) decoder decoderBinding
    (exactTag73OperationalK15Classifier transitionFuel configuration projection
      fixedInstance decoder decoderBinding basis rc poseidon environment)

/-- Concrete upstream ledger after the K1.2 term has been discharged. -/
def exactTag73ConcreteUpstreamTerms
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (k13 k14 k15 : ENNReal) : ConcreteUpstreamErrorTerms where
  k12TwoTreeMerkle208 := exactTag73K12ErrorBound configuration
  k13CircleListDecoding := k13
  k14CoherentChainSelection := k14
  k15SpendWitnessRecovery := k15

/-- Exact fixed-instance classical-ROM AoK with the deployed four classifiers
installed and the K1.2 numerical term proved.  Only the three remaining
concrete stage bounds are parameters. -/
theorem exact_tag73_concrete_k16_aok_raw_after_k12
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
    (environment : ExactTag73OperationalK15Environment transitionFuel
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
    (k13Term k14Term k15Term : ENNReal)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw
      (exactTag73OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      k13Term)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw
      (exactTag73OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      k14Term)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw
      (exactTag73OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      k15Term) :
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
          (exactTag73ConcreteUpstreamTerms configuration
            k13Term k14Term k15Term) parameters := by
  let stages := exactTag73OperationalStages transitionFuel configuration
    projection fixedInstance decoder decoderBinding basis rc poseidon environment
  have k12TransitionRoom : 2 ≤ transitionFuel :=
    le_trans (by decide : 2 ≤ 3) transitionRoom
  have k12Bound := exact_tag73_assembled_k12_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance
    (exactTag73SpendRelation (deployedOwner := deployedOwner)
      (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
      (deployedNode := deployedNode)) decoder decoderBinding
    (exactTag73OperationalK15Classifier transitionFuel configuration projection
      fixedInstance decoder decoderBinding basis rc poseidon environment)
    k12Source k12TransitionRoom
  exact exact_fixed_tag73_k16_classical_rom_aok_raw hiddenLaw transitionFuel
    configuration projection fixedInstance
    (exactTag73SpendRelation (deployedOwner := deployedOwner)
      (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
      (deployedNode := deployedNode)) transitionRoom driverCoversProtocol
    runtimeReserves cutoffBeyondCap stages
    (exactTag73ConcreteUpstreamTerms configuration k13Term k14Term k15Term)
    k12Bound k13Bound k14Bound k15Bound

/-- The same concrete theorem with the proved raw K1.4 and K1.5 ledger terms
fixed in its statement.  The remaining premises must prove that the actual
stage events are bounded by these values; work normalization is not used. -/
theorem exact_tag73_concrete_k16_aok_raw_with_fixed_k14_k15_terms
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
    (environment : ExactTag73OperationalK15Environment transitionFuel
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
    (k13Term : ENNReal)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw
      (exactTag73OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      k13Term)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw
      (exactTag73OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      exactK14IdealRawError)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw
      (exactTag73OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon environment)
      exactK15IdealRawError) :
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
          (exactTag73ConcreteUpstreamTerms configuration k13Term
            exactK14IdealRawError exactK15IdealRawError) parameters := by
  exact exact_tag73_concrete_k16_aok_raw_after_k12 hiddenLaw transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon environment k12Source transitionRoom driverCoversProtocol
    runtimeReserves cutoffBeyondCap k13Term exactK14IdealRawError
    exactK15IdealRawError k13Bound k14Bound k15Bound

#print axioms exactTag73OperationalStages
#print axioms exactTag73ConcreteUpstreamTerms
#print axioms exact_tag73_concrete_k16_aok_raw_after_k12
#print axioms exact_tag73_concrete_k16_aok_raw_with_fixed_k14_k15_terms

end

end AspisK1.V7Tag73ExactConcreteK16Assembly
