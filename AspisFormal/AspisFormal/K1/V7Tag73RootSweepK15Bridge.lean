import AspisFormal.K1.V7Tag73ConcreteRootSweepClient
import AspisFormal.K1.V7Tag73ExactOperationalK15Stage

/-!
# Production root-sweep bridge into operational K1.5

The generic K1.5 material record retains two distinct client facts: that the
client returned its fixed extractor, and that applying that extractor to the
literal terminal accumulator recovered the decoded witness.  For the
production root-sweep configuration the first fact is no longer a premise:
it follows from the exact request count, fuel closure and completed scheduler
trace.  The second fact remains the genuine extraction theorem to prove.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RootSweepK15Bridge

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5ComponentCQM31TowerExact
open AspisV5AcceptedSpendRelation

noncomputable section

/-- Construct exact operational K1.5 material for the production sweep.
`clientReturned` is derived from the completed run; only the substantive
accumulator-to-witness equality is supplied by the extraction layer. -/
def exactRootSweepOperationalK15Material
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    (positive : 0 < transitionFuel)
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor V5PublicStatement
      Tag73K12ParsedProof Payload DecodedSpendWitness)
    (withinForkCap : rounds * 1511 ≤ parameters.forkRequestCap)
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (input : ExactK12OperationalInput transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
      projection fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (data : ExactTag73OperationalK15Data input)
    (source : ExactTag73OperationalK15SourceBinding k14 basis rc data)
    (extracts : extractor input.package.root.full.clientRun.accumulator =
      some (decodeTag73SpendWitness fixedInstance.statement k14.extraction)) :
    ExactTag73OperationalK15Material input k12 k14 basis rc poseidon where
  data := data
  source := source
  clientExtractor := extractor
  clientReturned := completed_exact_root_sweep_returns_extractor
    transitionFuel positive base rounds extractor withinForkCap sample
    input.package.root.fixedRoot.base.runtime
    input.package.root.full.clientRun input.package.root.full.fullCompleted
  clientExtracts := extracts

#print axioms exactRootSweepOperationalK15Material

end

end AspisK1.V7Tag73RootSweepK15Bridge
