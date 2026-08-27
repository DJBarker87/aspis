import AspisFormal.K1.V7Tag73RestoredCausalK15Stage
import AspisFormal.K1.V7Tag73K15ExactMeasureLedger

/-!
# Literal event split for restoration-aware Tag-73 K1.5

The corrected operational classifier returns only two failure shapes: one of
the eight fixed-family algebraic categories, or the constrained restored-gamma
residual with no point-compatible restored chain.  This file identifies those
events on the exact compiler sample space and proves the deterministic cover
needed by the measured K1.5 composition theorem.

No probability premise, independence assumption, or work normalization occurs
here.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredK15Events

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
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7K15FixedFamilyCausalCover
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7PointClaimBatchBinding
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The literal source predicate for each of the eight constructors of
`FixedFamilyK15Failure`, indexed by the exact operational context. -/
def exactTag73FixedK15CategoryHolds
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (context : ExactTag73K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding) : FixedK15Category → Prop
  | .semantic =>
      FixedWidth29SemanticFailure decoder
        (extractedWidth29InitialWords context.k12.words)
        (environment.terminal context) (environment.sumcheck context)
        (exactOperationalChallenge context.input .theta)
        (fun coordinate => exactOperationalChallenge context.input
          (.zerocheckPoint coordinate))
        (context.run environment.operational).point
        (exactOperationalChallenge context.input .mu)
  | .copyLambda => ∃ candidate : FixedC1TupleCandidate decoder
      (c1Received context.k12.words),
      CopyTupleCompressionCollision
        (fixedC1CopySourceFamily decoder (c1Received context.k12.words)
          candidate).registry
        (exactOperationalChallenge context.input .lambda)
  | .copyChi => ∃ candidate : FixedC1TupleCandidate decoder
      (c1Received context.k12.words),
      DeployedCopyActivePole
          (fixedC1CopySourceFamily decoder (c1Received context.k12.words)
            candidate).registry
          (exactOperationalChallenge context.input .lambda)
          (exactOperationalChallenge context.input .chi) ∨
        CopyChiCollision
          (fixedC1CopySourceFamily decoder (c1Received context.k12.words)
            candidate).registry
          (exactOperationalChallenge context.input .lambda)
          (exactOperationalChallenge context.input .chi)
  | .muZero => exactOperationalChallenge context.input .mu = 0
  | .inactiveChi => DeployedCopyInactiveSlotCollision
      (exactOperationalChallenge context.input .chi)
  | .oodMix =>
      (context.material environment.operational).data.execution.discrepancyTrace
        |>.MixCancellation 0
  | .relationAlpha => ∃ round : Fin 4,
      (context.material environment.operational).data.execution.discrepancyTrace
        |>.AlphaRepair round
  | .kappaPointRow => KappaPointRowCollision
      (context.fields environment.operational) context.k14.extraction
      (context.run environment.operational).point
      (exactOperationalChallenge context.input .kappa)

/-- The eight exact source events on the compiler sample space. -/
def exactTag73RestoredFixedK15Events
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) : FixedK15Events (ExactCompilerSample HiddenTape parameters) where
  event category := {sample | ∃ context : ExactTag73K15Context transitionFuel
    configuration projection fixedInstance decoder decoderBinding,
    context.sample = sample ∧
      exactTag73FixedK15CategoryHolds environment context category}

/-- The only non-fixed residual: an original operational failure remains and
no point-compatible restored K1.4 chain exists for the same context. -/
def exactTag73RestoredK15ResidualEvent
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) : Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ context : ExactTag73K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    context.sample = sample ∧
      Nonempty (ExactTag73OperationalK15Failure
        (context.material environment.operational)) ∧
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder context.k12.words
        (context.run environment.operational).point
        (context.fields environment.operational).pointClaim
        (environment.family context)}

/-- Every actual error returned by the corrected K1.5 classifier is covered by
exactly the fixed-family union or the restored residual above. -/
theorem exact_restored_k15_error_event_subset_fixed_union_residual
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :
    k15SpendWitnessErrorEvent
        (exactTag73ProofRelevantStages transitionFuel configuration projection
          fixedInstance
          (exactTag73SpendRelation (deployedOwner := deployedOwner)
            (deployedNote := deployedNote)
            (deployedNullifier := deployedNullifier)
            (deployedNode := deployedNode)) decoder decoderBinding
          (exactTag73RestoredCausalK15Classifier transitionFuel configuration
            projection fixedInstance decoder decoderBinding basis rc poseidon
            environment)) ⊆
      (exactTag73RestoredFixedK15Events environment).failure ∪
        exactTag73RestoredK15ResidualEvent environment := by
  intro sample member
  rcases member with ⟨input, k12, k13, k14, ⟨failure⟩⟩
  let context : ExactTag73K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding := ⟨sample, input, k12, k13, k14⟩
  rcases failure.evidence with fixed | residual
  · apply Or.inl
    rcases fixed with semantic | copyLambda | copyChi | muZero | inactiveChi |
        oodMix | relationAlpha | kappaPointRow
    · exact Set.mem_iUnion_of_mem .semantic ⟨context, rfl, semantic⟩
    · exact Set.mem_iUnion_of_mem .copyLambda ⟨context, rfl, copyLambda⟩
    · exact Set.mem_iUnion_of_mem .copyChi ⟨context, rfl, copyChi⟩
    · exact Set.mem_iUnion_of_mem .muZero ⟨context, rfl, muZero⟩
    · exact Set.mem_iUnion_of_mem .inactiveChi ⟨context, rfl, inactiveChi⟩
    · exact Set.mem_iUnion_of_mem .oodMix ⟨context, rfl, oodMix⟩
    · exact Set.mem_iUnion_of_mem .relationAlpha
        ⟨context, rfl, relationAlpha⟩
    · exact Set.mem_iUnion_of_mem .kappaPointRow
        ⟨context, rfl, kappaPointRow⟩
  · exact Or.inr ⟨context, rfl, residual⟩

end

#print axioms exact_restored_k15_error_event_subset_fixed_union_residual

end AspisK1.V7Tag73ExactRestoredK15Events
