import AspisFormal.K1.V7Tag73ExactCausalK15Reduction

/-!
# Restoration-aware causal K1.5 stage for exact Tag-73

The first operational K1.5 classifier is intentionally local to the accepting
Fiat--Shamir branch.  Its gamma/point-lane failure can expose a coherent trace
on a restored gamma branch.  Such a trace is an extraction opportunity, not a
probabilistic error.

This module gives that distinction a typed operational form.  A restoration
environment supplies the concrete, future-free selected-chain family and the
client handoff for a point-compatible restored trace.  The classifier then
returns success for either the original branch or the restored branch.  Its
only errors are:

* one of the eight fixed-family K1.5 categories; or
* membership in the constrained gamma set while no point-compatible restored
  K1.4 certificate exists.

No probability bound, aggregate acceptance statement, or conclusion-shaped
Fiat--Shamir premise is stored here.  The remaining handoff field is exactly
the restoration-to-client source bridge that must be constructed from the
same-tape interactive execution.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

namespace AspisK1.V7Tag73RestoredCausalK15Stage

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactCausalK15Reduction
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

noncomputable section

/-- Bundle the complete dependent K1.5 index once.  Keeping this index in one
record avoids repeatedly elaborating the full operational type tower in every
restoration field. -/
structure ExactTag73K15Context
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
    (decoderBinding : InitialProjectionBinding decoder) where
  sample : ExactCompilerSample HiddenTape parameters
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance sample
  k12 : ExactPrefixK12Certificate input
  k13 : ExactK13Certificate decoder input k12
  k14 : ExactK14Certificate decoder decoderBinding input k12

def ExactTag73K15Context.material
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
    (context : ExactTag73K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (operational : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :=
  operational.material context.sample context.input context.k12 context.k13
    context.k14

def ExactTag73K15Context.fields
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
    (context : ExactTag73K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (operational : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) : FixedFieldView QM31Exact :=
  operationalFixedFields (context.material operational).data.decoded

def ExactTag73K15Context.run
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
    (context : ExactTag73K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (operational : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :=
  operationalAcceptedRun context.input (context.material operational).data.decoded
    (context.material operational).data.fixedDecode

/-- Source/restoration data needed to turn the local operational classifier
into the correct restoration-aware K1.5 classifier.  `pointCompatibleHandoff`
is deliberately a client-extraction handoff, not a claimed probability bound:
its eventual constructor must run the already checked restored coherent trace
through the semantic/relation endpoint and the actual restoration client. -/
structure ExactTag73RestoredCausalK15Environment
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
      deployedNullifier deployedNode) : Type where
  operational : ExactTag73OperationalK15Environment transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon
  family : (context : ExactTag73K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding) →
    RestoredSelectedChainFamily decoder context.k12.words
  familyAvailable : ∀ context,
    (family context).available (exactK13ParsedProof context.input).gamma
  familySelected : ∀ context,
    (family context).selected (exactK13ParsedProof context.input).gamma =
      context.k14.extraction.combined
  terminal : ∀ context : ExactTag73K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords context.k12.words) →
        FixedTerminalAlgebraPlan QM31Exact
  sumcheck : ∀ context : ExactTag73K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding,
    FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords context.k12.words) →
        AdaptiveDegree27MessagePlan QM31Exact
  terminalExact : ∀ (context : ExactTag73K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding)
      (member : context.k14.extraction.components ∈
        fixedWidth29TupleList decoder
          (extractedWidth29InitialWords context.k12.words)),
      terminal context
          (extractedFixedWidth29Candidate context.k14.extraction member) =
        extractedFixedTerminalPlan basis rc fixedInstance.statement
          context.k14.extraction
          (exactOperationalChallenge context.input .lambda)
          (exactOperationalChallenge context.input .chi)
          (context.material operational).data.helper
  sumcheckCausal : ∀ (context : ExactTag73K15Context transitionFuel configuration
      projection fixedInstance decoder decoderBinding)
      (member : context.k14.extraction.components ∈
        fixedWidth29TupleList decoder
          (extractedWidth29InitialWords context.k12.words)),
      WireUsesAdaptiveDegree27Plan
        (acceptedProductionWireOfCompact
          (context.fields operational)
          (context.run operational)
          (operationalCompactEvidence context.input
            (context.material operational).data.decoded
            (context.material operational).data.fixedDecode))
        (context.material operational).exactHonest
        (sumcheck context
          (extractedFixedWidth29Candidate context.k14.extraction member))
  pointCompatibleHandoff : ∀ (context : ExactTag73K15Context transitionFuel
      configuration projection fixedInstance decoder decoderBinding),
      (¬ FixedFamilyK15Failure (terminal context) (sumcheck context)
        (context.fields operational) context.k14.extraction
        (fun coordinate => exactOperationalChallenge context.input
          (.zerocheckPoint coordinate))
        (context.run operational).point
        (exactOperationalChallenge context.input .lambda)
        (exactOperationalChallenge context.input .chi)
        (exactOperationalChallenge context.input .theta)
        (exactOperationalChallenge context.input .mu)
        (exactOperationalChallenge context.input .kappa)
        (context.material operational).data.execution) →
      HasAcceptedRestoredPointCompatibleK14 decoder context.k12.words
          (context.run operational).point
          (context.fields operational).pointClaim
          (family context) →
        Nonempty
          (ExactFixedClientExtractionCertificate transitionFuel configuration
            fixedInstance
            (exactTag73SpendRelation (deployedOwner := deployedOwner)
              (deployedNote := deployedNote)
              (deployedNullifier := deployedNullifier)
              (deployedNode := deployedNode)) context.sample)

/-- The exact two residual failure shapes after a point-compatible restoration
has been routed to successful client extraction. -/
structure ExactTag73RestoredCausalK15Failure
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
      fixedInstance decoder decoderBinding) : Type where
  evidence : FixedFamilyK15Failure
      (environment.terminal context)
      (environment.sumcheck context)
      (context.fields environment.operational)
      context.k14.extraction
      (fun coordinate => exactOperationalChallenge context.input
        (.zerocheckPoint coordinate))
      (context.run environment.operational).point
      (exactOperationalChallenge context.input .lambda)
      (exactOperationalChallenge context.input .chi)
      (exactOperationalChallenge context.input .theta)
      (exactOperationalChallenge context.input .mu)
      (exactOperationalChallenge context.input .kappa)
      (context.material environment.operational).data.execution ∨
    (Nonempty (ExactTag73OperationalK15Failure
        (context.material environment.operational)) ∧
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder context.k12.words
          (context.run environment.operational).point
          (context.fields environment.operational).pointClaim
          (environment.family context))

/- The corrected classifier routes every point-compatible restoration to the
left branch.  The use of `Classical.choice` only eliminates the proof-valued
causal disjunction into the dependent data-valued stage result. -/
set_option linter.constructorNameAsVariable false in
noncomputable def exactTag73RestoredCausalK15Classifier
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
      poseidon) :
    ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance
      (exactTag73SpendRelation (deployedOwner := deployedOwner)
        (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
        (deployedNode := deployedNode)) decoder decoderBinding where
  error := fun sample input k12 k13 k14 =>
    ExactTag73RestoredCausalK15Failure environment
      ⟨sample, input, k12, k13, k14⟩
  classify := by
    intro sample input k12 k13 k14
    let material := environment.operational.material sample input k12 k13 k14
    let baseClassifier := exactTag73OperationalK15Classifier transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon environment.operational
    match baseClassifier.classify sample input k12 k13 k14 with
    | .inl extracted => exact .inl extracted
    | .inr failure =>
      let context : ExactTag73K15Context transitionFuel configuration projection
          fixedInstance decoder decoderBinding :=
        ⟨sample, input, k12, k13, k14⟩
      let fixedFailureProp : Prop :=
        FixedFamilyK15Failure (environment.terminal context)
          (environment.sumcheck context)
          (context.fields environment.operational) context.k14.extraction
          (fun coordinate => exactOperationalChallenge context.input
            (.zerocheckPoint coordinate))
          (context.run environment.operational).point
          (exactOperationalChallenge context.input .lambda)
          (exactOperationalChallenge context.input .chi)
          (exactOperationalChallenge context.input .theta)
          (exactOperationalChallenge context.input .mu)
          (exactOperationalChallenge context.input .kappa)
          (context.material environment.operational).data.execution
      by_cases anyFixed : fixedFailureProp
      · exact .inr ⟨Or.inl anyFixed⟩
      · have reduced :=
          exact_operational_k15_failure_reduces_to_restored_or_fixed
            (k13 := k13) material
            (environment.family context)
            (environment.familyAvailable context)
            (environment.familySelected context)
            (environment.terminal context)
            (environment.sumcheck context)
            (environment.terminalExact context)
            (environment.sumcheckCausal context) failure
        have result : Nonempty
          (ExactFixedClientExtractionCertificate transitionFuel configuration
              fixedInstance
              (exactTag73SpendRelation (deployedOwner := deployedOwner)
                (deployedNote := deployedNote)
                (deployedNullifier := deployedNullifier)
                (deployedNode := deployedNode)) sample ⊕
            ExactTag73RestoredCausalK15Failure environment
              ⟨sample, input, k12, k13, k14⟩) := by
          rcases reduced with restored | fixed | constrained
          · exact ⟨.inl (Classical.choice
              (environment.pointCompatibleHandoff
                context anyFixed restored))⟩
          · exact (anyFixed fixed).elim
          · by_cases restored : HasAcceptedRestoredPointCompatibleK14 decoder
                k12.words
                (operationalAcceptedRun input material.data.decoded
                  material.data.fixedDecode).point
                (operationalFixedFields material.data.decoded).pointClaim
                (environment.family ⟨sample, input, k12, k13, k14⟩)
            · exact ⟨.inl (Classical.choice
                (environment.pointCompatibleHandoff
                  context anyFixed restored))⟩
            · have noRestored : ¬ HasAcceptedRestoredPointCompatibleK14 decoder
                  k12.words
                  (operationalAcceptedRun input material.data.decoded
                    material.data.fixedDecode).point
                  (operationalFixedFields material.data.decoded).pointClaim
                  (environment.family ⟨sample, input, k12, k13, k14⟩) := restored
              exact ⟨.inr ⟨Or.inr ⟨⟨failure⟩, noRestored⟩⟩⟩
        exact Classical.choice result

#print axioms exactTag73RestoredCausalK15Classifier

-- Axiom reporting is performed on the classifier theorem below; printing the
-- two very large dependent data declarations themselves adds no proof fact.

end

end AspisK1.V7Tag73RestoredCausalK15Stage
