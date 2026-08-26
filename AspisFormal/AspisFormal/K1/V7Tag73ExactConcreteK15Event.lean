import AspisFormal.K1.V7Tag73ExactOperationalK15Stage

/-!
# Exact concrete K1.5 error event

The assembled stage package now uses the operational K1.5 classifier.  This
module identifies its abstract stage-error event with the literal event that
contains an exact input, the actual K1.2--K1.4 certificates, and one of the
thirteen causal `FailureEvidence` branches returned for that same execution.

No numerical probability is assigned here.  The subsequent causal-family
module must still prove that these literal failures enter the fixed
pre-challenge bad sets before applying the root inventory.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactConcreteK15Event

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
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7OpenedColumnsFromTrace
open AspisV6OneFoldCandidateExtraction
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Literal operational K1.5 failure event.  The environment selects no
success result: its classifier has already run the trace-to-witness theorem,
and this event retains only the typed failure evidence. -/
def exactTag73OperationalK15FailureEvent
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
    (poseidon : Poseidon2Faithful rc
      deployedOwner deployedNote deployedNullifier deployedNode)
    (environment : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) : Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (k13 : ExactK13Certificate decoder input k12)
      (k14 : ExactK14Certificate decoder decoderBinding input k12),
    Nonempty (ExactTag73OperationalK15Failure
      (environment.material sample input k12 k13 k14))}

/-- The abstract K1.5 stage event is definitionally the literal operational
failure event above. -/
theorem assembled_k15_error_event_exact
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
    (poseidon : Poseidon2Faithful rc
      deployedOwner deployedNote deployedNullifier deployedNode)
    (environment : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :
    k15SpendWitnessErrorEvent
        (exactTag73ProofRelevantStages transitionFuel configuration projection
          fixedInstance
          (exactTag73SpendRelation (deployedOwner := deployedOwner)
            (deployedNote := deployedNote)
            (deployedNullifier := deployedNullifier)
            (deployedNode := deployedNode)) decoder decoderBinding
          (exactTag73OperationalK15Classifier transitionFuel configuration
            projection fixedInstance decoder decoderBinding basis rc poseidon
            environment)) =
      exactTag73OperationalK15FailureEvent transitionFuel configuration
        projection fixedInstance decoder decoderBinding basis rc poseidon
        environment := by
  rfl

/-- Membership exposes the proposition-level causal branch itself, rather
than merely an inhabitant of an opaque stage error type. -/
theorem mem_exact_k15_failure_event_iff_failure_evidence
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
    {poseidon : Poseidon2Faithful rc
      deployedOwner deployedNote deployedNullifier deployedNode}
    {environment : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon}
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ exactTag73OperationalK15FailureEvent transitionFuel configuration
        projection fixedInstance decoder decoderBinding basis rc poseidon
        environment ↔
      ∃ (input : ExactK12OperationalInput transitionFuel configuration
            projection fixedInstance sample)
        (k12 : ExactPrefixK12Certificate input)
        (k13 : ExactK13Certificate decoder input k12)
        (k14 : ExactK14Certificate decoder decoderBinding input k12),
        FailureEvidence
          (failureEvent basis rc fixedInstance.statement
            (operationalFixedFields
              (environment.material sample input k12 k13 k14).data.decoded)
            (operationalAcceptedRun input
              (environment.material sample input k12 k13 k14).data.decoded
              (environment.material sample input k12 k13 k14).data.fixedDecode)
            (operationalCompactEvidence input
              (environment.material sample input k12 k13 k14).data.decoded
              (environment.material sample input k12 k13 k14).data.fixedDecode)
            k14.extraction
            (exactOperationalChallenge input .lambda)
            (exactOperationalChallenge input .chi)
            (exactOperationalChallenge input .theta)
            (fun coordinate => exactOperationalChallenge input
              (.zerocheckPoint coordinate))
            (exactOperationalChallenge input .mu)
            (environment.material sample input k12 k13 k14).data.helper
            (environment.material sample input k12 k13 k14).data.mask
            (environment.material sample input k12 k13 k14).exactHonest
            (exactOperationalChallenge input .kappa)
            (environment.material sample input k12 k13 k14).data.execution) := by
  constructor
  · rintro ⟨input, k12, k13, k14, ⟨failure⟩⟩
    exact ⟨input, k12, k13, k14, failure.evidence⟩
  · rintro ⟨input, k12, k13, k14, evidence⟩
    exact ⟨input, k12, k13, k14, ⟨⟨evidence⟩⟩⟩

#print axioms assembled_k15_error_event_exact
#print axioms mem_exact_k15_failure_event_iff_failure_evidence

end

end AspisK1.V7Tag73ExactConcreteK15Event
