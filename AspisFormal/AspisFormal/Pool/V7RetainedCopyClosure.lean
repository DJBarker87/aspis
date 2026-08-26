import AspisFormal.Pool.V7MerklePathsFromTrace

/-!
# Exact retained-hash Copy LogUp closure

The first 23 generated copy links have unique tags.  They carry the owner,
note, nullifier, absorption, and digest boundaries that remain after the two
Merkle paths have been reconstructed.  This file first isolates all 23 tuples
from the same complete tagged-multiset equality.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7RetainedCopyClosure

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PoseidonRowsFromTrace
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

theorem deployedCopyTag_unique_at_retained
    (index : Fin 23) (link : DeployedCopyLink)
    (tagEqual : deployedCopyTag link = deployedCopyTag (.retained index)) :
    link = .retained index := by
  cases link with
  | retained other =>
      congr 1
      apply Fin.ext
      simp [deployedCopyTag] at tagEqual
      omega
  | pathCurrent level output =>
      cases output <;> simp [deployedCopyTag] at tagEqual <;> omega
  | pathSelect level output item =>
      cases output <;> simp [deployedCopyTag] at tagEqual <;> omega
  | pathAlias level hop =>
      fin_cases hop <;> simp [deployedCopyTag] at tagEqual <;> omega

theorem retained_tuple_equal_of_tagged_multisets_equal
    {K : Type*} [Zero K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (taggedEqual : producerTaggedMultiset source =
      consumerTaggedMultiset source)
    (index : Fin 23) :
    source.producer (.retained index) = source.consumer (.retained index) := by
  classical
  have member : source.producer (.retained index) ∈
      producerTaggedMultiset source := by
    simp [producerTaggedMultiset]
  rw [taggedEqual] at member
  simp only [consumerTaggedMultiset, Multiset.mem_map] at member
  obtain ⟨link, _, tupleEqual⟩ := member
  have tagEqual : deployedCopyTag link = deployedCopyTag (.retained index) := by
    calc
      deployedCopyTag link = (source.consumer link).tag :=
        (source.consumerTag link).symm
      _ = (source.producer (.retained index)).tag :=
        congrArg TaggedCopyTuple.tag tupleEqual
      _ = deployedCopyTag (.retained index) := source.producerTag (.retained index)
  have linkEqual := deployedCopyTag_unique_at_retained index link tagEqual
  subst link
  exact tupleEqual.symm

theorem concrete_retained_tuple_equal
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (index : Fin 23) :
    deployedProducerTuple (extractedSelectedTrace extraction) (.retained index) =
      deployedConsumerTuple (extractedSelectedTrace extraction) (.retained index) := by
  exact retained_tuple_equal_of_tagged_multisets_equal
    (concreteDeployedCopyRegistryProjection extraction) taggedEqual index

/-- Base-field equality of any limb of any retained endpoint.  This is the
literal projection used by the typed owner/note/nullifier block bridge. -/
theorem retained_pattern_limb_base_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (index : Fin 23) (limb : Fin 16) :
    (deployedPatternLimb (extractedSelectedTrace extraction)
        (retainedProducerEndpoint index).row
        (retainedProducerEndpoint index).pattern limb).re.re =
      (deployedPatternLimb (extractedSelectedTrace extraction)
        (retainedConsumerEndpoint index).row
        (retainedConsumerEndpoint index).pattern limb).re.re := by
  have tupleEqual := concrete_retained_tuple_equal extraction taggedEqual index
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs limb) tupleEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  simpa [deployedProducerTuple, deployedConsumerTuple, deployedEndpointTuple,
    deployedProducerEndpoint, deployedConsumerEndpoint] using baseEqual

/-- Link zero copies the complete final state of input-note block one into the
initial row of input-note block two. -/
theorem retained_input_note_first_continuation_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    stateAt (extractedPhysicalTrace extraction) 27 =
      stateAt (extractedPhysicalTrace extraction) 32 := by
  funext lane
  have tupleEqual := concrete_retained_tuple_equal extraction taggedEqual 0
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs lane) tupleEqual
  simp [deployedProducerTuple, deployedConsumerTuple, deployedEndpointTuple,
    deployedProducerEndpoint, deployedConsumerEndpoint,
    retainedProducerEndpoint, retainedConsumerEndpoint,
    deployedPatternLimb, endpoint] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  simpa [extractedSelectedTrace, stateAt] using baseEqual

def retainedStateProducerRow : Fin 5 → Fin 1024 := ![27, 43, 715, 747, 763]
def retainedStateConsumerRow : Fin 5 → Fin 1024 := ![32, 48, 720, 752, 768]

/-- All five full-state continuation links: two input-note continuations, one
nullifier continuation, and two output-note continuations. -/
theorem retained_hash_state_continuations_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (which : Fin 5) :
    stateAt (extractedPhysicalTrace extraction) (retainedStateProducerRow which) =
      stateAt (extractedPhysicalTrace extraction)
        (retainedStateConsumerRow which) := by
  funext lane
  let index : Fin 23 := ⟨which.val, by omega⟩
  have tupleEqual := concrete_retained_tuple_equal extraction taggedEqual index
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs lane) tupleEqual
  simp [deployedProducerTuple, deployedConsumerTuple, deployedEndpointTuple,
    deployedProducerEndpoint, deployedConsumerEndpoint,
    retainedProducerEndpoint, retainedConsumerEndpoint,
    deployedPatternLimb, endpoint] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  fin_cases which <;>
    simpa [index, extractedSelectedTrace, stateAt, retainedStateProducerRow,
      retainedStateConsumerRow] using baseEqual

#print axioms deployedCopyTag_unique_at_retained
#print axioms retained_tuple_equal_of_tagged_multisets_equal
#print axioms retained_pattern_limb_base_exact
#print axioms retained_input_note_first_continuation_exact
#print axioms retained_hash_state_continuations_exact

end AspisPool.V7RetainedCopyClosure
