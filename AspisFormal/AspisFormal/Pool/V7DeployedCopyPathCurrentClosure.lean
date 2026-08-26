import AspisFormal.Pool.V7DeployedCopyEvaluatorBalanceBridge

/-!
# Exact current-digest closure for all forty Tag-73 path links

The earlier scalar alias capstone isolates 43 unique scalar tags.  The full
atomic-v3 registry also contains forty unique digest tags: one input-path and
one output-path current-value link at each of twenty levels.  This file
isolates those tags from the same 183-element tagged-multiset equality and
projects their literal generated tuple patterns to the selected M31 trace.

No new copy assumption is introduced.  The only input is equality of the full
producer and consumer tagged multisets already derived outside the named
`chi` and `lambda` collision events.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7DeployedCopyPathCurrentClosure

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7OpenedColumnsFromTrace
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

/-- A current-digest tag occurs at exactly one link in the 183-link registry. -/
theorem deployedCopyTag_unique_at_pathCurrent
    (level : Fin 20) (output : Bool) (link : DeployedCopyLink)
    (tagEqual : deployedCopyTag link =
      deployedCopyTag (.pathCurrent level output)) :
    link = .pathCurrent level output := by
  cases output with
  | false =>
      cases link with
      | retained index => simp [deployedCopyTag] at tagEqual; omega
      | pathCurrent otherLevel otherOutput =>
          cases otherOutput with
          | false =>
              congr 2
              apply Fin.ext
              simp [deployedCopyTag] at tagEqual
              omega
          | true => simp [deployedCopyTag] at tagEqual; omega
      | pathSelect otherLevel otherOutput item =>
          cases otherOutput <;> simp [deployedCopyTag] at tagEqual <;> omega
      | pathAlias otherLevel hop =>
          fin_cases hop <;> simp [deployedCopyTag] at tagEqual <;> omega
  | true =>
      cases link with
      | retained index => simp [deployedCopyTag] at tagEqual; omega
      | pathCurrent otherLevel otherOutput =>
          cases otherOutput with
          | false => simp [deployedCopyTag] at tagEqual; omega
          | true =>
              congr 2
              apply Fin.ext
              simp [deployedCopyTag] at tagEqual
              omega
      | pathSelect otherLevel otherOutput item =>
          cases otherOutput <;> simp [deployedCopyTag] at tagEqual <;> omega
      | pathAlias otherLevel hop =>
          fin_cases hop <;> simp [deployedCopyTag] at tagEqual <;> omega

/-- Full tagged-multiset equality isolates one unique current-digest tuple. -/
theorem pathCurrent_tuple_equal_of_tagged_multisets_equal
    {K : Type*} [Zero K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (taggedEqual : producerTaggedMultiset source =
      consumerTaggedMultiset source)
    (level : Fin 20) (output : Bool) :
    source.producer (.pathCurrent level output) =
      source.consumer (.pathCurrent level output) := by
  classical
  have member : source.producer (.pathCurrent level output) ∈
      producerTaggedMultiset source := by
    simp [producerTaggedMultiset]
  rw [taggedEqual] at member
  simp only [consumerTaggedMultiset, Multiset.mem_map] at member
  obtain ⟨link, _, tupleEqual⟩ := member
  have tagEqual : deployedCopyTag link =
      deployedCopyTag (.pathCurrent level output) := by
    calc
      deployedCopyTag link = (source.consumer link).tag :=
        (source.consumerTag link).symm
      _ = (source.producer (.pathCurrent level output)).tag :=
        congrArg TaggedCopyTuple.tag tupleEqual
      _ = deployedCopyTag (.pathCurrent level output) :=
        source.producerTag (.pathCurrent level output)
  have linkEqual := deployedCopyTag_unique_at_pathCurrent
    level output link tagEqual
  subst link
  exact tupleEqual.symm

theorem concrete_pathCurrent_tuple_equal
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
    (level : Fin 20) (output : Bool) :
    deployedProducerTuple (extractedSelectedTrace extraction)
        (.pathCurrent level output) =
      deployedConsumerTuple (extractedSelectedTrace extraction)
        (.pathCurrent level output) := by
  exact pathCurrent_tuple_equal_of_tagged_multisets_equal
    (concreteDeployedCopyRegistryProjection extraction) taggedEqual level output

/-- Every input-path current auxiliary digest equals the preceding block's
literal final digest.  At level zero that preceding block is input-note block
three; thereafter it is the previous input-path block. -/
theorem inputPathCurrent_exact_of_tagged_multisets_equal
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
    (level : Fin 20) :
    lowDigestAt (extractedPhysicalTrace extraction) (inputPathFinalRow level) =
      pathDigestAt (extractedPhysicalTrace extraction) (inputPathRow level) := by
  funext limb
  have tupleEqual := concrete_pathCurrent_tuple_equal extraction taggedEqual
    level false
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs
      ⟨limb.val, by omega⟩) tupleEqual
  rw [deployedProducerTuple_pathCurrent_input_limb,
    deployedConsumerTuple_pathCurrent_input_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  simpa [extractedSelectedTrace, lowDigestAt, pathDigestAt,
    Nat.add_comm] using baseEqual

/-- Every output-path current auxiliary digest equals the preceding block's
literal final digest.  At level zero that preceding block is output-note block
48; thereafter it is the previous output-path block. -/
theorem outputPathCurrent_exact_of_tagged_multisets_equal
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
    (level : Fin 20) :
    lowDigestAt (extractedPhysicalTrace extraction) (outputPathFinalRow level) =
      pathDigestAt (extractedPhysicalTrace extraction) (outputPathRow level) := by
  funext limb
  have tupleEqual := concrete_pathCurrent_tuple_equal extraction taggedEqual
    level true
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs
      ⟨limb.val, by omega⟩) tupleEqual
  rw [deployedProducerTuple_pathCurrent_output_limb,
    deployedConsumerTuple_pathCurrent_output_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  simpa [extractedSelectedTrace, lowDigestAt, pathDigestAt,
    Nat.add_comm] using baseEqual

#print axioms deployedCopyTag_unique_at_pathCurrent
#print axioms pathCurrent_tuple_equal_of_tagged_multisets_equal
#print axioms inputPathCurrent_exact_of_tagged_multisets_equal
#print axioms outputPathCurrent_exact_of_tagged_multisets_equal

end AspisPool.V7DeployedCopyPathCurrentClosure
