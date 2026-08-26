import AspisFormal.Pool.V7DeployedCopyPathCurrentClosure

/-!
# Exact path-selection closure for Tag-73 Copy LogUp

Each input/output Merkle level deliberately gives the two selection links one
shared copy tag.  Equality of the complete 183-element tagged multisets first
shows that either producer is matched to one of exactly those two consumers.
The deployed Boolean path bit then fixes the matching: bit zero sends current
left and sibling right; bit one swaps them.

This file proves that matching directly from the literal generated tuple
patterns.  In particular the right-child consumer removes the node tweak from
the committed capacity lane through its checked M31 offset; no unordered or
untyped copy premise is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7DeployedCopyPathSelectionClosure

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyPathCurrentClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7OpenedColumnsFromTrace
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

/-- A shared selection tag occurs at exactly its two item links. -/
theorem deployedCopyTag_classifies_pathSelect
    (level : Fin 20) (output : Bool) (link : DeployedCopyLink)
    (tagEqual : deployedCopyTag link =
      deployedCopyTag (.pathSelect level output 0)) :
    ∃ item : Fin 2, link = .pathSelect level output item := by
  cases output with
  | false =>
      cases link with
      | retained index => simp [deployedCopyTag] at tagEqual; omega
      | pathCurrent otherLevel otherOutput =>
          cases otherOutput <;> simp [deployedCopyTag] at tagEqual <;> omega
      | pathSelect otherLevel otherOutput item =>
          cases otherOutput with
          | false =>
              refine ⟨item, ?_⟩
              congr 2
              apply Fin.ext
              simp [deployedCopyTag] at tagEqual
              omega
          | true => simp [deployedCopyTag] at tagEqual; omega
      | pathAlias otherLevel hop =>
          fin_cases hop <;> simp [deployedCopyTag] at tagEqual <;> omega
  | true =>
      cases link with
      | retained index => simp [deployedCopyTag] at tagEqual; omega
      | pathCurrent otherLevel otherOutput =>
          cases otherOutput <;> simp [deployedCopyTag] at tagEqual <;> omega
      | pathSelect otherLevel otherOutput item =>
          cases otherOutput with
          | false => simp [deployedCopyTag] at tagEqual; omega
          | true =>
              refine ⟨item, ?_⟩
              congr 2
              apply Fin.ext
              simp [deployedCopyTag] at tagEqual
              omega
      | pathAlias otherLevel hop =>
          fin_cases hop <;> simp [deployedCopyTag] at tagEqual <;> omega

/-- One selected producer must equal one of the two consumers sharing its tag. -/
theorem pathSelect_producer_matches_consumer
    {K : Type*} [Zero K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (taggedEqual : producerTaggedMultiset source =
      consumerTaggedMultiset source)
    (level : Fin 20) (output : Bool) (producerItem : Fin 2) :
    ∃ consumerItem : Fin 2,
      source.producer (.pathSelect level output producerItem) =
        source.consumer (.pathSelect level output consumerItem) := by
  classical
  have member : source.producer (.pathSelect level output producerItem) ∈
      producerTaggedMultiset source := by
    simp [producerTaggedMultiset]
  rw [taggedEqual] at member
  simp only [consumerTaggedMultiset, Multiset.mem_map] at member
  obtain ⟨link, _, tupleEqual⟩ := member
  have tagEqual : deployedCopyTag link =
      deployedCopyTag (.pathSelect level output 0) := by
    calc
      deployedCopyTag link = (source.consumer link).tag :=
        (source.consumerTag link).symm
      _ = (source.producer (.pathSelect level output producerItem)).tag :=
        congrArg TaggedCopyTuple.tag tupleEqual
      _ = deployedCopyTag (.pathSelect level output producerItem) :=
        source.producerTag (.pathSelect level output producerItem)
      _ = deployedCopyTag (.pathSelect level output 0) := by
        cases output <;> simp [deployedCopyTag]
  obtain ⟨consumerItem, linkEqual⟩ :=
    deployedCopyTag_classifies_pathSelect level output link tagEqual
  subst link
  exact ⟨consumerItem, tupleEqual.symm⟩

theorem concrete_pathSelect_producer_matches_consumer
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
    (level : Fin 20) (output : Bool) (producerItem : Fin 2) :
    ∃ consumerItem : Fin 2,
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output producerItem) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output consumerItem) := by
  exact pathSelect_producer_matches_consumer
    (concreteDeployedCopyRegistryProjection extraction) taggedEqual
      level output producerItem

/-! ## The tag-zero limb fixes the matching -/

theorem current_match_left_forces_zero
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0)) :
    extractedPhysicalTrace extraction (selectedPathCurrentRow level output) 0 =
      0 := by
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs 0) tupleEqual
  rw [deployedProducerTuple_pathSelect_current_limb,
    deployedConsumerTuple_pathSelect_left_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  simpa [extractedSelectedTrace] using baseEqual

theorem current_match_right_forces_one
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1)) :
    extractedPhysicalTrace extraction (selectedPathCurrentRow level output) 0 =
      1 := by
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs 0) tupleEqual
  rw [deployedProducerTuple_pathSelect_current_limb,
    deployedConsumerTuple_pathSelect_right_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  have oneBase : ((1 : QM31Exact).re.re) =
      (1 : AspisFormal.ArithmetizationCore.F) := rfl
  simpa [extractedSelectedTrace, oneBase] using baseEqual

theorem sibling_match_left_forces_one
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0)) :
    extractedPhysicalTrace extraction (siblingPathRow level) 0 = 1 := by
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs 0) tupleEqual
  rw [deployedProducerTuple_pathSelect_sibling_limb,
    deployedConsumerTuple_pathSelect_left_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  have oneBase : ((1 : QM31Exact).re.re) =
      (1 : AspisFormal.ArithmetizationCore.F) := rfl
  have solved := sub_eq_zero.mp baseEqual
  rw [oneBase] at solved
  simpa [extractedSelectedTrace] using solved.symm

theorem sibling_match_right_forces_zero
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1)) :
    extractedPhysicalTrace extraction (siblingPathRow level) 0 = 0 := by
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs 0) tupleEqual
  rw [deployedProducerTuple_pathSelect_sibling_limb,
    deployedConsumerTuple_pathSelect_right_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  have : (1 : AspisFormal.ArithmetizationCore.F) -
      extractedPhysicalTrace extraction (siblingPathRow level) 0 = 1 := by
    simpa [extractedSelectedTrace] using baseEqual
  exact sub_eq_self.mp this

/-- With bit zero, the shared tag has the unswapped matching. -/
theorem pathSelect_pair_exact_of_bit_zero
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
    (level : Fin 20) (output : Bool)
    (currentZero :
      extractedPhysicalTrace extraction
          (selectedPathCurrentRow level output) 0 = 0)
    (siblingZero :
      extractedPhysicalTrace extraction (siblingPathRow level) 0 = 0) :
    deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) ∧
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) := by
  constructor
  · obtain ⟨consumerItem, tupleEqual⟩ :=
      concrete_pathSelect_producer_matches_consumer extraction taggedEqual
        level output 0
    fin_cases consumerItem
    · exact tupleEqual
    · have forcedOne := current_match_right_forces_one extraction
        level output tupleEqual
      exact False.elim (zero_ne_one (currentZero.symm.trans forcedOne))
  · obtain ⟨consumerItem, tupleEqual⟩ :=
      concrete_pathSelect_producer_matches_consumer extraction taggedEqual
        level output 1
    fin_cases consumerItem
    · have forcedOne := sibling_match_left_forces_one extraction
        level output tupleEqual
      exact False.elim (zero_ne_one (siblingZero.symm.trans forcedOne))
    · exact tupleEqual

/-- With bit one, the shared tag has the swapped matching. -/
theorem pathSelect_pair_exact_of_bit_one
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
    (level : Fin 20) (output : Bool)
    (currentOne :
      extractedPhysicalTrace extraction
          (selectedPathCurrentRow level output) 0 = 1)
    (siblingOne :
      extractedPhysicalTrace extraction (siblingPathRow level) 0 = 1) :
    deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) ∧
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) := by
  constructor
  · obtain ⟨consumerItem, tupleEqual⟩ :=
      concrete_pathSelect_producer_matches_consumer extraction taggedEqual
        level output 0
    fin_cases consumerItem
    · have forcedZero := current_match_left_forces_zero extraction
        level output tupleEqual
      exact False.elim (zero_ne_one (forcedZero.symm.trans currentOne))
    · exact tupleEqual
  · obtain ⟨consumerItem, tupleEqual⟩ :=
      concrete_pathSelect_producer_matches_consumer extraction taggedEqual
        level output 1
    fin_cases consumerItem
    · exact tupleEqual
    · have forcedZero := sibling_match_right_forces_zero extraction
        level output tupleEqual
      exact False.elim (zero_ne_one (forcedZero.symm.trans siblingOne))

theorem requiredTraceAliases_of_tagged_multisets_equal
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
    RequiredTraceAliases
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) := by
  let source := concreteDeployedCopyRegistryProjection extraction
  have allEqual : ∀ required,
      requiredProducerCell extraction required =
        requiredConsumerCell extraction required := by
    intro required
    exact required_value_equal_of_tagged_multisets_equal
      source taggedEqual required
  exact requiredTraceAliases_of_copy_sources extraction
    (requiredCopySourceEquations_of_all_required_values_equal extraction allEqual)

/-- Every shared selection tag receives the exact Boolean-dependent pairing. -/
theorem pathSelect_pair_exact_of_binary_and_tagged_multisets_equal
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
    (binary : PathBitsAreBinary
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)))
    (level : Fin 20) (output : Bool) :
    ((rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).inputPathBits level = 0 ∧
      deployedProducerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 0) =
          deployedConsumerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 0) ∧
      deployedProducerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 1) =
          deployedConsumerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 1)) ∨
    ((rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).inputPathBits level = 1 ∧
      deployedProducerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 0) =
          deployedConsumerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 1) ∧
      deployedProducerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 1) =
          deployedConsumerTuple (extractedSelectedTrace extraction)
            (.pathSelect level output 0)) := by
  have aliases := requiredTraceAliases_of_tagged_multisets_equal
    extraction taggedEqual
  rcases binary level with bitZero | bitOne
  · left
    refine ⟨bitZero, ?_⟩
    have currentZero : extractedPhysicalTrace extraction
        (selectedPathCurrentRow level output) 0 = 0 := by
      cases output with
      | false => exact bitZero
      | true => exact (aliases.outputPathBit level).trans bitZero
    have siblingZero : extractedPhysicalTrace extraction
        (siblingPathRow level) 0 = 0 := by
      exact (aliases.siblingPathBit level).trans bitZero
    exact pathSelect_pair_exact_of_bit_zero extraction taggedEqual
      level output currentZero siblingZero
  · right
    refine ⟨bitOne, ?_⟩
    have currentOne : extractedPhysicalTrace extraction
        (selectedPathCurrentRow level output) 0 = 1 := by
      cases output with
      | false => exact bitOne
      | true => exact (aliases.outputPathBit level).trans bitOne
    have siblingOne : extractedPhysicalTrace extraction
        (siblingPathRow level) 0 = 1 := by
      exact (aliases.siblingPathBit level).trans bitOne
    exact pathSelect_pair_exact_of_bit_one extraction taggedEqual
      level output currentOne siblingOne

#print axioms deployedCopyTag_classifies_pathSelect
#print axioms pathSelect_producer_matches_consumer
#print axioms current_match_left_forces_zero
#print axioms current_match_right_forces_one
#print axioms sibling_match_left_forces_one
#print axioms sibling_match_right_forces_zero
#print axioms pathSelect_pair_exact_of_bit_zero
#print axioms pathSelect_pair_exact_of_bit_one
#print axioms requiredTraceAliases_of_tagged_multisets_equal
#print axioms pathSelect_pair_exact_of_binary_and_tagged_multisets_equal

end AspisPool.V7DeployedCopyPathSelectionClosure
