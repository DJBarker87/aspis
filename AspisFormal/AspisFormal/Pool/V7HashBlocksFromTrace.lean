import AspisFormal.Pool.V7RetainedCopyClosure

/-!
# Typed owner, note, and nullifier blocks from the Tag-73 trace

The nine non-Merkle Poseidon blocks use four domain-separated initial rows,
five whole-state continuations, and the first 23 retained Copy LogUp links.
This file reduces those literal rows to the typed sponge inputs consumed by
`ExtractedHashMerkleResiduals`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7HashBlocksFromTrace

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7MerklePathsFromTrace
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RetainedCopyClosure
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV5ProductionPublicResidualBinding
open AspisV6OneFoldCandidateExtraction

theorem initialResidual_at_retainedInitialRow
    (trace : PhysicalTrace) (which : Fin 4) (column : Fin 16) :
    initialResidual trace (retainedInitialRow which) column =
      trace (retainedInitialRow which) column -
        initialExpected which column := by
  have retainedEqual : ∀ other : Fin 4,
      retainedInitialRow which = retainedInitialRow other ↔ other = which := by
    intro other
    constructor
    · intro equal
      apply Fin.ext
      have values := congrArg Fin.val equal
      fin_cases which <;> fin_cases other <;>
        simp [retainedInitialRow] at values ⊢
    · intro equal
      subst other
      rfl
  have noPath : ∀ block : Fin 40,
      retainedInitialRow which ≠ pathInitialRow block := by
    intro block equal
    have values := congrArg Fin.val equal
    fin_cases which <;>
      simp [retainedInitialRow, pathInitialRow] at values <;> omega
  simp [initialResidual, retainedEqual, noPath]

theorem retained_initial_state_exact_of_semantic_rows_vanish
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) (which : Fin 4) :
    stateAt trace (retainedInitialRow which) =
      initState (retainedInitialDomain which)
        (retainedInitialLength which) := by
  funext lane
  have residual := coordinate_residual_zero_of_semantic_rows_vanish
    fields trace vanish (.initial lane) (retainedInitialRow which)
  rw [atomicSemanticResidual,
    initialResidual_at_retainedInitialRow trace which lane] at residual
  have exact := sub_eq_zero.mp residual
  unfold stateAt
  rw [exact]
  unfold initialExpected initState
  by_cases laneEight : lane.val = 8
  · have laneExact : lane = (8 : Fin 16) := Fin.ext laneEight
    subst lane
    simp
  · by_cases laneNine : lane.val = 9
    · have laneExact : lane = (9 : Fin 16) := Fin.ext laneNine
      subst lane
      simp
    · have notEight : lane ≠ (8 : Fin 16) := by
        intro equal
        exact laneEight (congrArg Fin.val equal)
      have notNine : lane ≠ (9 : Fin 16) := by
        intro equal
        exact laneNine (congrArg Fin.val equal)
      simp [notEight, notNine, laneEight, laneNine]

theorem retained_link_low_digest_exact
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
    (index : Fin 23) (limb : Fin 8) :
    (deployedPatternLimb (extractedSelectedTrace extraction)
        (retainedProducerEndpoint index).row
        (retainedProducerEndpoint index).pattern
        ⟨limb.val, by omega⟩).re.re =
      (deployedPatternLimb (extractedSelectedTrace extraction)
        (retainedConsumerEndpoint index).row
        (retainedConsumerEndpoint index).pattern
        ⟨limb.val, by omega⟩).re.re :=
  retained_pattern_limb_base_exact extraction taggedEqual index
    ⟨limb.val, by omega⟩

theorem input_owner_digest_staging_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 11 ⟨limb.val, by omega⟩ =
      extractedPhysicalTrace extraction 793 ⟨limb.val, by omega⟩ := by
  have equal := retained_link_low_digest_exact extraction taggedEqual 5 limb
  have limbBound : limb.val < 16 := by omega
  simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
    deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
    limbBound] using equal

theorem low_absorption_padding_zero_of_semantic_rows_vanish
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace)
    (which : Fin 2) (column : Fin 16)
    (padding : 2 ≤ column.val) (rate : column.val < 8) :
    trace (absorptionLowRow which) column = 0 := by
  have residual := coordinate_residual_zero_of_semantic_rows_vanish
    fields trace vanish (.absorption column) (absorptionLowRow which)
  change absorptionResidual trace (absorptionLowRow which) column = 0 at residual
  have notHigh : ¬ 8 ≤ column.val := by omega
  fin_cases which <;>
    simp [absorptionResidual, absorptionLowRow,
      padding, rate, notHigh] at residual ⊢ <;> exact residual

theorem owner_key_absorption_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 12 ⟨limb.val, by omega⟩ =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).kNu limb := by
  have equal := retained_pattern_limb_base_exact extraction taggedEqual 11
    ⟨limb.val, by omega⟩
  have limbBound : limb.val < 16 := by omega
  have reduced : limb.val % 8 = limb.val := Nat.mod_eq_of_lt limb.isLt
  have highBound : 8 + limb.val < 16 := by omega
  simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
    deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
    limbBound, reduced, highBound, rawOpenedColumnsFromTrace,
    highDigestAt] using equal.symm

theorem input_note_owner_absorption_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 28 ⟨limb.val, by omega⟩ =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).inputOwnerKey limb := by
  have staged := input_owner_digest_staging_exact extraction taggedEqual limb
  have copied := retained_pattern_limb_base_exact extraction taggedEqual 12
    ⟨limb.val, by omega⟩
  have limbBound : limb.val < 16 := by omega
  have stagedToAbsorb :
      extractedPhysicalTrace extraction 793 ⟨limb.val, by omega⟩ =
        extractedPhysicalTrace extraction 28 ⟨limb.val, by omega⟩ := by
    simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
      deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
      limbBound] using copied
  exact stagedToAbsorb.symm.trans staged.symm

theorem input_note_value_staging_exact
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
    extractedPhysicalTrace extraction 795 0 =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).rin.value := by
  change extractedPhysicalTrace extraction 795 0 =
    extractedPhysicalTrace extraction 864 11
  have equal := retained_pattern_limb_base_exact extraction taggedEqual 20 0
  simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
    deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
    rawOpenedColumnsFromTrace, rangeWitnessFromRows] using equal.symm

theorem output_note_value_staging_exact
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
    extractedPhysicalTrace extraction 799 0 =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).rout.value := by
  change extractedPhysicalTrace extraction 799 0 =
    extractedPhysicalTrace extraction 866 11
  have equal := retained_pattern_limb_base_exact extraction taggedEqual 21 0
  simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
    deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
    rawOpenedColumnsFromTrace, rangeWitnessFromRows] using equal.symm

theorem input_note_chunk1_absorption_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 44 ⟨limb.val, by omega⟩ =
      noteChunk1
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).rin.value
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).inputAsset
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).inputSalt limb := by
  have copied := retained_pattern_limb_base_exact extraction taggedEqual 13
    ⟨limb.val, by omega⟩
  have limbBound : limb.val < 16 := by omega
  have copiedBase :
      extractedPhysicalTrace extraction 795 ⟨limb.val, by omega⟩ =
        extractedPhysicalTrace extraction 44 ⟨limb.val, by omega⟩ := by
    simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
      deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
      limbBound] using copied
  have value := input_note_value_staging_exact extraction taggedEqual
  fin_cases limb <;>
    simp [noteChunk1, rawOpenedColumnsFromTrace, saltDigestAt] at copiedBase ⊢
  all_goals first | exact copiedBase.symm.trans value | exact copiedBase.symm

theorem output_note_owner_absorption_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 748 ⟨limb.val, by omega⟩ =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).outputOwnerKey limb := by
  have copied := retained_pattern_limb_base_exact extraction taggedEqual 17
    ⟨limb.val, by omega⟩
  have limbBound : limb.val < 16 := by omega
  have highBound : 8 + limb.val < 16 := by omega
  simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
    deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
    limbBound, highBound, rawOpenedColumnsFromTrace, highDigestAt] using copied.symm

theorem output_note_chunk1_absorption_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 764 ⟨limb.val, by omega⟩ =
      noteChunk1
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).rout.value
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).outputAsset
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).outputSalt limb := by
  have copied := retained_pattern_limb_base_exact extraction taggedEqual 18
    ⟨limb.val, by omega⟩
  have limbBound : limb.val < 16 := by omega
  have copiedBase :
      extractedPhysicalTrace extraction 799 ⟨limb.val, by omega⟩ =
        extractedPhysicalTrace extraction 764 ⟨limb.val, by omega⟩ := by
    simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
      deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
      limbBound] using copied
  have value := output_note_value_staging_exact extraction taggedEqual
  fin_cases limb <;>
    simp [noteChunk1, rawOpenedColumnsFromTrace, saltDigestAt] at copiedBase ⊢
  all_goals first | exact copiedBase.symm.trans value | exact copiedBase.symm

theorem input_note_chunk2_head_exact
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
    (head : Fin 2) :
    extractedPhysicalTrace extraction 60 ⟨head.val, by omega⟩ =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).inputSalt
          ⟨6 + head.val, by omega⟩ := by
  fin_cases head
  · have saltCopy := retained_pattern_limb_base_exact extraction taggedEqual 13 14
    have rotate := retained_pattern_limb_base_exact extraction taggedEqual 8 6
    have absorbCopy := retained_pattern_limb_base_exact extraction taggedEqual 14 0
    have saltEq : extractedPhysicalTrace extraction 795 8 =
        extractedPhysicalTrace extraction 44 14 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using saltCopy
    have rotateEq : extractedPhysicalTrace extraction 44 14 =
        extractedPhysicalTrace extraction 797 0 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using rotate
    have absorbEq : extractedPhysicalTrace extraction 797 0 =
        extractedPhysicalTrace extraction 60 0 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using absorbCopy
    change extractedPhysicalTrace extraction 60 0 =
      extractedPhysicalTrace extraction 795 8
    exact absorbEq.symm.trans (rotateEq.symm.trans saltEq.symm)
  · have saltCopy := retained_pattern_limb_base_exact extraction taggedEqual 13 15
    have rotate := retained_pattern_limb_base_exact extraction taggedEqual 8 7
    have absorbCopy := retained_pattern_limb_base_exact extraction taggedEqual 14 1
    have saltEq : extractedPhysicalTrace extraction 795 9 =
        extractedPhysicalTrace extraction 44 15 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using saltCopy
    have rotateEq : extractedPhysicalTrace extraction 44 15 =
        extractedPhysicalTrace extraction 797 1 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using rotate
    have absorbEq : extractedPhysicalTrace extraction 797 1 =
        extractedPhysicalTrace extraction 60 1 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using absorbCopy
    change extractedPhysicalTrace extraction 60 1 =
      extractedPhysicalTrace extraction 795 9
    exact absorbEq.symm.trans (rotateEq.symm.trans saltEq.symm)

theorem input_note_chunk2_absorption_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 60 ⟨limb.val, by omega⟩ =
      noteChunk2
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).inputSalt limb := by
  fin_cases limb
  · exact input_note_chunk2_head_exact extraction taggedEqual 0
  · exact input_note_chunk2_head_exact extraction taggedEqual 1
  all_goals
    simp [noteChunk2]
    exact low_absorption_padding_zero_of_semantic_rows_vanish
      fields (extractedPhysicalTrace extraction) semanticVanish 0 _ (by omega) (by omega)

theorem nullifier_key_absorption_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 716 ⟨limb.val, by omega⟩ =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).kNu limb := by
  have ownerCopy := retained_pattern_limb_base_exact extraction taggedEqual 11
    ⟨8 + limb.val, by omega⟩
  have stagingCopy := retained_pattern_limb_base_exact extraction taggedEqual 7
    ⟨limb.val, by omega⟩
  have absorbCopy := retained_pattern_limb_base_exact extraction taggedEqual 15
    ⟨limb.val, by omega⟩
  fin_cases limb <;>
    simp [retainedProducerEndpoint, retainedConsumerEndpoint,
      deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
      rawOpenedColumnsFromTrace, highDigestAt] at ownerCopy stagingCopy absorbCopy ⊢
  all_goals
    exact absorbCopy.symm.trans
      (stagingCopy.symm.trans ownerCopy.symm)

theorem nullifier_salt_absorption_exact
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
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 732 ⟨limb.val, by omega⟩ =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).inputSalt limb := by
  have saltCopy := retained_pattern_limb_base_exact extraction taggedEqual 13
    ⟨8 + limb.val, by omega⟩
  have rotateCopy := retained_pattern_limb_base_exact extraction taggedEqual 8
    ⟨limb.val, by omega⟩
  have noteCopy := retained_pattern_limb_base_exact extraction taggedEqual 14
    ⟨8 + limb.val, by omega⟩
  have stagingCopy := retained_pattern_limb_base_exact extraction taggedEqual 9
    ⟨limb.val, by omega⟩
  have absorbCopy := retained_pattern_limb_base_exact extraction taggedEqual 16
    ⟨limb.val, by omega⟩
  fin_cases limb <;>
    simp [retainedProducerEndpoint, retainedConsumerEndpoint,
      deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace,
      rawOpenedColumnsFromTrace, saltDigestAt] at saltCopy rotateCopy noteCopy stagingCopy absorbCopy ⊢
  all_goals
    exact absorbCopy.symm.trans (stagingCopy.symm.trans
      (noteCopy.symm.trans (rotateCopy.symm.trans saltCopy.symm)))

theorem output_note_chunk2_head_exact
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
    (head : Fin 2) :
    extractedPhysicalTrace extraction 780 ⟨head.val, by omega⟩ =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).outputSalt
          ⟨6 + head.val, by omega⟩ := by
  fin_cases head
  · have saltCopy := retained_pattern_limb_base_exact extraction taggedEqual 18 14
    have rotate := retained_pattern_limb_base_exact extraction taggedEqual 10 6
    have absorbCopy := retained_pattern_limb_base_exact extraction taggedEqual 19 0
    have saltEq : extractedPhysicalTrace extraction 799 8 =
        extractedPhysicalTrace extraction 764 14 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using saltCopy
    have rotateEq : extractedPhysicalTrace extraction 764 14 =
        extractedPhysicalTrace extraction 809 0 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using rotate
    have absorbEq : extractedPhysicalTrace extraction 809 0 =
        extractedPhysicalTrace extraction 780 0 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using absorbCopy
    change extractedPhysicalTrace extraction 780 0 =
      extractedPhysicalTrace extraction 799 8
    exact absorbEq.symm.trans (rotateEq.symm.trans saltEq.symm)
  · have saltCopy := retained_pattern_limb_base_exact extraction taggedEqual 18 15
    have rotate := retained_pattern_limb_base_exact extraction taggedEqual 10 7
    have absorbCopy := retained_pattern_limb_base_exact extraction taggedEqual 19 1
    have saltEq : extractedPhysicalTrace extraction 799 9 =
        extractedPhysicalTrace extraction 764 15 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using saltCopy
    have rotateEq : extractedPhysicalTrace extraction 764 15 =
        extractedPhysicalTrace extraction 809 1 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using rotate
    have absorbEq : extractedPhysicalTrace extraction 809 1 =
        extractedPhysicalTrace extraction 780 1 := by
      simpa [retainedProducerEndpoint, retainedConsumerEndpoint,
        deployedPatternLimb, traceCell, endpoint, extractedSelectedTrace] using absorbCopy
    change extractedPhysicalTrace extraction 780 1 =
      extractedPhysicalTrace extraction 799 9
    exact absorbEq.symm.trans (rotateEq.symm.trans saltEq.symm)

theorem output_note_chunk2_absorption_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (limb : Fin 8) :
    extractedPhysicalTrace extraction 780 ⟨limb.val, by omega⟩ =
      noteChunk2
        (rawOpenedColumnsFromTrace
          (extractedPhysicalTrace extraction)).outputSalt limb := by
  fin_cases limb
  · exact output_note_chunk2_head_exact extraction taggedEqual 0
  · exact output_note_chunk2_head_exact extraction taggedEqual 1
  all_goals
    simp [noteChunk2]
    exact low_absorption_padding_zero_of_semantic_rows_vanish
      fields (extractedPhysicalTrace extraction) semanticVanish 1 _ (by omega) (by omega)

theorem absorbedBlockInput_eq_absorb_of_rows
    (trace : PhysicalTrace) (block : PoseidonBlock)
    (base : State) (chunk : Fin 8 → F)
    (baseExact : stateAt trace ⟨16 * block.val, by omega⟩ = base)
    (chunkExact : ∀ limb : Fin 8,
      trace ⟨16 * block.val + 12, by omega⟩
          ⟨limb.val, by omega⟩ = chunk limb) :
    absorbedBlockInput trace block = absorb base chunk := by
  funext lane
  by_cases low : lane.val < 8
  · let rateLane : Fin 8 := ⟨lane.val, low⟩
    have baseLane := congrFun baseExact lane
    have chunkLane :
        trace ⟨16 * block.val + 12, by omega⟩ lane = chunk rateLane := by
      simpa [rateLane] using chunkExact rateLane
    unfold absorbedBlockInput absorb
    simp only [dif_pos low]
    rw [show trace ⟨16 * block.val, by omega⟩ lane = base lane by
      simpa [stateAt] using baseLane]
    simpa [rateLane] using congrArg (fun value => base lane + value) chunkLane
  · have baseLane := congrFun baseExact lane
    unfold absorbedBlockInput absorb
    simp only [dif_neg low]
    simpa [stateAt] using baseLane

theorem owner_initial_state_exact
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) :
    stateAt trace 0 = initState DOM_OWNER 8 := by
  have exact := retained_initial_state_exact_of_semantic_rows_vanish
    fields trace vanish 0
  simpa [retainedInitialRow, retainedInitialDomain, retainedInitialLength,
    DOM_OWNER] using exact

theorem input_note_initial_state_exact
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) :
    stateAt trace 16 = initState DOM_NOTE 18 := by
  have exact := retained_initial_state_exact_of_semantic_rows_vanish
    fields trace vanish 1
  simpa [retainedInitialRow, retainedInitialDomain, retainedInitialLength,
    DOM_NOTE] using exact

theorem nullifier_initial_state_exact
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) :
    stateAt trace 704 = initState DOM_NULLIFIER 16 := by
  have exact := retained_initial_state_exact_of_semantic_rows_vanish
    fields trace vanish 2
  simpa [retainedInitialRow, retainedInitialDomain, retainedInitialLength,
    DOM_NULLIFIER] using exact

theorem output_note_initial_state_exact
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) :
    stateAt trace 736 = initState DOM_NOTE 18 := by
  have exact := retained_initial_state_exact_of_semantic_rows_vanish
    fields trace vanish 3
  simpa [retainedInitialRow, retainedInitialDomain, retainedInitialLength,
    DOM_NOTE] using exact

theorem absorbed_owner_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 0 =
      absorb (initState DOM_OWNER 8)
        (openedColumnsFromTrace
          (extractedPhysicalTrace extraction) fee).k_nu := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact owner_initial_state_exact fields _ semanticVanish
  · intro limb
    have exact := owner_key_absorption_exact extraction taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

theorem absorbed_input_note_first_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 1 =
      absorb (initState DOM_NOTE 18)
        (openedColumnsFromTrace
          (extractedPhysicalTrace extraction) fee).pk_in := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact input_note_initial_state_exact fields _ semanticVanish
  · intro limb
    have exact := input_note_owner_absorption_exact extraction taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

def retainedStateProducerBlock : Fin 5 → PoseidonBlock := ![1, 2, 44, 46, 47]
def retainedStateConsumerBlock : Fin 5 → PoseidonBlock := ![2, 3, 45, 47, 48]

theorem retained_continuation_block_base_exact
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
    stateAt (extractedPhysicalTrace extraction)
        ⟨16 * (retainedStateConsumerBlock which).val, by omega⟩ =
      blockFinalState (extractedPhysicalTrace extraction)
        (retainedStateProducerBlock which) := by
  have continuation := retained_hash_state_continuations_exact
    extraction taggedEqual which
  fin_cases which <;>
    simpa [retainedStateProducerBlock, retainedStateConsumerBlock,
      retainedStateProducerRow, retainedStateConsumerRow,
      blockFinalState, stateAt] using continuation.symm

theorem absorbed_input_note_second_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 2 =
      absorb (blockFinalState (extractedPhysicalTrace extraction) 1)
        (noteChunk1
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).rin.value
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).a_in
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).r_in) := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact retained_continuation_block_base_exact extraction taggedEqual 0
  · intro limb
    have exact := input_note_chunk1_absorption_exact extraction taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

theorem absorbed_input_note_third_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 3 =
      absorb (blockFinalState (extractedPhysicalTrace extraction) 2)
        (noteChunk2
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).r_in) := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact retained_continuation_block_base_exact extraction taggedEqual 1
  · intro limb
    have exact := input_note_chunk2_absorption_exact extraction fields
      semanticVanish taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

theorem absorbed_nullifier_first_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 44 =
      absorb (initState DOM_NULLIFIER 16)
        (openedColumnsFromTrace
          (extractedPhysicalTrace extraction) fee).k_nu := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact nullifier_initial_state_exact fields _ semanticVanish
  · intro limb
    have exact := nullifier_key_absorption_exact extraction taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

theorem absorbed_nullifier_second_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 45 =
      absorb (blockFinalState (extractedPhysicalTrace extraction) 44)
        (openedColumnsFromTrace
          (extractedPhysicalTrace extraction) fee).r_in := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact retained_continuation_block_base_exact extraction taggedEqual 2
  · intro limb
    have exact := nullifier_salt_absorption_exact extraction taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

theorem absorbed_output_note_first_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 46 =
      absorb (initState DOM_NOTE 18)
        (openedColumnsFromTrace
          (extractedPhysicalTrace extraction) fee).pk_out := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact output_note_initial_state_exact fields _ semanticVanish
  · intro limb
    have exact := output_note_owner_absorption_exact extraction taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

theorem absorbed_output_note_second_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 47 =
      absorb (blockFinalState (extractedPhysicalTrace extraction) 46)
        (noteChunk1
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).rout.value
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).a
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).r_out) := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact retained_continuation_block_base_exact extraction taggedEqual 3
  · intro limb
    have exact := output_note_chunk1_absorption_exact extraction taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

theorem absorbed_output_note_third_block_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction)) :
    absorbedBlockInput (extractedPhysicalTrace extraction) 48 =
      absorb (blockFinalState (extractedPhysicalTrace extraction) 47)
        (noteChunk2
          (openedColumnsFromTrace
            (extractedPhysicalTrace extraction) fee).r_out) := by
  apply absorbedBlockInput_eq_absorb_of_rows
  · exact retained_continuation_block_base_exact extraction taggedEqual 4
  · intro limb
    have exact := output_note_chunk2_absorption_exact extraction fields
      semanticVanish taggedEqual limb
    simpa [openedColumnsFromTrace, completeOpenedColumns, decodedOpenedCore]
      using exact

/-! ## Complete typed hash and Merkle residual object -/

def extractedHashMerkleResidualsOfTrace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (rc : RoundConstants)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (poseidonVanish : DeployedPoseidonRowsVanish rc
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (binary : PathBitsAreBinary
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction))) :
    ExtractedHashMerkleResiduals rc
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee) := by
  let trace := extractedPhysicalTrace extraction
  let opened := openedColumnsFromTrace trace fee
  have ownerGate := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 0
  have ownerInput := absorbed_owner_block_exact extraction fee fields
    semanticVanish taggedEqual
  rw [ownerInput] at ownerGate
  have inputGate1 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 1
  have input1 := absorbed_input_note_first_block_exact extraction fee fields
    semanticVanish taggedEqual
  rw [input1] at inputGate1
  have inputGate2 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 2
  have input2 := absorbed_input_note_second_block_exact extraction fee taggedEqual
  rw [input2] at inputGate2
  have inputGate3 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 3
  have input3 := absorbed_input_note_third_block_exact extraction fee fields
    semanticVanish taggedEqual
  rw [input3] at inputGate3
  have nullGate1 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 44
  have null1 := absorbed_nullifier_first_block_exact extraction fee fields
    semanticVanish taggedEqual
  rw [null1] at nullGate1
  have nullGate2 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 45
  have null2 := absorbed_nullifier_second_block_exact extraction fee taggedEqual
  rw [null2] at nullGate2
  have outputGate1 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 46
  have output1 := absorbed_output_note_first_block_exact extraction fee fields
    semanticVanish taggedEqual
  rw [output1] at outputGate1
  have outputGate2 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 47
  have output2 := absorbed_output_note_second_block_exact extraction fee taggedEqual
  rw [output2] at outputGate2
  have outputGate3 := twoRoundPermutationRowsOfVanish rc trace poseidonVanish 48
  have output3 := absorbed_output_note_third_block_exact extraction fee fields
    semanticVanish taggedEqual
  rw [output3] at outputGate3
  refine {
    ownerState := blockFinalState trace 0
    ownerGate := ownerGate
    ownerDigestResidual := ?_
    nullState1 := blockFinalState trace 44
    nullState2 := blockFinalState trace 45
    nullGate1 := nullGate1
    nullGate2 := nullGate2
    nullDigestResidual := ?_
    inputNoteState1 := blockFinalState trace 1
    inputNoteState2 := blockFinalState trace 2
    inputNoteState3 := blockFinalState trace 3
    inputNoteGate1 := inputGate1
    inputNoteGate2 := inputGate2
    inputNoteGate3 := inputGate3
    inputNoteDigestResidual := ?_
    outputNoteState1 := blockFinalState trace 46
    outputNoteState2 := blockFinalState trace 47
    outputNoteState3 := blockFinalState trace 48
    outputNoteGate1 := outputGate1
    outputNoteGate2 := outputGate2
    outputNoteGate3 := outputGate3
    outputNoteDigestResidual := ?_
    inputPath := inputMerklePathOfTrace rc extraction fee fields
      semanticVanish poseidonVanish taggedEqual binary
    outputPath := outputMerklePathOfTrace rc extraction fee fields
      semanticVanish poseidonVanish taggedEqual binary
  }
  · exact sub_self _
  · exact sub_self _
  · exact sub_self _
  · exact sub_self _

#print axioms low_absorption_padding_zero_of_semantic_rows_vanish
#print axioms owner_key_absorption_exact
#print axioms input_note_owner_absorption_exact
#print axioms input_note_chunk1_absorption_exact
#print axioms input_note_chunk2_absorption_exact
#print axioms nullifier_key_absorption_exact
#print axioms nullifier_salt_absorption_exact
#print axioms output_note_owner_absorption_exact
#print axioms output_note_chunk1_absorption_exact
#print axioms output_note_chunk2_absorption_exact
#print axioms absorbedBlockInput_eq_absorb_of_rows
#print axioms absorbed_owner_block_exact
#print axioms absorbed_input_note_first_block_exact
#print axioms retained_continuation_block_base_exact
#print axioms absorbed_input_note_second_block_exact
#print axioms absorbed_input_note_third_block_exact
#print axioms absorbed_nullifier_first_block_exact
#print axioms absorbed_nullifier_second_block_exact
#print axioms absorbed_output_note_first_block_exact
#print axioms absorbed_output_note_second_block_exact
#print axioms absorbed_output_note_third_block_exact
#print axioms extractedHashMerkleResidualsOfTrace

#print axioms initialResidual_at_retainedInitialRow
#print axioms retained_initial_state_exact_of_semantic_rows_vanish
#print axioms input_owner_digest_staging_exact

end AspisPool.V7HashBlocksFromTrace
