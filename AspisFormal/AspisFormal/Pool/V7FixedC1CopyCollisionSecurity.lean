import AspisFormal.Pool.V7FixedWidth29TupleList
import AspisFormal.Pool.V7DeployedCopyLogUpCollisionBounds
import AspisFormal.Pool.V7DeployedCopyEvaluatorBalanceBridge
import AspisFormal.V5SequentialTerminalChallengeBound

/-!
# Causal copy-collision accounting over the fixed C1 family

The C1 commitment precedes `lambda` and `chi`, while a coherent decoded trace
may be selected only later.  The local 2,928-root lambda and 731-root chi
bounds therefore must be unioned over one C1 candidate family fixed before
either challenge.  `V7FixedWidth29TupleList` proves that family has at most
100 members.

This module packages varying deployed copy sources behind one ordinary type,
forms the literal family unions, and proves the two-stage ideal subtotal

`100 * (2928 + 731) / |QM31| = 365900 / |QM31|`.

The final section constructs the source assigned to each fixed C1 tuple and
proves that every accepted extraction's concrete 183-link collision event is
contained in that pre-challenge family union.  No postselected source is
hidden in the probability bound.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisPool.V7FixedC1CopyCollisionSecurity

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyLogUpCollisionBounds
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

/-- Existentially package the required scalar endpoint functions together
with the complete deployed 183-link source. -/
structure PackedDeployedCopySource where
  producerValue : RequiredScalarLink → QM31Exact
  consumerValue : RequiredScalarLink → QM31Exact
  registry : DeployedCopyRegistryProjection QM31Exact producerValue
    consumerValue

/-! ## The canonical source of one fixed C1 tuple -/

/-- The first 1,024 coefficient rows and sixteen semantic columns read from
one fixed decoded C1 tuple.  This is the same table consumed by the deployed
copy registry once that tuple is selected. -/
def selectedTraceOfC1Tuple
    (components : C1InitialMessages) :
    Fin 1024 → Fin 16 → QM31Exact :=
  fun row column => components (semanticColumnIndex column) row

/-- The complete 183-link source determined by one fixed decoded C1 tuple. -/
noncomputable def packedCopySourceOfC1Tuple
    (components : C1InitialMessages) : PackedDeployedCopySource where
  producerValue := requiredProducerTraceCell
    (selectedTraceOfC1Tuple components)
  consumerValue := requiredConsumerTraceCell
    (selectedTraceOfC1Tuple components)
  registry := deployedCopyRegistryProjectionOfTrace
    (selectedTraceOfC1Tuple components)

/-- The literal source family fixed by C1 before `lambda` and `chi`. -/
noncomputable def fixedC1CopySourceFamily
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) :
    FixedC1TupleCandidate decoder lanes → PackedDeployedCopySource :=
  fun candidate => packedCopySourceOfC1Tuple candidate.1

/-- Collision sets factored through the selected trace.  This small wrapper
lets the causal bridge transport only equality of the 1,024-by-16 table,
without asking elaboration to normalize equality of a dependent registry
record containing topology proofs. -/
noncomputable def traceLambdaBad
    (trace : Fin 1024 → Fin 16 → QM31Exact) : Finset QM31Exact :=
  copyLambdaCollisionSet (deployedCopyRegistryProjectionOfTrace trace)

noncomputable def traceChiBad
    (trace : Fin 1024 → Fin 16 → QM31Exact) (lambda : QM31Exact) :
    Finset QM31Exact :=
  copyChiPoleSet (deployedCopyRegistryProjectionOfTrace trace) lambda ∪
    copyChiNonPoleCollisionSet
      (deployedCopyRegistryProjectionOfTrace trace) lambda

/-- Projecting an accepted width-29 tuple to C1 yields definitionally the
same selected trace that the deployed 183-link registry reads. -/
@[simp] theorem selectedTraceOfC1Tuple_project_extraction
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) :
    selectedTraceOfC1Tuple
        (projectWidth29ToC1 extraction.components) =
      extractedSelectedTrace extraction := by
  rfl

/-- Consequently the fixed candidate's packed source is exactly the
concrete deployed source of the accepted extraction, including all 183
producer and consumer tuples. -/
noncomputable def packedCopySourceOfExtraction
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) : PackedDeployedCopySource where
  producerValue := requiredProducerCell extraction
  consumerValue := requiredConsumerCell extraction
  registry := concreteDeployedCopyRegistryProjection extraction

theorem packedCopySourceOfC1Tuple_project_extraction
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) :
    packedCopySourceOfC1Tuple
        (projectWidth29ToC1 extraction.components) =
      packedCopySourceOfExtraction extraction := by
  rfl

noncomputable def packedLambdaBad
    (source : PackedDeployedCopySource) : Finset QM31Exact :=
  copyLambdaCollisionSet source.registry

noncomputable def packedChiBad
    (source : PackedDeployedCopySource) (lambda : QM31Exact) :
    Finset QM31Exact :=
  copyChiPoleSet source.registry lambda ∪
    copyChiNonPoleCollisionSet source.registry lambda

theorem packedLambdaBad_fixedC1CopySourceFamily_eq_trace
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords)
    (candidate : FixedC1TupleCandidate decoder lanes) :
    packedLambdaBad (fixedC1CopySourceFamily decoder lanes candidate) =
      traceLambdaBad (selectedTraceOfC1Tuple candidate.1) := by
  rfl

theorem packedChiBad_fixedC1CopySourceFamily_eq_trace
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords)
    (candidate : FixedC1TupleCandidate decoder lanes)
    (lambda : QM31Exact) :
    packedChiBad (fixedC1CopySourceFamily decoder lanes candidate) lambda =
      traceChiBad (selectedTraceOfC1Tuple candidate.1) lambda := by
  rfl

theorem concreteLambdaBad_eq_trace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) :
    copyLambdaCollisionSet
        (concreteDeployedCopyRegistryProjection extraction) =
      traceLambdaBad (extractedSelectedTrace extraction) := by
  rfl

theorem concreteChiBad_eq_trace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) (lambda : QM31Exact) :
    copyChiPoleSet
          (concreteDeployedCopyRegistryProjection extraction) lambda ∪
        copyChiNonPoleCollisionSet
          (concreteDeployedCopyRegistryProjection extraction) lambda =
      traceChiBad (extractedSelectedTrace extraction) lambda := by
  rfl

theorem packedLambdaBad_card_le_2928
    (source : PackedDeployedCopySource) :
    (packedLambdaBad source).card ≤ 2928 := by
  exact copyLambdaCollisionSet_card_le_2928 source.registry

theorem packedChiBad_card_le_731
    (source : PackedDeployedCopySource) (lambda : QM31Exact) :
    (packedChiBad source lambda).card ≤ 731 := by
  unfold packedChiBad
  calc
    (copyChiPoleSet source.registry lambda ∪
        copyChiNonPoleCollisionSet source.registry lambda).card ≤
        (copyChiPoleSet source.registry lambda).card +
          (copyChiNonPoleCollisionSet source.registry lambda).card :=
      Finset.card_union_le _ _
    _ ≤ 366 + 365 := Nat.add_le_add
      (copyChiPoleSet_card_le_366 source.registry lambda)
      (copyChiNonPoleCollisionSet_card_le_365 source.registry lambda)
    _ = 731 := by norm_num

/-- The lambda bad set unioned over one fixed finite source family. -/
noncomputable def familyLambdaBad
    {Candidate : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource) : Finset QM31Exact := by
  classical
  exact Finset.univ.biUnion fun candidate => packedLambdaBad (source candidate)

/-- The conditional chi bad set unioned over the same fixed family. -/
noncomputable def familyChiBad
    {Candidate : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource)
    (lambda : QM31Exact) : Finset QM31Exact := by
  classical
  exact Finset.univ.biUnion fun candidate =>
    packedChiBad (source candidate) lambda

/-! ## Accepted-source inclusion in the fixed pre-challenge family -/

/- If the concrete accepted registry collides at `lambda`, that challenge is
already covered by the union over the C1 family fixed before `lambda`. -/
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
theorem concrete_lambda_collision_mem_fixedC1_family
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (c1Member : projectWidth29ToC1 extraction.components ∈
      fixedC1TupleList decoder (c1Received words))
    {lambda : QM31Exact}
    (collision : lambda ∈ copyLambdaCollisionSet
      (concreteDeployedCopyRegistryProjection extraction)) :
    lambda ∈ familyLambdaBad
      (fixedC1CopySourceFamily decoder (c1Received words)) := by
  classical
  let candidate : FixedC1TupleCandidate decoder (c1Received words) :=
    ⟨projectWidth29ToC1 extraction.components, c1Member⟩
  unfold familyLambdaBad
  rw [Finset.mem_biUnion]
  refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
  have traceEq : selectedTraceOfC1Tuple candidate.1 =
      extractedSelectedTrace extraction := by
    simpa only [candidate] using
      selectedTraceOfC1Tuple_project_extraction extraction
  rw [packedLambdaBad_fixedC1CopySourceFamily_eq_trace]
  rw [traceEq]
  rw [← concreteLambdaBad_eq_trace extraction]
  simp only [copyLambdaCollisionSet, Finset.mem_filter, Finset.mem_univ,
    true_and]
    at collision ⊢
  exact collision

/- The same fixed-family inclusion for either a pole or a non-pole `chi`
collision after the sampled `lambda`. -/
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
theorem concrete_chi_collision_mem_fixedC1_family
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (c1Member : projectWidth29ToC1 extraction.components ∈
      fixedC1TupleList decoder (c1Received words))
    (lambda : QM31Exact) {chi : QM31Exact}
    (collision : chi ∈ copyChiPoleSet
        (concreteDeployedCopyRegistryProjection extraction) lambda ∪
      copyChiNonPoleCollisionSet
        (concreteDeployedCopyRegistryProjection extraction) lambda) :
    chi ∈ familyChiBad
      (fixedC1CopySourceFamily decoder (c1Received words)) lambda := by
  classical
  let candidate : FixedC1TupleCandidate decoder (c1Received words) :=
    ⟨projectWidth29ToC1 extraction.components, c1Member⟩
  unfold familyChiBad
  rw [Finset.mem_biUnion]
  refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
  have traceEq : selectedTraceOfC1Tuple candidate.1 =
      extractedSelectedTrace extraction := by
    simpa only [candidate] using
      selectedTraceOfC1Tuple_project_extraction extraction
  rw [packedChiBad_fixedC1CopySourceFamily_eq_trace]
  rw [traceEq]
  rw [← concreteChiBad_eq_trace extraction lambda]
  simp only [Finset.mem_union, copyChiPoleSet, copyChiNonPoleCollisionSet,
    Finset.mem_filter, Finset.mem_univ, true_and] at collision ⊢
  exact collision

theorem familyLambdaBad_card_le
    {Candidate : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource) :
    (familyLambdaBad source).card ≤ 2928 * Fintype.card Candidate := by
  classical
  unfold familyLambdaBad
  calc
    (Finset.univ.biUnion fun candidate =>
        packedLambdaBad (source candidate)).card ≤
        (Finset.univ : Finset Candidate).card * 2928 :=
      Finset.card_biUnion_le_card_mul _ _ 2928
        (fun candidate _ => packedLambdaBad_card_le_2928 (source candidate))
    _ = 2928 * Fintype.card Candidate := by simp [Nat.mul_comm]

theorem familyChiBad_card_le
    {Candidate : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource) (lambda : QM31Exact) :
    (familyChiBad source lambda).card ≤ 731 * Fintype.card Candidate := by
  classical
  unfold familyChiBad
  calc
    (Finset.univ.biUnion fun candidate =>
        packedChiBad (source candidate) lambda).card ≤
        (Finset.univ : Finset Candidate).card * 731 :=
      Finset.card_biUnion_le_card_mul _ _ 731
        (fun candidate _ => packedChiBad_card_le_731
          (source candidate) lambda)
    _ = 731 * Fintype.card Candidate := by simp [Nat.mul_comm]

/-- Exact two-stage ideal mass.  The chi set may depend on lambda, but the
source family itself is fixed before lambda. -/
noncomputable def fixedFamilyCopyCollisionProbability
    {Candidate : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource) : Rat :=
  (familyLambdaBad source).card / Fintype.card QM31Exact +
    ((Finset.univ.filter fun lambda => lambda ∉ familyLambdaBad source).sum
      (fun lambda =>
        ((familyChiBad source lambda).card : Rat) /
          Fintype.card QM31Exact)) /
      Fintype.card QM31Exact

set_option maxHeartbeats 1000000 in
theorem fixedFamilyCopyCollisionProbability_le_card_mul
    {Candidate : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource) :
    fixedFamilyCopyCollisionProbability source ≤
      (3659 * Fintype.card Candidate : Rat) /
        Fintype.card QM31Exact := by
  have fieldPositive : (0 : Rat) < Fintype.card QM31Exact := by
    exact_mod_cast Fintype.card_pos
  have lambdaFraction :
      ((familyLambdaBad source).card : Rat) / Fintype.card QM31Exact ≤
        (2928 * Fintype.card Candidate : Rat) /
          Fintype.card QM31Exact := by
    rw [div_le_div_iff_of_pos_right fieldPositive]
    exact_mod_cast familyLambdaBad_card_le source
  have chiAverage :
      ((Finset.univ.filter fun lambda =>
          lambda ∉ familyLambdaBad source).sum
        (fun lambda =>
          ((familyChiBad source lambda).card : Rat) /
            Fintype.card QM31Exact)) /
        Fintype.card QM31Exact ≤
      (731 * Fintype.card Candidate : Rat) /
        Fintype.card QM31Exact := by
    apply AspisV5SequentialTerminalChallengeBound.finiteSubsetAverage_le
    · apply div_nonneg
      · exact_mod_cast Nat.zero_le (731 * Fintype.card Candidate)
      · exact_mod_cast Nat.zero_le (Fintype.card QM31Exact)
    · intro lambda _
      rw [div_le_div_iff_of_pos_right fieldPositive]
      exact_mod_cast familyChiBad_card_le source lambda
  unfold fixedFamilyCopyCollisionProbability
  calc
    _ ≤ (2928 * Fintype.card Candidate : Rat) /
          Fintype.card QM31Exact +
        (731 * Fintype.card Candidate : Rat) /
          Fintype.card QM31Exact :=
      add_le_add lambdaFraction chiAverage
    _ = (3659 * Fintype.card Candidate : Rat) /
        Fintype.card QM31Exact := by ring

theorem fixedC1CopyCollisionProbability_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords)
    (source : FixedC1TupleCandidate decoder lanes →
      PackedDeployedCopySource) :
    fixedFamilyCopyCollisionProbability source ≤
      (365900 : Rat) / Fintype.card QM31Exact := by
  calc
    fixedFamilyCopyCollisionProbability source ≤
        (3659 * Fintype.card (FixedC1TupleCandidate decoder lanes) : Rat) /
          Fintype.card QM31Exact :=
      fixedFamilyCopyCollisionProbability_le_card_mul source
    _ ≤ (3659 * 100 : Rat) / Fintype.card QM31Exact := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.mul_le_mul_left 3659
          (fixedC1TupleCandidate_card_le_100 decoder lanes)
      · positivity
    _ = (365900 : Rat) / Fintype.card QM31Exact := by ring

theorem fixed_c1_copy_collision_subtotal_le_two_pow_neg_105 :
    (365900 : Real) / Fintype.card QM31Exact ≤
      (1 : Real) / 2 ^ 105 := by
  rw [qm31Exact_card]
  norm_num [P]

#print axioms packedLambdaBad_card_le_2928
#print axioms packedChiBad_card_le_731
#print axioms selectedTraceOfC1Tuple_project_extraction
#print axioms packedCopySourceOfC1Tuple_project_extraction
#print axioms concrete_lambda_collision_mem_fixedC1_family
#print axioms concrete_chi_collision_mem_fixedC1_family
#print axioms familyLambdaBad_card_le
#print axioms familyChiBad_card_le
#print axioms fixedFamilyCopyCollisionProbability_le_card_mul
#print axioms fixedC1CopyCollisionProbability_le
#print axioms fixed_c1_copy_collision_subtotal_le_two_pow_neg_105

end AspisPool.V7FixedC1CopyCollisionSecurity
