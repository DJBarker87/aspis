import AspisFormal.Pool.V7ExtractedCopyAliasBridge

/-!
# Deployed Tag-73 Copy LogUp closure for the 43 required scalar links

This leaf spells out the part of the frozen atomic-v3 copy registry needed by
`V7ExtractedCopyAliasBridge`.  The registry has 183 links:

* 23 retained links, with the three required scalar links at tags 21--23;
* at each of twenty path levels, two current links, two two-item selection
  multisets, and two scalar bit-alias links; and
* the scalar path tags are exactly `28 + 6 * level` and
  `29 + 6 * level`.

The selection pairs are the only repeated tags.  In particular, every one of
the 43 tags used below occurs at exactly one producer and one consumer.

The LogUp conclusion is necessarily collision-explicit.  A zero rational sum
at one sampled `chi` does not deterministically imply equality of compressed
multisets, and equality after one sampled `lambda` does not deterministically
imply equality of tagged tuples.  `CopyChiCollision` and
`CopyTupleCompressionCollision` name precisely those two failure branches.
Outside them, the exact scalar tuple shape `tag + lambda * C1[row,column]`
isolates all 43 source-cell equations.  No generic copy-lane-zero or blanket
faithfulness statement appears in this file.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7DeployedCopyLogUpAliasClosure

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7OpenedColumnsFromTrace
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

/-! ## Exact frozen registry tag schedule -/

/-- The 183 deployed atomic-v3 copy links, grouped exactly as constructed by
`build_atomic_state_only_registry_v3`. -/
inductive DeployedCopyLink where
  | retained (index : Fin 23)
  | pathCurrent (level : Fin 20) (output : Bool)
  | pathSelect (level : Fin 20) (output : Bool) (item : Fin 2)
  | pathAlias (level : Fin 20) (hop : Fin 2)
  deriving DecidableEq, Fintype

theorem deployedCopyLink_card : Fintype.card DeployedCopyLink = 183 := by
  decide

/-- Literal tag allocation order in
`atomic_state_only_registry.rs::build_atomic_state_only_registry_v3`. -/
def deployedCopyTag : DeployedCopyLink → Nat
  | .retained index => 1 + index.val
  | .pathCurrent level false => 24 + 6 * level.val
  | .pathCurrent level true => 26 + 6 * level.val
  | .pathSelect level false _ => 25 + 6 * level.val
  | .pathSelect level true _ => 27 + 6 * level.val
  | .pathAlias level hop => 28 + 6 * level.val + hop.val

/-- Exactly the three retained scalar links and forty path-bit links consumed
by `RequiredCopySourceEquations`. -/
inductive RequiredScalarLink where
  | inputRangeToNote
  | outputRangeToNote
  | outputNoteToBalance
  | path (level : Fin 20) (hop : Fin 2)
  deriving DecidableEq, Fintype

theorem requiredScalarLink_card : Fintype.card RequiredScalarLink = 43 := by
  decide

def requiredRegistryLink : RequiredScalarLink → DeployedCopyLink
  | .inputRangeToNote => .retained ⟨20, by omega⟩
  | .outputRangeToNote => .retained ⟨21, by omega⟩
  | .outputNoteToBalance => .retained ⟨22, by omega⟩
  | .path level hop => .pathAlias level hop

@[simp] theorem requiredRegistryLink_tag_inputRangeToNote :
    deployedCopyTag (requiredRegistryLink .inputRangeToNote) = 21 := rfl

@[simp] theorem requiredRegistryLink_tag_outputRangeToNote :
    deployedCopyTag (requiredRegistryLink .outputRangeToNote) = 22 := rfl

@[simp] theorem requiredRegistryLink_tag_outputNoteToBalance :
    deployedCopyTag (requiredRegistryLink .outputNoteToBalance) = 23 := rfl

@[simp] theorem requiredRegistryLink_tag_path
    (level : Fin 20) (hop : Fin 2) :
    deployedCopyTag (requiredRegistryLink (.path level hop)) =
      28 + 6 * level.val + hop.val := rfl

/-- Every required tag is unique in the full 183-link registry.  The proof
also checks that neither member of a repeated path-selection tag can be
confused with a required scalar tag. -/
theorem deployedCopyTag_unique_at_required
    (required : RequiredScalarLink) (link : DeployedCopyLink)
    (tagEqual : deployedCopyTag link =
      deployedCopyTag (requiredRegistryLink required)) :
    link = requiredRegistryLink required := by
  cases required with
  | inputRangeToNote =>
      cases link with
      | retained index =>
          simp [deployedCopyTag, requiredRegistryLink] at tagEqual
          have indexVal : index.val = 20 := by omega
          have indexEqual : index = (20 : Fin 23) := Fin.ext indexVal
          subst index
          rfl
      | pathCurrent level output =>
          cases output <;>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
      | pathSelect level output item =>
          cases output <;>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
      | pathAlias level hop =>
          simp [deployedCopyTag, requiredRegistryLink] at tagEqual
          omega
  | outputRangeToNote =>
      cases link with
      | retained index =>
          simp [deployedCopyTag, requiredRegistryLink] at tagEqual
          have indexVal : index.val = 21 := by omega
          have indexEqual : index = (21 : Fin 23) := Fin.ext indexVal
          subst index
          rfl
      | pathCurrent level output =>
          cases output <;>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
      | pathSelect level output item =>
          cases output <;>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
      | pathAlias level hop =>
          simp [deployedCopyTag, requiredRegistryLink] at tagEqual
          omega
  | outputNoteToBalance =>
      cases link with
      | retained index =>
          simp [deployedCopyTag, requiredRegistryLink] at tagEqual
          have indexVal : index.val = 22 := by omega
          have indexEqual : index = (22 : Fin 23) := Fin.ext indexVal
          subst index
          rfl
      | pathCurrent level output =>
          cases output <;>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
      | pathSelect level output item =>
          cases output <;>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
      | pathAlias level hop =>
          simp [deployedCopyTag, requiredRegistryLink] at tagEqual
          omega
  | path requiredLevel requiredHop =>
      fin_cases requiredHop
      · cases link with
        | retained index =>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual
            omega
        | pathCurrent level output =>
            cases output <;> simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
        | pathSelect level output item =>
            cases output <;> simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
        | pathAlias level hop =>
            fin_cases hop
            · simp only [deployedCopyTag, requiredRegistryLink] at tagEqual ⊢
              congr 2
              apply Fin.ext
              omega
            · simp [deployedCopyTag, requiredRegistryLink] at tagEqual
              omega
      · cases link with
        | retained index =>
            simp [deployedCopyTag, requiredRegistryLink] at tagEqual
            omega
        | pathCurrent level output =>
            cases output <;> simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
        | pathSelect level output item =>
            cases output <;> simp [deployedCopyTag, requiredRegistryLink] at tagEqual <;> omega
        | pathAlias level hop =>
            fin_cases hop
            · simp [deployedCopyTag, requiredRegistryLink] at tagEqual
              omega
            · simp only [deployedCopyTag, requiredRegistryLink] at tagEqual ⊢
              congr 2
              apply Fin.ext
              omega

/-! ## Exact scalar source coordinates -/

def requiredProducerCell
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) : RequiredScalarLink → QM31Exact
  | .inputRangeToNote => selectedC1Cell extraction 864 11
  | .outputRangeToNote => selectedC1Cell extraction 866 11
  | .outputNoteToBalance => selectedC1Cell extraction 799 0
  | .path level hop =>
      if hop.val = 0 then
        selectedC1Cell extraction (inputPathRow level) 0
      else
        selectedC1Cell extraction (outputPathRow level) 0

def requiredConsumerCell
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) : RequiredScalarLink → QM31Exact
  | .inputRangeToNote => selectedC1Cell extraction 795 0
  | .outputRangeToNote => selectedC1Cell extraction 799 0
  | .outputNoteToBalance => selectedC1Cell extraction 864 12
  | .path level hop =>
      if hop.val = 0 then
        selectedC1Cell extraction (outputPathRow level) 0
      else
        selectedC1Cell extraction (siblingPathRow level) 0

/-! ## Tagged tuples and the exact source projection -/

structure TaggedCopyTuple (K : Type*) where
  tag : Nat
  limbs : Fin 16 → K

def scalarTaggedTuple {K : Type*} [Zero K]
    (tag : Nat) (value : K) : TaggedCopyTuple K where
  tag := tag
  limbs := fun limb => if limb.val = 0 then value else 0

theorem scalarTaggedTuple_value_injective
    {K : Type*} [Zero K] {tag : Nat} {left right : K}
    (equal : scalarTaggedTuple tag left = scalarTaggedTuple tag right) :
    left = right := by
  have limbEqual := congrArg (fun tuple : TaggedCopyTuple K => tuple.limbs 0) equal
  simpa [scalarTaggedTuple] using limbEqual

/-- Exact source-facing projection of the deployed registry.  Its two
`required*` fields are topology equations, not copy equalities: they say that
the compiled endpoints at the 43 frozen indices read the listed C1 cells and
use the literal scalar tuple pattern.  All other 140 links remain present and
may carry arbitrary tuple values. -/
structure DeployedCopyRegistryProjection
    (K : Type*) [Zero K]
    (producerValue consumerValue : RequiredScalarLink → K) where
  producer : DeployedCopyLink → TaggedCopyTuple K
  consumer : DeployedCopyLink → TaggedCopyTuple K
  producerTag : ∀ link, (producer link).tag = deployedCopyTag link
  consumerTag : ∀ link, (consumer link).tag = deployedCopyTag link
  requiredProducer : ∀ required,
    producer (requiredRegistryLink required) =
      scalarTaggedTuple (deployedCopyTag (requiredRegistryLink required))
        (producerValue required)
  requiredConsumer : ∀ required,
    consumer (requiredRegistryLink required) =
      scalarTaggedTuple (deployedCopyTag (requiredRegistryLink required))
        (consumerValue required)

/-! ## Literal source compression and the two unavoidable collisions -/

/-- `logup.rs::compress_tagged_tuple`: `tag + Σ lambda^(i+1) * limb[i]`. -/
noncomputable def compressTaggedTuple
    {K : Type*} [Field K] (lambda : K) (tuple : TaggedCopyTuple K) : K :=
  (tuple.tag : K) + ∑ limb : Fin 16,
    lambda ^ (limb.val + 1) * tuple.limbs limb

noncomputable def producerTaggedMultiset
    {K : Type*} [Zero K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue) :
    Multiset (TaggedCopyTuple K) :=
  (Finset.univ : Finset DeployedCopyLink).1.map source.producer

noncomputable def consumerTaggedMultiset
    {K : Type*} [Zero K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue) :
    Multiset (TaggedCopyTuple K) :=
  (Finset.univ : Finset DeployedCopyLink).1.map source.consumer

noncomputable def producerCompressedMultiset
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) : Multiset K :=
  (Finset.univ : Finset DeployedCopyLink).1.map
    (fun link => compressTaggedTuple lambda (source.producer link))

noncomputable def consumerCompressedMultiset
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) : Multiset K :=
  (Finset.univ : Finset DeployedCopyLink).1.map
    (fun link => compressTaggedTuple lambda (source.consumer link))

/-- The exact global rational identity checked by Copy LogUp after local
helper equations and the zero-sum helper boundary are combined. -/
noncomputable def copyRationalBalance
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) : K :=
  (∑ link : DeployedCopyLink,
      (chi - compressTaggedTuple lambda (source.producer link))⁻¹) -
    ∑ link : DeployedCopyLink,
      (chi - compressTaggedTuple lambda (source.consumer link))⁻¹

/-- A sampled-`chi` rational-identity collision: the checked rational sum is
zero even though the two compressed 183-element multisets differ. -/
def CopyChiCollision
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) : Prop :=
  copyRationalBalance source lambda chi = 0 ∧
    producerCompressedMultiset source lambda ≠
      consumerCompressedMultiset source lambda

/-- A sampled-`lambda` tagged-tuple compression collision: the compressed
multisets agree but the underlying tagged 16-limb multisets differ. -/
def CopyTupleCompressionCollision
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) : Prop :=
  producerCompressedMultiset source lambda =
      consumerCompressedMultiset source lambda ∧
    producerTaggedMultiset source ≠ consumerTaggedMultiset source

theorem compressed_multisets_equal_outside_chi_collision
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K)
    (balance : copyRationalBalance source lambda chi = 0)
    (noCollision : ¬ CopyChiCollision source lambda chi) :
    producerCompressedMultiset source lambda =
      consumerCompressedMultiset source lambda := by
  by_contra different
  exact noCollision ⟨balance, different⟩

theorem tagged_multisets_equal_outside_compression_collision
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K)
    (compressedEqual : producerCompressedMultiset source lambda =
      consumerCompressedMultiset source lambda)
    (noCollision : ¬ CopyTupleCompressionCollision source lambda) :
    producerTaggedMultiset source = consumerTaggedMultiset source := by
  by_contra different
  exact noCollision ⟨compressedEqual, different⟩

/-! ## Unique-tag isolation of all 43 values -/

theorem required_value_equal_of_tagged_multisets_equal
    {K : Type*} [Zero K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (taggedEqual : producerTaggedMultiset source =
      consumerTaggedMultiset source)
    (required : RequiredScalarLink) :
    producerValue required = consumerValue required := by
  classical
  have producerMember : source.producer (requiredRegistryLink required) ∈
      producerTaggedMultiset source := by
    simp [producerTaggedMultiset]
  rw [taggedEqual] at producerMember
  simp only [consumerTaggedMultiset, Multiset.mem_map] at producerMember
  obtain ⟨link, linkMember, tupleEqual⟩ := producerMember
  have tagEqual : deployedCopyTag link =
      deployedCopyTag (requiredRegistryLink required) := by
    calc
      deployedCopyTag link = (source.consumer link).tag :=
        (source.consumerTag link).symm
      _ = (source.producer (requiredRegistryLink required)).tag := by
        exact congrArg TaggedCopyTuple.tag tupleEqual
      _ = deployedCopyTag (requiredRegistryLink required) :=
        source.producerTag (requiredRegistryLink required)
  have linkEqual := deployedCopyTag_unique_at_required required link tagEqual
  subst link
  rw [source.requiredProducer required, source.requiredConsumer required] at tupleEqual
  exact scalarTaggedTuple_value_injective tupleEqual.symm

/-- The exact Copy LogUp dichotomy for every required source value.  There is
no generic faithfulness premise: either one of the two named sampled
collisions occurred, or all 43 producer/consumer scalar cells agree. -/
theorem all_required_values_equal_or_copy_collision
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K)
    (balance : copyRationalBalance source lambda chi = 0) :
    CopyChiCollision source lambda chi ∨
      CopyTupleCompressionCollision source lambda ∨
      ∀ required, producerValue required = consumerValue required := by
  by_cases chiCollision : CopyChiCollision source lambda chi
  · exact Or.inl chiCollision
  · have compressedEqual :=
      compressed_multisets_equal_outside_chi_collision source lambda chi
        balance chiCollision
    by_cases lambdaCollision : CopyTupleCompressionCollision source lambda
    · exact Or.inr (Or.inl lambdaCollision)
    · have taggedEqual :=
        tagged_multisets_equal_outside_compression_collision source lambda
          compressedEqual lambdaCollision
      exact Or.inr (Or.inr fun required =>
        required_value_equal_of_tagged_multisets_equal source taggedEqual required)

theorem requiredCopySourceEquations_of_all_required_values_equal
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (allEqual : ∀ required,
      requiredProducerCell extraction required =
        requiredConsumerCell extraction required) :
    RequiredCopySourceEquations extraction where
  inputRangeToNote := allEqual .inputRangeToNote
  outputRangeToNote := allEqual .outputRangeToNote
  outputNoteToBalance := allEqual .outputNoteToBalance
  inputPathToOutput := by
    intro level
    simpa [requiredProducerCell, requiredConsumerCell] using
      allEqual (.path level 0)
  outputPathToSibling := by
    intro level
    simpa [requiredProducerCell, requiredConsumerCell] using
      allEqual (.path level 1)

/-- Final K1.5 source-cell closure: the deployed 183-link rational balance
gives exactly `RequiredCopySourceEquations`, outside the two explicit LogUp
challenge collisions. -/
theorem requiredCopySourceEquations_of_deployed_copy_logup
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : DeployedCopyRegistryProjection QM31Exact
      (requiredProducerCell extraction) (requiredConsumerCell extraction))
    (lambda chi : QM31Exact)
    (balance : copyRationalBalance source lambda chi = 0)
    (noChiCollision : ¬ CopyChiCollision source lambda chi)
    (noCompressionCollision :
      ¬ CopyTupleCompressionCollision source lambda) :
    RequiredCopySourceEquations extraction := by
  have compressedEqual :=
    compressed_multisets_equal_outside_chi_collision source lambda chi
      balance noChiCollision
  have taggedEqual :=
    tagged_multisets_equal_outside_compression_collision source lambda
      compressedEqual noCompressionCollision
  exact requiredCopySourceEquations_of_all_required_values_equal extraction
    (fun required =>
      required_value_equal_of_tagged_multisets_equal source taggedEqual required)

/-- Direct downstream form consumed by the pool plumbing. -/
theorem requiredTraceAliases_of_deployed_copy_logup
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : DeployedCopyRegistryProjection QM31Exact
      (requiredProducerCell extraction) (requiredConsumerCell extraction))
    (lambda chi : QM31Exact)
    (balance : copyRationalBalance source lambda chi = 0)
    (noChiCollision : ¬ CopyChiCollision source lambda chi)
    (noCompressionCollision :
      ¬ CopyTupleCompressionCollision source lambda) :
    RequiredTraceAliases
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) := by
  exact requiredTraceAliases_of_copy_sources extraction
    (requiredCopySourceEquations_of_deployed_copy_logup extraction source
      lambda chi balance noChiCollision noCompressionCollision)

/-! ## Audit -/

#print axioms deployedCopyLink_card
#print axioms requiredScalarLink_card
#print axioms deployedCopyTag_unique_at_required
#print axioms required_value_equal_of_tagged_multisets_equal
#print axioms all_required_values_equal_or_copy_collision
#print axioms requiredCopySourceEquations_of_deployed_copy_logup
#print axioms requiredTraceAliases_of_deployed_copy_logup

end AspisPool.V7DeployedCopyLogUpAliasClosure
