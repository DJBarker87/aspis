import AspisFormal.Pool.V7DeployedCopyLogUpAliasClosure

/-!
# Deployed Tag-73 copy evaluator and rational-balance bridge

This leaf gives the full source shape omitted by the 43-link alias closure:
all 183 deployed endpoints, both row-local slots, and all fifteen affine tuple
patterns.  It then isolates the exact Boolean copy-row evaluator and proves
the algebra which turns its cleared local identities plus the helper zero-sum
into `copyRationalBalance = 0`.

The proof keeps three distinct sampled-challenge failures visible:

* an active pole `chi = compressed(endpoint)`;
* the inactive-slot padding value `chi = 0`; and
* after rational balance is obtained, the existing sampled-`chi` rational
  collision and sampled-`lambda` tuple-compression collision.

No generic copy-lane faithfulness or blanket copy-zero premise is used.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace AspisPool.V7DeployedCopyEvaluatorBalanceBridge

open Module
open AspisFormal.ArithmetizationCore
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7OpenedColumnsFromTrace
open AspisV5ComponentCQM31TowerExact
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5AcceptedSpendRelation
open AspisV5ConstraintLaneBatching
open AspisV5FriConcreteEncoderApplicability
open AspisV5TowerPackedResidualExtraction
open AspisV6OneFoldCandidateExtraction
open AspisSumcheckMasking

/-! ## The complete deployed endpoint table -/

/-- One endpoint of the generated `CompiledAtomicCopyLink` table.  The slot
is side-local: producer slots and consumer slots are counted separately. -/
structure DeployedCopyEndpoint where
  row : Fin 1024
  slot : Fin 2
  pattern : Fin 15
  deriving DecidableEq, Repr

def endpoint (row : Fin 1024) (slot : Fin 2)
    (pattern : Fin 15) : DeployedCopyEndpoint :=
  { row := row, slot := slot, pattern := pattern }

/-- Literal first 23 producer endpoints from
`COMPILED_ATOMIC_COPY_LINKS[0..23]`. -/
def retainedProducerEndpoint : Fin 23 → DeployedCopyEndpoint := ![
  endpoint 27 0 0, endpoint 43 0 0, endpoint 715 0 0,
  endpoint 747 0 0, endpoint 763 0 0, endpoint 11 0 1,
  endpoint 59 0 1, endpoint 12 0 3, endpoint 44 0 3,
  endpoint 60 0 3, endpoint 764 0 3, endpoint 792 0 5,
  endpoint 793 0 1, endpoint 795 0 6, endpoint 797 0 7,
  endpoint 793 1 3, endpoint 794 0 3, endpoint 796 0 3,
  endpoint 799 0 6, endpoint 809 0 1, endpoint 864 0 8,
  endpoint 866 0 8, endpoint 799 1 9]

/-- Literal first 23 consumer endpoints from
`COMPILED_ATOMIC_COPY_LINKS[0..23]`. -/
def retainedConsumerEndpoint : Fin 23 → DeployedCopyEndpoint := ![
  endpoint 32 0 0, endpoint 48 0 0, endpoint 720 0 0,
  endpoint 752 0 0, endpoint 768 0 0, endpoint 793 0 1,
  endpoint 784 0 2, endpoint 793 1 3, endpoint 797 0 4,
  endpoint 794 0 3, endpoint 809 0 4, endpoint 12 0 0,
  endpoint 28 0 0, endpoint 44 0 0, endpoint 60 0 0,
  endpoint 716 0 0, endpoint 732 0 0, endpoint 748 0 0,
  endpoint 764 0 0, endpoint 780 0 0, endpoint 795 0 9,
  endpoint 799 0 9, endpoint 864 0 10]

def inputPathFinalRow (level : Fin 20) : Fin 1024 :=
  ⟨59 + 16 * level.val, by omega⟩

def outputPathFinalRow (level : Fin 20) : Fin 1024 :=
  if level.val = 0 then 779 else ⟨379 + 16 * level.val, by omega⟩

def inputPathLeftRow (level : Fin 20) : Fin 1024 :=
  ⟨76 + 16 * level.val, by omega⟩

def inputPathRightRow (level : Fin 20) : Fin 1024 :=
  ⟨64 + 16 * level.val, by omega⟩

def outputPathLeftRow (level : Fin 20) : Fin 1024 :=
  ⟨396 + 16 * level.val, by omega⟩

def outputPathRightRow (level : Fin 20) : Fin 1024 :=
  ⟨384 + 16 * level.val, by omega⟩

/-- The current/left/right physical rows selected by an input/output path flag. -/
def selectedPathCurrentRow (level : Fin 20) (output : Bool) : Fin 1024 :=
  if output then outputPathRow level else inputPathRow level

def selectedPathLeftRow (level : Fin 20) (output : Bool) : Fin 1024 :=
  if output then outputPathLeftRow level else inputPathLeftRow level

def selectedPathRightRow (level : Fin 20) (output : Bool) : Fin 1024 :=
  if output then outputPathRightRow level else inputPathRightRow level

/-- Full producer endpoint projection, including the regular eight-link path
block at each of twenty levels. -/
def deployedProducerEndpoint : DeployedCopyLink → DeployedCopyEndpoint
  | .retained index => retainedProducerEndpoint index
  | .pathCurrent level false =>
      endpoint (inputPathFinalRow level) (if level.val = 0 then 1 else 0) 1
  | .pathCurrent level true => endpoint (outputPathFinalRow level) 0 1
  | .pathSelect level false 0 => endpoint (inputPathRow level) 0 11
  | .pathSelect level false 1 => endpoint (siblingPathRow level) 0 13
  | .pathSelect level true 0 => endpoint (outputPathRow level) 0 11
  | .pathSelect level true 1 => endpoint (siblingPathRow level) 1 13
  | .pathAlias level 0 => endpoint (inputPathRow level) 1 9
  | .pathAlias level 1 => endpoint (outputPathRow level) 1 9

/-- Full consumer endpoint projection. -/
def deployedConsumerEndpoint : DeployedCopyLink → DeployedCopyEndpoint
  | .retained index => retainedConsumerEndpoint index
  | .pathCurrent level false =>
      endpoint (inputPathRow level) (if level.val = 0 then 1 else 0) 2
  | .pathCurrent level true => endpoint (outputPathRow level) 0 2
  | .pathSelect level false 0 => endpoint (inputPathLeftRow level) 0 12
  | .pathSelect level false 1 => endpoint (inputPathRightRow level) 0 14
  | .pathSelect level true 0 => endpoint (outputPathLeftRow level) 0 12
  | .pathSelect level true 1 => endpoint (outputPathRightRow level) 0 14
  | .pathAlias level 0 => endpoint (outputPathRow level) 1 9
  | .pathAlias level 1 => endpoint (siblingPathRow level) 0 9

theorem deployedProducerEndpoint_injective :
    Function.Injective deployedProducerEndpoint := by
  decide

theorem deployedConsumerEndpoint_injective :
    Function.Injective deployedConsumerEndpoint := by
  decide

/-- Source-array index of each structured link. -/
def deployedCopySourceIndex : DeployedCopyLink → Fin 183
  | .retained index => ⟨index.val, by omega⟩
  | .pathCurrent level false => ⟨23 + 8 * level.val, by omega⟩
  | .pathSelect level false item =>
      ⟨24 + 8 * level.val + item.val, by omega⟩
  | .pathCurrent level true => ⟨26 + 8 * level.val, by omega⟩
  | .pathSelect level true item =>
      ⟨27 + 8 * level.val + item.val, by omega⟩
  | .pathAlias level hop => ⟨29 + 8 * level.val + hop.val, by omega⟩

/-! ## All fifteen affine tuple patterns -/

def traceCell
    {K : Type*} [Zero K]
    (trace : Fin 1024 → Fin 16 → K) (row : Fin 1024) (column : Nat) : K :=
  if h : column < 16 then trace row ⟨column, h⟩ else 0

/-- Semantic value of one limb of the generated fifteen-pattern table.
Patterns 13 and 14 retain their literal affine offsets. -/
def deployedPatternLimb
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (row : Fin 1024)
    (pattern : Fin 15) (limb : Fin 16) : K :=
  match pattern.val with
  | 0 => trace row limb
  | 1 => if limb.val < 8 then traceCell trace row limb.val else 0
  | 2 => if limb.val < 8 then traceCell trace row (limb.val + 1) else 0
  | 3 => if limb.val < 8 then traceCell trace row (8 + limb.val) else 0
  | 4 => if limb.val < 8 then
      traceCell trace row (if limb.val < 6 then 8 + limb.val else limb.val - 6)
    else 0
  | 5 => traceCell trace row (8 + limb.val % 8)
  | 6 => if limb.val < 8 then traceCell trace row limb.val
    else traceCell trace row (limb.val - 6)
  | 7 => if limb.val < 14 then traceCell trace row limb.val
    else traceCell trace row (limb.val - 14)
  | 8 => if limb.val = 0 then traceCell trace row 11 else 0
  | 9 => if limb.val = 0 then traceCell trace row 0 else 0
  | 10 => if limb.val = 0 then traceCell trace row 12 else 0
  | 11 => if limb.val < 9 then traceCell trace row limb.val else 0
  | 12 => if limb.val = 0 then 0 else if limb.val < 9 then
      traceCell trace row (limb.val - 1) else 0
  | 13 => if limb.val = 0 then 1 - traceCell trace row 0
    else if limb.val < 9 then traceCell trace row limb.val else 0
  | _ => if limb.val = 0 then 1 else if limb.val < 9 then
      traceCell trace row (7 + limb.val) +
        (if limb.val = 8 then (1051521018 : K) else 0)
    else 0

def deployedEndpointTuple
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (tag : Nat)
    (source : DeployedCopyEndpoint) : TaggedCopyTuple K where
  tag := tag
  limbs := deployedPatternLimb trace source.row source.pattern

def deployedProducerTuple
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (link : DeployedCopyLink) :
    TaggedCopyTuple K :=
  deployedEndpointTuple trace (deployedCopyTag link)
    (deployedProducerEndpoint link)

def deployedConsumerTuple
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (link : DeployedCopyLink) :
    TaggedCopyTuple K :=
  deployedEndpointTuple trace (deployedCopyTag link)
    (deployedConsumerEndpoint link)

/-! Literal limb views for the forty unique current-digest links.  Publishing
these reductions keeps downstream path extraction independent of the private
`endpoint` and `traceCell` construction helpers. -/

@[simp] theorem deployedProducerTuple_pathCurrent_input_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (limb : Fin 8) :
    (deployedProducerTuple trace (.pathCurrent level false)).limbs
        ⟨limb.val, by omega⟩ =
      trace (inputPathFinalRow level) ⟨limb.val, by omega⟩ := by
  have limbBound : limb.val < 16 := by omega
  simp [deployedProducerTuple, deployedEndpointTuple,
    deployedProducerEndpoint, deployedPatternLimb, endpoint, traceCell,
    limbBound]

@[simp] theorem deployedConsumerTuple_pathCurrent_input_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (limb : Fin 8) :
    (deployedConsumerTuple trace (.pathCurrent level false)).limbs
        ⟨limb.val, by omega⟩ =
      trace (inputPathRow level) ⟨limb.val + 1, by omega⟩ := by
  have limbBound : limb.val + 1 < 16 := by omega
  simp [deployedConsumerTuple, deployedEndpointTuple,
    deployedConsumerEndpoint, deployedPatternLimb, endpoint, traceCell,
    limbBound]

@[simp] theorem deployedProducerTuple_pathCurrent_output_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (limb : Fin 8) :
    (deployedProducerTuple trace (.pathCurrent level true)).limbs
        ⟨limb.val, by omega⟩ =
      trace (outputPathFinalRow level) ⟨limb.val, by omega⟩ := by
  have limbBound : limb.val < 16 := by omega
  simp [deployedProducerTuple, deployedEndpointTuple,
    deployedProducerEndpoint, deployedPatternLimb, endpoint, traceCell,
    limbBound]

@[simp] theorem deployedConsumerTuple_pathCurrent_output_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (limb : Fin 8) :
    (deployedConsumerTuple trace (.pathCurrent level true)).limbs
        ⟨limb.val, by omega⟩ =
      trace (outputPathRow level) ⟨limb.val + 1, by omega⟩ := by
  have limbBound : limb.val + 1 < 16 := by omega
  simp [deployedConsumerTuple, deployedEndpointTuple,
    deployedConsumerEndpoint, deployedPatternLimb, endpoint, traceCell,
    limbBound]

/-! Literal tuple views for the two-by-two selection links.  A selection tag
is intentionally shared by its two items, so these shapes are kept distinct
until the Boolean path bit determines the only legal matching. -/

@[simp] theorem deployedProducerTuple_pathSelect_current_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (output : Bool) (limb : Fin 16) :
    (deployedProducerTuple trace (.pathSelect level output 0)).limbs limb =
      if limb.val < 9 then trace (selectedPathCurrentRow level output) limb
      else 0 := by
  cases output <;>
    simp [deployedProducerTuple, deployedEndpointTuple,
      deployedProducerEndpoint, deployedPatternLimb, selectedPathCurrentRow,
      endpoint, traceCell]

@[simp] theorem deployedProducerTuple_pathSelect_sibling_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (output : Bool) (limb : Fin 16) :
    (deployedProducerTuple trace (.pathSelect level output 1)).limbs limb =
      if limb.val = 0 then 1 - trace (siblingPathRow level) 0
      else if limb.val < 9 then trace (siblingPathRow level) limb else 0 := by
  cases output <;>
    simp [deployedProducerTuple, deployedEndpointTuple,
      deployedProducerEndpoint, deployedPatternLimb, endpoint, traceCell]

@[simp] theorem deployedConsumerTuple_pathSelect_left_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (output : Bool) (limb : Fin 16) :
    (deployedConsumerTuple trace (.pathSelect level output 0)).limbs limb =
      if limb.val = 0 then 0
      else if limbBound : limb.val < 9 then
        trace (selectedPathLeftRow level output)
          ⟨limb.val - 1, by omega⟩
      else 0 := by
  cases output <;>
    simp only [deployedConsumerTuple, deployedEndpointTuple,
      deployedConsumerEndpoint, deployedPatternLimb, selectedPathLeftRow,
      Bool.false_eq_true, ↓reduceIte, endpoint]
  all_goals
    by_cases isZero : limb.val = 0
    · simp [isZero]
    · by_cases active : limb.val < 9
      · have cellBound : limb.val - 1 < 16 := by omega
        simp [isZero, active, traceCell, cellBound]
      · simp [isZero, active]

@[simp] theorem deployedConsumerTuple_pathSelect_right_limb
    {K : Type*} [Field K] (trace : Fin 1024 → Fin 16 → K)
    (level : Fin 20) (output : Bool) (limb : Fin 16) :
    (deployedConsumerTuple trace (.pathSelect level output 1)).limbs limb =
      if limb.val = 0 then 1
      else if limbBound : limb.val < 9 then
        trace (selectedPathRightRow level output)
            ⟨7 + limb.val, by omega⟩ +
          (if limb.val = 8 then (1051521018 : K) else 0)
      else 0 := by
  cases output <;>
    simp only [deployedConsumerTuple, deployedEndpointTuple,
      deployedConsumerEndpoint, deployedPatternLimb, selectedPathRightRow,
      Bool.false_eq_true, ↓reduceIte, endpoint]
  all_goals
    by_cases isZero : limb.val = 0
    · simp [isZero]
    · by_cases active : limb.val < 9
      · have cellBound : 7 + limb.val < 16 := by omega
        simp [isZero, active, traceCell, cellBound]
      · simp [isZero, active]

private theorem taggedCopyTuple_ext
    {K : Type*} {left right : TaggedCopyTuple K}
    (tag : left.tag = right.tag)
    (limbs : ∀ limb, left.limbs limb = right.limbs limb) : left = right := by
  cases left with
  | mk leftTag leftLimbs =>
      cases right with
      | mk rightTag rightLimbs =>
          simp only at tag limbs
          subst rightTag
          have : leftLimbs = rightLimbs := funext limbs
          subst rightLimbs
          rfl

/-! ## The concrete 183-link registry projection -/

def extractedSelectedTrace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) : Fin 1024 → Fin 16 → QM31Exact :=
  fun row column => selectedC1Cell extraction row column

/-- All 183 producer/consumer tuples read their literal generated endpoint
and affine pattern.  The 43 required fields reduce to their exact scalar
coordinates rather than to an assumed equality. -/
noncomputable def concreteDeployedCopyRegistryProjection
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) :
    DeployedCopyRegistryProjection QM31Exact
      (requiredProducerCell extraction) (requiredConsumerCell extraction) where
  producer := deployedProducerTuple (extractedSelectedTrace extraction)
  consumer := deployedConsumerTuple (extractedSelectedTrace extraction)
  producerTag := by intro link; rfl
  consumerTag := by intro link; rfl
  requiredProducer := by
    intro required
    cases required with
    | inputRangeToNote =>
        apply taggedCopyTuple_ext rfl
        intro limb
        simp [deployedProducerTuple, deployedEndpointTuple,
          deployedProducerEndpoint, retainedProducerEndpoint,
          deployedPatternLimb, traceCell, extractedSelectedTrace,
          requiredRegistryLink]
    | outputRangeToNote =>
        apply taggedCopyTuple_ext rfl
        intro limb
        simp [deployedProducerTuple, deployedEndpointTuple,
          deployedProducerEndpoint, retainedProducerEndpoint,
          deployedPatternLimb, traceCell, extractedSelectedTrace,
          requiredRegistryLink]
    | outputNoteToBalance =>
        apply taggedCopyTuple_ext rfl
        intro limb
        simp [deployedProducerTuple, deployedEndpointTuple,
          deployedProducerEndpoint, retainedProducerEndpoint,
          deployedPatternLimb, traceCell, extractedSelectedTrace,
          requiredRegistryLink]
    | path level hop =>
        fin_cases hop <;>
          apply taggedCopyTuple_ext rfl <;>
          intro limb <;>
          simp [deployedProducerTuple, deployedEndpointTuple,
            deployedProducerEndpoint, deployedPatternLimb, traceCell,
            extractedSelectedTrace, requiredRegistryLink]
  requiredConsumer := by
    intro required
    cases required with
    | inputRangeToNote =>
        apply taggedCopyTuple_ext rfl
        intro limb
        simp [deployedConsumerTuple, deployedEndpointTuple,
          deployedConsumerEndpoint, retainedConsumerEndpoint,
          deployedPatternLimb, traceCell, extractedSelectedTrace,
          requiredRegistryLink]
    | outputRangeToNote =>
        apply taggedCopyTuple_ext rfl
        intro limb
        simp [deployedConsumerTuple, deployedEndpointTuple,
          deployedConsumerEndpoint, retainedConsumerEndpoint,
          deployedPatternLimb, traceCell, extractedSelectedTrace,
          requiredRegistryLink]
    | outputNoteToBalance =>
        apply taggedCopyTuple_ext rfl
        intro limb
        simp [deployedConsumerTuple, deployedEndpointTuple,
          deployedConsumerEndpoint, retainedConsumerEndpoint,
          deployedPatternLimb, traceCell, extractedSelectedTrace,
          requiredRegistryLink]
    | path level hop =>
        fin_cases hop <;>
          apply taggedCopyTuple_ext rfl <;>
          intro limb <;>
          simp [deployedConsumerTuple, deployedEndpointTuple,
            deployedConsumerEndpoint, deployedPatternLimb, traceCell,
            extractedSelectedTrace, requiredRegistryLink]

/-! ## Exact two-slot Boolean row evaluator -/

abbrev DeployedCopyRowSlot := Fin 1024 × Fin 2

def producerRowSlot (link : DeployedCopyLink) : DeployedCopyRowSlot :=
  ((deployedProducerEndpoint link).row, (deployedProducerEndpoint link).slot)

def consumerRowSlot (link : DeployedCopyLink) : DeployedCopyRowSlot :=
  ((deployedConsumerEndpoint link).row, (deployedConsumerEndpoint link).slot)

theorem producerRowSlot_injective : Function.Injective producerRowSlot := by
  decide

theorem consumerRowSlot_injective : Function.Injective consumerRowSlot := by
  decide

noncomputable def slotValue
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (value : DeployedCopyLink → K) (target : DeployedCopyRowSlot) : K :=
  ∑ link : DeployedCopyLink,
    if placement link = target then value link else 0

noncomputable def slotWeight
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (target : DeployedCopyRowSlot) : K :=
  if ∃ link, placement link = target then 1 else 0

theorem slotValue_eq_of_placed
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (injective : Function.Injective placement)
    (value : DeployedCopyLink → K) (link : DeployedCopyLink) :
    slotValue placement value (placement link) = value link := by
  classical
  unfold slotValue
  rw [Finset.sum_eq_single link]
  · simp
  · intro other _ different
    have placementDifferent : placement other ≠ placement link := by
      exact fun equal => different (injective equal)
    simp [placementDifferent]
  · simp

theorem slotWeight_eq_one_of_placed
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (link : DeployedCopyLink) :
    slotWeight (K := K) placement (placement link) = 1 := by
  classical
  simp [slotWeight]

theorem slotValue_eq_zero_of_unoccupied
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (value : DeployedCopyLink → K) (target : DeployedCopyRowSlot)
    (empty : ∀ link, placement link ≠ target) :
    slotValue placement value target = 0 := by
  classical
  simp [slotValue, empty]

theorem slotWeight_eq_zero_of_unoccupied
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (target : DeployedCopyRowSlot)
    (empty : ∀ link, placement link ≠ target) :
    slotWeight (K := K) placement target = 0 := by
  classical
  simp [slotWeight, empty]

/-- The exact four-value/four-weight `CopyLogUpRow` shape. -/
structure DeployedCopyRow (K : Type*) where
  producerValue : Fin 2 → K
  producerWeight : Fin 2 → K
  consumerValue : Fin 2 → K
  consumerWeight : Fin 2 → K

noncomputable def deployedCopyRows
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) (row : Fin 1024) : DeployedCopyRow K where
  producerValue := fun slot => slotValue producerRowSlot
    (fun link => compressTaggedTuple lambda (source.producer link)) (row, slot)
  producerWeight := fun slot => slotWeight producerRowSlot (row, slot)
  consumerValue := fun slot => slotValue consumerRowSlot
    (fun link => compressTaggedTuple lambda (source.consumer link)) (row, slot)
  consumerWeight := fun slot => slotWeight consumerRowSlot (row, slot)

/-- Literal expansion of `logup.rs::copy_logup_residual`. -/
def copyLocalResidual
    {K : Type*} [Field K]
    (row : DeployedCopyRow K) (helper chi : K) : K :=
  let p0 := chi - row.producerValue 0
  let p1 := chi - row.producerValue 1
  let c0 := chi - row.consumerValue 0
  let c1 := chi - row.consumerValue 1
  helper * p0 * p1 * c0 * c1
    - row.producerWeight 0 * p1 * c0 * c1
    - row.producerWeight 1 * p0 * c0 * c1
    + row.consumerWeight 0 * p0 * p1 * c1
    + row.consumerWeight 1 * p0 * p1 * c0

noncomputable def copyRowRationalContribution
    {K : Type*} [Field K]
    (row : DeployedCopyRow K) (chi : K) : K :=
  (∑ slot : Fin 2,
      row.producerWeight slot * (chi - row.producerValue slot)⁻¹) -
    ∑ slot : Fin 2,
      row.consumerWeight slot * (chi - row.consumerValue slot)⁻¹

/-- A row is active exactly when one of the 366 deployed endpoints occupies
one of its side-local slots. -/
noncomputable def deployedCopyRowActive (row : Fin 1024) : Prop :=
  (∃ link, (deployedProducerEndpoint link).row = row) ∨
    ∃ link, (deployedConsumerEndpoint link).row = row

/-- Boolean restriction of the generated evaluator.  On an inactive row the
source `copy_active` selector is zero; on an active row it exposes the exact
four-denominator cleared residual. -/
noncomputable def deployedCompiledCopyLane
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) (helper : Fin 1024 → K) : Fin 1024 → K := by
  classical
  exact fun row => if deployedCopyRowActive row then
    copyLocalResidual (deployedCopyRows source lambda row) (helper row) chi
  else 0

/-! ## Cleared local identity to the row rational contribution -/

theorem helper_eq_copyRowRationalContribution_of_residual_zero
    {K : Type*} [Field K]
    (row : DeployedCopyRow K) (helper chi : K)
    (p0 : chi - row.producerValue 0 ≠ 0)
    (p1 : chi - row.producerValue 1 ≠ 0)
    (c0 : chi - row.consumerValue 0 ≠ 0)
    (c1 : chi - row.consumerValue 1 ≠ 0)
    (residual : copyLocalResidual row helper chi = 0) :
    helper = copyRowRationalContribution row chi := by
  unfold copyRowRationalContribution
  simp only [Fin.sum_univ_two]
  field_simp [p0, p1, c0, c1]
  unfold copyLocalResidual at residual
  dsimp only at residual
  linear_combination residual

/-! ## Explicit denominator failures -/

/-- A pole at any active deployed producer or consumer. -/
def DeployedCopyActivePole
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) : Prop :=
  (∃ link, chi = compressTaggedTuple lambda (source.producer link)) ∨
    ∃ link, chi = compressTaggedTuple lambda (source.consumer link)

/-- The generated four-slot residual retains `chi - 0` for every inactive
slot.  Thus `chi = 0` is a separate exact degeneracy, even when no active
endpoint itself is a pole. -/
def DeployedCopyInactiveSlotCollision {K : Type*} [Zero K] (chi : K) : Prop :=
  chi = 0

theorem slot_denominator_ne_zero
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (injective : Function.Injective placement)
    (value : DeployedCopyLink → K) (chi : K)
    (chiNonzero : chi ≠ 0)
    (noPole : ∀ link, chi ≠ value link)
    (target : DeployedCopyRowSlot) :
    chi - slotValue placement value target ≠ 0 := by
  classical
  by_cases occupied : ∃ link, placement link = target
  · obtain ⟨link, placed⟩ := occupied
    have slotValueExact : slotValue placement value target = value link := by
      rw [← placed]
      exact slotValue_eq_of_placed placement injective value link
    rw [slotValueExact]
    exact sub_ne_zero.mpr (noPole link)
  · have empty : ∀ link, placement link ≠ target := by
      intro link equal
      exact occupied ⟨link, equal⟩
    rw [slotValue_eq_zero_of_unoccupied placement value target empty, sub_zero]
    exact chiNonzero

theorem deployed_row_denominators_ne_zero
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole source lambda chi)
    (row : Fin 1024) :
    (∀ slot, chi - (deployedCopyRows source lambda row).producerValue slot ≠ 0) ∧
      ∀ slot, chi - (deployedCopyRows source lambda row).consumerValue slot ≠ 0 := by
  have producerNoPole : ∀ link,
      chi ≠ compressTaggedTuple lambda (source.producer link) := by
    intro link equal
    exact noPole (Or.inl ⟨link, equal⟩)
  have consumerNoPole : ∀ link,
      chi ≠ compressTaggedTuple lambda (source.consumer link) := by
    intro link equal
    exact noPole (Or.inr ⟨link, equal⟩)
  constructor
  · intro slot
    exact slot_denominator_ne_zero producerRowSlot producerRowSlot_injective
      (fun link => compressTaggedTuple lambda (source.producer link)) chi
      chiNonzero producerNoPole (row, slot)
  · intro slot
    exact slot_denominator_ne_zero consumerRowSlot consumerRowSlot_injective
      (fun link => compressTaggedTuple lambda (source.consumer link)) chi
      chiNonzero consumerNoPole (row, slot)

/-! ## Row sums are exactly the 183-link rational balance -/

theorem slot_rational_eq_link_sum
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (injective : Function.Injective placement)
    (value : DeployedCopyLink → K) (chi : K)
    (target : DeployedCopyRowSlot) :
    slotWeight placement target *
        (chi - slotValue placement value target)⁻¹ =
      ∑ link : DeployedCopyLink,
        if placement link = target then (chi - value link)⁻¹ else 0 := by
  classical
  by_cases occupied : ∃ link, placement link = target
  · obtain ⟨link, placed⟩ := occupied
    have valueExact : slotValue placement value target = value link := by
      rw [← placed]
      exact slotValue_eq_of_placed placement injective value link
    have weightExact : slotWeight (K := K) placement target = 1 := by
      rw [← placed]
      exact slotWeight_eq_one_of_placed placement link
    rw [valueExact, weightExact, one_mul]
    symm
    rw [Finset.sum_eq_single link]
    · simp [placed]
    · intro other _ different
      have placementDifferent : placement other ≠ target := by
        intro equal
        exact different (injective (equal.trans placed.symm))
      simp [placementDifferent]
    · simp
  · have empty : ∀ link, placement link ≠ target := by
      intro link equal
      exact occupied ⟨link, equal⟩
    rw [slotWeight_eq_zero_of_unoccupied placement target empty]
    simp [empty]

theorem sum_slot_rational_eq_link_sum
    {K : Type*} [Field K]
    (placement : DeployedCopyLink → DeployedCopyRowSlot)
    (injective : Function.Injective placement)
    (value : DeployedCopyLink → K) (chi : K) :
    (∑ target : DeployedCopyRowSlot,
      slotWeight placement target *
        (chi - slotValue placement value target)⁻¹) =
      ∑ link : DeployedCopyLink, (chi - value link)⁻¹ := by
  classical
  simp_rw [slot_rational_eq_link_sum placement injective value chi]
  rw [Finset.sum_comm]
  simp

theorem tableSum_copyRowRationalContribution_eq_balance
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) :
    tableSum (fun row =>
      copyRowRationalContribution (deployedCopyRows source lambda row) chi) =
      copyRationalBalance source lambda chi := by
  classical
  unfold tableSum copyRowRationalContribution copyRationalBalance
  rw [Finset.sum_sub_distrib]
  have producerSum :
      (∑ row : Fin 1024, ∑ slot : Fin 2,
        slotWeight producerRowSlot (row, slot) *
          (chi - slotValue producerRowSlot
            (fun link => compressTaggedTuple lambda (source.producer link))
            (row, slot))⁻¹) =
        ∑ link : DeployedCopyLink,
          (chi - compressTaggedTuple lambda (source.producer link))⁻¹ := by
    calc
      _ = ∑ target : DeployedCopyRowSlot,
          slotWeight producerRowSlot target *
            (chi - slotValue producerRowSlot
              (fun link => compressTaggedTuple lambda (source.producer link))
              target)⁻¹ := by
        simpa using (Fintype.sum_prod_type'
          (fun row : Fin 1024 => fun slot : Fin 2 =>
            slotWeight producerRowSlot (row, slot) *
              (chi - slotValue producerRowSlot
                (fun link => compressTaggedTuple lambda (source.producer link))
                (row, slot))⁻¹)).symm
      _ = _ := sum_slot_rational_eq_link_sum producerRowSlot
        producerRowSlot_injective
        (fun link => compressTaggedTuple lambda (source.producer link)) chi
  have consumerSum :
      (∑ row : Fin 1024, ∑ slot : Fin 2,
        slotWeight consumerRowSlot (row, slot) *
          (chi - slotValue consumerRowSlot
            (fun link => compressTaggedTuple lambda (source.consumer link))
            (row, slot))⁻¹) =
        ∑ link : DeployedCopyLink,
          (chi - compressTaggedTuple lambda (source.consumer link))⁻¹ := by
    calc
      _ = ∑ target : DeployedCopyRowSlot,
          slotWeight consumerRowSlot target *
            (chi - slotValue consumerRowSlot
              (fun link => compressTaggedTuple lambda (source.consumer link))
              target)⁻¹ := by
        simpa using (Fintype.sum_prod_type'
          (fun row : Fin 1024 => fun slot : Fin 2 =>
            slotWeight consumerRowSlot (row, slot) *
              (chi - slotValue consumerRowSlot
                (fun link => compressTaggedTuple lambda (source.consumer link))
                (row, slot))⁻¹)).symm
      _ = _ := sum_slot_rational_eq_link_sum consumerRowSlot
        consumerRowSlot_injective
        (fun link => compressTaggedTuple lambda (source.consumer link)) chi
  change
    (∑ row : Fin 1024, ∑ slot : Fin 2,
      slotWeight producerRowSlot (row, slot) *
        (chi - slotValue producerRowSlot
          (fun link => compressTaggedTuple lambda (source.producer link))
          (row, slot))⁻¹) -
      (∑ row : Fin 1024, ∑ slot : Fin 2,
        slotWeight consumerRowSlot (row, slot) *
          (chi - slotValue consumerRowSlot
            (fun link => compressTaggedTuple lambda (source.consumer link))
            (row, slot))⁻¹) = _
  rw [producerSum, consumerSum]

/-! ## Local acceptance plus helper boundary gives global balance -/

/-- Exact helper support fact supplied by `build_copy_logup_helper`: no
deployed endpoint on a row means the constructed helper entry is zero. -/
def DeployedCopyHelperInactiveZero
    {K : Type*} [Zero K] (helper : Fin 1024 → K) : Prop :=
  ∀ row, ¬ deployedCopyRowActive row → helper row = 0

theorem copyRowRationalContribution_zero_of_inactive
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) (row : Fin 1024)
    (inactive : ¬ deployedCopyRowActive row) :
    copyRowRationalContribution (deployedCopyRows source lambda row) chi = 0 := by
  classical
  have producerEmpty : ∀ link, producerRowSlot link ≠ (row, (0 : Fin 2)) := by
    intro link equal
    apply inactive
    exact Or.inl ⟨link, congrArg Prod.fst equal⟩
  have producerEmpty1 : ∀ link, producerRowSlot link ≠ (row, (1 : Fin 2)) := by
    intro link equal
    apply inactive
    exact Or.inl ⟨link, congrArg Prod.fst equal⟩
  have consumerEmpty : ∀ link, consumerRowSlot link ≠ (row, (0 : Fin 2)) := by
    intro link equal
    apply inactive
    exact Or.inr ⟨link, congrArg Prod.fst equal⟩
  have consumerEmpty1 : ∀ link, consumerRowSlot link ≠ (row, (1 : Fin 2)) := by
    intro link equal
    apply inactive
    exact Or.inr ⟨link, congrArg Prod.fst equal⟩
  unfold copyRowRationalContribution deployedCopyRows
  simp only [Fin.sum_univ_two]
  rw [slotWeight_eq_zero_of_unoccupied producerRowSlot (row, 0) producerEmpty,
    slotWeight_eq_zero_of_unoccupied producerRowSlot (row, 1) producerEmpty1,
    slotWeight_eq_zero_of_unoccupied consumerRowSlot (row, 0) consumerEmpty,
    slotWeight_eq_zero_of_unoccupied consumerRowSlot (row, 1) consumerEmpty1]
  ring

theorem copyRationalBalance_zero_of_local_residuals
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) (helper : Fin 1024 → K)
    (localZero : ∀ row,
      deployedCompiledCopyLane source lambda chi helper row = 0)
    (inactiveZero : DeployedCopyHelperInactiveZero helper)
    (helperSumZero : tableSum helper = 0)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole source lambda chi) :
    copyRationalBalance source lambda chi = 0 := by
  have pointwise : ∀ row,
      helper row =
        copyRowRationalContribution (deployedCopyRows source lambda row) chi := by
    intro row
    by_cases active : deployedCopyRowActive row
    · have residualZero :
          copyLocalResidual (deployedCopyRows source lambda row)
            (helper row) chi = 0 := by
        simpa [deployedCompiledCopyLane, active] using localZero row
      have denominators := deployed_row_denominators_ne_zero source lambda chi
        chiNonzero noPole row
      exact helper_eq_copyRowRationalContribution_of_residual_zero
        (deployedCopyRows source lambda row) (helper row) chi
        (denominators.1 0) (denominators.1 1)
        (denominators.2 0) (denominators.2 1) residualZero
    · rw [inactiveZero row active,
        copyRowRationalContribution_zero_of_inactive source lambda chi row active]
  rw [← tableSum_copyRowRationalContribution_eq_balance source lambda chi]
  unfold tableSum
  simp_rw [← pointwise]
  exact helperSumZero

/-- The local premise above is exactly the `copy` field extracted by the
accepted K1.5 semantic composition when its independent copy function is
instantiated with the concrete deployed evaluator. -/
theorem copyRationalBalance_zero_of_accepted_copy_rows
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi : QM31Exact) (helper : Fin 1024 → QM31Exact)
    (acceptedRows : ExtractedConstraintRowsVanish statement extraction
      poseidonRows
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection extraction)
        lambda chi helper))
    (inactiveZero : DeployedCopyHelperInactiveZero helper)
    (helperSumZero : tableSum helper = 0)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi) :
    copyRationalBalance (concreteDeployedCopyRegistryProjection extraction)
      lambda chi = 0 := by
  exact copyRationalBalance_zero_of_local_residuals
    (concreteDeployedCopyRegistryProjection extraction) lambda chi helper
    acceptedRows.copy inactiveZero helperSumZero chiNonzero noPole

/-! ## Recovering the helper zero-sum from the accepted unmasked equation -/

/-- Once every row lane is zero, the constraint MLE is zero for every
`theta` and equality point. -/
theorem constraintMLE_zero_of_extracted_rows_vanish
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (copyLane : Fin 1024 → QM31Exact)
    (theta : QM31Exact) (point : Fin 10 → QM31Exact)
    (vanish : ExtractedConstraintRowsVanish statement extraction
      poseidonRows copyLane) :
    constraintMLE basis
      (extractedConstraintRows statement extraction poseidonRows copyLane)
      theta point = 0 := by
  classical
  let rows := extractedConstraintRows statement extraction poseidonRows copyLane
  have laneVectorZero : ∀ row, (rows row).laneVector basis = 0 := by
    intro row
    funext lane
    unfold ConstraintRowResiduals.laneVector constraintLaneVector
    by_cases poseidonLane : lane.val < 4
    · simp only [poseidonLane, dite_true]
      apply (towerPack_eq_zero_iff basis _).mpr
      intro slot
      exact vanish.poseidon row ⟨lane.val, poseidonLane⟩ slot
    · simp only [poseidonLane, dite_false]
      by_cases semanticLane : lane.val < 24
      · simp only [semanticLane, dite_true]
        apply (towerPack_eq_zero_iff basis _).mpr
        intro slot
        exact vanish.semantic row ⟨lane.val - 4, by omega⟩ slot
      · simp only [semanticLane, dite_false]
        exact vanish.copy row
  unfold constraintMLE tableMLEValue thetaConstraintTable rowConstraintPolynomial
  apply Finset.sum_eq_zero
  intro row _
  have rowLanes := laneVectorZero row
  change (extractedConstraintRows statement extraction poseidonRows copyLane row).laneVector
    basis = 0 at rowLanes
  rw [rowLanes]
  simp [monomialPolynomial]

/-- The source-shaped unmasked sum equation then authenticates the helper
zero-sum outside the one exact `mu = 0` branch. -/
theorem helper_sum_zero_of_unmasked_sum
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (copyLane : Fin 1024 → QM31Exact)
    (theta : QM31Exact) (point : Fin 10 → QM31Exact)
    (mu : QM31Exact) (helper : Fin 1024 → QM31Exact)
    (vanish : ExtractedConstraintRowsVanish statement extraction
      poseidonRows copyLane)
    (unmaskedSumZero : tableSum
      (sourceUnmaskedZerocheckTable basis
        (extractedConstraintRows statement extraction poseidonRows copyLane)
        theta point mu helper) = 0)
    (muNonzero : mu ≠ 0) :
    tableSum helper = 0 := by
  have sourceEquation := tableSum_sourceUnmaskedZerocheckTable basis
    (extractedConstraintRows statement extraction poseidonRows copyLane)
    theta point mu helper
  have mleZero := constraintMLE_zero_of_extracted_rows_vanish basis statement
    extraction poseidonRows copyLane theta point vanish
  have productZero : mu * tableSum helper = 0 := by
    rw [sourceEquation, mleZero, zero_add] at unmaskedSumZero
    exact unmaskedSumZero
  exact (mul_eq_zero.mp productZero).resolve_left muNonzero

/-- Direct collision-explicit alias closure from the accepted Boolean copy
lane and the helper boundary. -/
theorem requiredTraceAliases_of_local_copy_residuals
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (lambda chi : QM31Exact) (helper : Fin 1024 → QM31Exact)
    (localZero : ∀ row,
      deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection extraction)
        lambda chi helper row = 0)
    (inactiveZero : DeployedCopyHelperInactiveZero helper)
    (helperSumZero : tableSum helper = 0)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda) :
    RequiredTraceAliases
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) := by
  apply requiredTraceAliases_of_deployed_copy_logup extraction
    (concreteDeployedCopyRegistryProjection extraction) lambda chi
  · exact copyRationalBalance_zero_of_local_residuals
      (concreteDeployedCopyRegistryProjection extraction) lambda chi helper
      localZero inactiveZero helperSumZero chiNonzero noPole
  · exact noChiCollision
  · exact noCompressionCollision

/-- The same collision-explicit closure with the local-zero premise supplied
directly by the accepted K1.5 semantic row record. -/
theorem requiredTraceAliases_of_accepted_copy_rows
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi : QM31Exact) (helper : Fin 1024 → QM31Exact)
    (acceptedRows : ExtractedConstraintRowsVanish statement extraction
      poseidonRows
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection extraction)
        lambda chi helper))
    (inactiveZero : DeployedCopyHelperInactiveZero helper)
    (helperSumZero : tableSum helper = 0)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda) :
    RequiredTraceAliases
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) := by
  exact requiredTraceAliases_of_local_copy_residuals extraction lambda chi helper
    acceptedRows.copy inactiveZero helperSumZero chiNonzero noPole
    noChiCollision noCompressionCollision

#print axioms concreteDeployedCopyRegistryProjection
#print axioms producerRowSlot_injective
#print axioms consumerRowSlot_injective
#print axioms helper_eq_copyRowRationalContribution_of_residual_zero
#print axioms tableSum_copyRowRationalContribution_eq_balance
#print axioms copyRationalBalance_zero_of_local_residuals
#print axioms copyRationalBalance_zero_of_accepted_copy_rows
#print axioms constraintMLE_zero_of_extracted_rows_vanish
#print axioms helper_sum_zero_of_unmasked_sum
#print axioms requiredTraceAliases_of_local_copy_residuals
#print axioms requiredTraceAliases_of_accepted_copy_rows

end AspisPool.V7DeployedCopyEvaluatorBalanceBridge
