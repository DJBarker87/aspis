import AspisFormal.Pool.NativePaymentCompiledActiveExecutableV1

/-!
# Native Pool V1 compiled Copy LogUp bridge

This leaf pins the checked-in 78-link transfer and 75-link withdrawal endpoint
tables used by the native Tag-73 terminal.  It models the exact two-slot
Boolean-row evaluator and proves that vanishing local residuals, the total
helper boundary, and the compiled inactive-helper boundary imply the global
rational balance.  The final section isolates the scalar value/conservation
links outside separately named `chi` and tuple-compression collisions.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisPool.NativePaymentCompiledCopyLogUpV1

open Module
open AspisPool.NativePaymentCompiledActiveExecutableV1
open AspisPool.NativePaymentCompiledActiveMaskV1
open AspisPool.NativePaymentMaskedTerminalBridgeV1
open AspisPool.NativePaymentRandomizedExtractionV1
open AspisPool.NativePaymentTerminalBridgeV1
open AspisSumcheckMasking

/-! ## Literal generated endpoint tables -/

structure NativeCompiledCopyEndpoint where
  row : Fin 1024
  slot : Fin 2
  pattern : Fin 13
  deriving DecidableEq, Repr

structure NativeCompiledCopyLink where
  producer : NativeCompiledCopyEndpoint
  consumer : NativeCompiledCopyEndpoint
  deriving DecidableEq, Repr

private def endpoint (row : Fin 1024) (slot : Fin 2)
    (pattern : Fin 13) : NativeCompiledCopyEndpoint :=
  { row := row, slot := slot, pattern := pattern }

private def link (producerRow : Fin 1024) (producerSlot : Fin 2)
    (producerPattern : Fin 13) (consumerRow : Fin 1024)
    (consumerSlot : Fin 2) (consumerPattern : Fin 13) :
    NativeCompiledCopyLink :=
  { producer := endpoint producerRow producerSlot producerPattern
    consumer := endpoint consumerRow consumerSlot consumerPattern }

/-- Exact `PRIVATE_TRANSFER_COPY_LINKS`, with the sequential tag represented
separately by `nativeCopyTag`. -/
def privateTransferCopyLinks : Fin 78 → NativeCompiledCopyLink := ![
  link 27 0 0 32 0 0,
  link 43 0 0 48 0 0,
  link 395 0 0 400 0 0,
  link 475 0 0 480 0 0,
  link 491 0 0 496 0 0,
  link 427 0 0 432 0 0,
  link 443 0 0 448 0 0,
  link 11 0 1 28 0 1,
  link 12 0 1 396 0 1,
  link 44 0 2 412 0 3,
  link 60 0 4 412 1 5,
  link 59 0 1 784 0 6,
  link 785 0 1 76 0 1,
  link 785 1 7 64 0 8,
  link 75 0 1 786 0 6,
  link 787 0 1 92 0 1,
  link 787 1 7 80 0 8,
  link 91 0 1 788 0 6,
  link 789 0 1 108 0 1,
  link 789 1 7 96 0 8,
  link 107 0 1 790 0 6,
  link 791 0 1 124 0 1,
  link 791 1 7 112 0 8,
  link 123 0 1 800 0 6,
  link 801 0 1 140 0 1,
  link 801 1 7 128 0 8,
  link 139 0 1 802 0 6,
  link 803 0 1 156 0 1,
  link 803 1 7 144 0 8,
  link 155 0 1 804 0 6,
  link 805 0 1 172 0 1,
  link 805 1 7 160 0 8,
  link 171 0 1 806 0 6,
  link 807 0 1 188 0 1,
  link 807 1 7 176 0 8,
  link 187 0 1 816 0 6,
  link 817 0 1 204 0 1,
  link 817 1 7 192 0 8,
  link 203 0 1 818 0 6,
  link 819 0 1 220 0 1,
  link 819 1 7 208 0 8,
  link 219 0 1 820 0 6,
  link 821 0 1 236 0 1,
  link 821 1 7 224 0 8,
  link 235 0 1 822 0 6,
  link 823 0 1 252 0 1,
  link 823 1 7 240 0 8,
  link 251 0 1 832 0 6,
  link 833 0 1 268 0 1,
  link 833 1 7 256 0 8,
  link 267 0 1 834 0 6,
  link 835 0 1 284 0 1,
  link 835 1 7 272 0 8,
  link 283 0 1 836 0 6,
  link 837 0 1 300 0 1,
  link 837 1 7 288 0 8,
  link 299 0 1 838 0 6,
  link 839 0 1 316 0 1,
  link 839 1 7 304 0 8,
  link 315 0 1 848 0 6,
  link 849 0 1 332 0 1,
  link 849 1 7 320 0 8,
  link 331 0 1 850 0 6,
  link 851 0 1 348 0 1,
  link 851 1 7 336 0 8,
  link 347 0 1 852 0 6,
  link 853 0 1 364 0 1,
  link 853 1 7 352 0 8,
  link 363 0 1 854 0 6,
  link 855 0 1 380 0 1,
  link 855 1 7 368 0 8,
  link 44 1 9 864 0 10,
  link 444 0 9 866 0 10,
  link 492 0 9 868 0 10,
  link 864 0 10 870 0 9,
  link 866 0 10 870 1 11,
  link 868 0 10 871 0 11,
  link 870 0 12 871 1 9
]

/-- Exact `WITHDRAWAL_COPY_LINKS`, again without duplicating its sequential
tag field. -/
def withdrawalCopyLinks : Fin 75 → NativeCompiledCopyLink := ![
  link 27 0 0 32 0 0,
  link 43 0 0 48 0 0,
  link 395 0 0 400 0 0,
  link 475 0 0 480 0 0,
  link 491 0 0 496 0 0,
  link 11 0 1 28 0 1,
  link 12 0 1 396 0 1,
  link 44 0 2 412 0 3,
  link 60 0 4 412 1 5,
  link 59 0 1 784 0 6,
  link 785 0 1 76 0 1,
  link 785 1 7 64 0 8,
  link 75 0 1 786 0 6,
  link 787 0 1 92 0 1,
  link 787 1 7 80 0 8,
  link 91 0 1 788 0 6,
  link 789 0 1 108 0 1,
  link 789 1 7 96 0 8,
  link 107 0 1 790 0 6,
  link 791 0 1 124 0 1,
  link 791 1 7 112 0 8,
  link 123 0 1 800 0 6,
  link 801 0 1 140 0 1,
  link 801 1 7 128 0 8,
  link 139 0 1 802 0 6,
  link 803 0 1 156 0 1,
  link 803 1 7 144 0 8,
  link 155 0 1 804 0 6,
  link 805 0 1 172 0 1,
  link 805 1 7 160 0 8,
  link 171 0 1 806 0 6,
  link 807 0 1 188 0 1,
  link 807 1 7 176 0 8,
  link 187 0 1 816 0 6,
  link 817 0 1 204 0 1,
  link 817 1 7 192 0 8,
  link 203 0 1 818 0 6,
  link 819 0 1 220 0 1,
  link 819 1 7 208 0 8,
  link 219 0 1 820 0 6,
  link 821 0 1 236 0 1,
  link 821 1 7 224 0 8,
  link 235 0 1 822 0 6,
  link 823 0 1 252 0 1,
  link 823 1 7 240 0 8,
  link 251 0 1 832 0 6,
  link 833 0 1 268 0 1,
  link 833 1 7 256 0 8,
  link 267 0 1 834 0 6,
  link 835 0 1 284 0 1,
  link 835 1 7 272 0 8,
  link 283 0 1 836 0 6,
  link 837 0 1 300 0 1,
  link 837 1 7 288 0 8,
  link 299 0 1 838 0 6,
  link 839 0 1 316 0 1,
  link 839 1 7 304 0 8,
  link 315 0 1 848 0 6,
  link 849 0 1 332 0 1,
  link 849 1 7 320 0 8,
  link 331 0 1 850 0 6,
  link 851 0 1 348 0 1,
  link 851 1 7 336 0 8,
  link 347 0 1 852 0 6,
  link 853 0 1 364 0 1,
  link 853 1 7 352 0 8,
  link 363 0 1 854 0 6,
  link 855 0 1 380 0 1,
  link 855 1 7 368 0 8,
  link 44 1 9 864 0 10,
  link 492 0 9 868 0 10,
  link 864 0 10 870 0 9,
  link 866 0 10 870 1 11,
  link 868 0 10 871 0 11,
  link 870 0 12 871 1 9
]

def nativeCopyLinkCount : NativePaymentVariantV1 → Nat
  | .privateTransfer => 78
  | .withdrawal => 75

abbrev NativeCopyIndex (variant : NativePaymentVariantV1) :=
  Fin (nativeCopyLinkCount variant)

def nativeCompiledCopyLink (variant : NativePaymentVariantV1) :
    NativeCopyIndex variant → NativeCompiledCopyLink :=
  match variant with
  | .privateTransfer => privateTransferCopyLinks
  | .withdrawal => withdrawalCopyLinks

def nativeCopyTagBase : Nat := 1090519040

/-- `COPY_TAG_BASE + link.id`, exactly as frozen in both generated arrays. -/
def nativeCopyTag (variant : NativePaymentVariantV1)
    (index : NativeCopyIndex variant) : Nat :=
  nativeCopyTagBase + index.val

abbrev NativeCopyRowSlot := Fin 1024 × Fin 2

def nativeProducerRowSlot (variant : NativePaymentVariantV1)
    (index : NativeCopyIndex variant) : NativeCopyRowSlot :=
  let endpoint := (nativeCompiledCopyLink variant index).producer
  (endpoint.row, endpoint.slot)

def nativeConsumerRowSlot (variant : NativePaymentVariantV1)
    (index : NativeCopyIndex variant) : NativeCopyRowSlot :=
  let endpoint := (nativeCompiledCopyLink variant index).consumer
  (endpoint.row, endpoint.slot)

theorem nativeProducerRowSlot_injective (variant : NativePaymentVariantV1) :
    Function.Injective (nativeProducerRowSlot variant) := by
  cases variant <;> decide

theorem nativeConsumerRowSlot_injective (variant : NativePaymentVariantV1) :
    Function.Injective (nativeConsumerRowSlot variant) := by
  cases variant <;> decide

/- The generated active mask is exactly the union of rows occupied on either
side of the generated endpoint table. -/
set_option maxHeartbeats 1200000 in
-- Kernel evaluation of both complete generated tables over all 1,024 rows.
theorem compiledCopyRowActive_iff_endpoint
    (variant : NativePaymentVariantV1) (row : Fin 1024) :
    compiledCopyRowActive variant row ↔
      (∃ index, (nativeCompiledCopyLink variant index).producer.row = row) ∨
      ∃ index, (nativeCompiledCopyLink variant index).consumer.row = row := by
  revert row
  cases variant <;> decide

/-! ## The thirteen exact affine patterns -/

private def traceCell
    {K : Type*} [Zero K]
    (trace : Fin 1024 → Fin 16 → K) (row : Fin 1024) (column : Nat) : K :=
  if h : column < 16 then trace row ⟨column, h⟩ else 0

/-- Literal semantics of both checked-in 13-pattern arrays.  Pattern eight's
last active limb retains the generated M31 offset `1051521018`. -/
def nativePatternLimb
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (row : Fin 1024)
    (pattern : Fin 13) (limb : Fin 16) : K :=
  match pattern.val with
  | 0 => trace row limb
  | 1 => if limb.val < 8 then traceCell trace row limb.val else 0
  | 2 => if limb.val < 6 then traceCell trace row (2 + limb.val) else 0
  | 3 => if limb.val < 6 then traceCell trace row limb.val else 0
  | 4 => if limb.val < 2 then traceCell trace row limb.val else 0
  | 5 => if limb.val < 2 then traceCell trace row (6 + limb.val) else 0
  | 6 => if limb.val < 8 then traceCell trace row (1 + limb.val) else 0
  | 7 => if limb.val < 8 then traceCell trace row (8 + limb.val) else 0
  | 8 => if limb.val < 8 then
      traceCell trace row (8 + limb.val) +
        (if limb.val = 7 then (1051521018 : K) else 0)
    else 0
  | 9 => if limb.val = 0 then traceCell trace row 0 else 0
  | 10 => if limb.val = 0 then traceCell trace row 10 else 0
  | 11 => if limb.val = 0 then traceCell trace row 1 else 0
  | _ => if limb.val = 0 then traceCell trace row 2 else 0

structure NativeTaggedCopyTuple (K : Type*) where
  tag : Nat
  limbs : Fin 16 → K

def nativeEndpointTuple
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (tag : Nat)
    (source : NativeCompiledCopyEndpoint) : NativeTaggedCopyTuple K where
  tag := tag
  limbs := nativePatternLimb trace source.row source.pattern

def nativeProducerTuple
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (index : NativeCopyIndex variant) :
    NativeTaggedCopyTuple K :=
  nativeEndpointTuple trace (nativeCopyTag variant index)
    (nativeCompiledCopyLink variant index).producer

def nativeConsumerTuple
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (index : NativeCopyIndex variant) :
    NativeTaggedCopyTuple K :=
  nativeEndpointTuple trace (nativeCopyTag variant index)
    (nativeCompiledCopyLink variant index).consumer

/-- `tag + sum lambda^(limb + 1) * limb`, matching `pattern_values` plus the
tag addition in `copy_lane`. -/
noncomputable def nativeCompressTuple
    {K : Type*} [Field K] (lambda : K) (tuple : NativeTaggedCopyTuple K) : K :=
  (tuple.tag : K) + ∑ limb : Fin 16,
    lambda ^ (limb.val + 1) * tuple.limbs limb

noncomputable def nativeProducerValue
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda : K)
    (index : NativeCopyIndex variant) : K :=
  nativeCompressTuple lambda (nativeProducerTuple variant trace index)

noncomputable def nativeConsumerValue
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda : K)
    (index : NativeCopyIndex variant) : K :=
  nativeCompressTuple lambda (nativeConsumerTuple variant trace index)

/-! ## Exact two-slot Boolean row and helper algebra -/

noncomputable def nativeSlotValue
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (value : NativeCopyIndex variant → K) (target : NativeCopyRowSlot) : K :=
  ∑ index : NativeCopyIndex variant,
    if placement index = target then value index else 0

noncomputable def nativeSlotWeight
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (target : NativeCopyRowSlot) : K :=
  if ∃ index, placement index = target then 1 else 0

theorem nativeSlotValue_eq_of_placed
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (injective : Function.Injective placement)
    (value : NativeCopyIndex variant → K) (index : NativeCopyIndex variant) :
    nativeSlotValue placement value (placement index) = value index := by
  classical
  unfold nativeSlotValue
  rw [Finset.sum_eq_single index]
  · simp
  · intro other _ different
    have placementDifferent : placement other ≠ placement index := by
      exact fun equal => different (injective equal)
    simp [placementDifferent]
  · simp

theorem nativeSlotValue_eq_zero_of_unoccupied
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (value : NativeCopyIndex variant → K) (target : NativeCopyRowSlot)
    (empty : ∀ index, placement index ≠ target) :
    nativeSlotValue placement value target = 0 := by
  classical
  simp [nativeSlotValue, empty]

theorem nativeSlotWeight_eq_zero_of_unoccupied
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (target : NativeCopyRowSlot)
    (empty : ∀ index, placement index ≠ target) :
    nativeSlotWeight (K := K) placement target = 0 := by
  classical
  simp [nativeSlotWeight, empty]

structure NativeCompiledCopyRow (K : Type*) where
  producerValue : Fin 2 → K
  producerWeight : Fin 2 → K
  consumerValue : Fin 2 → K
  consumerWeight : Fin 2 → K

noncomputable def nativeCompiledCopyRows
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda : K)
    (row : Fin 1024) : NativeCompiledCopyRow K where
  producerValue := fun slot => nativeSlotValue
    (nativeProducerRowSlot variant)
    (nativeProducerValue variant trace lambda) (row, slot)
  producerWeight := fun slot => nativeSlotWeight
    (K := K) (nativeProducerRowSlot variant) (row, slot)
  consumerValue := fun slot => nativeSlotValue
    (nativeConsumerRowSlot variant)
    (nativeConsumerValue variant trace lambda) (row, slot)
  consumerWeight := fun slot => nativeSlotWeight
    (K := K) (nativeConsumerRowSlot variant) (row, slot)

/-- Algebraically identical to both `copy_residual` in the native terminal and
`copy_logup_residual` in the helper verifier. -/
def nativeCopyLocalResidual
    {K : Type*} [Field K]
    (row : NativeCompiledCopyRow K) (helper chi : K) : K :=
  let p0 := chi - row.producerValue 0
  let p1 := chi - row.producerValue 1
  let c0 := chi - row.consumerValue 0
  let c1 := chi - row.consumerValue 1
  helper * p0 * p1 * c0 * c1
    - row.producerWeight 0 * p1 * c0 * c1
    - row.producerWeight 1 * p0 * c0 * c1
    + row.consumerWeight 0 * p0 * p1 * c1
    + row.consumerWeight 1 * p0 * p1 * c0

noncomputable def nativeCopyRowRationalContribution
    {K : Type*} [Field K]
    (row : NativeCompiledCopyRow K) (chi : K) : K :=
  (∑ slot : Fin 2,
      row.producerWeight slot * (chi - row.producerValue slot)⁻¹) -
    ∑ slot : Fin 2,
      row.consumerWeight slot * (chi - row.consumerValue slot)⁻¹

/-- Boolean restriction of the production compiled copy lane. -/
noncomputable def nativeCompiledCopyLane
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K)
    (helper : Fin 1024 → K) (row : Fin 1024) : K :=
  if compiledCopyRowActive variant row then
    nativeCopyLocalResidual
      (nativeCompiledCopyRows variant trace lambda row) (helper row) chi
  else 0

noncomputable def nativeCopyRationalBalance
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K) : K :=
  (∑ index : NativeCopyIndex variant,
      (chi - nativeProducerValue variant trace lambda index)⁻¹) -
    ∑ index : NativeCopyIndex variant,
      (chi - nativeConsumerValue variant trace lambda index)⁻¹

def NativeCopyActivePole
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K) : Prop :=
  (∃ index, chi = nativeProducerValue variant trace lambda index) ∨
    ∃ index, chi = nativeConsumerValue variant trace lambda index

def NativeCopyInactiveSlotCollision {K : Type*} [Zero K] (chi : K) : Prop :=
  chi = 0

theorem helper_eq_nativeCopyRowRationalContribution_of_residual_zero
    {K : Type*} [Field K]
    (row : NativeCompiledCopyRow K) (helper chi : K)
    (p0 : chi - row.producerValue 0 ≠ 0)
    (p1 : chi - row.producerValue 1 ≠ 0)
    (c0 : chi - row.consumerValue 0 ≠ 0)
    (c1 : chi - row.consumerValue 1 ≠ 0)
    (residual : nativeCopyLocalResidual row helper chi = 0) :
    helper = nativeCopyRowRationalContribution row chi := by
  unfold nativeCopyRowRationalContribution
  simp only [Fin.sum_univ_two]
  field_simp [p0, p1, c0, c1]
  unfold nativeCopyLocalResidual at residual
  dsimp only at residual
  linear_combination residual

theorem nativeSlot_denominator_ne_zero
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (injective : Function.Injective placement)
    (value : NativeCopyIndex variant → K) (chi : K)
    (chiNonzero : chi ≠ 0) (noPole : ∀ index, chi ≠ value index)
    (target : NativeCopyRowSlot) :
    chi - nativeSlotValue placement value target ≠ 0 := by
  classical
  by_cases occupied : ∃ index, placement index = target
  · obtain ⟨index, placed⟩ := occupied
    have slotValueExact : nativeSlotValue placement value target = value index := by
      rw [← placed]
      exact nativeSlotValue_eq_of_placed placement injective value index
    rw [slotValueExact]
    exact sub_ne_zero.mpr (noPole index)
  · have empty : ∀ index, placement index ≠ target := by
      intro index equal
      exact occupied ⟨index, equal⟩
    rw [nativeSlotValue_eq_zero_of_unoccupied placement value target empty,
      sub_zero]
    exact chiNonzero

theorem native_row_denominators_ne_zero
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K)
    (chiNonzero : ¬ NativeCopyInactiveSlotCollision chi)
    (noPole : ¬ NativeCopyActivePole variant trace lambda chi)
    (row : Fin 1024) :
    (∀ slot,
      chi - (nativeCompiledCopyRows variant trace lambda row).producerValue slot ≠ 0) ∧
    ∀ slot,
      chi - (nativeCompiledCopyRows variant trace lambda row).consumerValue slot ≠ 0 := by
  have producerNoPole : ∀ index,
      chi ≠ nativeProducerValue variant trace lambda index := by
    intro index equal
    exact noPole (Or.inl ⟨index, equal⟩)
  have consumerNoPole : ∀ index,
      chi ≠ nativeConsumerValue variant trace lambda index := by
    intro index equal
    exact noPole (Or.inr ⟨index, equal⟩)
  constructor
  · intro slot
    exact nativeSlot_denominator_ne_zero (nativeProducerRowSlot variant)
      (nativeProducerRowSlot_injective variant)
      (nativeProducerValue variant trace lambda) chi chiNonzero
      producerNoPole (row, slot)
  · intro slot
    exact nativeSlot_denominator_ne_zero (nativeConsumerRowSlot variant)
      (nativeConsumerRowSlot_injective variant)
      (nativeConsumerValue variant trace lambda) chi chiNonzero
      consumerNoPole (row, slot)

theorem native_slot_rational_eq_link_sum
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (injective : Function.Injective placement)
    (value : NativeCopyIndex variant → K) (chi : K)
    (target : NativeCopyRowSlot) :
    nativeSlotWeight placement target *
        (chi - nativeSlotValue placement value target)⁻¹ =
      ∑ index : NativeCopyIndex variant,
        if placement index = target then (chi - value index)⁻¹ else 0 := by
  classical
  by_cases occupied : ∃ index, placement index = target
  · obtain ⟨index, placed⟩ := occupied
    have valueExact : nativeSlotValue placement value target = value index := by
      rw [← placed]
      exact nativeSlotValue_eq_of_placed placement injective value index
    have weightExact : nativeSlotWeight (K := K) placement target = 1 := by
      unfold nativeSlotWeight
      rw [if_pos ⟨index, placed⟩]
    rw [valueExact, weightExact, one_mul]
    symm
    rw [Finset.sum_eq_single index]
    · simp [placed]
    · intro other _ different
      have placementDifferent : placement other ≠ target := by
        intro equal
        exact different (injective (equal.trans placed.symm))
      simp [placementDifferent]
    · simp
  · have empty : ∀ index, placement index ≠ target := by
      intro index equal
      exact occupied ⟨index, equal⟩
    rw [nativeSlotWeight_eq_zero_of_unoccupied placement target empty]
    simp [empty]

theorem native_sum_slot_rational_eq_link_sum
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (injective : Function.Injective placement)
    (value : NativeCopyIndex variant → K) (chi : K) :
    (∑ target : NativeCopyRowSlot,
      nativeSlotWeight placement target *
        (chi - nativeSlotValue placement value target)⁻¹) =
      ∑ index : NativeCopyIndex variant, (chi - value index)⁻¹ := by
  classical
  simp_rw [native_slot_rational_eq_link_sum placement injective value chi]
  rw [Finset.sum_comm]
  simp

theorem tableSum_nativeCopyRowRationalContribution_eq_balance
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K) :
    tableSum (fun row => nativeCopyRowRationalContribution
      (nativeCompiledCopyRows variant trace lambda row) chi) =
      nativeCopyRationalBalance variant trace lambda chi := by
  classical
  unfold tableSum nativeCopyRowRationalContribution nativeCopyRationalBalance
  rw [Finset.sum_sub_distrib]
  have producerSum :
      (∑ row : Fin 1024, ∑ slot : Fin 2,
        nativeSlotWeight (nativeProducerRowSlot variant) (row, slot) *
          (chi - nativeSlotValue (nativeProducerRowSlot variant)
            (nativeProducerValue variant trace lambda) (row, slot))⁻¹) =
        ∑ index : NativeCopyIndex variant,
          (chi - nativeProducerValue variant trace lambda index)⁻¹ := by
    calc
      _ = ∑ target : NativeCopyRowSlot,
          nativeSlotWeight (nativeProducerRowSlot variant) target *
            (chi - nativeSlotValue (nativeProducerRowSlot variant)
              (nativeProducerValue variant trace lambda) target)⁻¹ := by
        simpa using (Fintype.sum_prod_type'
          (fun row : Fin 1024 => fun slot : Fin 2 =>
            nativeSlotWeight (nativeProducerRowSlot variant) (row, slot) *
              (chi - nativeSlotValue (nativeProducerRowSlot variant)
                (nativeProducerValue variant trace lambda) (row, slot))⁻¹)).symm
      _ = _ := native_sum_slot_rational_eq_link_sum
        (nativeProducerRowSlot variant)
        (nativeProducerRowSlot_injective variant)
        (nativeProducerValue variant trace lambda) chi
  have consumerSum :
      (∑ row : Fin 1024, ∑ slot : Fin 2,
        nativeSlotWeight (nativeConsumerRowSlot variant) (row, slot) *
          (chi - nativeSlotValue (nativeConsumerRowSlot variant)
            (nativeConsumerValue variant trace lambda) (row, slot))⁻¹) =
        ∑ index : NativeCopyIndex variant,
          (chi - nativeConsumerValue variant trace lambda index)⁻¹ := by
    calc
      _ = ∑ target : NativeCopyRowSlot,
          nativeSlotWeight (nativeConsumerRowSlot variant) target *
            (chi - nativeSlotValue (nativeConsumerRowSlot variant)
              (nativeConsumerValue variant trace lambda) target)⁻¹ := by
        simpa using (Fintype.sum_prod_type'
          (fun row : Fin 1024 => fun slot : Fin 2 =>
            nativeSlotWeight (nativeConsumerRowSlot variant) (row, slot) *
              (chi - nativeSlotValue (nativeConsumerRowSlot variant)
                (nativeConsumerValue variant trace lambda) (row, slot))⁻¹)).symm
      _ = _ := native_sum_slot_rational_eq_link_sum
        (nativeConsumerRowSlot variant)
        (nativeConsumerRowSlot_injective variant)
        (nativeConsumerValue variant trace lambda) chi
  change
    (∑ row : Fin 1024, ∑ slot : Fin 2,
      nativeSlotWeight (nativeProducerRowSlot variant) (row, slot) *
        (chi - nativeSlotValue (nativeProducerRowSlot variant)
          (nativeProducerValue variant trace lambda) (row, slot))⁻¹) -
      (∑ row : Fin 1024, ∑ slot : Fin 2,
        nativeSlotWeight (nativeConsumerRowSlot variant) (row, slot) *
          (chi - nativeSlotValue (nativeConsumerRowSlot variant)
            (nativeConsumerValue variant trace lambda) (row, slot))⁻¹) = _
  rw [producerSum, consumerSum]

noncomputable def nativeActiveHelperPart
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1) (helper : Fin 1024 → K)
    (row : Fin 1024) : K :=
  if compiledCopyRowActive variant row then helper row else 0

theorem native_helper_sum_eq_active_add_inactive
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1) (helper : Fin 1024 → K) :
    tableSum helper =
      tableSum (nativeActiveHelperPart variant helper) +
      tableSum (compiledInactiveHelperTable variant helper) := by
  classical
  unfold tableSum nativeActiveHelperPart compiledInactiveHelperTable
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  by_cases active : compiledCopyRowActive variant row <;> simp [active]

theorem native_active_helper_sum_zero_of_boundaries
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1) (helper : Fin 1024 → K)
    (totalZero : tableSum helper = 0)
    (inactiveZero : tableSum (compiledInactiveHelperTable variant helper) = 0) :
    tableSum (nativeActiveHelperPart variant helper) = 0 := by
  have partition := native_helper_sum_eq_active_add_inactive variant helper
  rw [totalZero, inactiveZero, add_zero] at partition
  exact partition.symm

theorem nativeCopyRowRationalContribution_zero_of_inactive
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K)
    (row : Fin 1024) (inactive : ¬ compiledCopyRowActive variant row) :
    nativeCopyRowRationalContribution
      (nativeCompiledCopyRows variant trace lambda row) chi = 0 := by
  classical
  have noProducer : ∀ index,
      nativeProducerRowSlot variant index ≠ (row, (0 : Fin 2)) := by
    intro index equal
    apply inactive
    rw [compiledCopyRowActive_iff_endpoint]
    exact Or.inl ⟨index, congrArg Prod.fst equal⟩
  have noProducer1 : ∀ index,
      nativeProducerRowSlot variant index ≠ (row, (1 : Fin 2)) := by
    intro index equal
    apply inactive
    rw [compiledCopyRowActive_iff_endpoint]
    exact Or.inl ⟨index, congrArg Prod.fst equal⟩
  have noConsumer : ∀ index,
      nativeConsumerRowSlot variant index ≠ (row, (0 : Fin 2)) := by
    intro index equal
    apply inactive
    rw [compiledCopyRowActive_iff_endpoint]
    exact Or.inr ⟨index, congrArg Prod.fst equal⟩
  have noConsumer1 : ∀ index,
      nativeConsumerRowSlot variant index ≠ (row, (1 : Fin 2)) := by
    intro index equal
    apply inactive
    rw [compiledCopyRowActive_iff_endpoint]
    exact Or.inr ⟨index, congrArg Prod.fst equal⟩
  unfold nativeCopyRowRationalContribution nativeCompiledCopyRows
  simp only [Fin.sum_univ_two]
  rw [nativeSlotWeight_eq_zero_of_unoccupied
      (nativeProducerRowSlot variant) (row, 0) noProducer,
    nativeSlotWeight_eq_zero_of_unoccupied
      (nativeProducerRowSlot variant) (row, 1) noProducer1,
    nativeSlotWeight_eq_zero_of_unoccupied
      (nativeConsumerRowSlot variant) (row, 0) noConsumer,
    nativeSlotWeight_eq_zero_of_unoccupied
      (nativeConsumerRowSlot variant) (row, 1) noConsumer1]
  ring

/-- Exact helper-total closure immediately downstream of randomized
extraction.  Inactive helper cells may be arbitrary; only their authenticated
sum is used. -/
theorem native_copy_rational_balance_zero_of_local_residuals
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K)
    (helper : Fin 1024 → K)
    (localZero : ∀ row,
      nativeCompiledCopyLane variant trace lambda chi helper row = 0)
    (helperSumZero : tableSum helper = 0)
    (inactiveSumZero :
      tableSum (compiledInactiveHelperTable variant helper) = 0)
    (chiNonzero : ¬ NativeCopyInactiveSlotCollision chi)
    (noPole : ¬ NativeCopyActivePole variant trace lambda chi) :
    nativeCopyRationalBalance variant trace lambda chi = 0 := by
  classical
  have activePointwise : ∀ row,
      nativeActiveHelperPart variant helper row =
        nativeCopyRowRationalContribution
          (nativeCompiledCopyRows variant trace lambda row) chi := by
    intro row
    by_cases active : compiledCopyRowActive variant row
    · have residualZero : nativeCopyLocalResidual
          (nativeCompiledCopyRows variant trace lambda row) (helper row) chi = 0 := by
        simpa [nativeCompiledCopyLane, active] using localZero row
      have denominators := native_row_denominators_ne_zero variant trace lambda
        chi chiNonzero noPole row
      have helperExact :=
        helper_eq_nativeCopyRowRationalContribution_of_residual_zero
          (nativeCompiledCopyRows variant trace lambda row) (helper row) chi
          (denominators.1 0) (denominators.1 1)
          (denominators.2 0) (denominators.2 1) residualZero
      simpa [nativeActiveHelperPart, active] using helperExact
    · rw [nativeCopyRowRationalContribution_zero_of_inactive variant trace
        lambda chi row active]
      simp [nativeActiveHelperPart, active]
  have activeSumZero := native_active_helper_sum_zero_of_boundaries variant
    helper helperSumZero inactiveSumZero
  rw [← tableSum_nativeCopyRowRationalContribution_eq_balance variant trace
    lambda chi]
  calc
    tableSum (fun row => nativeCopyRowRationalContribution
        (nativeCompiledCopyRows variant trace lambda row) chi) =
      tableSum (nativeActiveHelperPart variant helper) := by
        unfold tableSum
        apply Finset.sum_congr rfl
        intro row _
        exact (activePointwise row).symm
    _ = 0 := activeSumZero

/-- Direct consumer of the coefficient conclusion extracted from the sampled
`mu` aggregate. -/
theorem native_copy_rational_balance_zero_of_accepted_terminal
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (variant : NativePaymentVariantV1)
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi theta : K)
    (point : Fin 10 → K) (mu : K) (helper : Fin 1024 → K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      (nativeTotalHelperSum helper)
      (tableSum (compiledInactiveHelperTable variant helper)))
    (noMu : ¬ NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point)
      (nativeTotalHelperSum helper)
      (tableSum (compiledInactiveHelperTable variant helper)) mu)
    (noZerocheck : ¬ NativeZerocheckEvaluationCollision basis rows theta point)
    (noTheta : ¬ NativeThetaLaneCollision basis rows theta)
    (copyExact : ∀ row,
      (rows row).copy = nativeCompiledCopyLane variant trace lambda chi helper row)
    (chiNonzero : ¬ NativeCopyInactiveSlotCollision chi)
    (noPole : ¬ NativeCopyActivePole variant trace lambda chi) :
    nativeCopyRationalBalance variant trace lambda chi = 0 := by
  have extracted := native_rows_vanish_of_accepted_randomized_terminal basis
    rows theta point mu (nativeTotalHelperSum helper)
    (tableSum (compiledInactiveHelperTable variant helper)) accepted noMu
    noZerocheck noTheta
  apply native_copy_rational_balance_zero_of_local_residuals variant trace
    lambda chi helper
  · intro row
    rw [← copyExact row]
    exact extracted.1.copy row
  · exact extracted.2.1
  · exact extracted.2.2
  · exact chiNonzero
  · exact noPole

/-! ## Collision-explicit scalar endpoint isolation -/

noncomputable def nativeProducerTaggedMultiset
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) : Multiset (NativeTaggedCopyTuple K) :=
  (Finset.univ : Finset (NativeCopyIndex variant)).1.map
    (nativeProducerTuple variant trace)

noncomputable def nativeConsumerTaggedMultiset
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) : Multiset (NativeTaggedCopyTuple K) :=
  (Finset.univ : Finset (NativeCopyIndex variant)).1.map
    (nativeConsumerTuple variant trace)

noncomputable def nativeProducerCompressedMultiset
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda : K) : Multiset K :=
  (Finset.univ : Finset (NativeCopyIndex variant)).1.map
    (nativeProducerValue variant trace lambda)

noncomputable def nativeConsumerCompressedMultiset
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda : K) : Multiset K :=
  (Finset.univ : Finset (NativeCopyIndex variant)).1.map
    (nativeConsumerValue variant trace lambda)

def NativeCopyChiCollision
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K) : Prop :=
  nativeCopyRationalBalance variant trace lambda chi = 0 ∧
    nativeProducerCompressedMultiset variant trace lambda ≠
      nativeConsumerCompressedMultiset variant trace lambda

def NativeCopyTupleCompressionCollision
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda : K) : Prop :=
  nativeProducerCompressedMultiset variant trace lambda =
      nativeConsumerCompressedMultiset variant trace lambda ∧
    nativeProducerTaggedMultiset variant trace ≠
      nativeConsumerTaggedMultiset variant trace

theorem nativeCopyTag_injective (variant : NativePaymentVariantV1) :
    Function.Injective (nativeCopyTag variant) := by
  intro left right equal
  apply Fin.ext
  simp [nativeCopyTag] at equal
  omega

theorem native_all_link_tuples_equal_outside_collisions
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (lambda chi : K)
    (balance : nativeCopyRationalBalance variant trace lambda chi = 0)
    (noChiCollision : ¬ NativeCopyChiCollision variant trace lambda chi)
    (noCompressionCollision :
      ¬ NativeCopyTupleCompressionCollision variant trace lambda) :
    ∀ index, nativeProducerTuple variant trace index =
      nativeConsumerTuple variant trace index := by
  classical
  have compressedEqual : nativeProducerCompressedMultiset variant trace lambda =
      nativeConsumerCompressedMultiset variant trace lambda := by
    by_contra different
    exact noChiCollision ⟨balance, different⟩
  have taggedEqual : nativeProducerTaggedMultiset variant trace =
      nativeConsumerTaggedMultiset variant trace := by
    by_contra different
    exact noCompressionCollision ⟨compressedEqual, different⟩
  intro index
  have producerMember : nativeProducerTuple variant trace index ∈
      nativeProducerTaggedMultiset variant trace := by
    simp [nativeProducerTaggedMultiset]
  rw [taggedEqual] at producerMember
  simp only [nativeConsumerTaggedMultiset, Multiset.mem_map] at producerMember
  obtain ⟨other, _, tupleEqual⟩ := producerMember
  have tagEqual : nativeCopyTag variant other = nativeCopyTag variant index := by
    calc
      nativeCopyTag variant other =
          (nativeConsumerTuple variant trace other).tag := by
        rfl
      _ = (nativeProducerTuple variant trace index).tag := by
        exact congrArg NativeTaggedCopyTuple.tag tupleEqual
      _ = nativeCopyTag variant index := by
        rfl
  have indexEqual := nativeCopyTag_injective variant tagEqual
  subst other
  exact tupleEqual.symm

def nativeFieldTrace
    {K : Type*} (fieldCell : CellAddress → K) : Fin 1024 → Fin 16 → K :=
  fun row column => fieldCell ⟨row.val, column.val⟩

structure NativeCommonFieldEndpointEquations
    {K : Type*} (fieldCell : CellAddress → K) : Prop where
  inputSource : fieldCell inputValueCell = fieldCell (valueAuxSourceCell 0)
  changeSource : fieldCell changeValueCell = fieldCell (valueAuxSourceCell 2)
  conservationInput : fieldCell (valueAuxSourceCell 0) =
    fieldCell conservationInputCell
  conservationRecipientOrAmount : fieldCell (valueAuxSourceCell 1) =
    fieldCell conservationRecipientOrAmountCell
  conservationChange : fieldCell (valueAuxSourceCell 2) =
    fieldCell conservationChangeCell
  conservationPartial : fieldCell conservationPartialCell =
    fieldCell conservationCarriedPartialCell

structure NativePrivateTransferFieldEndpointEquations
    {K : Type*} (fieldCell : CellAddress → K) : Prop where
  common : NativeCommonFieldEndpointEquations fieldCell
  recipientSource : fieldCell recipientValueCell =
    fieldCell (valueAuxSourceCell 1)

theorem native_private_transfer_field_endpoints_of_all_link_tuples_equal
    {K : Type*} [Field K] (fieldCell : CellAddress → K)
    (allEqual : ∀ index : Fin 78,
      nativeProducerTuple .privateTransfer (nativeFieldTrace fieldCell) index =
        nativeConsumerTuple .privateTransfer (nativeFieldTrace fieldCell) index) :
    NativePrivateTransferFieldEndpointEquations fieldCell := by
  have limbEqual (index : Fin 78) := congrArg
    (fun tuple : NativeTaggedCopyTuple K => tuple.limbs 0) (allEqual index)
  refine { common := ?_, recipientSource := ?_ }
  · refine {
      inputSource := ?_
      changeSource := ?_
      conservationInput := ?_
      conservationRecipientOrAmount := ?_
      conservationChange := ?_
      conservationPartial := ?_ }
    · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
        nativeCompiledCopyLink, privateTransferCopyLinks, link, endpoint,
        nativePatternLimb,
        traceCell, nativeFieldTrace, inputValueCell, valueAuxSourceCell,
        valueAuxBaseRows] using limbEqual (71 : Fin 78)
    · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
        nativeCompiledCopyLink, privateTransferCopyLinks, link, endpoint,
        nativePatternLimb,
        traceCell, nativeFieldTrace, changeValueCell, valueAuxSourceCell,
        valueAuxBaseRows] using limbEqual (73 : Fin 78)
    · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
        nativeCompiledCopyLink, privateTransferCopyLinks, link, endpoint,
        nativePatternLimb,
        traceCell, nativeFieldTrace, conservationInputCell,
        valueAuxSourceCell, valueAuxBaseRows] using limbEqual (74 : Fin 78)
    · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
        nativeCompiledCopyLink, privateTransferCopyLinks, link, endpoint,
        nativePatternLimb,
        traceCell, nativeFieldTrace, conservationRecipientOrAmountCell,
        valueAuxSourceCell, valueAuxBaseRows] using limbEqual (75 : Fin 78)
    · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
        nativeCompiledCopyLink, privateTransferCopyLinks, link, endpoint,
        nativePatternLimb,
        traceCell, nativeFieldTrace, conservationChangeCell,
        valueAuxSourceCell, valueAuxBaseRows] using limbEqual (76 : Fin 78)
    · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
        nativeCompiledCopyLink, privateTransferCopyLinks, link, endpoint,
        nativePatternLimb,
        traceCell, nativeFieldTrace, conservationPartialCell,
        conservationCarriedPartialCell] using limbEqual (77 : Fin 78)
  · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
      nativeCompiledCopyLink, privateTransferCopyLinks, link, endpoint,
      nativePatternLimb,
      traceCell, nativeFieldTrace, recipientValueCell, valueAuxSourceCell,
      valueAuxBaseRows] using limbEqual (72 : Fin 78)

theorem native_withdrawal_field_endpoints_of_all_link_tuples_equal
    {K : Type*} [Field K] (fieldCell : CellAddress → K)
    (allEqual : ∀ index : Fin 75,
      nativeProducerTuple .withdrawal (nativeFieldTrace fieldCell) index =
        nativeConsumerTuple .withdrawal (nativeFieldTrace fieldCell) index) :
    NativeCommonFieldEndpointEquations fieldCell := by
  have limbEqual (index : Fin 75) := congrArg
    (fun tuple : NativeTaggedCopyTuple K => tuple.limbs 0) (allEqual index)
  refine {
    inputSource := ?_
    changeSource := ?_
    conservationInput := ?_
    conservationRecipientOrAmount := ?_
    conservationChange := ?_
    conservationPartial := ?_ }
  · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
      nativeCompiledCopyLink, withdrawalCopyLinks, link, endpoint,
      nativePatternLimb,
      traceCell, nativeFieldTrace, inputValueCell, valueAuxSourceCell,
      valueAuxBaseRows] using limbEqual (69 : Fin 75)
  · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
      nativeCompiledCopyLink, withdrawalCopyLinks, link, endpoint,
      nativePatternLimb,
      traceCell, nativeFieldTrace, changeValueCell, valueAuxSourceCell,
      valueAuxBaseRows] using limbEqual (70 : Fin 75)
  · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
      nativeCompiledCopyLink, withdrawalCopyLinks, link, endpoint,
      nativePatternLimb,
      traceCell, nativeFieldTrace, conservationInputCell, valueAuxSourceCell,
      valueAuxBaseRows] using limbEqual (71 : Fin 75)
  · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
      nativeCompiledCopyLink, withdrawalCopyLinks, link, endpoint,
      nativePatternLimb,
      traceCell, nativeFieldTrace, conservationRecipientOrAmountCell,
      valueAuxSourceCell, valueAuxBaseRows] using limbEqual (72 : Fin 75)
  · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
      nativeCompiledCopyLink, withdrawalCopyLinks, link, endpoint,
      nativePatternLimb,
      traceCell, nativeFieldTrace, conservationChangeCell, valueAuxSourceCell,
      valueAuxBaseRows] using limbEqual (73 : Fin 75)
  · simpa [nativeProducerTuple, nativeConsumerTuple, nativeEndpointTuple,
      nativeCompiledCopyLink, withdrawalCopyLinks, link, endpoint,
      nativePatternLimb,
      traceCell, nativeFieldTrace, conservationPartialCell,
      conservationCarriedPartialCell] using limbEqual (74 : Fin 75)

theorem native_private_transfer_field_endpoints_of_logup
    {K : Type*} [Field K] (fieldCell : CellAddress → K) (lambda chi : K)
    (balance : nativeCopyRationalBalance .privateTransfer
      (nativeFieldTrace fieldCell) lambda chi = 0)
    (noChiCollision : ¬ NativeCopyChiCollision .privateTransfer
      (nativeFieldTrace fieldCell) lambda chi)
    (noCompressionCollision : ¬ NativeCopyTupleCompressionCollision
      .privateTransfer (nativeFieldTrace fieldCell) lambda) :
    NativePrivateTransferFieldEndpointEquations fieldCell := by
  apply native_private_transfer_field_endpoints_of_all_link_tuples_equal
  exact native_all_link_tuples_equal_outside_collisions .privateTransfer
    (nativeFieldTrace fieldCell) lambda chi balance noChiCollision
    noCompressionCollision

theorem native_withdrawal_field_endpoints_of_logup
    {K : Type*} [Field K] (fieldCell : CellAddress → K) (lambda chi : K)
    (balance : nativeCopyRationalBalance .withdrawal
      (nativeFieldTrace fieldCell) lambda chi = 0)
    (noChiCollision : ¬ NativeCopyChiCollision .withdrawal
      (nativeFieldTrace fieldCell) lambda chi)
    (noCompressionCollision : ¬ NativeCopyTupleCompressionCollision
      .withdrawal (nativeFieldTrace fieldCell) lambda) :
    NativeCommonFieldEndpointEquations fieldCell := by
  apply native_withdrawal_field_endpoints_of_all_link_tuples_equal
  exact native_all_link_tuples_equal_outside_collisions .withdrawal
    (nativeFieldTrace fieldCell) lambda chi balance noChiCollision
    noCompressionCollision

/-! ## Typed Nat-cell projection boundary -/

/-- Exact, conclusion-independent binding between authenticated field cells
and the typed Nat projection.  Injectivity is isolated here because it belongs
to the still-separate M31/subfield recovery bridge, not to LogUp algebra. -/
structure NativeNatCellBinding
    {K : Type*} {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (fieldCell : CellAddress → K) where
  encode : Nat → K
  encodeInjective : Function.Injective encode
  cellExact : ∀ address, fieldCell address = encode (trace.natCell address)

theorem common_logup_endpoints_of_field_binding
    {K : Type*} {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (fieldCell : CellAddress → K)
    (binding : NativeNatCellBinding trace fieldCell)
    (field : NativeCommonFieldEndpointEquations fieldCell) :
    CommonLogUpEndpointEquations trace := by
  have liftEqual {left right : CellAddress}
      (equal : fieldCell left = fieldCell right) :
      trace.natCell left = trace.natCell right := by
    apply binding.encodeInjective
    calc
      binding.encode (trace.natCell left) = fieldCell left :=
        (binding.cellExact left).symm
      _ = fieldCell right := equal
      _ = binding.encode (trace.natCell right) := binding.cellExact right
  exact {
    inputSource := liftEqual field.inputSource
    changeSource := liftEqual field.changeSource
    conservationInput := liftEqual field.conservationInput
    conservationRecipientOrAmount :=
      liftEqual field.conservationRecipientOrAmount
    conservationChange := liftEqual field.conservationChange
    conservationPartial := liftEqual field.conservationPartial }

theorem private_transfer_logup_endpoints_of_field_binding
    {K : Type*} {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (fieldCell : CellAddress → K)
    (binding : NativeNatCellBinding trace fieldCell)
    (field : NativePrivateTransferFieldEndpointEquations fieldCell) :
    PrivateTransferLogUpEndpointEquations trace := by
  have recipient : trace.natCell recipientValueCell =
      trace.natCell (valueAuxSourceCell 1) := by
    apply binding.encodeInjective
    calc
      binding.encode (trace.natCell recipientValueCell) =
          fieldCell recipientValueCell :=
        (binding.cellExact recipientValueCell).symm
      _ = fieldCell (valueAuxSourceCell 1) := field.recipientSource
      _ = binding.encode (trace.natCell (valueAuxSourceCell 1)) :=
        binding.cellExact (valueAuxSourceCell 1)
  exact {
    common := common_logup_endpoints_of_field_binding trace fieldCell binding
      field.common
    recipientSource := recipient }

#print axioms nativeProducerRowSlot_injective
#print axioms nativeConsumerRowSlot_injective
#print axioms compiledCopyRowActive_iff_endpoint
#print axioms helper_eq_nativeCopyRowRationalContribution_of_residual_zero
#print axioms tableSum_nativeCopyRowRationalContribution_eq_balance
#print axioms native_copy_rational_balance_zero_of_local_residuals
#print axioms native_copy_rational_balance_zero_of_accepted_terminal
#print axioms native_all_link_tuples_equal_outside_collisions
#print axioms native_private_transfer_field_endpoints_of_logup
#print axioms native_withdrawal_field_endpoints_of_logup
#print axioms common_logup_endpoints_of_field_binding
#print axioms private_transfer_logup_endpoints_of_field_binding

end AspisPool.NativePaymentCompiledCopyLogUpV1
