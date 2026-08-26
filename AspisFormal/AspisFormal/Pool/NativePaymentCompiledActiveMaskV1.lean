import AspisFormal.Pool.NativePaymentMaskedTerminalBridgeV1
import AspisFormal.V5ProductionRowSelector

/-!
# Native Pool V1 compiled Copy-active masks

This module closes the variant-specific active-row-table part of the native
Tag-73 terminal boundary.  It pins both checked-in `[u16; 64]` tables, models
the exact `row >> 4` / `row & 15` lookup, and proves that the production
64-by-16 selector factorization evaluates their multilinear active indicator.

The resulting field-valued Boolean indicator is connected directly to the
`mu^2 * (1 - copyActive) * H1` term in
`NativePaymentMaskedTerminalBridgeV1`.  Equality between the optimized Rust
loops and the source-shaped high/low sums below remains a small executable
source-refinement seam; no semantic-terminal conclusion is assumed here.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.NativePaymentCompiledActiveMaskV1

open AspisPool.NativePaymentMaskedTerminalBridgeV1
open AspisPool.NativePaymentRandomizedExtractionV1
open AspisSumcheckMasking
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ProductionRowSelector
open Module

inductive NativePaymentVariantV1
  | privateTransfer
  | withdrawal
  deriving DecidableEq

/-! ## Literal generated tables -/

/-- Exact decimal spelling of `PRIVATE_TRANSFER_ACTIVE_ROW_MASKS`. -/
def privateTransferActiveRowMasks : Fin 64 → Nat := ![
  6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 6145, 6145, 4097,
  6144, 4097, 2048, 6145, 1, 2048, 6145, 1,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 255, 255, 255, 255, 255, 213, 0,
  0, 0, 0, 0, 0, 0, 0, 0
]

/-- Exact decimal spelling of `WITHDRAWAL_ACTIVE_ROW_MASKS`. -/
def withdrawalActiveRowMasks : Fin 64 → Nat := ![
  6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 6145, 6145, 4097,
  6144, 4097, 0, 0, 0, 2048, 6145, 1,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 255, 255, 255, 255, 255, 213, 0,
  0, 0, 0, 0, 0, 0, 0, 0
]

def compiledActiveRowMasks : NativePaymentVariantV1 → Fin 64 → Nat
  | .privateTransfer => privateTransferActiveRowMasks
  | .withdrawal => withdrawalActiveRowMasks

theorem compiled_active_masks_fit_u16
    (variant : NativePaymentVariantV1) (block : Fin 64) :
    compiledActiveRowMasks variant block < 2 ^ 16 := by
  cases variant <;> fin_cases block <;> decide

/-! ## Exact block/bit row lookup -/

def rowBlock (row : Fin 1024) : Fin 64 :=
  ⟨row.val / 16, by omega⟩

def rowLocal (row : Fin 1024) : Fin 16 :=
  ⟨row.val % 16, Nat.mod_lt _ (by omega)⟩

def rowOfBlockLocal (block : Fin 64) (slot : Fin 16) : Fin 1024 :=
  finProdFinEquiv (block, slot)

@[simp] theorem rowOfBlockLocal_val (block : Fin 64) (slot : Fin 16) :
    (rowOfBlockLocal block slot).val = slot.val + 16 * block.val := by
  rfl

@[simp] theorem rowBlock_rowOfBlockLocal
    (block : Fin 64) (slot : Fin 16) :
    rowBlock (rowOfBlockLocal block slot) = block := by
  apply Fin.ext
  change (slot.val + 16 * block.val) / 16 = block.val
  omega

@[simp] theorem rowLocal_rowOfBlockLocal
    (block : Fin 64) (slot : Fin 16) :
    rowLocal (rowOfBlockLocal block slot) = slot := by
  apply Fin.ext
  change (slot.val + 16 * block.val) % 16 = slot.val
  omega

/-- Literal Boolean semantics of
`masks[row >> 4] & (1 << (row & 15)) != 0`. -/
def compiledCopyRowActive
    (variant : NativePaymentVariantV1) (row : Fin 1024) : Bool :=
  Nat.testBit (compiledActiveRowMasks variant (rowBlock row)) (rowLocal row).val

@[simp] theorem compiledCopyRowActive_rowOfBlockLocal
    (variant : NativePaymentVariantV1) (block : Fin 64) (slot : Fin 16) :
    compiledCopyRowActive variant (rowOfBlockLocal block slot) =
      Nat.testBit (compiledActiveRowMasks variant block) slot.val := by
  simp [compiledCopyRowActive]

def compiledActiveRows (variant : NativePaymentVariantV1) :
    Finset (Fin 1024) :=
  Finset.univ.filter fun row => compiledCopyRowActive variant row

/-- The two generated tables contain exactly 128 and 123 active rows. -/
theorem private_transfer_active_row_count :
    (compiledActiveRows .privateTransfer).card = 128 := by
  decide

theorem withdrawal_active_row_count :
    (compiledActiveRows .withdrawal).card = 123 := by
  decide

/-- The transfer registry has exactly five active rows absent from withdrawal;
withdrawal has no active row absent from transfer. -/
def transferOnlyActiveRows : Finset (Fin 1024) :=
  {⟨427, by omega⟩, ⟨432, by omega⟩, ⟨443, by omega⟩,
    ⟨444, by omega⟩, ⟨448, by omega⟩}

theorem exact_variant_active_row_difference :
    compiledActiveRows .privateTransfer \ compiledActiveRows .withdrawal =
        transferOnlyActiveRows ∧
      compiledActiveRows .withdrawal \ compiledActiveRows .privateTransfer = ∅ := by
  decide

/-! ## Source-shaped 64-by-16 selector evaluator -/

noncomputable def compiledHighWeight
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (block : Fin 64) : K :=
  ∏ coordinate : Fin 6,
    if Nat.testBit block.val (5 - coordinate.val) then
      point ⟨coordinate.val, by omega⟩
    else 1 - point ⟨coordinate.val, by omega⟩

noncomputable def compiledLowWeight
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (slot : Fin 16) : K :=
  ∏ coordinate : Fin 4,
    if Nat.testBit slot.val (3 - coordinate.val) then
      point ⟨6 + coordinate.val, by omega⟩
    else 1 - point ⟨6 + coordinate.val, by omega⟩

theorem sourceHighWeight_rowOfBlockLocal
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (block : Fin 64) (slot : Fin 16) :
    sourceHighWeight point (rowOfBlockLocal block slot) =
      compiledHighWeight point block := by
  have hdiv : (slot.val + 16 * block.val) / 16 = block.val := by
    omega
  simp [sourceHighWeight, compiledHighWeight, rowOfBlockLocal,
    finProdFinEquiv, hdiv]

theorem sourceLowWeight_rowOfBlockLocal
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (block : Fin 64) (slot : Fin 16) :
    sourceLowWeight point (rowOfBlockLocal block slot) =
      compiledLowWeight point slot := by
  have hmod : (slot.val + 16 * block.val) % 16 = slot.val := by
    omega
  simp [sourceLowWeight, compiledLowWeight, rowOfBlockLocal,
    finProdFinEquiv, hmod]

theorem factoredSourceRowSelector_rowOfBlockLocal
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (block : Fin 64) (slot : Fin 16) :
    factoredSourceRowSelector point (rowOfBlockLocal block slot) =
      compiledHighWeight point block * compiledLowWeight point slot := by
  rw [factoredSourceRowSelector, sourceHighWeight_rowOfBlockLocal,
    sourceLowWeight_rowOfBlockLocal]

/-- Mathematical result of `selector_mask_sum_16` for one block. -/
noncomputable def compiledSelectorMaskSum16
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (point : TerminalPoint K)
    (block : Fin 64) : K :=
  ∑ slot : Fin 16,
    if Nat.testBit (compiledActiveRowMasks variant block) slot.val then
      compiledLowWeight point slot
    else 0

/-- Exact high-table/low-mask sum computed by `Selectors::copy_active`, after
the complement optimization inside `selector_mask_sum_16` is interpreted as
its selected-weight sum. -/
noncomputable def compiledCopyActiveAtPoint
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (point : TerminalPoint K) : K :=
  ∑ block : Fin 64,
    compiledHighWeight point block *
      compiledSelectorMaskSum16 variant point block

/-- Expanded active-row selector MLE used by the host reference evaluator. -/
noncomputable def expandedCopyActiveAtPoint
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (point : TerminalPoint K) : K :=
  ∑ row : Fin 1024,
    if compiledCopyRowActive variant row then
      factoredSourceRowSelector point row
    else 0

/-- The generated 64-by-16 mask evaluator is exactly the ordinary sum of
active physical-row equality selectors, at every point. -/
theorem compiledCopyActiveAtPoint_eq_expanded
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (point : TerminalPoint K) :
    compiledCopyActiveAtPoint variant point =
      expandedCopyActiveAtPoint variant point := by
  classical
  unfold compiledCopyActiveAtPoint compiledSelectorMaskSum16
    expandedCopyActiveAtPoint
  calc
    (∑ block : Fin 64,
        compiledHighWeight point block *
          ∑ slot : Fin 16,
            if Nat.testBit (compiledActiveRowMasks variant block) slot.val then
              compiledLowWeight point slot else 0) =
        ∑ block : Fin 64, ∑ slot : Fin 16,
          if Nat.testBit (compiledActiveRowMasks variant block) slot.val then
            compiledHighWeight point block * compiledLowWeight point slot
          else 0 := by
            apply Finset.sum_congr rfl
            intro block _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro slot _
            by_cases active :
                Nat.testBit (compiledActiveRowMasks variant block) slot.val
            · simp [active]
            · simp [active]
    _ = ∑ pair : Fin 64 × Fin 16,
          if compiledCopyRowActive variant (rowOfBlockLocal pair.1 pair.2) then
            factoredSourceRowSelector point
              (rowOfBlockLocal pair.1 pair.2)
          else 0 := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro block _
            apply Finset.sum_congr rfl
            intro slot _
            rw [compiledCopyRowActive_rowOfBlockLocal,
              factoredSourceRowSelector_rowOfBlockLocal]
    _ = ∑ row : Fin 1024,
          if compiledCopyRowActive variant row then
            factoredSourceRowSelector point row
          else 0 :=
      (finProdFinEquiv : Fin 64 × Fin 16 ≃ Fin 1024).sum_comp
        (fun row => if compiledCopyRowActive variant row then
          factoredSourceRowSelector point row else 0)

/-- Field-valued Boolean row activity supplied to the native terminal table. -/
def compiledCopyActiveField
    {K : Type*} [Zero K] [One K]
    (variant : NativePaymentVariantV1) (row : Fin 1024) : K :=
  if compiledCopyRowActive variant row then 1 else 0

/-- At a Boolean trace point the exact compiled evaluator is its pinned table
bit, embedded as zero or one in the field. -/
theorem compiledCopyActiveAtPoint_booleanPoint
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (selected : Fin 1024) :
    compiledCopyActiveAtPoint variant (booleanPointOfRow (F := K) selected) =
      compiledCopyActiveField variant selected := by
  rw [compiledCopyActiveAtPoint_eq_expanded]
  classical
  unfold expandedCopyActiveAtPoint compiledCopyActiveField
  simp_rw [factoredSourceRowSelector_at_booleanPoint]
  rw [Finset.sum_eq_single selected]
  · simp
  · intro row _ rowNe
    simp [rowNe]
  · simp

/-! ## Specialization of the strengthened terminal -/

noncomputable def compiledInactiveHelperTable
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1) (helper : Fin 1024 → K) :
    Fin 1024 → K := fun row =>
  if compiledCopyRowActive variant row then 0 else helper row

theorem nativeInactiveHelperSum_compiled
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1) (helper : Fin 1024 → K) :
    nativeInactiveHelperSum (compiledCopyActiveField variant) helper =
      tableSum (compiledInactiveHelperTable variant helper) := by
  classical
  unfold nativeInactiveHelperSum tableSum compiledInactiveHelperTable
    compiledCopyActiveField
  apply Finset.sum_congr rfl
  intro row _
  by_cases active : compiledCopyRowActive variant row
  · simp [active]
  · simp [active]

noncomputable def compiledStrengthenedUnmaskedTerminalTable
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (variant : NativePaymentVariantV1)
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu : K)
    (helper : Fin 1024 → K) : Fin 1024 → K :=
  nativeStrengthenedUnmaskedTerminalTable basis rows theta zerocheckPoint mu
    (compiledCopyActiveField variant) helper

/-- The exact variant-specific compiled table produces the aggregate consumed
by randomized extraction, with no abstract `copyActive` function remaining. -/
theorem tableSum_compiledStrengthenedUnmaskedTerminalTable
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (variant : NativePaymentVariantV1)
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu : K)
    (helper : Fin 1024 → K) :
    tableSum (compiledStrengthenedUnmaskedTerminalTable variant basis rows
      theta zerocheckPoint mu helper) =
      nativeConstraintMLE basis rows theta zerocheckPoint +
        mu * nativeTotalHelperSum helper +
        mu ^ 2 * tableSum (compiledInactiveHelperTable variant helper) := by
  rw [compiledStrengthenedUnmaskedTerminalTable,
    tableSum_nativeStrengthenedUnmaskedTerminalTable,
    nativeInactiveHelperSum_compiled]

/-- An extracted masked boundary for either exact compiled variant constructs
the precise randomized-terminal aggregate with that variant's inactive-helper
sum. -/
theorem native_accepted_randomized_terminal_of_compiled_masked_boundary
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (variant : NativePaymentVariantV1)
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu eta : K)
    (helper mask : Fin 1024 → K)
    (boundary : ExtractedMaskedSumcheckBoundary eta
      (compiledStrengthenedUnmaskedTerminalTable variant basis rows theta
        zerocheckPoint mu helper) mask) :
    NativeAcceptedRandomizedTerminal basis rows theta zerocheckPoint mu
      (nativeTotalHelperSum helper)
      (tableSum (compiledInactiveHelperTable variant helper)) := by
  have accepted := native_accepted_randomized_terminal_of_masked_boundary
    basis rows theta zerocheckPoint mu eta (compiledCopyActiveField variant)
    helper mask boundary
  rwa [nativeInactiveHelperSum_compiled] at accepted

#print axioms compiled_active_masks_fit_u16
#print axioms private_transfer_active_row_count
#print axioms withdrawal_active_row_count
#print axioms exact_variant_active_row_difference
#print axioms compiledCopyActiveAtPoint_eq_expanded
#print axioms compiledCopyActiveAtPoint_booleanPoint
#print axioms nativeInactiveHelperSum_compiled
#print axioms tableSum_compiledStrengthenedUnmaskedTerminalTable
#print axioms native_accepted_randomized_terminal_of_compiled_masked_boundary

end AspisPool.NativePaymentCompiledActiveMaskV1
