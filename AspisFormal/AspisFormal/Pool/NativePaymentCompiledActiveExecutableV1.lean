import AspisFormal.Pool.NativePaymentCompiledActiveMaskV1

/-!
# Native Pool V1 executable compiled active-selector bridge

This module refines the three source loops underneath the compiled Copy-active
evaluator: `Selectors::expand`, `selector_mask_sum_16`, and
`Selectors::copy_active`.  The model keeps the production doubling order,
the `count_ones > 8` complement branch, ascending trailing-zero scan order,
and the zero-mask filter explicit.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.NativePaymentCompiledActiveExecutableV1

open AspisPool.NativePaymentCompiledActiveMaskV1
open AspisV5ProductionRowSelector

/-! ## `Selectors::expand` -/

/-- One source-loop iteration.  Rust walks the old prefix backwards so that
each saved parent becomes the adjacent `(1 - coordinate)`/`coordinate` pair.
The resulting observable list is the same left-to-right pair expansion. -/
def rustSelectorExpandStep
    {K : Type*} [Ring K] (weights : List K) (coordinate : K) : List K :=
  weights.flatMap fun parent =>
    [parent - coordinate * parent, coordinate * parent]

/-- Source-shaped `weights[0] = 1; for coordinate { ...; len *= 2; }`. -/
def rustSelectorExpand
    {K : Type*} [Ring K] (coordinates : List K) : List K :=
  coordinates.foldl rustSelectorExpandStep [1]

def rustHighCoordinates
    {K : Type*} (point : TerminalPoint K) : List K :=
  List.ofFn fun coordinate : Fin 6 =>
    point ⟨coordinate.val, by omega⟩

def rustLowCoordinates
    {K : Type*} (point : TerminalPoint K) : List K :=
  List.ofFn fun coordinate : Fin 4 =>
    point ⟨6 + coordinate.val, by omega⟩

/-- The source high-table read after expanding `point[..6]`. -/
def rustExpandedHighWeight
    {K : Type*} [Ring K] (point : TerminalPoint K) (block : Fin 64) : K :=
  (rustSelectorExpand (rustHighCoordinates point)).getD block.val 0

/-- The source low-table read after expanding `point[6..]`. -/
def rustExpandedLowWeight
    {K : Type*} [Ring K] (point : TerminalPoint K) (slot : Fin 16) : K :=
  (rustSelectorExpand (rustLowCoordinates point)).getD slot.val 0

set_option maxHeartbeats 2000000 in
-- Finite normalization of all 64 source table positions.
theorem rustExpandedHighWeight_eq_compiled
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (block : Fin 64) :
    rustExpandedHighWeight point block = compiledHighWeight point block := by
  fin_cases block <;>
    norm_num [rustExpandedHighWeight, rustSelectorExpand,
      rustSelectorExpandStep, rustHighCoordinates, compiledHighWeight,
      Fin.prod_univ_six, Nat.testBit_eq_decide_div_mod_eq] <;> ring_nf

set_option maxHeartbeats 1000000 in
-- Finite normalization of all 16 source table positions.
theorem rustExpandedLowWeight_eq_compiled
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (slot : Fin 16) :
    rustExpandedLowWeight point slot = compiledLowWeight point slot := by
  fin_cases slot <;>
    norm_num [rustExpandedLowWeight, rustSelectorExpand,
      rustSelectorExpandStep, rustLowCoordinates, compiledLowWeight,
      Fin.prod_univ_four, Nat.testBit_eq_decide_div_mod_eq] <;> ring_nf

theorem rustSelectorExpandStep_sum
    {K : Type*} [CommRing K] (weights : List K) (coordinate : K) :
    (rustSelectorExpandStep weights coordinate).sum = weights.sum := by
  induction weights with
  | nil => simp [rustSelectorExpandStep]
  | cons parent tail ih =>
      change
        ([parent - coordinate * parent, coordinate * parent] ++
          rustSelectorExpandStep tail coordinate).sum =
        parent + tail.sum
      rw [List.sum_append, ih]
      simp

theorem rustSelectorExpand_sum
    {K : Type*} [CommRing K] (coordinates : List K) :
    (rustSelectorExpand coordinates).sum = 1 := by
  unfold rustSelectorExpand
  have invariant : ∀ (coords : List K) (weights : List K),
      (coords.foldl rustSelectorExpandStep weights).sum = weights.sum := by
    intro coords
    induction coords with
    | nil => intro weights; rfl
    | cons coordinate tail ih =>
        intro weights
        rw [List.foldl_cons, ih, rustSelectorExpandStep_sum]
  simpa using invariant coordinates [1]

set_option maxHeartbeats 1000000 in
-- The fixed 16-entry low expansion is normalized once to prove total weight.
theorem sum_rustExpandedLowWeight_eq_one
    {K : Type*} [CommRing K] (point : TerminalPoint K) :
    ∑ slot : Fin 16, rustExpandedLowWeight point slot = 1 := by
  simp_rw [rustExpandedLowWeight_eq_compiled]
  norm_num [compiledLowWeight, Fin.sum_univ_succ, Fin.prod_univ_four,
    Nat.testBit_eq_decide_div_mod_eq]
  ring

/-! ## `selector_mask_sum_16` -/

/-- The exact low sixteen bits visible through a Rust `u16`. -/
def u16SetBits (mask : Fin (2 ^ 16)) : Finset (Fin 16) :=
  Finset.univ.filter fun slot => Nat.testBit mask.val slot.val

/-- Exact `u16::count_ones` semantics. -/
def u16CountOnes (mask : Fin (2 ^ 16)) : Nat :=
  (u16SetBits mask).card

/-- Exact 16-bit `!mask`, written arithmetically as `2^16 - (mask + 1)`. -/
def u16Complement (mask : Fin (2 ^ 16)) : Fin (2 ^ 16) :=
  ⟨2 ^ 16 - (mask.val + 1), by omega⟩

theorem u16SetBits_complement (mask : Fin (2 ^ 16)) :
    u16SetBits (u16Complement mask) = Finset.univ \ u16SetBits mask := by
  ext slot
  simp only [u16SetBits, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  rw [show (u16Complement mask).val = 2 ^ 16 - (mask.val + 1) by rfl]
  rw [Nat.testBit_two_pow_sub_succ mask.isLt]
  simp [slot.isLt]

/-- Sorting the set bits increasingly is the observable sequence of repeated
`trailing_zeros` followed by `mask &= mask - 1`. -/
def u16TrailingZeroScanOrder (mask : Fin (2 ^ 16)) : List (Fin 16) :=
  (u16SetBits mask).sort (fun left right => left ≤ right)

theorem u16TrailingZeroScanOrder_sorted (mask : Fin (2 ^ 16)) :
    (u16TrailingZeroScanOrder mask).Pairwise (fun left right => left ≤ right) := by
  exact Finset.pairwise_sort _ _

theorem u16TrailingZeroScanOrder_nodup (mask : Fin (2 ^ 16)) :
    (u16TrailingZeroScanOrder mask).Nodup := by
  exact Finset.sort_nodup _ _

theorem u16TrailingZeroScanOrder_toFinset (mask : Fin (2 ^ 16)) :
    (u16TrailingZeroScanOrder mask).toFinset = u16SetBits mask := by
  exact Finset.sort_toFinset _ _

/-- The source accumulator update used by the sparse and complement scans. -/
def rustBitScanFold
    {K : Type*} [Ring K]
    (subtract : Bool) (values : Fin 16 → K)
    (order : List (Fin 16)) (initial : K) : K :=
  order.foldl
    (fun sum slot => if subtract then sum - values slot else sum + values slot)
    initial

private theorem foldl_add_values
    {K : Type*} [CommRing K]
    (values : Fin 16 → K) (order : List (Fin 16)) (initial : K) :
    order.foldl (fun sum slot => sum + values slot) initial =
      initial + (order.map values).sum := by
  induction order generalizing initial with
  | nil => simp
  | cons slot tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem foldl_sub_values
    {K : Type*} [CommRing K]
    (values : Fin 16 → K) (order : List (Fin 16)) (initial : K) :
    order.foldl (fun sum slot => sum - values slot) initial =
      initial - (order.map values).sum := by
  induction order generalizing initial with
  | nil => simp
  | cons slot tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem sorted_set_sum
    {K : Type*} [CommRing K]
    (values : Fin 16 → K) (bits : Finset (Fin 16)) :
    ((bits.sort (fun left right => left ≤ right)).map values).sum =
      ∑ slot ∈ bits, values slot := by
  rw [← List.sum_toFinset values (Finset.sort_nodup bits _)]
  simp

theorem rustBitScanFold_eq_set_sum
    {K : Type*} [CommRing K]
    (subtract : Bool) (values : Fin 16 → K)
    (bits : Finset (Fin 16)) (initial : K) :
    rustBitScanFold subtract values
        (bits.sort (fun left right => left ≤ right)) initial =
      if subtract then initial - ∑ slot ∈ bits, values slot
      else initial + ∑ slot ∈ bits, values slot := by
  cases subtract <;>
    simp [rustBitScanFold, foldl_add_values, foldl_sub_values,
      sorted_set_sum]

/-- Source-shaped complement choice, bit scan, and accumulator initialization.
The bound makes the input exactly a Rust `u16`. -/
def rustSelectorMaskSum16
    {K : Type*} [Ring K]
    (values : Fin 16 → K) (mask : Fin (2 ^ 16)) : K :=
  if dense : 8 < u16CountOnes mask then
    rustBitScanFold true values (u16TrailingZeroScanOrder (u16Complement mask)) 1
  else
    rustBitScanFold false values (u16TrailingZeroScanOrder mask) 0

/-- Both the sparse addition loop and dense complement/subtraction loop return
the selected-weight sum when the sixteen selector weights sum to one. -/
theorem rustSelectorMaskSum16_eq_selected
    {K : Type*} [CommRing K]
    (values : Fin 16 → K) (mask : Fin (2 ^ 16))
    (total : ∑ slot : Fin 16, values slot = 1) :
    rustSelectorMaskSum16 values mask =
      ∑ slot ∈ u16SetBits mask, values slot := by
  unfold rustSelectorMaskSum16
  split_ifs
  · unfold u16TrailingZeroScanOrder
    rw [rustBitScanFold_eq_set_sum, u16SetBits_complement]
    have partition := Finset.sum_sdiff (f := values)
      (Finset.subset_univ (u16SetBits mask))
    have all : ∑ slot ∈ (Finset.univ : Finset (Fin 16)), values slot = 1 := by
      simpa using total
    rw [all] at partition
    rw [if_pos rfl]
    rw [← partition]
    ring
  · unfold u16TrailingZeroScanOrder
    rw [rustBitScanFold_eq_set_sum]
    simp

theorem selected_u16_sum_eq_indicator_sum
    {K : Type*} [CommRing K]
    (values : Fin 16 → K) (mask : Fin (2 ^ 16)) :
    (∑ slot ∈ u16SetBits mask, values slot) =
      ∑ slot : Fin 16,
        if Nat.testBit mask.val slot.val then values slot else 0 := by
  simp [u16SetBits, Finset.sum_filter]

/-! ## `Selectors::copy_active` -/

def compiledMaskU16
    (variant : NativePaymentVariantV1) (block : Fin 64) : Fin (2 ^ 16) :=
  ⟨compiledActiveRowMasks variant block,
    compiled_active_masks_fit_u16 variant block⟩

/-- Exact source-level zero-mask filter and left-to-right fold after selector
expansion and `selector_mask_sum_16`. -/
noncomputable def rustCopyActiveAtPoint
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (point : TerminalPoint K) : K :=
  ∑ block : Fin 64,
    if compiledActiveRowMasks variant block = 0 then 0
    else rustExpandedHighWeight point block *
      rustSelectorMaskSum16 (rustExpandedLowWeight point)
        (compiledMaskU16 variant block)

/-- The executable expand/complement/bit-scan/filter pipeline refines exactly
to the compiled active-mask evaluator from the previous checkpoint. -/
theorem rustCopyActiveAtPoint_eq_compiled
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (point : TerminalPoint K) :
    rustCopyActiveAtPoint variant point =
      compiledCopyActiveAtPoint variant point := by
  unfold rustCopyActiveAtPoint compiledCopyActiveAtPoint
    compiledSelectorMaskSum16
  apply Finset.sum_congr rfl
  intro block _
  rw [rustExpandedHighWeight_eq_compiled,
    rustSelectorMaskSum16_eq_selected _ _
      (sum_rustExpandedLowWeight_eq_one point),
    selected_u16_sum_eq_indicator_sum]
  simp_rw [rustExpandedLowWeight_eq_compiled]
  change
    (if compiledActiveRowMasks variant block = 0 then 0
      else compiledHighWeight point block *
        ∑ slot : Fin 16,
          if Nat.testBit (compiledActiveRowMasks variant block) slot.val then
            compiledLowWeight point slot else 0) =
      compiledHighWeight point block *
        ∑ slot : Fin 16,
          if Nat.testBit (compiledActiveRowMasks variant block) slot.val then
            compiledLowWeight point slot else 0
  by_cases zeroMask : compiledActiveRowMasks variant block = 0
  · simp [zeroMask]
  · rw [if_neg zeroMask]

theorem rustCopyActiveAtBooleanPoint_eq_compiled_bit
    {K : Type*} [CommRing K]
    (variant : NativePaymentVariantV1) (selected : Fin 1024) :
    rustCopyActiveAtPoint variant (booleanPointOfRow (F := K) selected) =
      compiledCopyActiveField variant selected := by
  rw [rustCopyActiveAtPoint_eq_compiled,
    compiledCopyActiveAtPoint_booleanPoint]

#print axioms rustExpandedHighWeight_eq_compiled
#print axioms rustExpandedLowWeight_eq_compiled
#print axioms rustSelectorExpand_sum
#print axioms u16SetBits_complement
#print axioms rustBitScanFold_eq_set_sum
#print axioms rustSelectorMaskSum16_eq_selected
#print axioms rustCopyActiveAtPoint_eq_compiled
#print axioms rustCopyActiveAtBooleanPoint_eq_compiled_bit

end AspisPool.NativePaymentCompiledActiveExecutableV1
