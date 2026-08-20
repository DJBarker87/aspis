import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFull.Funs
import V5MerkleTopologyConstructorModel

/-!
# The unchanged topology constructor agrees with the maintained model

This file proves the semantics of the nested loops emitted by Aeneas for the
unchanged `Radix4BinaryCapTopology::new` implementation.  It deliberately
uses the exact full-graph extraction rather than the earlier loop-factored
extraction view.

The only inputs needed by the released verifier are strictly increasing query
lists.  Their ordering is proved by the query-derivation layer, so the lemmas
below state that property explicitly instead of assigning meaning to an
unreachable duplicate-index branch.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullConstructorSemantics

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleTopologyConstructorModel
open AspisV5TopologyConstruction

abbrev IndexVec := alloc.vec.Vec Std.U32
abbrev MaskVec := alloc.vec.Vec Std.U8
abbrev LevelOffsets := Array Std.Usize 17#usize
abbrev GroupOffsets := Array Std.Usize 16#usize

def indexValues (values : IndexVec) : List Nat :=
  values.val.map fun value => value.val

def maskValues (values : MaskVec) : List Nat :=
  values.val.map fun value => value.val

theorem shr2 (value : Std.U32) :
    (Std.U32.wrapping_shr value 2#u32).val = value.val / 4 := by
  unfold Std.U32.wrapping_shr UScalar.wrapping_shr
  norm_num
  change (BitVec.ushiftRight value.bv 2).toNat = value.bv.toNat / 4
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem shr2_i32 (value : Std.U32) :
    (Std.U32.wrapping_shr value 2#u32).val = value.val / 4 := by
  unfold Std.U32.wrapping_shr UScalar.wrapping_shr
  norm_num
  change (BitVec.ushiftRight value.bv 2).toNat = value.bv.toNat / 4
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem and3 (value : Std.U32) :
    (value &&& 3#u32).val = value.val % 4 := by
  change value.val &&& 3 = value.val % 4
  simpa using Nat.and_two_pow_sub_one_eq_mod value.val 2

theorem slot_cast (value : Std.U32) (bound : value.val < 4) :
    (UScalar.cast .U8 value).val = value.val := by
  simp [UScalar.cast_val_eq]
  omega

theorem shl_slot (value : Std.U32) (bound : value.val < 4) :
    (Std.U8.wrapping_shl 1#u8
      (UScalar.cast .U32 (UScalar.cast .U8 value))).val = 2 ^ value.val := by
  have cast8 : (UScalar.cast .U8 value).val = value.val := slot_cast value bound
  have cast32 : (UScalar.cast .U32 (UScalar.cast .U8 value)).val = value.val := by
    rw [Std.U8.cast_U32_val_eq, cast8]
  unfold Std.U8.wrapping_shl UScalar.wrapping_shl
  norm_num
  unfold UScalar.val
  simp [Nat.shiftLeft_eq]
  change value.bv.toNat < 4 at bound
  change 2 ^ (value.bv.toNat % 8) % 256 = 2 ^ value.bv.toNat
  interval_cases current : value.bv.toNat <;> norm_num [current] at *

theorem shl_slot_u8 (value : Std.U32) (bound : value.val < 4) :
    (Std.U8.wrapping_shl 1#u8
      (UScalar.cast .U32 (UScalar.cast .U8 value))).val =
      2 ^ value.val := by
  exact shl_slot value bound

theorem slotMask_four (slots : Finset (Fin 4)) :
    slotMask slots =
      (if (0 : Fin 4) ∈ slots then 1 else 0) +
      (if (1 : Fin 4) ∈ slots then 2 else 0) +
      (if (2 : Fin 4) ∈ slots then 4 else 0) +
      (if (3 : Fin 4) ∈ slots then 8 else 0) := by
  unfold slotMask
  have equality : (∑ slot ∈ slots, 2 ^ slot.val) =
      ∑ slot : Fin 4, if slot ∈ slots then 2 ^ slot.val else 0 := by
    rw [← Finset.sum_filter]
    congr
    ext slot
    simp
  rw [equality, Fin.sum_univ_four]
  norm_num

theorem slotMask_and_fresh_bit_eq_zero
    (slots : Finset (Fin 4)) (slot : Fin 4) (fresh : slot ∉ slots) :
    slotMask slots &&& 2 ^ slot.val = 0 := by
  rw [slotMask_four]
  fin_cases slot <;>
    by_cases h0 : (0 : Fin 4) ∈ slots <;>
    by_cases h1 : (1 : Fin 4) ∈ slots <;>
    by_cases h2 : (2 : Fin 4) ∈ slots <;>
    by_cases h3 : (3 : Fin 4) ∈ slots <;>
    simp [h0, h1, h2, h3] at fresh ⊢

theorem slotMask_insert_or (slots : Finset (Fin 4)) (slot : Fin 4)
    (fresh : slot ∉ slots) :
    slotMask slots ||| 2 ^ slot.val = slotMask (insert slot slots) := by
  rw [slotMask_four, slotMask_four]
  fin_cases slot <;>
    by_cases h0 : (0 : Fin 4) ∈ slots <;>
    by_cases h1 : (1 : Fin 4) ∈ slots <;>
    by_cases h2 : (2 : Fin 4) ∈ slots <;>
    by_cases h3 : (3 : Fin 4) ∈ slots <;>
    simp [h0, h1, h2, h3] at fresh ⊢

theorem presentSlots_append_same_parent (values : List Nat) (value parent : Nat)
    (sameParent : value / 4 = parent) :
    presentSlotsOf (values ++ [value]) parent =
      insert ⟨value % 4, Nat.mod_lt _ (by decide)⟩
        (presentSlotsOf values parent) := by
  ext slot
  simp only [presentSlotsOf, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_append, List.mem_singleton, Finset.mem_insert]
  have decomposition : 4 * parent + value % 4 = value := by
    have := Nat.mod_add_div value 4
    omega
  constructor
  · intro member
    rcases member with member | member
    · exact Or.inr member
    · left
      apply Fin.ext
      exact Nat.add_left_cancel (member.trans decomposition.symm)
  · intro member
    rcases member with member | member
    · right
      have equalValue := congrArg Fin.val member
      simpa [equalValue] using decomposition
    · exact Or.inl member

theorem sort_insert_greatest (values : Finset Nat) (value : Nat)
    (greatest : ∀ prior ∈ values, prior < value) :
    (insert value values).sort (fun left right => left ≤ right) =
      values.sort (fun left right => left ≤ right) ++ [value] := by
  apply @List.Perm.eq_of_pairwise Nat (fun left right => left ≤ right)
  · intro left right _ _ leftRight rightLeft
    omega
  · exact Finset.pairwise_sort (insert value values) (fun left right => left ≤ right)
  · rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort values (fun left right => left ≤ right), by simp, ?_⟩
    intro prior priorMem _ valueMem
    simp only [List.mem_singleton] at valueMem
    subst valueMem
    exact Nat.le_of_lt (greatest prior ((Finset.mem_sort (fun left right => left ≤ right)).mp priorMem))
  · have valueNotMem : value ∉ values := by
      intro member
      exact (Nat.lt_irrefl value) (greatest value member)
    apply List.perm_of_nodup_nodup_toFinset_eq
      (Finset.sort_nodup (insert value values) (fun left right => left ≤ right))
    · rw [List.nodup_append]
      exact ⟨Finset.sort_nodup values (fun left right => left ≤ right), by simp,
        by simp [valueNotMem]⟩
    ext candidate
    simp

theorem presentSlots_append_group_old_parent
    (processed group : List Nat) (parent oldParent : Nat)
    (groupParent : ∀ value ∈ group, value / 4 = parent)
    (different : oldParent ≠ parent) :
    presentSlotsOf (processed ++ group) oldParent =
      presentSlotsOf processed oldParent := by
  ext slot
  simp only [presentSlotsOf, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_append]
  constructor
  · intro member
    rcases member with member | member
    · exact member
    · exfalso
      have quotient : (4 * oldParent + slot.val) / 4 = oldParent := by
        have slotBound := slot.isLt
        omega
      exact different (quotient.symm.trans (groupParent _ member))
  · exact Or.inl

theorem presentSlots_append_group_new_parent
    (processed group : List Nat) (parent : Nat)
    (processedFresh : ∀ value ∈ processed, value / 4 ≠ parent) :
    presentSlotsOf (processed ++ group) parent = presentSlotsOf group parent := by
  ext slot
  simp only [presentSlotsOf, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_append]
  constructor
  · intro member
    rcases member with member | member
    · exfalso
      apply processedFresh _ member
      have slotBound := slot.isLt
      omega
    · exact member
  · exact Or.inr

theorem parent_models_append_new_group
    (processed group : List Nat) (parent : Nat)
    (sorted : (processed ++ group).Pairwise (fun left right => left < right))
    (groupNonempty : group ≠ [])
    (groupParent : ∀ value ∈ group, value / 4 = parent)
    (processedFresh : ∀ value ∈ processed, value / 4 ≠ parent) :
    parentIndicesOf (processed ++ group) = parentIndicesOf processed ++ [parent] ∧
    parentMasksOf (processed ++ group) = parentMasksOf processed ++
      [slotMask (presentSlotsOf group parent)] := by
  have parentImage :
      (processed ++ group).toFinset.image (fun value => value / 4) =
        insert parent (processed.toFinset.image fun value => value / 4) := by
    ext candidate
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_append,
      Finset.mem_insert]
    constructor
    · rintro ⟨value, valueMem, rfl⟩
      rcases valueMem with valueMem | valueMem
      · exact Or.inr ⟨value, valueMem, rfl⟩
      · exact Or.inl (groupParent value valueMem)
    · intro member
      rcases member with member | member
      · obtain ⟨first, rest, groupShape⟩ := List.exists_cons_of_ne_nil groupNonempty
        subst candidate
        subst group
        exact ⟨first, Or.inr (by simp), groupParent first (by simp)⟩
      · obtain ⟨value, valueMem, rfl⟩ := member
        exact ⟨value, Or.inl valueMem, rfl⟩
  have parentGreatest :
      ∀ prior ∈ processed.toFinset.image (fun value => value / 4),
        prior < parent := by
    intro prior priorMem
    obtain ⟨value, valueMem, rfl⟩ := Finset.mem_image.mp priorMem
    obtain ⟨first, rest, groupShape⟩ := List.exists_cons_of_ne_nil groupNonempty
    have cross := (List.pairwise_append.mp sorted).2.2
    have valueLtFirst : value < first := by
      apply cross value (List.mem_toFinset.mp valueMem) first
      simpa [groupShape]
    have quotientLe : value / 4 ≤ first / 4 :=
      Nat.div_le_div_right (Nat.le_of_lt valueLtFirst)
    have quotientNe : value / 4 ≠ parent :=
      processedFresh value (List.mem_toFinset.mp valueMem)
    rw [groupParent first (by simpa [groupShape])] at quotientLe
    omega
  have indicesEquality :
      parentIndicesOf (processed ++ group) = parentIndicesOf processed ++ [parent] := by
    unfold parentIndicesOf
    rw [parentImage]
    exact sort_insert_greatest _ _ parentGreatest
  refine ⟨indicesEquality, ?_⟩
  unfold parentMasksOf
  rw [indicesEquality, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro oldParent oldParentMem
    have oldDifferent : oldParent ≠ parent := by
      intro equality
      have oldMem : oldParent ∈ parentIndicesOf processed := oldParentMem
      unfold parentIndicesOf at oldMem
      obtain ⟨value, valueMem, quotient⟩ :=
        Finset.mem_image.mp ((Finset.mem_sort (fun left right => left ≤ right)).mp oldMem)
      exact processedFresh value (List.mem_toFinset.mp valueMem)
        (quotient.trans equality)
    exact congrArg slotMask
      (presentSlots_append_group_old_parent processed group parent oldParent
        groupParent oldDifferent)
  · exact congrArg List.singleton (congrArg slotMask
      (presentSlots_append_group_new_parent processed group parent processedFresh))

theorem parentIndices_length_le (values : List Nat) :
    (parentIndicesOf values).length ≤ values.length := by
  unfold parentIndicesOf
  calc
    ((values.toFinset.image fun value => value / 4).sort
      (fun left right => left ≤ right)).length =
        (values.toFinset.image fun value => value / 4).card := by simp
    _ ≤ values.toFinset.card := Finset.card_image_le
    _ ≤ values.length := List.toFinset_card_le values

theorem parentMasks_length_le (values : List Nat) :
    (parentMasksOf values).length ≤ values.length := by
  unfold parentMasksOf
  simpa using parentIndices_length_le values

theorem parentIndices_pairwise_lt (values : List Nat) :
    (parentIndicesOf values).Pairwise (fun left right => left < right) := by
  unfold parentIndicesOf
  exact ((Finset.pairwise_sort
    (values.toFinset.image fun value => value / 4)
    (fun left right : Nat => left ≤ right)).sortedLE.sortedLT_of_nodup
      (Finset.sort_nodup _ _)).pairwise

theorem parentLevelFrom_length_le (initial : List Nat) (level : Nat) :
    (parentLevelFrom initial level).length ≤ initial.length := by
  induction level with
  | zero => simp [parentLevelFrom]
  | succ level inductionHypothesis =>
      rw [parentLevelFrom]
      exact (parentIndices_length_le _).trans inductionHypothesis

theorem parentLevelFrom_pairwise_lt
    (initial : List Nat)
    (initialSorted : initial.Pairwise (fun left right => left < right))
    (level : Nat) :
    (parentLevelFrom initial level).Pairwise
      (fun left right => left < right) := by
  cases level with
  | zero => exact initialSorted
  | succ level =>
      rw [parentLevelFrom]
      exact parentIndices_pairwise_lt _

theorem levelPrefix_length_le (initial : List Nat) (count : Nat) :
    (levelPrefix initial count).length ≤ count * initial.length := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [show count + 1 = count + 1 by rfl, levelPrefix_succ,
        List.length_append]
      have current := parentLevelFrom_length_le initial count
      calc
        (levelPrefix initial count).length +
            (parentLevelFrom initial count).length ≤
            count * initial.length + initial.length :=
          Nat.add_le_add inductionHypothesis current
        _ = (count + 1) * initial.length := by
          rw [Nat.add_mul]
          simp

theorem maskPrefix_length_le (initial : List Nat) (count : Nat) :
    (maskPrefix initial count).length ≤ count * initial.length := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [show count + 1 = count + 1 by rfl, maskPrefix_succ,
        List.length_append]
      unfold parentMaskLevelFrom
      have current := parentMasks_length_le (parentLevelFrom initial count)
      have levelBound := parentLevelFrom_length_le initial count
      calc
        (maskPrefix initial count).length +
            (parentMasksOf (parentLevelFrom initial count)).length ≤
            count * initial.length + initial.length :=
          Nat.add_le_add inductionHypothesis (current.trans levelBound)
        _ = (count + 1) * initial.length := by
          rw [Nat.add_mul]
          simp

def rangeValues (values : IndexVec) (start position : Nat) : List Nat :=
  (indexValues values).take position |>.drop start

@[simp] theorem rangeValues_self (values : IndexVec) (position : Nat) :
    rangeValues values position position = [] := by
  simp [rangeValues]

theorem rangeValues_next (values : IndexVec) (start position : Nat)
    (startBound : start ≤ position)
    (positionBound : position < values.val.length) :
    rangeValues values start (position + 1) =
      rangeValues values start position ++ [values.val[position].val] := by
  unfold rangeValues indexValues
  have mappedBound : position <
      (values.val.map fun value => value.val).length := by
    simpa using positionBound
  rw [List.take_succ_eq_append_getElem mappedBound,
    List.drop_append_of_le_length]
  · simp
  · simp
    exact ⟨startBound, startBound.trans (Nat.le_of_lt positionBound)⟩

theorem rangeValues_split (values : IndexVec) (start middle finish : Nat)
    (start_le_middle : start ≤ middle)
    (middle_le_finish : middle ≤ finish) :
    rangeValues values start finish =
      rangeValues values start middle ++ rangeValues values middle finish := by
  unfold rangeValues
  let whole := (indexValues values).take finish |>.drop start
  have decomposition := List.take_append_drop (middle - start) whole
  change whole = _
  calc
    whole = whole.take (middle - start) ++ whole.drop (middle - start) :=
      decomposition.symm
    _ = _ := by
      congr 1
      · rw [List.take_drop, List.take_take]
        simp only [Nat.add_sub_of_le start_le_middle,
          Nat.min_eq_left middle_le_finish]
      · rw [List.drop_drop, Nat.add_sub_of_le start_le_middle]

theorem rangeValues_of_appended
    (current base : IndexVec) (suffix : List Std.U32)
    (current_eq : current.val = base.val ++ suffix)
    (start position : Nat) (position_le_base : position ≤ base.val.length) :
    rangeValues current start position = rangeValues base start position := by
  unfold rangeValues indexValues
  rw [current_eq, List.map_append, List.take_append_of_le_length]
  simpa using position_le_base

theorem rangeValues_length (values : IndexVec) (start position : Nat)
    (start_le_position : start ≤ position)
    (position_le_length : position ≤ values.val.length) :
    (rangeValues values start position).length = position - start := by
  simp [rangeValues, indexValues, List.length_drop, List.length_take,
    Nat.min_eq_left position_le_length]

theorem rangeValues_levelPrefix
    (values : IndexVec) (initial : List Nat) (level : Nat)
    (values_eq : indexValues values = levelPrefix initial (level + 1)) :
    rangeValues values (levelPrefix initial level).length
        (levelPrefix initial (level + 1)).length =
      parentLevelFrom initial level := by
  unfold rangeValues
  rw [values_eq, List.take_length, levelPrefix_succ,
    List.drop_append_length]

theorem processed_and_group_fresh_for_next
    (processed group : List Nat) (parent next : Nat)
    (sorted : (processed ++ group ++ [next]).Pairwise
      (fun left right => left < right))
    (groupNonempty : group ≠ [])
    (groupParent : ∀ value ∈ group, value / 4 = parent)
    (nextDifferent : next / 4 ≠ parent) :
    ∀ value ∈ processed ++ group, value / 4 ≠ next / 4 := by
  obtain ⟨first, rest, groupShape⟩ := List.exists_cons_of_ne_nil groupNonempty
  have firstMem : first ∈ group := by simp [groupShape]
  have firstParent := groupParent first firstMem
  have pairwiseOuter := List.pairwise_append.mp sorted
  have firstLtNext : first < next := by
    exact pairwiseOuter.2.2 first (by simp [firstMem]) next (by simp)
  have parentLtNext : parent < next / 4 := by
    have quotientLe : first / 4 ≤ next / 4 :=
      Nat.div_le_div_right (Nat.le_of_lt firstLtNext)
    rw [firstParent] at quotientLe
    omega
  intro value member equality
  simp only [List.mem_append] at member
  rcases member with member | member
  · have processedGroup := List.pairwise_append.mp pairwiseOuter.1
    have valueLtFirst := processedGroup.2.2 value member first firstMem
    have quotientLe : value / 4 ≤ first / 4 :=
      Nat.div_le_div_right (Nat.le_of_lt valueLtFirst)
    rw [firstParent] at quotientLe
    omega
  · rw [groupParent value member] at equality
    omega

theorem rangeValues_pairwise
    (values : IndexVec) (start position : Nat)
    (sorted : (indexValues values).Pairwise (fun left right => left < right)) :
    (rangeValues values start position).Pairwise (fun left right => left < right) := by
  exact List.Pairwise.drop (i := start)
    (List.Pairwise.take (i := position) sorted)

theorem rangeValues_pairwise_of_prefix
    (values : IndexVec) (start position currentEnd : Nat)
    (position_le_end : position ≤ currentEnd)
    (sorted : ((indexValues values).take currentEnd).Pairwise
      (fun left right => left < right)) :
    (rangeValues values start position).Pairwise
      (fun left right => left < right) := by
  have taken := List.Pairwise.take (i := position) sorted
  have dropped := List.Pairwise.drop (i := start) taken
  simpa [rangeValues, List.take_take, Nat.min_eq_left position_le_end]
    using dropped

theorem rangeValues_pairwise_prefix_of_range
    (values : IndexVec) (start position currentEnd : Nat)
    (start_le_position : start ≤ position)
    (position_le_end : position ≤ currentEnd)
    (sorted : (rangeValues values start currentEnd).Pairwise
      (fun left right => left < right)) :
    (rangeValues values start position).Pairwise
      (fun left right => left < right) := by
  have split := rangeValues_split values start position currentEnd
    start_le_position position_le_end
  rw [split] at sorted
  exact (List.pairwise_append.mp sorted).1

theorem rangeValues_pairwise_suffix_of_range
    (values : IndexVec) (start position currentEnd : Nat)
    (start_le_position : start ≤ position)
    (position_le_end : position ≤ currentEnd)
    (sorted : (rangeValues values start currentEnd).Pairwise
      (fun left right => left < right)) :
    (rangeValues values position currentEnd).Pairwise
      (fun left right => left < right) := by
  have split := rangeValues_split values start position currentEnd
    start_le_position position_le_end
  rw [split] at sorted
  exact (List.pairwise_append.mp sorted).2.1

private theorem usize_succ_val_below_vec_length
    (values : alloc.vec.Vec α) (position : Std.Usize)
    (positionBound : position.val < values.val.length) :
    (Std.Usize.wrapping_add position 1#usize).val = position.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  have lengthBound : values.val.length ≤ Std.Usize.max := values.property
  have maxBound0 : Std.Usize.max < UScalar.size .Usize := by
    rw [Std.Usize.max, Std.Usize.numBits, UScalar.size_def,
      UScalarTy.Usize_numBits_eq]
    exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have maxBound : Std.Usize.max < Std.Usize.size := by
    rw [← UScalar.size_UScalarTyUsize]
    exact maxBound0
  omega

structure ParentLevelInvariant
    (baseValues : IndexVec) (baseMasks : MaskVec)
    (start currentEnd : Std.Usize)
    (values : IndexVec) (masks : MaskVec) (position : Std.Usize) : Type where
  parentSuffix : List Std.U32
  maskSuffix : List Std.U8
  values_eq : values.val = baseValues.val ++ parentSuffix
  masks_eq : masks.val = baseMasks.val ++ maskSuffix
  parent_values : parentSuffix.map (fun value => value.val) =
    parentIndicesOf (rangeValues baseValues start.val position.val)
  mask_values : maskSuffix.map (fun value => value.val) =
    parentMasksOf (rangeValues baseValues start.val position.val)
  start_le_position : start.val ≤ position.val
  position_le_end : position.val ≤ currentEnd.val
  next_parent_fresh : ∀ (next : Std.U32),
    baseValues.val[position.val]? = some next →
      ∀ value ∈ rangeValues baseValues start.val position.val,
        value / 4 ≠ next.val / 4

def ParentLevelPost
    (baseValues : IndexVec) (baseMasks : MaskVec)
    (start currentEnd : Std.Usize)
    (output : IndexVec × MaskVec ×
      Option (Option aspis_core.merkle.Radix4BinaryCapTopology)) : Prop :=
  output.2.2 = none ∧
    indexValues output.1 = indexValues baseValues ++
      parentIndicesOf (rangeValues baseValues start.val currentEnd.val) ∧
    maskValues output.2.1 = maskValues baseMasks ++
      parentMasksOf (rangeValues baseValues start.val currentEnd.val)

theorem same_parent_same_slot_eq
    {left right : Nat}
    (sameParent : left / 4 = right / 4)
    (sameSlot : left % 4 = right % 4) :
    left = right := by
  omega

theorem fresh_slot_of_strict_prefix
    {processed : List Nat} {value parent : Nat}
    (sorted : (processed ++ [value]).Pairwise (fun left right => left < right))
    (processedParent : ∀ prior ∈ processed, prior / 4 = parent)
    (valueParent : value / 4 = parent) :
    ⟨value % 4, Nat.mod_lt _ (by decide)⟩ ∉
      presentSlotsOf processed parent := by
  intro present
  simp only [presentSlotsOf, Finset.mem_filter, Finset.mem_univ,
    true_and] at present
  have member : 4 * parent + value % 4 ∈ processed := present
  have decomposition : 4 * parent + value % 4 = value := by
    have := Nat.mod_add_div value 4
    omega
  rw [List.pairwise_append] at sorted
  have strict := sorted.2.2 _ member value (by simp)
  omega

structure GroupInvariant
    (values : IndexVec) (start currentEnd : Std.Usize)
    (parent : Std.U32) (position : Std.Usize) (present : Std.U8) : Prop where
  start_le_position : start.val ≤ position.val
  position_le_end : position.val ≤ currentEnd.val
  end_le_length : currentEnd.val ≤ values.val.length
  same_parent : ∀ value ∈ rangeValues values start.val position.val,
    value / 4 = parent.val
  present_value : present.val =
    slotMask (presentSlotsOf
      (rangeValues values start.val position.val) parent.val)

def GroupPost
    (values : IndexVec) (start currentEnd : Std.Usize)
    (parent : Std.U32)
    (output : Std.Usize × Std.U8 ×
      Option (Option aspis_core.merkle.Radix4BinaryCapTopology)) : Prop :=
  let position := output.1
  let present := output.2.1
  let pending := output.2.2
  pending = none ∧
    GroupInvariant values start currentEnd parent position present ∧
    (position.val = currentEnd.val ∨
      (∃ next,
        values.val[position.val]? = some next ∧
        next.val / 4 ≠ parent.val))

set_option maxHeartbeats 1000000 in
theorem exact_group_loop_spec
    (values : IndexVec) (start currentEnd : Std.Usize)
    (parent : Std.U32)
    (sorted : (rangeValues values start.val currentEnd.val).Pairwise
      (fun left right => left < right))
    (start_lt_end : start.val < currentEnd.val)
    (end_le_length : currentEnd.val ≤ values.val.length) :
    aspis_core.merkle.Radix4BinaryCapTopology.new_loop0_loop0_loop0
      values currentEnd start parent 0#u8
      ⦃ output => GroupPost values start currentEnd parent output ⦄ := by
  simp only [aspis_core.merkle.Radix4BinaryCapTopology.new_loop0_loop0_loop0]
  apply Aeneas.Std.loop.spec_decr_nat
    (fun state : Std.Usize × Std.U8 => currentEnd.val - state.1.val)
    (fun state => GroupInvariant values start currentEnd parent state.1 state.2)
    (GroupPost values start currentEnd parent)
  · rintro ⟨position, present⟩ invariant
    unfold aspis_core.merkle.Radix4BinaryCapTopology.new_loop0_loop0_loop0.body
    simp only [Prod.fst, Prod.snd]
    by_cases active : position.val < currentEnd.val
    · have activeScalar : position < currentEnd := by scalar_tac
      rw [if_pos activeScalar]
      have positionBound : position.val < values.val.length :=
        active.trans_le invariant.end_le_length
      obtain ⟨index, indexRun, indexValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec values position positionBound)
      rw [alloc.vec.Vec.index_slice_index, indexRun]
      simp only [Aeneas.Std.bind_tc_ok, lift]
      let indexParent := Std.U32.wrapping_shr index 2#u32
      have indexParentValue : indexParent.val = index.val / 4 := shr2_i32 index
      by_cases sameParent : indexParent = parent
      · rw [if_pos sameParent]
        let lowSlot := index &&& 3#u32
        let slotMaskScalar := Std.U8.wrapping_shl 1#u8
          (UScalar.cast .U32 (UScalar.cast .U8 lowSlot))
        have lowSlotValue : lowSlot.val = index.val % 4 := and3 index
        have lowSlotBound : lowSlot.val < 4 := by
          rw [lowSlotValue]
          exact Nat.mod_lt _ (by decide)
        have slotMaskValue : slotMaskScalar.val = 2 ^ (index.val % 4) := by
          rw [show slotMaskScalar = Std.U8.wrapping_shl 1#u8
              (UScalar.cast .U32 (UScalar.cast .U8 lowSlot)) by rfl,
            shl_slot_u8 lowSlot lowSlotBound, lowSlotValue]
        have valueParent : index.val / 4 = parent.val := by
          have equality := congrArg (fun value : Std.U32 => value.val) sameParent
          rw [indexParentValue] at equality
          exact equality
        have nextRange := rangeValues_next values start.val position.val
          invariant.start_le_position positionBound
        have nextRangeIndex :
            rangeValues values start.val (position.val + 1) =
              rangeValues values start.val position.val ++ [index.val] := by
          simpa [indexValue] using nextRange
        have nextPairwise := rangeValues_pairwise_prefix_of_range values
          start.val (position.val + 1) currentEnd.val
          (invariant.start_le_position.trans (Nat.le_succ _)) active sorted
        rw [nextRangeIndex] at nextPairwise
        have freshSlot := fresh_slot_of_strict_prefix nextPairwise
          invariant.same_parent valueParent
        have zeroValue : (present &&& slotMaskScalar).val = 0 := by
          rw [UScalar.val_and, invariant.present_value, slotMaskValue]
          exact slotMask_and_fresh_bit_eq_zero _ _ freshSlot
        have zeroScalar : present &&& slotMaskScalar = 0#u8 :=
          UScalar.eq_of_val_eq zeroValue
        rw [show Std.U8.wrapping_shl 1#u8
            (UScalar.cast .U32 (UScalar.cast .U8 lowSlot)) = slotMaskScalar by rfl]
        rw [zeroScalar]
        simp only [ne_eq, not_true_eq_false, if_false, lift,
          Aeneas.Std.bind_tc_ok, Aeneas.Std.WP.spec, Aeneas.Std.WP.theta]
        have nextPosition := usize_succ_val_below_vec_length values position
          positionBound
        refine ⟨?_, ?_⟩
        · refine {
            start_le_position := by
              rw [nextPosition]
              exact invariant.start_le_position.trans (Nat.le_succ _)
            position_le_end := by
              rw [nextPosition]
              exact active
            end_le_length := invariant.end_le_length
            same_parent := ?_
            present_value := ?_
          }
          · intro value member
            rw [nextPosition, nextRangeIndex] at member
            simp only [List.mem_append, List.mem_singleton] at member
            rcases member with member | member
            · exact invariant.same_parent value member
            · simpa [member] using valueParent
          · rw [UScalar.val_or, slotMaskValue, nextPosition, nextRangeIndex,
              presentSlots_append_same_parent _ _ _ valueParent,
              invariant.present_value]
            exact slotMask_insert_or _ _ freshSlot
        · rw [nextPosition]
          omega
      · rw [if_neg sameParent]
        simp only [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta]
        refine ⟨rfl, invariant, Or.inr ⟨index, ?_, ?_⟩⟩
        · simpa [indexValue] using List.getElem?_eq_getElem positionBound
        · intro equality
          apply sameParent
          apply UScalar.eq_of_val_eq
          rw [indexParentValue]
          exact equality
    · have inactiveScalar : ¬ position < currentEnd := by scalar_tac
      rw [if_neg inactiveScalar]
      simp only [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta]
      exact ⟨rfl, invariant, Or.inl (Nat.le_antisymm invariant.position_le_end
        (Nat.le_of_not_gt active))⟩
  · refine {
      start_le_position := Nat.le_refl _
      position_le_end := Nat.le_of_lt start_lt_end
      end_le_length := end_le_length
      same_parent := by simp
      present_value := by simp [slotMask, presentSlotsOf]
    }

set_option maxHeartbeats 2000000 in
theorem exact_parent_level_loop_spec
    (baseValues : IndexVec) (baseMasks : MaskVec)
    (start currentEnd : Std.Usize)
    (sorted : (rangeValues baseValues start.val currentEnd.val).Pairwise
      (fun left right => left < right))
    (start_le_end : start.val ≤ currentEnd.val)
    (end_eq_length : currentEnd.val = baseValues.val.length)
    (value_room : baseValues.val.length + baseValues.val.length < Std.Usize.max)
    (mask_room : baseMasks.val.length + baseValues.val.length < Std.Usize.max) :
    aspis_core.merkle.Radix4BinaryCapTopology.new_loop0_loop0
      baseValues baseMasks currentEnd start
      ⦃ output => ParentLevelPost baseValues baseMasks start currentEnd output ⦄ := by
  simp only [aspis_core.merkle.Radix4BinaryCapTopology.new_loop0_loop0]
  apply Aeneas.Std.loop.spec_decr_nat
    (fun state : IndexVec × MaskVec × Std.Usize =>
      currentEnd.val - state.2.2.val)
    (fun state => Nonempty (ParentLevelInvariant baseValues baseMasks
      start currentEnd state.1 state.2.1 state.2.2))
    (ParentLevelPost baseValues baseMasks start currentEnd)
  · rintro ⟨values, masks, position⟩ invariantExists
    let invariant := Classical.choice invariantExists
    unfold aspis_core.merkle.Radix4BinaryCapTopology.new_loop0_loop0.body
    simp only [Prod.fst, Prod.snd]
    by_cases active : position.val < currentEnd.val
    · have activeScalar : position < currentEnd := by scalar_tac
      rw [if_pos activeScalar]
      have basePositionBound : position.val < baseValues.val.length := by
        rw [← end_eq_length]
        exact active
      have valuesPositionBound : position.val < values.val.length := by
        rw [invariant.values_eq, List.length_append]
        omega
      obtain ⟨index, indexRun, indexValue⟩ := Aeneas.Std.WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec values position valuesPositionBound)
      rw [alloc.vec.Vec.index_slice_index, indexRun]
      simp only [Aeneas.Std.bind_tc_ok, lift]
      let parent := Std.U32.wrapping_shr index 2#u32
      have parentValue : parent.val = index.val / 4 := shr2_i32 index
      have currentGet : values.val[position.val]? = some index := by
        simpa [indexValue] using List.getElem?_eq_getElem valuesPositionBound
      have baseGet : baseValues.val[position.val]? = some index := by
        rw [← currentGet, invariant.values_eq,
          List.getElem?_append_left basePositionBound]
      have indexBase : index = baseValues.val[position.val] := by
        exact Option.some.inj
          (baseGet.symm.trans (List.getElem?_eq_getElem basePositionBound))
      have endLeValues : currentEnd.val ≤ values.val.length := by
        rw [invariant.values_eq, List.length_append, end_eq_length]
        omega
      have currentLevelEq :
          rangeValues values start.val currentEnd.val =
            rangeValues baseValues start.val currentEnd.val := by
        exact rangeValues_of_appended values baseValues invariant.parentSuffix
          invariant.values_eq start.val currentEnd.val
          (by rw [end_eq_length])
      have currentLevelSorted :
          (rangeValues values start.val currentEnd.val).Pairwise
            (fun left right => left < right) := by
        rw [currentLevelEq]
        exact sorted
      have currentGroupSorted :
          (rangeValues values position.val currentEnd.val).Pairwise
            (fun left right => left < right) :=
        rangeValues_pairwise_suffix_of_range values start.val position.val
          currentEnd.val invariant.start_le_position invariant.position_le_end
          currentLevelSorted
      obtain ⟨groupOutput, groupRun, groupPost⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (exact_group_loop_spec values position currentEnd parent currentGroupSorted
            active endLeValues)
      rw [groupRun]
      rcases groupOutput with ⟨nextPosition, present, pending⟩
      change pending = none ∧
        GroupInvariant values position currentEnd parent nextPosition present ∧
        (nextPosition.val = currentEnd.val ∨
          ∃ next, values.val[nextPosition.val]? = some next ∧
            next.val / 4 ≠ parent.val) at groupPost
      rcases groupPost with ⟨pendingNone, groupInvariant, groupBoundary⟩
      subst pending
      simp only [Aeneas.Std.bind_tc_ok]
      let processed := rangeValues baseValues start.val position.val
      let group := rangeValues baseValues position.val nextPosition.val
      have nextLeBase : nextPosition.val ≤ baseValues.val.length := by
        rw [← end_eq_length]
        exact groupInvariant.position_le_end
      have groupEq :
          rangeValues values position.val nextPosition.val = group := by
        exact rangeValues_of_appended values baseValues invariant.parentSuffix
          invariant.values_eq position.val nextPosition.val nextLeBase
      have nextPositionStrict : position.val < nextPosition.val := by
        have positionLe := groupInvariant.start_le_position
        by_contra notStrict
        have positionEq : nextPosition.val = position.val := by omega
        rcases groupBoundary with atEnd | nextBoundary
        · omega
        · obtain ⟨next, nextRun, nextDifferent⟩ := nextBoundary
          have currentGet : values.val[position.val]? = some index := by
            simpa [indexValue] using List.getElem?_eq_getElem valuesPositionBound
          rw [positionEq] at nextRun
          have nextEq : next = index := Option.some.inj (nextRun.symm.trans currentGet)
          subst next
          exact nextDifferent (by rw [parentValue])
      have groupNonempty : group ≠ [] := by
        intro empty
        have groupLength := rangeValues_length baseValues position.val
          nextPosition.val (Nat.le_of_lt nextPositionStrict) nextLeBase
        change group.length = nextPosition.val - position.val at groupLength
        rw [empty] at groupLength
        simp at groupLength
        omega
      have groupParent : ∀ value ∈ group, value / 4 = parent.val := by
        intro value member
        apply groupInvariant.same_parent value
        rw [groupEq]
        exact member
      have processedFresh : ∀ value ∈ processed,
          value / 4 ≠ parent.val := by
        intro value member equality
        have fresh := invariant.next_parent_fresh index baseGet value member
        apply fresh
        exact equality.trans parentValue
      have combinedEq :
          rangeValues baseValues start.val nextPosition.val = processed ++ group := by
        exact rangeValues_split baseValues start.val position.val nextPosition.val
          invariant.start_le_position (Nat.le_of_lt nextPositionStrict)
      have combinedSorted : (processed ++ group).Pairwise
          (fun left right => left < right) := by
        rw [← combinedEq]
        exact rangeValues_pairwise_prefix_of_range baseValues start.val
          nextPosition.val currentEnd.val
          (invariant.start_le_position.trans (Nat.le_of_lt nextPositionStrict))
          groupInvariant.position_le_end sorted
      have modelUpdate := parent_models_append_new_group processed group parent.val
        combinedSorted groupNonempty groupParent processedFresh
      have processedEq :
          rangeValues baseValues start.val position.val = processed := rfl
      have parentSuffixLength : invariant.parentSuffix.length ≤
          baseValues.val.length := by
        rw [← List.length_map (fun value : Std.U32 => value.val),
          invariant.parent_values, processedEq]
        exact (parentIndices_length_le processed).trans (by
          rw [rangeValues_length baseValues start.val position.val
            invariant.start_le_position (Nat.le_of_lt basePositionBound)]
          omega)
      have maskSuffixLength : invariant.maskSuffix.length ≤
          baseValues.val.length := by
        rw [← List.length_map (fun value : Std.U8 => value.val),
          invariant.mask_values, processedEq]
        exact (parentMasks_length_le processed).trans (by
          rw [rangeValues_length baseValues start.val position.val
            invariant.start_le_position (Nat.le_of_lt basePositionBound)]
          omega)
      have valuesRoom : values.val.length < Std.Usize.max := by
        rw [invariant.values_eq, List.length_append]
        omega
      have masksRoom : masks.val.length < Std.Usize.max := by
        rw [invariant.masks_eq, List.length_append]
        omega
      obtain ⟨masksOut, masksRun, masksValue⟩ := Aeneas.Std.WP.spec_imp_exists
        (alloc.vec.Vec.push_spec masks present masksRoom)
      rw [masksRun]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨valuesOut, valuesRun, valuesValue⟩ := Aeneas.Std.WP.spec_imp_exists
        (alloc.vec.Vec.push_spec values parent valuesRoom)
      rw [valuesRun]
      simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.WP.spec,
        Aeneas.Std.WP.theta]
      refine ⟨?_, ?_⟩
      · refine ⟨{
          parentSuffix := invariant.parentSuffix ++ [parent]
          maskSuffix := invariant.maskSuffix ++ [present]
          values_eq := by rw [valuesValue, invariant.values_eq, List.append_assoc]
          masks_eq := by rw [masksValue, invariant.masks_eq, List.append_assoc]
          parent_values := by
            rw [List.map_append, List.map_singleton, invariant.parent_values,
              combinedEq, modelUpdate.1]
          mask_values := by
            rw [List.map_append, List.map_singleton, invariant.mask_values,
              combinedEq, modelUpdate.2]
            rw [groupInvariant.present_value, groupEq]
          start_le_position := invariant.start_le_position.trans
            (Nat.le_of_lt nextPositionStrict)
          position_le_end := groupInvariant.position_le_end
          next_parent_fresh := ?_
        }⟩
        intro next nextRun value member equality
        by_cases atEnd : nextPosition.val = currentEnd.val
        · rw [atEnd, end_eq_length] at nextRun
          simp at nextRun
        · obtain ⟨boundaryNext, boundaryRun, boundaryDifferent⟩ :=
            groupBoundary.resolve_left atEnd
          have nextLtEnd : nextPosition.val < currentEnd.val := by omega
          have baseNextBound : nextPosition.val < baseValues.val.length := by
            rw [← end_eq_length]
            exact nextLtEnd
          have boundaryBase : baseValues.val[nextPosition.val]? =
              some boundaryNext := by
            have currentRun := boundaryRun
            rw [invariant.values_eq,
              List.getElem?_append_left baseNextBound] at currentRun
            exact currentRun
          have nextEq : next = boundaryNext :=
            Option.some.inj (nextRun.symm.trans boundaryBase)
          subst next
          have nextRange := rangeValues_next baseValues start.val nextPosition.val
            (invariant.start_le_position.trans (Nat.le_of_lt nextPositionStrict))
            baseNextBound
          have nextValue : baseValues.val[nextPosition.val] = boundaryNext := by
            exact Option.some.inj
              ((List.getElem?_eq_getElem baseNextBound).symm.trans boundaryBase)
          have throughNextSorted := rangeValues_pairwise_prefix_of_range baseValues
            start.val (nextPosition.val + 1) currentEnd.val
            ((invariant.start_le_position.trans
              (Nat.le_of_lt nextPositionStrict)).trans (Nat.le_succ _))
            nextLtEnd sorted
          rw [nextRange, nextValue, combinedEq] at throughNextSorted
          change value ∈ rangeValues baseValues start.val nextPosition.val at member
          rw [combinedEq] at member
          exact processed_and_group_fresh_for_next processed group parent.val
            boundaryNext.val throughNextSorted groupNonempty groupParent
            (by simpa [parentValue] using boundaryDifferent) value member equality
      · change currentEnd.val - nextPosition.val <
          currentEnd.val - position.val
        omega
    · have inactiveScalar : ¬ position < currentEnd := by scalar_tac
      rw [if_neg inactiveScalar]
      simp only [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta]
      have positionEq : position.val = currentEnd.val :=
        Nat.le_antisymm invariant.position_le_end (Nat.le_of_not_gt active)
      refine ⟨rfl, ?_, ?_⟩
      · unfold indexValues
        rw [invariant.values_eq, List.map_append, invariant.parent_values,
          positionEq]
      · unfold maskValues
        rw [invariant.masks_eq, List.map_append, invariant.mask_values,
          positionEq]
  · exact ⟨{
      parentSuffix := []
      maskSuffix := []
      values_eq := by simp
      masks_eq := by simp
      parent_values := by simp [parentIndicesOf]
      mask_values := by simp [parentMasksOf, parentIndicesOf]
      start_le_position := Nat.le_refl _
      position_le_end := start_le_end
      next_parent_fresh := by simp
    }⟩

private theorem usize_succ_val_below_nine
    (level : Std.Usize) (level_lt_nine : level.val < 9) :
    (Std.Usize.wrapping_add level 1#usize).val = level.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  have size_large : 11 < UScalar.size .Usize := by
    rw [UScalar.size_def, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with bits | bits <;>
      rw [bits] <;> norm_num
  rw [← UScalar.size_UScalarTyUsize]
  omega

private theorem array_update_success_eq
    {n : Std.Usize} (values : Array α n) (index : Std.Usize)
    (value : α) (out : Array α n) (bound : index.val < values.length)
    (run : Array.update values index value = .ok out) :
    out = Aeneas.Std.Array.set values index value := by
  obtain ⟨witness, witnessRun, witnessEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.update_spec values index value bound)
  have witnessOut : witness = out :=
    Result.ok.inj (witnessRun.symm.trans run)
  simpa [witnessOut] using witnessEq

private theorem usize_max_gt_324 : 324 < Std.Usize.max := by
  rw [Std.Usize.max, Std.Usize.numBits, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with bits | bits <;>
    rw [bits] <;> norm_num

/-- Meaning of one entry to the unchanged eight-level constructor loop. -/
structure OuterInvariant
    (initial : List Nat)
    (iter : core.ops.range.Range Std.Usize)
    (values : IndexVec) (levelOffsets : LevelOffsets)
    (masks : MaskVec) (groupOffsets : GroupOffsets)
    (currentStart currentEnd : Std.Usize) : Prop where
  iter_end : iter.end.val = 8
  level_le_eight : iter.start.val ≤ 8
  current_start : currentStart.val =
    (levelPrefix initial iter.start.val).length
  current_end : currentEnd.val =
    (levelPrefix initial (iter.start.val + 1)).length
  level_values : indexValues values =
    levelPrefix initial (iter.start.val + 1)
  mask_values : maskValues masks = maskPrefix initial iter.start.val
  level_offsets : ∀ index, index ≤ iter.start.val →
    (levelOffsets.val[index]!).val = (levelPrefix initial index).length
  group_offsets : ∀ index, index < iter.start.val →
    (groupOffsets.val[index]!).val = (maskPrefix initial index).length

/-- Exact state returned after all eight unchanged constructor iterations. -/
structure OuterCompleted
    (initial : List Nat)
    (values : IndexVec) (levelOffsets : LevelOffsets)
    (masks : MaskVec) (groupOffsets : GroupOffsets)
    (currentEnd : Std.Usize)
    (pending : Option (Option aspis_core.merkle.Radix4BinaryCapTopology)) : Prop where
  pending_none : pending = none
  current_end : currentEnd.val = (levelPrefix initial 9).length
  level_values : indexValues values = levelPrefix initial 9
  mask_values : maskValues masks = maskPrefix initial 8
  level_offsets : ∀ index, index ≤ 8 →
    (levelOffsets.val[index]!).val = (levelPrefix initial index).length
  group_offsets : ∀ index, index < 8 →
    (groupOffsets.val[index]!).val = (maskPrefix initial index).length

def outerInvariantFor (initial : List Nat) :
    (core.ops.range.Range Std.Usize × IndexVec × LevelOffsets × MaskVec ×
      GroupOffsets × Std.Usize × Std.Usize) → Prop
  | (iter, values, levelOffsets, masks, groupOffsets,
      currentStart, currentEnd) =>
    OuterInvariant initial iter values levelOffsets masks groupOffsets
      currentStart currentEnd

def outerCompletedFor (initial : List Nat) :
    (IndexVec × LevelOffsets × MaskVec × GroupOffsets × Std.Usize ×
      Option (Option aspis_core.merkle.Radix4BinaryCapTopology)) → Prop
  | (values, levelOffsets, masks, groupOffsets, currentEnd, pending) =>
    OuterCompleted initial values levelOffsets masks groupOffsets currentEnd
      pending

set_option maxHeartbeats 4000000 in
theorem exact_outer_loop_spec
    (initial : List Nat)
    (initialSorted : initial.Pairwise (fun left right => left < right))
    (initialLength : initial.length ≤ 18)
    (iter : core.ops.range.Range Std.Usize)
    (values : IndexVec) (levelOffsets : LevelOffsets)
    (masks : MaskVec) (groupOffsets : GroupOffsets)
    (currentStart currentEnd : Std.Usize)
    (invariant : OuterInvariant initial iter values levelOffsets masks
      groupOffsets currentStart currentEnd) :
    aspis_core.merkle.Radix4BinaryCapTopology.new_loop0 iter values levelOffsets masks
      groupOffsets currentStart currentEnd
      ⦃ output => outerCompletedFor initial output ⦄ := by
  simp only [aspis_core.merkle.Radix4BinaryCapTopology.new_loop0]
  apply Aeneas.Std.loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize × IndexVec × LevelOffsets ×
        MaskVec × GroupOffsets × Std.Usize × Std.Usize =>
      8 - state.1.start.val)
    (outerInvariantFor initial)
    (outerCompletedFor initial)
  · rintro ⟨iter, values, levelOffsets, masks, groupOffsets,
      currentStart, currentEnd⟩ currentInvariant
    change OuterInvariant initial iter values levelOffsets masks groupOffsets
      currentStart currentEnd at currentInvariant
    unfold aspis_core.merkle.Radix4BinaryCapTopology.new_loop0.body
    by_cases active : iter.start.val < iter.end.val
    · have activeLevel : iter.start.val < 8 := by
        rw [currentInvariant.iter_end] at active
        exact active
      obtain ⟨⟨option, nextIter⟩, nextRun, optionEq, nextStart,
          nextEnd⟩ := Aeneas.Std.WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec iter active)
      rw [optionEq] at nextRun
      simp only [nextRun, Aeneas.Std.bind_tc_ok, lift]
      have groupOffsetBound : iter.start.val < groupOffsets.length := by
        scalar_tac
      obtain ⟨⟨oldGroupOffset, groupOffsetBack⟩, groupOffsetRun,
          oldGroupOffsetEq, groupOffsetBackEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Array.index_mut_usize_spec groupOffsets iter.start
            groupOffsetBound)
      rw [groupOffsetRun]
      simp only [Aeneas.Std.bind_tc_ok]
      have currentRange :
          rangeValues values currentStart.val currentEnd.val =
            parentLevelFrom initial iter.start.val := by
        rw [currentInvariant.current_start, currentInvariant.current_end]
        exact rangeValues_levelPrefix values initial iter.start.val
          currentInvariant.level_values
      have currentSorted :
          (rangeValues values currentStart.val currentEnd.val).Pairwise
            (fun left right => left < right) := by
        rw [currentRange]
        exact parentLevelFrom_pairwise_lt initial initialSorted iter.start.val
      have startLeEnd : currentStart.val ≤ currentEnd.val := by
        rw [currentInvariant.current_start, currentInvariant.current_end,
          levelPrefix_succ, List.length_append]
        omega
      have endEqLength : currentEnd.val = values.val.length := by
        calc
          currentEnd.val =
              (levelPrefix initial (iter.start.val + 1)).length :=
            currentInvariant.current_end
          _ = (indexValues values).length :=
            congrArg List.length currentInvariant.level_values.symm
          _ = values.val.length := by simp [indexValues]
      have valueLengthBound : values.val.length ≤ 162 := by
        calc
          values.val.length =
              (levelPrefix initial (iter.start.val + 1)).length := by
            rw [← endEqLength, currentInvariant.current_end]
          _ ≤ (iter.start.val + 1) * initial.length :=
            levelPrefix_length_le initial (iter.start.val + 1)
          _ ≤ 9 * 18 := Nat.mul_le_mul (by omega) initialLength
          _ = 162 := by norm_num
      have maskLengthBound : masks.val.length ≤ 144 := by
        calc
          masks.val.length = (maskValues masks).length := by
            simp [maskValues]
          _ = (maskPrefix initial iter.start.val).length :=
            congrArg List.length currentInvariant.mask_values
          _ ≤ iter.start.val * initial.length :=
            maskPrefix_length_le initial iter.start.val
          _ ≤ 8 * 18 := Nat.mul_le_mul (by omega) initialLength
          _ = 144 := by norm_num
      have valueRoom :
          values.val.length + values.val.length < Std.Usize.max := by
        have maxBound := usize_max_gt_324
        omega
      have maskRoom :
          masks.val.length + values.val.length < Std.Usize.max := by
        have maxBound := usize_max_gt_324
        omega
      obtain ⟨parentOutput, parentRun, parentPost⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (exact_parent_level_loop_spec values masks currentStart currentEnd
            currentSorted startLeEnd endEqLength valueRoom maskRoom)
      rw [parentRun]
      rcases parentOutput with ⟨nextValues, nextMasks, pending⟩
      change pending = none ∧
        indexValues nextValues = indexValues values ++
          parentIndicesOf
            (rangeValues values currentStart.val currentEnd.val) ∧
        maskValues nextMasks = maskValues masks ++
          parentMasksOf
            (rangeValues values currentStart.val currentEnd.val) at parentPost
      rcases parentPost with ⟨pendingNone, nextValuesEq, nextMasksEq⟩
      subst pending
      simp only [Aeneas.Std.bind_tc_ok, lift]
      let nextLevel := Std.Usize.wrapping_add iter.start 1#usize
      have nextLevelValue : nextLevel.val = iter.start.val + 1 :=
        usize_succ_val_below_nine iter.start (by omega)
      have nextLevelBound : nextLevel.val < levelOffsets.length := by
        scalar_tac
      obtain ⟨nextLevelOffsets, nextLevelOffsetsRun,
          nextLevelOffsetsEq⟩ := Aeneas.Std.WP.spec_imp_exists
        (Array.update_spec levelOffsets nextLevel currentEnd nextLevelBound)
      rw [nextLevelOffsetsRun]
      simp only [Aeneas.Std.bind_tc_ok]
      have nextValuesModel : indexValues nextValues =
          levelPrefix initial (iter.start.val + 2) := by
        have parentStep :
            parentIndicesOf (parentLevelFrom initial iter.start.val) =
              parentLevelFrom initial (iter.start.val + 1) := rfl
        rw [nextValuesEq, currentInvariant.level_values, currentRange,
          parentStep]
        simpa [Nat.add_assoc] using
          (levelPrefix_succ initial (iter.start.val + 1)).symm
      have nextMasksModel : maskValues nextMasks =
          maskPrefix initial (iter.start.val + 1) := by
        rw [nextMasksEq, currentInvariant.mask_values, currentRange]
        exact (maskPrefix_succ initial iter.start.val).symm
      have nextEndValue : (alloc.vec.Vec.len nextValues).val =
          (levelPrefix initial (iter.start.val + 2)).length := by
        rw [alloc.vec.Vec.len_val]
        calc
          nextValues.val.length = (indexValues nextValues).length := by
            simp [indexValues]
          _ = _ := congrArg List.length nextValuesModel
      have groupStartValue : (alloc.vec.Vec.len masks).val =
          (maskPrefix initial iter.start.val).length := by
        rw [alloc.vec.Vec.len_val]
        calc
          masks.val.length = (maskValues masks).length := by simp [maskValues]
          _ = _ := congrArg List.length currentInvariant.mask_values
      have storedLevelOffsets : nextLevelOffsets =
          Aeneas.Std.Array.set levelOffsets nextLevel currentEnd :=
        array_update_success_eq levelOffsets nextLevel currentEnd
          nextLevelOffsets nextLevelBound nextLevelOffsetsRun
      rw [groupOffsetBackEq]
      simp only [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta]
      constructor
      · change OuterInvariant initial nextIter nextValues nextLevelOffsets
          nextMasks
          (Aeneas.Std.Array.set groupOffsets iter.start
            (alloc.vec.Vec.len masks))
          currentEnd (alloc.vec.Vec.len nextValues)
        refine {
          iter_end := by rw [nextEnd, currentInvariant.iter_end]
          level_le_eight := by omega
          current_start := by
            rw [nextStart, currentInvariant.current_end]
          current_end := by
            rw [nextStart]
            simpa [Nat.add_assoc] using nextEndValue
          level_values := by
            rw [nextStart]
            simpa [Nat.add_assoc] using nextValuesModel
          mask_values := by
            rw [nextStart]
            exact nextMasksModel
          level_offsets := ?_
          group_offsets := ?_
        }
        · intro index indexLe
          rw [nextStart] at indexLe
          by_cases isNew : index = iter.start.val + 1
          · subst index
            rw [storedLevelOffsets, Aeneas.Std.Array.set_val_eq]
            rw [List.set_getElem!_eq levelOffsets.val nextLevel.val
              (iter.start.val + 1) currentEnd
              (by constructor <;> scalar_tac)]
            exact currentInvariant.current_end
          · have oldIndex : index ≤ iter.start.val := by omega
            rw [storedLevelOffsets, Aeneas.Std.Array.set_val_eq,
              List.set_getElem!_ne levelOffsets.val nextLevel.val index
                currentEnd
                (Or.inl (by simpa [nextLevelValue] using Ne.symm isNew))]
            exact currentInvariant.level_offsets index oldIndex
        · intro index indexLt
          rw [nextStart] at indexLt
          by_cases isNew : index = iter.start.val
          · subst index
            rw [Aeneas.Std.Array.set_val_eq]
            rw [List.set_getElem!_eq groupOffsets.val iter.start.val
              iter.start.val (alloc.vec.Vec.len masks)
              (by constructor <;> scalar_tac)]
            exact groupStartValue
          · have oldIndex : index < iter.start.val := by omega
            rw [Aeneas.Std.Array.set_val_eq,
              List.set_getElem!_ne groupOffsets.val iter.start.val index
                (alloc.vec.Vec.len masks) (Or.inl (Ne.symm isNew))]
            exact currentInvariant.group_offsets index oldIndex
      · change 8 - nextIter.start.val < 8 - iter.start.val
        omega
    · have inactive : iter.end.val ≤ iter.start.val := Nat.le_of_not_gt active
      obtain ⟨⟨option, nextIter⟩, nextRun, optionEq, nextIterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_none_spec iter inactive)
      rw [optionEq, nextIterEq] at nextRun
      simp only [nextRun, Aeneas.Std.bind_tc_ok, Aeneas.Std.WP.spec,
        Aeneas.Std.WP.theta]
      have finished : iter.start.val = 8 := by
        have eightLe : 8 ≤ iter.start.val := by
          rw [← currentInvariant.iter_end]
          exact inactive
        exact Nat.le_antisymm currentInvariant.level_le_eight eightLe
      change OuterCompleted initial values levelOffsets masks groupOffsets
        currentEnd none
      refine {
        pending_none := rfl
        current_end := by simpa [finished] using currentInvariant.current_end
        level_values := by simpa [finished] using currentInvariant.level_values
        mask_values := by simpa [finished] using currentInvariant.mask_values
        level_offsets := by
          intro index indexLe
          exact currentInvariant.level_offsets index (by omega)
        group_offsets := by
          intro index indexLt
          exact currentInvariant.group_offsets index (by omega)
      }
  · exact invariant

private theorem clone_u32_slice_eq (slice : Slice Std.U32) :
    Slice.clone core.clone.CloneU32.clone slice = .ok slice := by
  obtain ⟨cloned, run, equality⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.clone_spec (clone := core.clone.CloneU32.clone)
      (s := slice) (by simp))
  subst cloned
  exact run

private theorem u32_extend_value
    (base : IndexVec) (suffix : Slice Std.U32) (out : IndexVec)
    (run : alloc.vec.Vec.extend_from_slice core.clone.CloneU32
      base suffix = .ok out) :
    out.val = base.val ++ suffix.val := by
  unfold alloc.vec.Vec.extend_from_slice at run
  split at run
  · split at run
    · rename_i cloned cloneRun
      have clonedEq : cloned = suffix := by
        obtain ⟨witness, witnessRun, witnessEq⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Slice.clone_spec (clone := core.clone.CloneU32.clone)
              (s := suffix) (by simp))
        have witnessCloned : witness = cloned :=
          Result.ok.inj (witnessRun.symm.trans cloneRun)
        exact witnessCloned ▸ witnessEq.symm
      subst cloned
      exact congrArg (fun value : IndexVec => value.val)
        (Result.ok.inj run).symm
    · simp at run
    · simp at run
  · simp at run

private theorem bind_eq_ok_iff {A B : Type} (input : Result A)
    (next : A → Result B) (output : B) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem array_index_success_getElem!
    {n : Std.Usize} [Inhabited α] (values : Array α n)
    (index : Std.Usize) (value : α) (bound : index.val < values.length)
    (run : Array.index_usize values index = .ok value) :
    value = values.val[index.val]! := by
  obtain ⟨witness, witnessRun, witnessEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec values index bound)
  have witnessValue : witness = value :=
    Result.ok.inj (witnessRun.symm.trans run)
  calc
    value = witness := witnessValue.symm
    _ = values.val[index.val] := witnessEq
    _ = values.val[index.val]! := by
      have valueSome : values.val[index.val]? =
          some values.val[index.val] := by simp
      exact (List.getElem!_of_getElem? valueSome).symm

/-- Exact query-specific fields produced by the unchanged constructor. -/
structure FullExactConstructedTopologyFields
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology) : Prop where
  binaryDepth : topology.binary_depth.val = 17
  radixLevels : topology.radix_levels.val = 8
  levelValues : indexValues topology.level_indices =
    (sharedLevelLists queries).flatten
  groupMaskValues : maskValues topology.group_masks =
    (sharedGroupMaskLists queries).flatten
  levelOffset : ∀ (level offset : Std.Usize), level.val ≤ 9 →
    Array.index_usize topology.level_offsets level = .ok offset →
    offset.val = prefixOffset (sharedLevelLists queries) level.val
  groupOffset : ∀ (level offset : Std.Usize), level.val ≤ 8 →
    Array.index_usize topology.group_offsets level = .ok offset →
    offset.val = prefixOffset (sharedGroupMaskLists queries) level.val

private theorem shared_level_indices_pairwise_lt
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (level : Nat) :
    (sharedLevelIndices queries level).Pairwise
      (fun left right => left < right) := by
  unfold sharedLevelIndices AspisV5MerkleRustBridge.orderedActiveIndices
  exact ((Finset.pairwise_sort
    (AspisV5MerkleRustBridge.activeIndices .c1 queries level)
    (fun left right : Nat => left ≤ right)).sortedLE.sortedLT_of_nodup
      (Finset.sort_nodup _ _)).pairwise

private theorem shared_level_indices_length_le_card
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (level : Nat) :
    (sharedLevelIndices queries level).length ≤ queries.card := by
  unfold sharedLevelIndices AspisV5MerkleRustBridge.orderedActiveIndices
  rw [Finset.length_sort]
  unfold AspisV5MerkleRustBridge.activeIndices
  exact Finset.card_image_le

set_option maxHeartbeats 4000000 in
theorem exact_new_17_success_has_topology_fields
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (queryCount : queries.card = 18)
    (indices : Slice Std.U32)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (indicesModel : indices.val.map (fun index => index.val) =
      sharedLevelIndices queries 0)
    (run : aspis_core.merkle.Radix4BinaryCapTopology.new 17#u32 indices =
      .ok (some topology)) :
    FullExactConstructedTopologyFields queries topology := by
  unfold aspis_core.merkle.Radix4BinaryCapTopology.new at run
  simp only [lift, Aeneas.Std.bind_tc_ok] at run
  rw [bind_eq_ok_iff] at run
  rcases run with ⟨empty, emptyRun, run⟩
  by_cases isEmpty : empty = true
  · rw [if_pos isEmpty] at run
    simp at run
  · rw [if_neg isEmpty] at run
    norm_num at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨windows, windowsRun, run⟩
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨anyOutput, badOrderRun, run⟩
    rcases anyOutput with ⟨badOrder, finalClosure⟩
    by_cases hasBadOrder : badOrder = true
    · rw [if_pos hasBadOrder] at run
      simp at run
    · rw [if_neg hasBadOrder] at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨lastOption, lastOptionRun, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨copiedLast, copiedLastRun, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨lastControl, lastControlRun, run⟩
      cases lastControl with
      | Break residual =>
          simp only at run
          cases residual with
          | none =>
              change (.ok none : Result (Option aspis_core.merkle.Radix4BinaryCapTopology)) =
                .ok (some topology) at run
              simp at run
          | some impossible => exact nomatch impossible
      | Continue lastIndex =>
          simp only at run
          by_cases lastTooLarge :
              (Std.U32.wrapping_shl 1#u32 17#u32).val ≤ lastIndex.val
          · rw [if_pos lastTooLarge] at run
            simp at run
          · rw [if_neg lastTooLarge] at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨radixDepth, radixDepthRun, run⟩
            obtain ⟨computedDepth, computedDepthRun, computedDepthValue⟩ :=
              UScalar.div_spec (ty := .U32) 17#u32 (y := 2#u32)
                (by norm_num)
            have computedEq : computedDepth = radixDepth :=
              Result.ok.inj (computedDepthRun.symm.trans radixDepthRun)
            subst computedDepth
            have radixValue : radixDepth.val = 8 := by
              norm_num at computedDepthValue ⊢
              exact computedDepthValue
            have radixEq : radixDepth = 8#u32 :=
              UScalar.eq_of_val_eq (by simpa using radixValue)
            subst radixDepth
            have castEq : UScalar.cast .Usize (8#u32 : Std.U32) =
                8#usize := by
              apply UScalar.eq_of_val_eq
              rw [Std.U32.cast_Usize_val_eq]
              norm_num
            rw [castEq] at run
            simp only [alloc.vec.Vec.with_capacity] at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨initialValues, initialValuesRun, run⟩
            have initialRaw := u32_extend_value
              (alloc.vec.Vec.new Std.U32) indices initialValues
              initialValuesRun
            have initialValuesEq : initialValues.val = indices.val := by
              simpa using initialRaw
            have initialModel : indexValues initialValues =
                sharedLevelIndices queries 0 := by
              unfold indexValues
              rw [initialValuesEq, indicesModel]
            have initialSorted : (indexValues initialValues).Pairwise
                (fun left right => left < right) := by
              rw [initialModel]
              exact shared_level_indices_pairwise_lt queries 0
            have initialLength : (indexValues initialValues).length ≤ 18 := by
              rw [initialModel]
              exact (shared_level_indices_length_le_card queries 0).trans_eq
                queryCount
            let initial := indexValues initialValues
            have initialEq : initial = sharedLevelIndices queries 0 := by
              exact initialModel
            have initialInvariant : OuterInvariant initial
                { start := 0#usize, «end» := 8#usize }
                initialValues (Array.repeat 17#usize 0#usize)
                (alloc.vec.Vec.new Std.U8)
                (Array.repeat 16#usize 0#usize) 0#usize
                (alloc.vec.Vec.len initialValues) := by
              refine {
                iter_end := by norm_num
                level_le_eight := by norm_num
                current_start := by simp [initial]
                current_end := by
                  rw [alloc.vec.Vec.len_val]
                  simp [initial, levelPrefix_succ, parentLevelFrom,
                    indexValues]
                level_values := by
                  simp [initial, levelPrefix_succ, parentLevelFrom]
                mask_values := by simp [initial, maskValues]
                level_offsets := ?_
                group_offsets := ?_
              }
              · intro index indexLe
                have indexZero : index = 0 := by norm_num at indexLe ⊢; omega
                subst index
                simp [initial]
              · intro index indexLt
                norm_num at indexLt
            obtain ⟨outerOutput, outerRun, outerPost⟩ :=
              Aeneas.Std.WP.spec_imp_exists
                (exact_outer_loop_spec initial initialSorted
                  (by simpa [initial] using initialLength)
                  { start := 0#usize, «end» := 8#usize }
                  initialValues (Array.repeat 17#usize 0#usize)
                  (alloc.vec.Vec.new Std.U8)
                  (Array.repeat 16#usize 0#usize) 0#usize
                  (alloc.vec.Vec.len initialValues) initialInvariant)
            rw [outerRun] at run
            rcases outerOutput with
              ⟨finalValues, outerLevelOffsets, finalMasks,
                outerGroupOffsets, finalEnd, pending⟩
            change OuterCompleted initial finalValues outerLevelOffsets
              finalMasks outerGroupOffsets finalEnd pending at outerPost
            rw [outerPost.pending_none] at run
            simp only [Aeneas.Std.bind_tc_ok, lift] at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨finalLevelOffsets, finalLevelOffsetsRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨finalGroupOffsets, finalGroupOffsetsRun, run⟩
            have topologyEq : topology = {
                binary_depth := 17#u32
                radix_levels := 8#usize
                level_indices := finalValues
                level_offsets := finalLevelOffsets
                group_masks := finalMasks
                group_offsets := finalGroupOffsets
              } := by
              exact (Option.some.inj (Result.ok.inj run)).symm
            let finalLevel := Std.Usize.wrapping_add 8#usize 1#usize
            have finalLevelValue : finalLevel.val = 9 := by
              exact usize_succ_val_below_nine 8#usize (by norm_num)
            have finalLevelBound : finalLevel.val <
                outerLevelOffsets.length := by scalar_tac
            have finalGroupBound : (8#usize : Std.Usize).val <
                outerGroupOffsets.length := by scalar_tac
            have finalLevelSet : finalLevelOffsets =
                Aeneas.Std.Array.set outerLevelOffsets finalLevel finalEnd :=
              array_update_success_eq outerLevelOffsets finalLevel finalEnd
                finalLevelOffsets finalLevelBound finalLevelOffsetsRun
            have finalGroupSet : finalGroupOffsets =
                Aeneas.Std.Array.set outerGroupOffsets 8#usize
                  (alloc.vec.Vec.len finalMasks) :=
              array_update_success_eq outerGroupOffsets 8#usize
                (alloc.vec.Vec.len finalMasks) finalGroupOffsets
                finalGroupBound finalGroupOffsetsRun
            have finalMaskEnd : (alloc.vec.Vec.len finalMasks).val =
                (maskPrefix initial 8).length := by
              rw [alloc.vec.Vec.len_val]
              calc
                finalMasks.val.length = (maskValues finalMasks).length := by
                  simp [maskValues]
                _ = _ := congrArg List.length outerPost.mask_values
            have levelOffsetValues : ∀ index, index ≤ 9 →
                (finalLevelOffsets.val[index]!).val =
                  (levelPrefix initial index).length := by
              intro index indexLe
              by_cases isFinal : index = 9
              · subst index
                rw [finalLevelSet, Aeneas.Std.Array.set_val_eq]
                rw [List.set_getElem!_eq outerLevelOffsets.val
                  finalLevel.val 9 finalEnd
                  (by constructor <;> scalar_tac)]
                exact outerPost.current_end
              · have oldIndex : index ≤ 8 := by omega
                rw [finalLevelSet, Aeneas.Std.Array.set_val_eq,
                  List.set_getElem!_ne outerLevelOffsets.val finalLevel.val
                    index finalEnd
                    (Or.inl (by simpa [finalLevelValue] using Ne.symm isFinal))]
                exact outerPost.level_offsets index oldIndex
            have groupOffsetValues : ∀ index, index ≤ 8 →
                (finalGroupOffsets.val[index]!).val =
                  (maskPrefix initial index).length := by
              intro index indexLe
              by_cases isFinal : index = 8
              · subst index
                rw [finalGroupSet, Aeneas.Std.Array.set_val_eq]
                rw [List.set_getElem!_eq outerGroupOffsets.val
                  (8#usize : Std.Usize).val 8
                  (alloc.vec.Vec.len finalMasks)
                  (by constructor <;> scalar_tac)]
                exact finalMaskEnd
              · have oldIndex : index < 8 := by omega
                rw [finalGroupSet, Aeneas.Std.Array.set_val_eq,
                  List.set_getElem!_ne outerGroupOffsets.val
                    (8#usize : Std.Usize).val index
                    (alloc.vec.Vec.len finalMasks)
                    (Or.inl (Ne.symm isFinal))]
                exact outerPost.group_offsets index oldIndex
            have levelValues : indexValues finalValues =
                (sharedLevelLists queries).flatten := by
              rw [outerPost.level_values, initialEq]
              unfold levelPrefix
              rw [source_level_lists_are_shared]
            have groupMaskValues : maskValues finalMasks =
                (sharedGroupMaskLists queries).flatten := by
              rw [outerPost.mask_values, initialEq]
              unfold maskPrefix
              rw [source_group_mask_lists_are_shared]
            rw [topologyEq]
            refine {
              binaryDepth := rfl
              radixLevels := rfl
              levelValues := levelValues
              groupMaskValues := groupMaskValues
              levelOffset := ?_
              groupOffset := ?_
            }
            · intro level offset levelLe readRun
              have bound : level.val < finalLevelOffsets.length := by
                scalar_tac
              have readValue := array_index_success_getElem!
                finalLevelOffsets level offset bound readRun
              calc
                offset.val =
                    (finalLevelOffsets.val[level.val]!).val :=
                  congrArg (fun value : Std.Usize => value.val) readValue
                _ = (levelPrefix initial level.val).length :=
                  levelOffsetValues level.val (by norm_num at levelLe ⊢; omega)
                _ = (levelPrefix (sharedLevelIndices queries 0)
                    level.val).length := by rw [initialEq]
                _ = prefixOffset (sharedLevelLists queries) level.val :=
                  levelPrefix_shared_length_eq_prefixOffset queries level.val
                    levelLe
            · intro level offset levelLe readRun
              have bound : level.val < finalGroupOffsets.length := by
                scalar_tac
              have readValue := array_index_success_getElem!
                finalGroupOffsets level offset bound readRun
              calc
                offset.val =
                    (finalGroupOffsets.val[level.val]!).val :=
                  congrArg (fun value : Std.Usize => value.val) readValue
                _ = (maskPrefix initial level.val).length :=
                  groupOffsetValues level.val
                    (by norm_num at levelLe ⊢; omega)
                _ = (maskPrefix (sharedLevelIndices queries 0)
                    level.val).length := by rw [initialEq]
                _ = prefixOffset (sharedGroupMaskLists queries) level.val :=
                  maskPrefix_shared_length_eq_prefixOffset queries level.val
                    levelLe

#print axioms slotMask_and_fresh_bit_eq_zero
#print axioms same_parent_same_slot_eq
#print axioms fresh_slot_of_strict_prefix
#print axioms exact_group_loop_spec
#print axioms exact_parent_level_loop_spec
#print axioms exact_outer_loop_spec
#print axioms exact_new_17_success_has_topology_fields

end AspisV5MerkleUnchangedFullConstructorSemantics
