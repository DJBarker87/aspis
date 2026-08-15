import V5MerkleTopologyConstructorModel
import V5MerkleDeployedSource.Funs

/-!
This module proves the value-level behavior of the extracted parent-level
scan used by the Merkle topology constructor. The generated function is
defined in the extraction adapter because Aeneas cannot currently translate
the production nested loop directly. A separate source-equivalence argument
is still required to connect this adapter function to the unmodified Rust.
-/
open Aeneas Aeneas.Std Result ControlFlow Error


theorem shr2 (x : Std.U32) :
    (Std.U32.wrapping_shr x 2#u32).val = x.val / 4 := by
  unfold Std.U32.wrapping_shr UScalar.wrapping_shr
  norm_num
  change (BitVec.ushiftRight x.bv 2).toNat = x.bv.toNat / 4
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem and3 (x : Std.U32) : (x &&& 3#u32).val = x.val % 4 := by
  change x.val &&& 3 = x.val % 4
  simpa using Nat.and_two_pow_sub_one_eq_mod x.val 2

theorem slot_cast (x : Std.U32) (h : x.val < 4) :
    (UScalar.cast .U8 x).val = x.val := by
  simp [UScalar.cast_val_eq]
  omega

theorem shl_slot (x : Std.U32) (h : x.val < 4) :
    (Std.U8.wrapping_shl 1#u8
      (UScalar.cast .U32 (UScalar.cast .U8 x))).val = 2 ^ x.val := by
  have h8 : (UScalar.cast .U8 x).val = x.val := slot_cast x h
  have h32 : (UScalar.cast .U32 (UScalar.cast .U8 x)).val = x.val := by
    rw [Std.U8.cast_U32_val_eq, h8]
  unfold Std.U8.wrapping_shl UScalar.wrapping_shl
  norm_num
  unfold UScalar.val
  simp [Nat.shiftLeft_eq]
  change x.bv.toNat < 4 at h
  change 2 ^ (x.bv.toNat % 8) % 256 = 2 ^ x.bv.toNat
  interval_cases hx : x.bv.toNat <;> norm_num [hx] at *


theorem sort_insert_greatest (s : Finset Nat) (x : Nat)
    (hgreat : ∀ y ∈ s, y < x) :
    (insert x s).sort (· ≤ ·) = s.sort (· ≤ ·) ++ [x] := by
  apply @List.Perm.eq_of_pairwise Nat (· ≤ ·)
  · intro a b _ _ hab hba
    omega
  · exact Finset.pairwise_sort (insert x s) (· ≤ ·)
  · rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort s (· ≤ ·), by simp, ?_⟩
    intro y hy _ hz
    simp only [List.mem_singleton] at hz
    subst hz
    exact Nat.le_of_lt (hgreat y ((Finset.mem_sort (· ≤ ·)).mp hy))
  · have hxnot : x ∉ s.sort (· ≤ ·) := by
      intro hx
      have := hgreat x ((Finset.mem_sort (· ≤ ·)).mp hx)
      omega
    have hxnotS : x ∉ s := by
      intro hx
      have := hgreat x hx
      omega
    apply List.perm_of_nodup_nodup_toFinset_eq
      (Finset.sort_nodup (insert x s) (· ≤ ·))
    · rw [List.nodup_append]
      exact ⟨Finset.sort_nodup s (· ≤ ·), by simp,
        by simp [hxnotS]⟩
    ext y
    simp


open AspisV5MerkleTopologyConstructorModel

theorem parentIndices_append_same (xs : List Nat) (x : Nat)
    (hseen : ∃ y ∈ xs, y / 4 = x / 4) :
    parentIndicesOf (xs ++ [x]) = parentIndicesOf xs := by
  unfold parentIndicesOf
  have happ : (xs ++ [x]).toFinset = insert x xs.toFinset := by
    ext y
    simp
  rw [happ, Finset.image_insert]
  apply congrArg (Finset.sort · (· ≤ ·))
  apply Finset.insert_eq_self.mpr
  obtain ⟨old, hold, heq⟩ := hseen
  exact Finset.mem_image.mpr ⟨old, List.mem_toFinset.mpr hold, heq⟩

theorem parentIndices_append_new (xs : List Nat) (x : Nat)
    (hlt : ∀ y ∈ xs, y < x)
    (hfresh : ¬ ∃ y ∈ xs, y / 4 = x / 4) :
    parentIndicesOf (xs ++ [x]) = parentIndicesOf xs ++ [x / 4] := by
  unfold parentIndicesOf
  have hgreat : ∀ parent ∈ xs.toFinset.image (fun index => index / 4),
      parent < x / 4 := by
    intro parent hparent
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hparent
    have hle : y / 4 ≤ x / 4 := Nat.div_le_div_right (Nat.le_of_lt
      (hlt y (List.mem_toFinset.mp hy)))
    have hne : y / 4 ≠ x / 4 := by
      intro heq
      exact hfresh ⟨y, List.mem_toFinset.mp hy, heq⟩
    omega
  have happ : (xs ++ [x]).toFinset = insert x xs.toFinset := by
    ext y
    simp
  rw [happ, Finset.image_insert]
  exact sort_insert_greatest _ _ hgreat


theorem slotMask_four (slots : Finset (Fin 4)) :
    AspisV5TopologyConstruction.slotMask slots =
      (if (0 : Fin 4) ∈ slots then 1 else 0) +
      (if (1 : Fin 4) ∈ slots then 2 else 0) +
      (if (2 : Fin 4) ∈ slots then 4 else 0) +
      (if (3 : Fin 4) ∈ slots then 8 else 0) := by
  unfold AspisV5TopologyConstruction.slotMask
  have heq : (∑ slot ∈ slots, 2 ^ slot.val) =
      ∑ slot : Fin 4, if slot ∈ slots then 2 ^ slot.val else 0 := by
    rw [← Finset.sum_filter]
    congr
    ext slot
    simp
  rw [heq, Fin.sum_univ_four]
  norm_num

theorem slotMask_insert_or (slots : Finset (Fin 4)) (slot : Fin 4)
    (hnot : slot ∉ slots) :
    AspisV5TopologyConstruction.slotMask slots ||| 2 ^ slot.val =
      AspisV5TopologyConstruction.slotMask (insert slot slots) := by
  rw [slotMask_four, slotMask_four]
  fin_cases slot <;>
    by_cases h0 : (0 : Fin 4) ∈ slots <;>
    by_cases h1 : (1 : Fin 4) ∈ slots <;>
    by_cases h2 : (2 : Fin 4) ∈ slots <;>
    by_cases h3 : (3 : Fin 4) ∈ slots <;>
    simp [h0, h1, h2, h3] at hnot ⊢


theorem presentSlots_append_same_parent (xs : List Nat) (x : Nat) :
    presentSlotsOf (xs ++ [x]) (x / 4) =
      insert ⟨x % 4, Nat.mod_lt _ (by decide)⟩
        (presentSlotsOf xs (x / 4)) := by
  ext slot
  simp only [presentSlotsOf, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_append, List.mem_singleton, Finset.mem_insert]
  have hdecomp := Nat.mod_add_div x 4
  have hx : 4 * (x / 4) + x % 4 = x := by
    simpa [Nat.add_comm] using hdecomp
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · left
      apply Fin.ext
      exact Nat.add_left_cancel (h.trans hx.symm)
  · intro h
    rcases h with h | h
    · right
      have hval := congrArg Fin.val h
      simpa [hval] using hx
    · exact Or.inl h

theorem presentSlots_append_other_parent (xs : List Nat) (x parent : Nat)
    (hne : parent ≠ x / 4) :
    presentSlotsOf (xs ++ [x]) parent = presentSlotsOf xs parent := by
  ext slot
  simp only [presentSlotsOf, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_append, List.mem_singleton]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exfalso
      have hslot := slot.isLt
      have hdecomp := Nat.mod_add_div x 4
      apply hne
      omega
  · exact Or.inl

theorem slotMask_presentSlots_append_same (xs : List Nat) (x : Nat)
    (hfresh : x ∉ xs) :
    AspisV5TopologyConstruction.slotMask
        (presentSlotsOf (xs ++ [x]) (x / 4)) =
      AspisV5TopologyConstruction.slotMask (presentSlotsOf xs (x / 4)) |||
        2 ^ (x % 4) := by
  rw [presentSlots_append_same_parent]
  symm
  have hnot : (⟨x % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) ∉
      presentSlotsOf xs (x / 4) := by
    simp only [presentSlotsOf, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    apply hfresh
    have hdecomp := Nat.mod_add_div x 4
    have hx : 4 * (x / 4) + x % 4 = x := by
      simpa [Nat.add_comm] using hdecomp
    simpa [hx] using h
  simpa using slotMask_insert_or (presentSlotsOf xs (x / 4))
    (⟨x % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) hnot

theorem slotMask_presentSlots_append_other (xs : List Nat) (x parent : Nat)
    (hne : parent ≠ x / 4) :
    AspisV5TopologyConstruction.slotMask
        (presentSlotsOf (xs ++ [x]) parent) =
      AspisV5TopologyConstruction.slotMask (presentSlotsOf xs parent) := by
  rw [presentSlots_append_other_parent xs x parent hne]


theorem parentIndicesOf_pairwise_lt (xs : List Nat) :
    (parentIndicesOf xs).Pairwise (· < ·) := by
  unfold parentIndicesOf
  exact ((Finset.pairwise_sort
    (xs.toFinset.image fun index => index / 4)
    (fun left right : Nat => left ≤ right)).sortedLE.sortedLT_of_nodup
      (Finset.sort_nodup _ _)).pairwise


theorem parent_mem_yields_child {xs : List Nat} {parent : Nat}
    (hparent : parent ∈ parentIndicesOf xs) :
    ∃ child ∈ xs, child / 4 = parent := by
  unfold parentIndicesOf at hparent
  have hfin := (Finset.mem_sort (· ≤ ·)).mp hparent
  obtain ⟨child, hchild, rfl⟩ := Finset.mem_image.mp hfin
  exact ⟨child, List.mem_toFinset.mp hchild, rfl⟩

theorem last_parent_eq_of_seen (xs : List Nat) (x parent : Nat)
    (completed : List Nat)
    (hparents : parentIndicesOf xs = completed ++ [parent])
    (hlt : ∀ y ∈ xs, y < x)
    (hseen : ∃ y ∈ xs, y / 4 = x / 4) :
    parent = x / 4 := by
  have hparentMem : parent ∈ parentIndicesOf xs := by
    rw [hparents]
    simp
  obtain ⟨lastChild, hlastChild, hlastQuotient⟩ :=
    parent_mem_yields_child hparentMem
  have hparentLe : parent ≤ x / 4 := by
    rw [← hlastQuotient]
    exact Nat.div_le_div_right (Nat.le_of_lt (hlt lastChild hlastChild))
  obtain ⟨seenChild, hseenChild, hseenQuotient⟩ := hseen
  have hseenMem : x / 4 ∈ parentIndicesOf xs := by
    unfold parentIndicesOf
    rw [Finset.mem_sort]
    exact Finset.mem_image.mpr
      ⟨seenChild, List.mem_toFinset.mpr hseenChild, hseenQuotient⟩
  rw [hparents] at hseenMem
  simp only [List.mem_append, List.mem_singleton] at hseenMem
  rcases hseenMem with hcompleted | heq
  · have hpairs := parentIndicesOf_pairwise_lt xs
    rw [hparents, List.pairwise_append] at hpairs
    have hltParent := hpairs.2.2 (x / 4) hcompleted parent (by simp)
    omega
  · exact heq.symm


namespace ScanProof

open V5MerkleDeployedSource

def scanValues (input : Slice Std.U32) : List Nat :=
  input.val.map fun index => index.val

def scanPrefix (input : Slice Std.U32) (position : Std.Usize) : List Nat :=
  (scanValues input).take position.val

structure ActiveParentScanState
    (input : Slice Std.U32)
    (parents : alloc.vec.Vec Std.U32)
    (masks : alloc.vec.Vec Std.U8)
    (position : Std.Usize)
    (parent : Std.U32)
    (present : Std.U8) : Type where
  completed : List Nat
  parent_indices :
    parentIndicesOf (scanPrefix input position) = completed ++ [parent.val]
  parent_values : parents.val.map (fun value => value.val) = completed
  mask_values : masks.val.map (fun value => value.val) =
    completed.map fun completedParent =>
      AspisV5TopologyConstruction.slotMask
        (presentSlotsOf (scanPrefix input position) completedParent)
  present_value : present.val = AspisV5TopologyConstruction.slotMask
    (presentSlotsOf (scanPrefix input position) parent.val)
  parent_count_lt_position : parents.val.length < position.val

def ParentScanInvariant (input : Slice Std.U32) :
    (alloc.vec.Vec Std.U32 × alloc.vec.Vec Std.U8 × Std.Usize × Bool ×
      Std.U32 × Std.U8) → Prop
  | (parents, masks, position, haveParent, parent, present) =>
      position.val ≤ input.val.length ∧
        if haveParent then
          Nonempty (ActiveParentScanState input parents masks position parent present)
        else
          position.val = 0 ∧ parents.val = [] ∧ masks.val = []

def ParentLoopPost (input : Slice Std.U32) :
    (alloc.vec.Vec Std.U32 × alloc.vec.Vec Std.U8 × Bool × Std.U32 ×
      Std.U8) → Prop
  | (parents, masks, haveParent, parent, present) =>
      if haveParent then
        parents.val.map (fun value => value.val) ++ [parent.val] =
            parentIndicesOf (scanValues input) ∧
          masks.val.map (fun value => value.val) ++ [present.val] =
            parentMasksOf (scanValues input) ∧
          parents.val.length < input.val.length ∧
          masks.val.length < input.val.length
      else
        scanValues input = [] ∧ parents.val = [] ∧ masks.val = []

private theorem usize_succ_val_below_length
    (input : Slice α) (position : Std.Usize)
    (hposition : position.val < input.val.length) :
    (Std.Usize.wrapping_add position 1#usize).val = position.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  have hlength : input.val.length ≤ Std.Usize.max := input.property
  have hmax : Std.Usize.max < UScalar.size .Usize := by
    rw [Std.Usize.max, Std.Usize.numBits, UScalar.size_def,
      UScalarTy.Usize_numBits_eq]
    exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hmaxUsize : Std.Usize.max < Std.Usize.size := by
    rw [← UScalar.size_UScalarTyUsize]
    exact hmax
  omega

private theorem slice_index_success_value
    (input : Slice α) (position : Std.Usize) (value : α)
    (hposition : position.val < input.val.length)
    (hrun : Slice.index_usize input position = .ok value) :
    value = input.val[position.val] := by
  obtain ⟨witness, hwitness, heq⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Slice.index_usize_spec input position hposition)
  have : witness = value := Result.ok.inj (hwitness.symm.trans hrun)
  exact this ▸ heq

private theorem vec_push_success_value
    (values : alloc.vec.Vec α) (value : α)
    (out : alloc.vec.Vec α) (hbound : values.val.length < Std.Usize.max)
    (hrun : alloc.vec.Vec.push values value = .ok out) :
    out.val = values.val ++ [value] := by
  obtain ⟨witness, hwitness, heq⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec values value hbound)
  have : witness = out := Result.ok.inj (hwitness.symm.trans hrun)
  exact this ▸ heq

private theorem scanPrefix_next
    (input : Slice Std.U32) (position : Std.Usize) (index : Std.U32)
    (hposition : position.val < input.val.length)
    (hindex : index = input.val[position.val]) :
    scanPrefix input (Std.Usize.wrapping_add position 1#usize) =
      scanPrefix input position ++ [index.val] := by
  unfold scanPrefix scanValues
  rw [usize_succ_val_below_length input position hposition]
  have hmapBound : position.val <
      (input.val.map fun value => value.val).length := by
    simpa using hposition
  rw [← List.take_append_getElem hmapBound, List.getElem_map]
  simp [hindex]

private theorem prefix_values_lt_current
    (input : Slice Std.U32) (position : Std.Usize) (index : Std.U32)
    (hsorted : (scanValues input).Pairwise (· < ·))
    (hposition : position.val < input.val.length)
    (hindex : index = input.val[position.val]) :
    ∀ value ∈ scanPrefix input position, value < index.val := by
  intro value hvalue
  apply hsorted.rel_of_mem_take_of_mem_drop hvalue
  rw [List.mem_drop_iff_getElem]
  refine ⟨0, by simpa [scanValues] using hposition, ?_⟩
  unfold scanValues
  rw [List.getElem_map]
  simp [hindex]

private theorem prefix_current_fresh
    (input : Slice Std.U32) (position : Std.Usize) (index : Std.U32)
    (hsorted : (scanValues input).Pairwise (· < ·))
    (hposition : position.val < input.val.length)
    (hindex : index = input.val[position.val]) :
    index.val ∉ scanPrefix input position := by
  intro hmem
  have := prefix_values_lt_current input position index hsorted hposition hindex
    index.val hmem
  omega

private theorem masks_length_eq_parents_length
    {input : Slice Std.U32} {parents : alloc.vec.Vec Std.U32}
    {masks : alloc.vec.Vec Std.U8} {position : Std.Usize}
    {parent : Std.U32} {present : Std.U8}
    (hstate : ActiveParentScanState input parents masks position parent present) :
    masks.val.length = parents.val.length := by
  rw [← List.length_map (fun value : Std.U8 => value.val),
    hstate.mask_values, List.length_map, ← hstate.parent_values,
    List.length_map]

private theorem completed_masks_unchanged
    (processed : List Nat) (x : Nat) (completed : List Nat)
    (currentParent : Nat)
    (hparents : parentIndicesOf processed = completed ++ [currentParent])
    (hlt : ∀ value ∈ processed, value < x)
    (hne : currentParent ≠ x / 4) :
    completed.map (fun p => AspisV5TopologyConstruction.slotMask
        (presentSlotsOf (processed ++ [x]) p)) =
      completed.map (fun p => AspisV5TopologyConstruction.slotMask
        (presentSlotsOf processed p)) := by
  apply List.map_congr_left
  intro p hp
  have hpNeCurrent : p ≠ currentParent := by
    intro heq
    subst p
    have hpairs := parentIndicesOf_pairwise_lt processed
    rw [hparents, List.pairwise_append] at hpairs
    have := hpairs.2.2 currentParent hp currentParent (by simp)
    omega
  have hpNeNext : p ≠ x / 4 := by
    intro heq
    have hnextMem : x / 4 ∈ parentIndicesOf processed := by
      rw [hparents]
      simp [← heq, hp]
    have hseen := parent_mem_yields_child hnextMem
    exact hne (last_parent_eq_of_seen processed x currentParent completed
      hparents hlt hseen)
  exact slotMask_presentSlots_append_other processed x p hpNeNext

private theorem completed_masks_same_parent_unchanged
    (processed : List Nat) (x : Nat) (completed : List Nat)
    (currentParent : Nat)
    (hparents : parentIndicesOf processed = completed ++ [currentParent])
    (hsame : currentParent = x / 4) :
    completed.map (fun p => AspisV5TopologyConstruction.slotMask
        (presentSlotsOf (processed ++ [x]) p)) =
      completed.map (fun p => AspisV5TopologyConstruction.slotMask
        (presentSlotsOf processed p)) := by
  apply List.map_congr_left
  intro p hp
  have hpNeCurrent : p ≠ currentParent := by
    intro heq
    subst p
    have hpairs := parentIndicesOf_pairwise_lt processed
    rw [hparents, List.pairwise_append] at hpairs
    have := hpairs.2.2 currentParent hp currentParent (by simp)
    omega
  apply slotMask_presentSlots_append_other
  exact fun heq => hpNeCurrent (heq.trans hsame.symm)

theorem generated_parent_loop_spec
    (input : Slice Std.U32)
    (hsorted : (scanValues input).Pairwise (· < ·)) :
    merkle.topology_parent_level_loop input
      (alloc.vec.Vec.new Std.U32) (alloc.vec.Vec.new Std.U8)
      0#usize false 0#u32 0#u8
      ⦃ output => ParentLoopPost input output ⦄ := by
  simp only [merkle.topology_parent_level_loop]
  apply Aeneas.Std.loop.spec_decr_nat
    (fun state : alloc.vec.Vec Std.U32 × alloc.vec.Vec Std.U8 ×
        Std.Usize × Bool × Std.U32 × Std.U8 =>
      input.val.length - state.2.2.1.val)
    (ParentScanInvariant input)
    (ParentLoopPost input)
  · rintro ⟨parents, masks, position, haveParent, parent, present⟩ hinvariant
    rcases hinvariant with ⟨hpositionLe, hstate⟩
    unfold merkle.topology_parent_level_loop.body
    simp only [Prod.fst, Prod.snd]
    by_cases hactive : position.val < input.val.length
    · have hactiveScalar : position < Slice.len input := by scalar_tac
      rw [if_pos hactiveScalar]
      obtain ⟨index, hindexRun, hindexValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.index_usize_spec input position hactive)
      rw [hindexRun]
      simp only [Aeneas.Std.bind_tc_ok, lift]
      let indexParent := Std.U32.wrapping_shr index 2#u32
      let lowSlot := index &&& 3#u32
      let slotMaskScalar := Std.U8.wrapping_shl 1#u8
        (UScalar.cast .U32 (UScalar.cast .U8 lowSlot))
      have hindexParent : indexParent.val = index.val / 4 := by
        exact shr2 index
      have hlowSlot : lowSlot.val = index.val % 4 := and3 index
      have hlowSlotBound : lowSlot.val < 4 := by
        rw [hlowSlot]
        exact Nat.mod_lt _ (by decide)
      have hslotMask : slotMaskScalar.val = 2 ^ (index.val % 4) := by
        rw [show slotMaskScalar = Std.U8.wrapping_shl 1#u8
            (UScalar.cast .U32 (UScalar.cast .U8 lowSlot)) by rfl,
          shl_slot lowSlot hlowSlotBound, hlowSlot]
      cases haveParent with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstate ⊢
          rcases hstate with ⟨hpositionZero, hparentsEmpty, hmasksEmpty⟩
          simp only [lift, Aeneas.Std.bind_tc_ok, Aeneas.Std.WP.spec,
            Aeneas.Std.WP.theta]
          have hnextPosition := usize_succ_val_below_length input position hactive
          have hprefixEmpty : scanPrefix input position = [] := by
            simp [scanPrefix, hpositionZero]
          have hprefixNext := scanPrefix_next input position index hactive
            hindexValue
          refine ⟨?_, ?_⟩
          · refine ⟨by rw [hnextPosition]; omega, ?_⟩
            exact ⟨{
              completed := []
              parent_indices := by
                rw [hprefixNext, hprefixEmpty, hindexParent]
                simp [parentIndicesOf]
              parent_values := by simpa using hparentsEmpty
              mask_values := by simpa using hmasksEmpty
              present_value := by
                rw [hslotMask, hprefixNext, hprefixEmpty, hindexParent]
                symm
                simpa [presentSlotsOf, AspisV5TopologyConstruction.slotMask]
                  using slotMask_presentSlots_append_same [] index.val
                    (by simp)
              parent_count_lt_position := by
                rw [hparentsEmpty, hnextPosition]
                simp
            }⟩
          · rw [hnextPosition]
            omega
      | true =>
          simp only [if_pos rfl] at hstate ⊢
          let activeState := Classical.choice hstate
          by_cases hsame : Std.U32.wrapping_shr index 2#u32 = parent
          · rw [if_pos hsame]
            simp only [lift, Aeneas.Std.bind_tc_ok, Aeneas.Std.WP.spec,
              Aeneas.Std.WP.theta]
            have hsameParent : parent.val = index.val / 4 := by
              have hvalue := congrArg (fun value : Std.U32 => value.val) hsame
              rw [shr2 index] at hvalue
              exact hvalue.symm
            have hnextPosition := usize_succ_val_below_length input position
              hactive
            have hprefixNext := scanPrefix_next input position index hactive
              hindexValue
            have hlt := prefix_values_lt_current input position index hsorted
              hactive hindexValue
            have hfresh := prefix_current_fresh input position index hsorted
              hactive hindexValue
            have hparentMem : parent.val ∈
                parentIndicesOf (scanPrefix input position) := by
              rw [activeState.parent_indices]
              simp
            obtain ⟨oldChild, holdChild, holdParent⟩ :=
              parent_mem_yields_child hparentMem
            have hseen : ∃ value ∈ scanPrefix input position,
                value / 4 = index.val / 4 := by
              exact ⟨oldChild, holdChild, holdParent.trans hsameParent⟩
            refine ⟨?_, ?_⟩
            · refine ⟨by rw [hnextPosition]; omega, ?_⟩
              exact ⟨{
                completed := activeState.completed
                parent_indices := by
                  rw [hprefixNext,
                    parentIndices_append_same _ _ hseen,
                    activeState.parent_indices, hsameParent]
                parent_values := activeState.parent_values
                mask_values := by
                  rw [hprefixNext,
                    completed_masks_same_parent_unchanged
                      (scanPrefix input position) index.val
                      activeState.completed parent.val
                      activeState.parent_indices hsameParent]
                  exact activeState.mask_values
                present_value := by
                  rw [UScalar.val_or, hslotMask, activeState.present_value,
                    hprefixNext, hsameParent]
                  exact (slotMask_presentSlots_append_same
                    (scanPrefix input position) index.val hfresh).symm
                parent_count_lt_position := by
                  rw [hnextPosition]
                  exact Nat.lt_succ_of_lt activeState.parent_count_lt_position
              }⟩
            · rw [hnextPosition]
              omega
          · rw [if_neg hsame]
            have hparentBound : parents.val.length < Std.Usize.max := by
              have hinputBound := input.property
              have hcount := activeState.parent_count_lt_position
              omega
            have hmasksLength := masks_length_eq_parents_length activeState
            have hmasksBound : masks.val.length < Std.Usize.max := by omega
            obtain ⟨parents2, hparentsRun, hparentsValue⟩ :=
              Aeneas.Std.WP.spec_imp_exists
                (alloc.vec.Vec.push_spec parents parent hparentBound)
            rw [hparentsRun]
            simp only [Aeneas.Std.bind_tc_ok]
            obtain ⟨masks2, hmasksRun, hmasksValue⟩ :=
              Aeneas.Std.WP.spec_imp_exists
                (alloc.vec.Vec.push_spec masks present hmasksBound)
            rw [hmasksRun]
            simp only [Aeneas.Std.bind_tc_ok, lift, Aeneas.Std.WP.spec,
              Aeneas.Std.WP.theta]
            have hnextPosition := usize_succ_val_below_length input position
              hactive
            have hprefixNext := scanPrefix_next input position index hactive
              hindexValue
            have hlt := prefix_values_lt_current input position index hsorted
              hactive hindexValue
            have hindexFresh := prefix_current_fresh input position index
              hsorted hactive hindexValue
            have hparentsValue' : parents2.val = parents.val ++ [parent] := by
              exact hparentsValue
            have hmasksValue' : masks2.val = masks.val ++ [present] := by
              exact hmasksValue
            have hdifferentParent : parent.val ≠ index.val / 4 := by
              intro heq
              apply hsame
              apply UScalar.eq_of_val_eq
              rw [shr2 index]
              exact heq.symm
            have hfreshParent : ¬ ∃ value ∈ scanPrefix input position,
                value / 4 = index.val / 4 := by
              intro hseen
              exact hdifferentParent
                (last_parent_eq_of_seen (scanPrefix input position)
                  index.val parent.val activeState.completed
                  activeState.parent_indices hlt hseen)
            have hpresentEmpty :
                presentSlotsOf (scanPrefix input position) (index.val / 4) = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro slot hmem
              simp only [presentSlotsOf, Finset.mem_filter,
                Finset.mem_univ, true_and] at hmem
              apply hfreshParent
              exact ⟨4 * (index.val / 4) + slot.val, hmem, by
                have hslot := slot.isLt
                omega⟩
            refine ⟨?_, ?_⟩
            · refine ⟨by rw [hnextPosition]; omega, ?_⟩
              exact ⟨{
                completed := activeState.completed ++ [parent.val]
                parent_indices := by
                  rw [hprefixNext,
                    parentIndices_append_new _ _ hlt hfreshParent,
                    activeState.parent_indices, hindexParent,
                    List.append_assoc]
                parent_values := by
                  rw [hparentsValue', List.map_append,
                    activeState.parent_values]
                  rfl
                mask_values := by
                  rw [hmasksValue', List.map_append,
                    activeState.mask_values, List.map_append,
                    hprefixNext,
                    completed_masks_unchanged
                      (scanPrefix input position) index.val
                      activeState.completed parent.val
                      activeState.parent_indices hlt hdifferentParent]
                  simp only [List.map_singleton]
                  rw [activeState.present_value,
                    slotMask_presentSlots_append_other
                    (scanPrefix input position) index.val parent.val
                    hdifferentParent]
                present_value := by
                  rw [hslotMask, hprefixNext, hindexParent]
                  have hmodel := slotMask_presentSlots_append_same
                    (scanPrefix input position) index.val hindexFresh
                  rw [hpresentEmpty] at hmodel
                  simpa [AspisV5TopologyConstruction.slotMask] using hmodel.symm
                parent_count_lt_position := by
                  rw [hparentsValue', List.length_append, hnextPosition]
                  simp
                  exact activeState.parent_count_lt_position
              }⟩
            · rw [hnextPosition]
              omega
    · have hdoneScalar : ¬ position < Slice.len input := by scalar_tac
      rw [if_neg hdoneScalar]
      simp only [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta]
      have hpositionEq : position.val = input.val.length := by omega
      have hprefixFull : scanPrefix input position = scanValues input := by
        unfold scanPrefix
        rw [hpositionEq]
        have hlength : (scanValues input).length = input.val.length := by
          simp [scanValues]
        rw [← hlength, List.take_length]
      cases haveParent with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstate ⊢
          rcases hstate with ⟨hzero, hparents, hmasks⟩
          refine ⟨?_, hparents, hmasks⟩
          have hlength : (scanValues input).length = 0 := by
            unfold scanValues
            simp [← hpositionEq, hzero]
          exact List.length_eq_zero_iff.mp hlength
      | true =>
          simp only [if_pos rfl] at hstate ⊢
          let activeState := Classical.choice hstate
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [activeState.parent_values, ← activeState.parent_indices,
              hprefixFull]
          · unfold parentMasksOf
            rw [← hprefixFull, activeState.parent_indices, List.map_append,
              List.map_singleton, activeState.mask_values,
              activeState.present_value]
          · rw [← hpositionEq]
            exact activeState.parent_count_lt_position
          · rw [masks_length_eq_parents_length activeState,
              ← hpositionEq]
            exact activeState.parent_count_lt_position
  · refine ⟨by norm_num, ?_⟩
    norm_num


end ScanProof

namespace ScanProof

open V5MerkleDeployedSource

def GeneratedParentLevelSourceEquality : Prop :=
  ∀ (input : Slice Std.U32)
      (nextIndices : alloc.vec.Vec Std.U32)
      (nextMasks : alloc.vec.Vec Std.U8),
    (input.val.map fun index => index.val).Pairwise (· < ·) →
      merkle.topology_parent_level input = .ok (nextIndices, nextMasks) →
        nextIndices.val.map (fun index => index.val) =
            parentIndicesOf (input.val.map fun index => index.val) ∧
          nextMasks.val.map (fun mask => mask.val) =
            parentMasksOf (input.val.map fun index => index.val)

theorem generated_parent_level_source_equality :
    GeneratedParentLevelSourceEquality := by
  intro input nextIndices nextMasks hsorted hrun
  change (alloc.vec.Vec.v nextIndices).map (fun index => index.val) =
      parentIndicesOf (scanValues input) ∧
    (alloc.vec.Vec.v nextMasks).map (fun mask => mask.val) =
      parentMasksOf (scanValues input)
  unfold merkle.topology_parent_level at hrun
  simp only [alloc.vec.Vec.with_capacity] at hrun
  obtain ⟨loopOut, hloopRun, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (generated_parent_loop_spec input hsorted)
  rw [hloopRun] at hrun
  rcases loopOut with ⟨parents, masks, haveParent, parent, present⟩
  cases haveParent with
  | false =>
      simp only [Aeneas.Std.bind_tc_ok, Bool.false_eq_true, if_false] at hrun
      have hout : (parents, masks) = (nextIndices, nextMasks) :=
        Result.ok.inj hrun
      have hnextIndices : nextIndices = parents :=
        (congrArg Prod.fst hout).symm
      have hnextMasks : nextMasks = masks :=
        (congrArg Prod.snd hout).symm
      constructor
      · rw [hnextIndices, show alloc.vec.Vec.v parents = [] from hpost.2.1,
          hpost.1]
        simp [parentIndicesOf]
      · rw [hnextMasks, show alloc.vec.Vec.v masks = [] from hpost.2.2,
          hpost.1]
        simp [parentMasksOf, parentIndicesOf]
  | true =>
      have hparentBound : parents.val.length < Std.Usize.max := by
        exact lt_of_lt_of_le hpost.2.2.1 input.property
      have hmaskBound : masks.val.length < Std.Usize.max := by
        exact lt_of_lt_of_le hpost.2.2.2 input.property
      simp only [Aeneas.Std.bind_tc_ok, if_pos rfl] at hrun
      obtain ⟨parents2, hparentsRun, hparentsValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec parents parent hparentBound)
      rw [hparentsRun] at hrun
      simp only [Aeneas.Std.bind_tc_ok] at hrun
      obtain ⟨masks2, hmasksRun, hmasksValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec masks present hmaskBound)
      rw [hmasksRun] at hrun
      have hout : (parents2, masks2) = (nextIndices, nextMasks) :=
        Result.ok.inj hrun
      cases hout
      have hparentsValue' : alloc.vec.Vec.v nextIndices =
          alloc.vec.Vec.v parents ++ [parent] := hparentsValue
      have hmasksValue' : alloc.vec.Vec.v nextMasks =
          alloc.vec.Vec.v masks ++ [present] := hmasksValue
      constructor
      · rw [hparentsValue', List.map_append, List.map_singleton]
        simpa [scanValues] using hpost.1
      · rw [hmasksValue', List.map_append, List.map_singleton]
        simpa [scanValues] using hpost.2.1


#print axioms generated_parent_level_source_equality

end ScanProof
