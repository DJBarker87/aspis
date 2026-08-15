import AspisFormal.V5TopologyConstruction

/-!
A hash-free reference model for the topology constructor used by the released
private-opening verifier. These definitions express one parent-level step
directly in terms of sorted sets. The theorems below connect that stable
source/model interface to the maintained five-tree topology plan; the
generated Rust proof only has to show that its scan constructs these lists.
-/

namespace AspisV5MerkleTopologyConstructorModel

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction

/-- Sorted, deduplicated parents produced by one radix-four topology step. -/
def parentIndicesOf (indices : List Nat) : List Nat :=
  (indices.toFinset.image fun index => index / 4).sort (. ≤ .)

/-- Child slots represented by one input list under a given parent. -/
def presentSlotsOf (indices : List Nat) (parent : Nat) : Finset (Fin 4) :=
  Finset.univ.filter fun slot => 4 * parent + slot.val ∈ indices

/-- Literal low-four-bit masks paired with parentIndicesOf, in the same
parent order. -/
def parentMasksOf (indices : List Nat) : List Nat :=
  (parentIndicesOf indices).map fun parent =>
    slotMask (presentSlotsOf indices parent)

theorem parentIndicesOf_shared (queries : Finset V5Query) (level : Nat) :
    parentIndicesOf (sharedLevelIndices queries level) =
      sharedLevelIndices queries (level + 1) := by
  unfold parentIndicesOf sharedLevelIndices orderedActiveIndices
  congr 1
  rw [activeIndices_succ]
  ext parent
  simp only [Finset.mem_image, List.mem_toFinset, Finset.mem_sort]

theorem presentSlotsOf_shared (queries : Finset V5Query) (level parent : Nat) :
    presentSlotsOf (sharedLevelIndices queries level) parent =
      presentSlots queries level parent := by
  ext slot
  simp [presentSlotsOf, presentSlots, sharedLevelIndices,
    sharedActiveIndices, orderedActiveIndices]

theorem parentMasksOf_shared (queries : Finset V5Query) (level : Nat) :
    parentMasksOf (sharedLevelIndices queries level) =
      sharedGroupMasks queries level := by
  unfold parentMasksOf sharedGroupMasks sharedGroupSlots
  rw [parentIndicesOf_shared, List.map_map]
  apply List.map_congr_left
  intro parent _
  simp [presentSlotsOf_shared]

/-- Repeated source-level parent construction, beginning with the supplied
leaf list. -/
def parentLevelFrom (indices : List Nat) : Nat → List Nat
  | 0 => indices
  | level + 1 => parentIndicesOf (parentLevelFrom indices level)

def parentMaskLevelFrom (indices : List Nat) (level : Nat) : List Nat :=
  parentMasksOf (parentLevelFrom indices level)

def levelPrefix (indices : List Nat) (count : Nat) : List Nat :=
  ((List.range count).map (parentLevelFrom indices)).flatten

def maskPrefix (indices : List Nat) (count : Nat) : List Nat :=
  ((List.range count).map (parentMaskLevelFrom indices)).flatten

@[simp] theorem levelPrefix_zero (indices : List Nat) :
    levelPrefix indices 0 = [] := rfl

@[simp] theorem maskPrefix_zero (indices : List Nat) :
    maskPrefix indices 0 = [] := rfl

theorem levelPrefix_succ (indices : List Nat) (count : Nat) :
    levelPrefix indices (count + 1) =
      levelPrefix indices count ++ parentLevelFrom indices count := by
  simp [levelPrefix, List.range_succ, List.map_append,
    List.flatten_append]

theorem maskPrefix_succ (indices : List Nat) (count : Nat) :
    maskPrefix indices (count + 1) =
      maskPrefix indices count ++ parentMaskLevelFrom indices count := by
  simp [maskPrefix, List.range_succ, List.map_append,
    List.flatten_append]

theorem parentLevelFrom_shared (queries : Finset V5Query) (level : Nat) :
    parentLevelFrom (sharedLevelIndices queries 0) level =
      sharedLevelIndices queries level := by
  induction level with
  | zero => rfl
  | succ level ih =>
      rw [parentLevelFrom, ih, parentIndicesOf_shared]

theorem parentMaskLevelFrom_shared (queries : Finset V5Query) (level : Nat) :
    parentMaskLevelFrom (sharedLevelIndices queries 0) level =
      sharedGroupMasks queries level := by
  rw [parentMaskLevelFrom, parentLevelFrom_shared, parentMasksOf_shared]

theorem source_level_lists_are_shared (queries : Finset V5Query) :
    (List.range 9).map
        (parentLevelFrom (sharedLevelIndices queries 0)) =
      sharedLevelLists queries := by
  unfold sharedLevelLists
  apply List.map_congr_left
  intro level _
  exact parentLevelFrom_shared queries level

theorem source_group_mask_lists_are_shared (queries : Finset V5Query) :
    (List.range 8).map
        (parentMaskLevelFrom (sharedLevelIndices queries 0)) =
      sharedGroupMaskLists queries := by
  unfold sharedGroupMaskLists
  apply List.map_congr_left
  intro level _
  exact parentMaskLevelFrom_shared queries level

theorem levelPrefix_shared_length_eq_prefixOffset
    (queries : Finset V5Query) (count : Nat) (hcount : count ≤ 9) :
    (levelPrefix (sharedLevelIndices queries 0) count).length =
      prefixOffset (sharedLevelLists queries) count := by
  unfold levelPrefix prefixOffset sharedLevelLists
  simp only [List.length_flatten, List.map_map]
  rw [← List.map_take, List.take_range, Nat.min_eq_left hcount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro level _
  simp only [Function.comp_apply]
  rw [parentLevelFrom_shared]

theorem maskPrefix_shared_length_eq_prefixOffset
    (queries : Finset V5Query) (count : Nat) (hcount : count ≤ 8) :
    (maskPrefix (sharedLevelIndices queries 0) count).length =
      prefixOffset (sharedGroupMaskLists queries) count := by
  unfold maskPrefix prefixOffset sharedGroupMaskLists
  simp only [List.length_flatten, List.map_map]
  rw [← List.map_take, List.take_range, Nat.min_eq_left hcount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro level _
  simp only [Function.comp_apply]
  rw [parentMaskLevelFrom_shared]

#print axioms parentIndicesOf_shared
#print axioms presentSlotsOf_shared
#print axioms parentMasksOf_shared
#print axioms parentLevelFrom_shared
#print axioms parentMaskLevelFrom_shared
#print axioms source_level_lists_are_shared
#print axioms source_group_mask_lists_are_shared
#print axioms levelPrefix_shared_length_eq_prefixOffset
#print axioms maskPrefix_shared_length_eq_prefixOffset

end AspisV5MerkleTopologyConstructorModel
