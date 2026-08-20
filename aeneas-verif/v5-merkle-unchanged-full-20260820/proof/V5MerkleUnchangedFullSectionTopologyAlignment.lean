import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullLevelTraceLists

/-! Align each released section's local radix levels with the shared plan. -/

namespace AspisV5MerkleUnchangedFullSectionTopologyAlignment

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction

/-- First shared C1 radix level used by each released private section. -/
def sectionRadixStart : V5PrivateSection -> Nat
  | .c1 | .c2 => 0
  | .line1 => 1
  | .line2 => 2
  | .line3 => 3

/-- The five section suffixes all terminate at the shared plan's level eight. -/
theorem section_start_add_radix_count (tree : V5PrivateSection) :
    sectionRadixStart tree + radixLevelCount tree = 8 := by
  cases tree <;> decide

/-- A local node level in any released section is exactly the corresponding
suffix level of the shared C1 topology. -/
theorem activeIndices_eq_shared_suffix
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    activeIndices tree queries level =
      sharedActiveIndices queries (sectionRadixStart tree + level) := by
  cases tree <;>
    ext index <;>
    simp only [activeIndices, sharedActiveIndices, Finset.mem_image] <;>
    constructor <;>
    rintro ⟨query, query_mem, rfl⟩ <;>
    refine ⟨query, query_mem, ?_⟩ <;>
    simp [sectionRadixStart, sectionIndex, indexAtRadixLevel_eq_div_pow,
      Nat.div_div_eq_div_mul] <;>
    congr 1 <;>
    simp [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem orderedActiveIndices_eq_shared_suffix
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    orderedActiveIndices tree queries level =
      sharedLevelIndices queries (sectionRadixStart tree + level) := by
  unfold sharedLevelIndices
  unfold orderedActiveIndices
  rw [activeIndices_eq_shared_suffix]
  rfl

/-- Local child-slot sets, in the exact parent order used by one section. -/
def sectionGroupSlots (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) : List (Finset (Fin 4)) :=
  (orderedActiveIndices tree queries (level + 1)).map fun parent =>
    Finset.univ.filter fun slot =>
      4 * parent + slot.val ∈ activeIndices tree queries level

def sectionGroupMasks (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) : List Nat :=
  (sectionGroupSlots tree queries level).map slotMask

theorem sectionGroupSlots_eq_shared_suffix
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    sectionGroupSlots tree queries level =
      sharedGroupSlots queries (sectionRadixStart tree + level) := by
  unfold sectionGroupSlots sharedGroupSlots presentSlots
  rw [orderedActiveIndices_eq_shared_suffix]
  have successor : sectionRadixStart tree + (level + 1) =
      sectionRadixStart tree + level + 1 := by omega
  rw [successor]
  apply List.map_congr_left
  intro parent _
  ext slot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [activeIndices_eq_shared_suffix]

theorem sectionGroupMasks_eq_shared_suffix
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    sectionGroupMasks tree queries level =
      sharedGroupMasks queries (sectionRadixStart tree + level) := by
  unfold sectionGroupMasks sharedGroupMasks
  rw [sectionGroupSlots_eq_shared_suffix]

/-- The exact frontier's radix part is the flattening of the absent local
child slots in the same level/parent/slot order consumed by Rust. -/
theorem radixFrontierPositions_eq_section_groups
    (tree : V5PrivateSection) (queries : Finset V5Query) :
    radixFrontierPositions tree queries =
      (List.range (radixLevelCount tree)).flatMap fun level =>
        (orderedActiveIndices tree queries (level + 1)).flatMap fun parent =>
          ([0, 1, 2, 3].filter fun slot =>
            4 * parent + slot ∉ activeIndices tree queries level).map
              fun slot => ⟨level, 4 * parent + slot⟩ := rfl

#print axioms section_start_add_radix_count
#print axioms activeIndices_eq_shared_suffix
#print axioms orderedActiveIndices_eq_shared_suffix
#print axioms sectionGroupSlots_eq_shared_suffix
#print axioms sectionGroupMasks_eq_shared_suffix
#print axioms radixFrontierPositions_eq_section_groups

end AspisV5MerkleUnchangedFullSectionTopologyAlignment
