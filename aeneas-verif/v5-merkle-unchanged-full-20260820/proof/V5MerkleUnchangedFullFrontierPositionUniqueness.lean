import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullSectionChildOrder

/-! No maintained Merkle-frontier position is consumed twice. -/

namespace AspisV5MerkleUnchangedFullFrontierPositionUniqueness

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullSectionChildOrder

theorem absentChildIndices_nodup
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent : Nat) :
    (absentChildIndices tree queries level parent).Nodup := by
  unfold absentChildIndices
  apply List.Nodup.map
  · intro left right equal
    exact Nat.add_left_cancel equal
  · exact (List.nodup_range : (List.range 4).Nodup) |>.filter _

theorem levelAbsentChildIndices_nodup
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    (levelAbsentChildIndices tree queries level).Nodup := by
  unfold levelAbsentChildIndices
  apply List.nodup_flatMap.mpr
  constructor
  · intro parent parent_mem
    exact absentChildIndices_nodup tree queries level parent
  · exact (orderedActiveIndices_nodup tree queries (level + 1)).imp
      (fun {left right} different index inLeft inRight => by
        simp only [absentChildIndices, List.mem_map, List.mem_filter,
          List.mem_range] at inLeft inRight
        obtain ⟨leftSlot, ⟨leftBound, leftAbsent⟩, leftEq⟩ := inLeft
        obtain ⟨rightSlot, ⟨rightBound, rightAbsent⟩, rightEq⟩ := inRight
        have childrenEqual : 4 * left + leftSlot =
            4 * right + rightSlot := leftEq.trans rightEq.symm
        have parentsEqual : left = right := by omega
        exact different parentsEqual)

theorem radixFrontierPositions_nodup
    (tree : V5PrivateSection) (queries : Finset V5Query) :
    (radixFrontierPositions tree queries).Nodup := by
  rw [radixFrontierPositions_eq_levelAbsentChildIndices]
  apply List.nodup_flatMap.mpr
  constructor
  · intro level level_mem
    apply List.Nodup.map
    · intro left right equal
      exact congrArg FrontierPosition.index equal
    · exact levelAbsentChildIndices_nodup tree queries level
  · exact (List.nodup_range :
      (List.range (radixLevelCount tree)).Nodup).imp
      (fun {leftLevel rightLevel} different position inLeft inRight => by
        simp only [List.mem_map] at inLeft inRight
        obtain ⟨leftIndex, leftMem, leftEq⟩ := inLeft
        obtain ⟨rightIndex, rightMem, rightEq⟩ := inRight
        have levelsEqual : leftLevel = rightLevel := by
          have positionsEqual := leftEq.trans rightEq.symm
          exact congrArg FrontierPosition.level positionsEqual
        exact different levelsEqual)

theorem binaryCapFrontierPositions_nodup
    (tree : V5PrivateSection) (queries : Finset V5Query) :
    (binaryCapFrontierPositions tree queries).Nodup := by
  unfold binaryCapFrontierPositions
  apply List.Nodup.map
  · intro left right equal
    exact congrArg FrontierPosition.index equal
  · exact (by decide : ([0, 1] : List Nat).Nodup) |>.filter _

theorem radix_binary_frontiers_disjoint
    (tree : V5PrivateSection) (queries : Finset V5Query) :
    List.Disjoint (radixFrontierPositions tree queries)
      (binaryCapFrontierPositions tree queries) := by
  intro position inRadix inBinary
  rw [radixFrontierPositions_eq_levelAbsentChildIndices] at inRadix
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at inRadix
  obtain ⟨level, levelBound, index, indexMem, radixEq⟩ := inRadix
  unfold binaryCapFrontierPositions at inBinary
  simp only [List.mem_map, List.mem_filter, List.mem_cons] at inBinary
  obtain ⟨binaryIndex, binaryMem, binaryEq⟩ := inBinary
  have levelsEqual : level = radixLevelCount tree := by
    have positionsEqual := radixEq.trans binaryEq.symm
    exact congrArg FrontierPosition.level positionsEqual
  omega

theorem frontierPositions_nodup
    (tree : V5PrivateSection) (queries : Finset V5Query) :
    (frontierPositions tree queries).Nodup := by
  unfold frontierPositions
  exact (radixFrontierPositions_nodup tree queries).append
    (binaryCapFrontierPositions_nodup tree queries)
    (radix_binary_frontiers_disjoint tree queries)

#print axioms absentChildIndices_nodup
#print axioms levelAbsentChildIndices_nodup
#print axioms radixFrontierPositions_nodup
#print axioms binaryCapFrontierPositions_nodup
#print axioms frontierPositions_nodup

end AspisV5MerkleUnchangedFullFrontierPositionUniqueness
