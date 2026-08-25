import Mathlib
import AspisFormal.Pool.FormatV1

/-!
# Pool V1 root-history indexing

Root sequence zero retains the empty-tree root.  Appending leaf `i` creates
sequence `i + 1`.  Pages hold exactly 256 consecutive roots and are addressed
by `(pool, pageNumber)` in the future program layer; this pure module proves
the sequence/page/slot arithmetic only.
-/

set_option autoImplicit false

namespace AspisPool.RootHistoryV1

def pageCapacity : Nat := 256

structure Location where
  pageNumber : Nat
  slot : Nat
  deriving DecidableEq, Repr

def location (sequence : Nat) : Location where
  pageNumber := sequence / pageCapacity
  slot := sequence % pageCapacity

def firstSequence (pageNumber : Nat) : Nat := pageNumber * pageCapacity

/-- Empty root is sequence zero; every leaf append advances once. -/
def rootSequenceAfterLeaf (leafIndex : Nat) : Nat := leafIndex + 1

def rootLocationAfterLeaf (leafIndex : Nat) : Location :=
  location (rootSequenceAfterLeaf leafIndex)

theorem slot_lt_pageCapacity (sequence : Nat) :
    (location sequence).slot < pageCapacity := by
  exact Nat.mod_lt sequence (by norm_num [pageCapacity])

theorem location_recomposes (sequence : Nat) :
    firstSequence (location sequence).pageNumber +
        (location sequence).slot = sequence := by
  rw [location, firstSequence]
  rw [Nat.mul_comm]
  exact Nat.div_add_mod sequence pageCapacity

theorem exact_page_boundaries :
    location 0 = ⟨0, 0⟩ ∧
    location 255 = ⟨0, 255⟩ ∧
    location 256 = ⟨1, 0⟩ ∧
    location 511 = ⟨1, 255⟩ := by
  norm_num [location, pageCapacity]

theorem empty_root_location : location 0 = ⟨0, 0⟩ := by
  norm_num [location, pageCapacity]

theorem poolV1_terminal_root_location :
    location AspisPool.FormatV1.treeCapacity = ⟨4096, 0⟩ := by
  norm_num [location, pageCapacity, AspisPool.FormatV1.treeCapacity,
    AspisPool.FormatV1.binding]

/-- Within a page, the quotient/remainder address is exact. -/
theorem location_of_page_slot (page slot : Nat) (slotBound : slot < pageCapacity) :
    location (firstSequence page + slot) = ⟨page, slot⟩ := by
  simp only [location, firstSequence, Location.mk.injEq]
  constructor
  · rw [Nat.mul_comm page pageCapacity]
    rw [Nat.mul_add_div (m := pageCapacity) (by norm_num [pageCapacity]) page slot]
    rw [Nat.div_eq_of_lt slotBound]
    simp
  · rw [Nat.mul_comm page pageCapacity]
    rw [Nat.mul_add_mod pageCapacity page slot]
    exact Nat.mod_eq_of_lt slotBound

/-- Two ordered leaf appends create two consecutive retained-root sequences. -/
theorem two_leaf_sequences_are_consecutive (firstLeafIndex : Nat) :
    rootSequenceAfterLeaf (firstLeafIndex + 1) =
      rootSequenceAfterLeaf firstLeafIndex + 1 := by
  simp [rootSequenceAfterLeaf]

#print axioms slot_lt_pageCapacity
#print axioms location_recomposes
#print axioms exact_page_boundaries
#print axioms empty_root_location
#print axioms poolV1_terminal_root_location
#print axioms location_of_page_slot
#print axioms two_leaf_sequences_are_consecutive

end AspisPool.RootHistoryV1
