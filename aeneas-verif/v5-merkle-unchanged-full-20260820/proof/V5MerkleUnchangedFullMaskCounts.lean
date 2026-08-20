import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullMaskSemantics

/-! Exact live/frontier counts of a released four-bit group mask. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace AspisV5MerkleUnchangedFullMaskCounts

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5MerkleUnchangedFullOrderedChildPositions
open AspisV5MerkleUnchangedFullMaskSemantics

/-- Membership of a natural slot number in one maintained four-slot set. -/
def PresentNat (slots : Finset (Fin 4)) (slot : Nat) : Prop :=
  ∃ bounded : Fin 4, bounded.val = slot ∧ bounded ∈ slots

noncomputable def presentNatBool
    (slots : Finset (Fin 4)) (slot : Nat) : Bool := by
  classical
  exact decide (PresentNat slots slot)

noncomputable def liveSlotCount
    (slots : Finset (Fin 4)) (count : Nat) : Nat :=
  ((List.range count).filter (presentNatBool slots)).length

noncomputable def frontierSlotCount
    (slots : Finset (Fin 4)) (count : Nat) : Nat :=
  ((List.range count).filter fun slot => !presentNatBool slots slot).length

theorem childPresent_iff_presentNat
    (present : Std.U8) (slots : Finset (Fin 4))
    (presentValue : present.val =
      AspisV5TopologyConstruction.slotMask slots)
    (slot : Nat) (slot_lt : slot < 4) :
    ChildPresent present slot ↔ PresentNat slots slot := by
  let bounded : Fin 4 := ⟨slot, slot_lt⟩
  rw [show slot = bounded.val by rfl,
    childPresent_iff_mem_slots present slots presentValue bounded]
  constructor
  · intro member
    exact ⟨bounded, rfl, member⟩
  · rintro ⟨other, otherValue, member⟩
    have same : other = bounded := Fin.ext otherValue
    simpa [same] using member

/-- The generated live-value cursor counts precisely the maintained present
slots strictly before `count`. -/
theorem liveBefore_eq_liveSlotCount
    (present : Std.U8) (slots : Finset (Fin 4))
    (presentValue : present.val =
      AspisV5TopologyConstruction.slotMask slots)
    (count : Nat) (count_le : count ≤ 4) :
    liveBefore present count = liveSlotCount slots count := by
  induction count with
  | zero => simp [liveBefore, liveSlotCount]
  | succ count ih =>
      have count_lt : count < 4 := by omega
      rw [liveBefore, ih (by omega)]
      have bit := childPresent_iff_presentNat present slots presentValue
        count count_lt
      by_cases member : PresentNat slots count
      · have child : ChildPresent present count := bit.mpr member
        simp [liveSlotCount, List.range_succ, presentNatBool, member, child]
      · have child : ¬ ChildPresent present count := fun found =>
          member (bit.mp found)
        simp [liveSlotCount, List.range_succ, presentNatBool, member, child]

/-- The generated frontier cursor counts precisely the maintained absent
slots strictly before `count`. -/
theorem frontierBefore_eq_frontierSlotCount
    (present : Std.U8) (slots : Finset (Fin 4))
    (presentValue : present.val =
      AspisV5TopologyConstruction.slotMask slots)
    (count : Nat) (count_le : count ≤ 4) :
    frontierBefore present count = frontierSlotCount slots count := by
  induction count with
  | zero => simp [frontierBefore, frontierSlotCount]
  | succ count ih =>
      have count_lt : count < 4 := by omega
      rw [frontierBefore, ih (by omega)]
      have bit := childPresent_iff_presentNat present slots presentValue
        count count_lt
      by_cases member : PresentNat slots count
      · have child : ChildPresent present count := bit.mpr member
        simp [frontierSlotCount, List.range_succ, presentNatBool, member, child]
      · have child : ¬ ChildPresent present count := fun found =>
          member (bit.mp found)
        simp [frontierSlotCount, List.range_succ, presentNatBool, member, child]

#print axioms childPresent_iff_presentNat
#print axioms liveBefore_eq_liveSlotCount
#print axioms frontierBefore_eq_frontierSlotCount

end AspisV5MerkleUnchangedFullMaskCounts
