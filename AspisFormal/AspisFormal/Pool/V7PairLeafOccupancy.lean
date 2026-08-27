import Mathlib

/-!
# Algebraic occupancy for V7 Pool pair leaves

The Pool pair leaf never represents an empty slot by asking that a particular
digest have no preimage.  The first slot is occupied by construction.  The
second slot carries a field-valued occupancy bit and a zero-test witness for a
fixed sentinel limb of its commitment.  The constraints make occupancy zero
exactly when that sentinel is zero; an empty slot additionally forces every
commitment limb to zero.  Spending a selected slot separately requires its
occupancy value to equal one.

The pair-tree leaf is the ordinary lowest internal node of a depth-21 note
tree: its one-permutation compression input is the ordered pair of complete
eight-limb commitments.  Occupancy is not squeezed into an already-full hash
lane.  Instead it is a function of the fully committed second digest.  An
honest second output whose sentinel happens to be zero must resample its note
salt; this is a liveness rejection event, not an assumption that zero has no
preimage.  Collision resistance of Poseidon compression is deliberately
outside this algebraic file.
-/

set_option autoImplicit false

namespace AspisPool.V7PairLeafOccupancy

abbrev Digest (K : Type) := Fin 8 → K

/-- One transaction appends one pair.  Slot zero is always occupied; slot one
is present exactly when `secondOccupied = 1`. -/
structure PairLeaf (K : Type) where
  firstCommitment : Digest K
  secondOccupied : K
  secondCommitment : Digest K
  secondOccupancyInverse : K

/-- The last M31 limb is the fixed zero-test sentinel.  Any fixed limb would
work; pinning lane seven makes the encoding and source bridge unambiguous. -/
def PairLeaf.secondSentinel {K : Type} (leaf : PairLeaf K) : K :=
  leaf.secondCommitment ⟨7, by decide⟩

/-- Exact algebraic validity constraints for a pair leaf. -/
def PairLeaf.Valid {K : Type} [CommRing K] (leaf : PairLeaf K) : Prop :=
  leaf.secondOccupied * (leaf.secondOccupied - 1) = 0 ∧
    leaf.secondSentinel * leaf.secondOccupancyInverse =
      leaf.secondOccupied ∧
    (1 - leaf.secondOccupied) * leaf.secondOccupancyInverse = 0 ∧
    ∀ lane, (1 - leaf.secondOccupied) * leaf.secondCommitment lane = 0

/-- The occupancy value selected by a private membership witness. -/
def PairLeaf.selectedOccupied {K : Type} [OfNat K 1]
    (leaf : PairLeaf K) (secondSlot : Bool) : K :=
  if secondSlot then leaf.secondOccupied else 1

/-- The commitment selected by the same private side bit. -/
def PairLeaf.selectedCommitment {K : Type}
    (leaf : PairLeaf K) (secondSlot : Bool) : Digest K :=
  if secondSlot then leaf.secondCommitment else leaf.firstCommitment

/-- The relation-level spend gate.  Membership in the pair hash is not enough:
the privately selected slot must also be occupied. -/
def PairLeaf.SelectedSlotIsSpendable {K : Type} [OfNat K 1]
    (leaf : PairLeaf K) (secondSlot : Bool) : Prop :=
  leaf.selectedOccupied secondSlot = 1

theorem selected_spendable_implies_occupied_one
    {K : Type} [OfNat K 1] (leaf : PairLeaf K) (secondSlot : Bool)
    (spendable : leaf.SelectedSlotIsSpendable secondSlot) :
    leaf.selectedOccupied secondSlot = 1 :=
  spendable

theorem first_slot_is_spendable
    {K : Type} [OfNat K 1] (leaf : PairLeaf K) :
    leaf.SelectedSlotIsSpendable false := by
  simp [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied]

theorem second_slot_spendable_iff
    {K : Type} [OfNat K 1] (leaf : PairLeaf K) :
    leaf.SelectedSlotIsSpendable true ↔ leaf.secondOccupied = 1 := by
  simp [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied]

/-- A canonical empty second slot is rejected by the spend gate by an exact
field inequality, not by a preimage-resistance claim. -/
theorem canonical_empty_second_slot_not_spendable
    {K : Type} [Semiring K] [Nontrivial K]
    (first : Digest K) :
    let leaf : PairLeaf K := ⟨first, 0, fun _ => 0, 0⟩
    ¬ leaf.SelectedSlotIsSpendable true := by
  intro leaf
  change ¬ (0 : K) = 1
  exact zero_ne_one

/-- Booleanity gives the intended exhaustive occupied/empty cases over any
integral domain. -/
theorem valid_second_occupied_cases
    {K : Type} [CommRing K] [NoZeroDivisors K]
    (leaf : PairLeaf K) (valid : leaf.Valid) :
    leaf.secondOccupied = 0 ∨ leaf.secondOccupied = 1 := by
  rcases eq_zero_or_eq_zero_of_mul_eq_zero valid.1 with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

/-- In the empty case the commitment is algebraically the canonical all-zero
digest. -/
theorem valid_empty_second_commitment_zero
    {K : Type} [CommRing K]
    (leaf : PairLeaf K) (valid : leaf.Valid)
    (empty : leaf.secondOccupied = 0) :
    leaf.secondCommitment = fun _ => 0 := by
  funext lane
  have constrained := valid.2.2.2 lane
  simpa [empty] using constrained

theorem valid_empty_second_inverse_zero
    {K : Type} [CommRing K]
    (leaf : PairLeaf K) (valid : leaf.Valid)
    (empty : leaf.secondOccupied = 0) :
    leaf.secondOccupancyInverse = 0 := by
  have constrained := valid.2.2.1
  simpa [empty] using constrained

/-- Occupancy one algebraically certifies a nonzero sentinel. -/
theorem valid_occupied_second_sentinel_ne_zero
    {K : Type} [CommRing K] [Nontrivial K]
    (leaf : PairLeaf K) (valid : leaf.Valid)
    (occupied : leaf.secondOccupied = 1) :
    leaf.secondSentinel ≠ 0 := by
  intro zero
  have inverse := valid.2.1
  simp [zero, occupied] at inverse

/-- The bit is not free metadata: validity makes it the exact zero test of the
committed sentinel limb. -/
theorem valid_second_occupied_zero_iff_sentinel_zero
    {K : Type} [CommRing K] [NoZeroDivisors K]
    (leaf : PairLeaf K) (valid : leaf.Valid) :
    leaf.secondOccupied = 0 ↔ leaf.secondSentinel = 0 := by
  constructor
  · intro empty
    have allZero := valid_empty_second_commitment_zero leaf valid empty
    simp [PairLeaf.secondSentinel, allZero]
  · intro zero
    have inverse := valid.2.1
    rw [zero, zero_mul] at inverse
    exact inverse.symm

/-- A single-output append has an algebraically empty second slot. -/
def singleOutputPair {K : Type} [Zero K]
    (commitment : Digest K) : PairLeaf K :=
  ⟨commitment, 0, fun _ => 0, 0⟩

/-- A private transfer has two algebraically occupied slots. -/
def twoOutputPair {K : Type} [One K]
    (recipient change : Digest K) (sentinelInverse : K) : PairLeaf K :=
  ⟨recipient, 1, change, sentinelInverse⟩

theorem singleOutputPair_valid
    {K : Type} [CommRing K] (commitment : Digest K) :
    (singleOutputPair commitment).Valid := by
  constructor <;> simp [singleOutputPair]

theorem twoOutputPair_valid
    {K : Type} [CommRing K] (recipient change : Digest K)
    (sentinelInverse : K)
    (inverseCorrect : change ⟨7, by decide⟩ * sentinelInverse = 1) :
    (twoOutputPair recipient change sentinelInverse).Valid := by
  refine ⟨by simp [twoOutputPair], ?_, by simp [twoOutputPair], ?_⟩
  · simpa [twoOutputPair, PairLeaf.secondSentinel] using inverseCorrect
  · intro lane
    simp [twoOutputPair]

/-- The exact one-permutation preimage.  This is also the ordinary ordered
input to the lowest internal-node compression in the depth-21 note tree. -/
def PairLeaf.compressionPreimage {K : Type} (leaf : PairLeaf K) :
    Digest K × Digest K :=
  (leaf.firstCommitment, leaf.secondCommitment)

/-- Two valid witnesses for the same committed second digest cannot disagree
about whether the slot is empty. -/
theorem valid_same_second_commitment_same_occupancy
    {K : Type} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (left right : PairLeaf K) (leftValid : left.Valid)
    (rightValid : right.Valid)
    (sameSecond : left.secondCommitment = right.secondCommitment) :
    left.secondOccupied = right.secondOccupied := by
  rcases valid_second_occupied_cases left leftValid with leftEmpty | leftOccupied
  · have leftSentinel : left.secondSentinel = 0 :=
      (valid_second_occupied_zero_iff_sentinel_zero left leftValid).mp leftEmpty
    have rightSentinel : right.secondSentinel = 0 := by
      simpa [PairLeaf.secondSentinel, sameSecond] using leftSentinel
    exact leftEmpty.trans
      ((valid_second_occupied_zero_iff_sentinel_zero right rightValid).mpr
        rightSentinel).symm
  · rcases valid_second_occupied_cases right rightValid with rightEmpty | rightOccupied
    · have rightSentinel : right.secondSentinel = 0 :=
        (valid_second_occupied_zero_iff_sentinel_zero right rightValid).mp rightEmpty
      have leftSentinel : left.secondSentinel = 0 := by
        simpa [PairLeaf.secondSentinel, sameSecond] using rightSentinel
      exact False.elim
        ((valid_occupied_second_sentinel_ne_zero left leftValid leftOccupied)
          leftSentinel)
    · exact leftOccupied.trans rightOccupied.symm

theorem valid_same_compression_preimage_same_occupancy
    {K : Type} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (left right : PairLeaf K) (leftValid : left.Valid)
    (rightValid : right.Valid)
    (sameInput : left.compressionPreimage = right.compressionPreimage) :
    left.secondOccupied = right.secondOccupied := by
  exact valid_same_second_commitment_same_occupancy left right leftValid rightValid
    (congrArg Prod.snd sameInput)

#print axioms selected_spendable_implies_occupied_one
#print axioms canonical_empty_second_slot_not_spendable
#print axioms valid_second_occupied_cases
#print axioms valid_empty_second_commitment_zero
#print axioms valid_empty_second_inverse_zero
#print axioms valid_occupied_second_sentinel_ne_zero
#print axioms valid_second_occupied_zero_iff_sentinel_zero
#print axioms singleOutputPair_valid
#print axioms twoOutputPair_valid
#print axioms valid_same_compression_preimage_same_occupancy

end AspisPool.V7PairLeafOccupancy
