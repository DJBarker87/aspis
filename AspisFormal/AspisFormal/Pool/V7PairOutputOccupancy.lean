import AspisFormal.Pool.V7PairLeafOccupancy

/-!
# V7 pair-output arity is part of the payment relation

Leaf validity proves that an occupancy bit is the exact zero test of the
committed second digest. It does not, by itself, choose whether a particular
payment appends one or two notes. This file freezes the missing variant gate:

* a private transfer requires second occupancy `1`;
* a withdrawal requires second occupancy `0`.

The latter therefore appends the canonical algebraic empty digest, rather
than an unconstrained spendable second note.
-/

set_option autoImplicit false

namespace AspisPool.V7PairOutputOccupancy

open AspisPool.V7PairLeafOccupancy

inductive OutputKind where
  | privateTransfer
  | withdrawal
  deriving DecidableEq, Repr

def expectedSecondOccupied {K : Type} [Zero K] [One K] : OutputKind → K
  | .privateTransfer => 1
  | .withdrawal => 0

/-- Literal final row-local residual added to the Rust pair relation. -/
def outputOccupancyResidual {K : Type} [Sub K] [Zero K] [One K]
    (kind : OutputKind) (leaf : PairLeaf K) : K :=
  leaf.secondOccupied - expectedSecondOccupied kind

def OutputValid {K : Type} [CommRing K]
    (kind : OutputKind) (leaf : PairLeaf K) : Prop :=
  leaf.Valid ∧ outputOccupancyResidual kind leaf = 0

theorem residual_zero_iff_expected
    {K : Type} [AddGroup K] [One K]
    (kind : OutputKind) (leaf : PairLeaf K) :
    outputOccupancyResidual kind leaf = 0 ↔
      leaf.secondOccupied = expectedSecondOccupied kind := by
  unfold outputOccupancyResidual
  exact sub_eq_zero

theorem private_transfer_output_second_occupied
    {K : Type} [CommRing K]
    (leaf : PairLeaf K) (valid : OutputValid .privateTransfer leaf) :
    leaf.secondOccupied = 1 := by
  exact (residual_zero_iff_expected .privateTransfer leaf).mp valid.2

theorem withdrawal_output_second_empty
    {K : Type} [CommRing K]
    (leaf : PairLeaf K) (valid : OutputValid .withdrawal leaf) :
    leaf.secondOccupied = 0 := by
  exact (residual_zero_iff_expected .withdrawal leaf).mp valid.2

theorem withdrawal_output_second_commitment_zero
    {K : Type} [CommRing K]
    (leaf : PairLeaf K) (valid : OutputValid .withdrawal leaf) :
    leaf.secondCommitment = fun _ => 0 := by
  exact valid_empty_second_commitment_zero leaf valid.1
    (withdrawal_output_second_empty leaf valid)

theorem withdrawal_output_second_not_spendable
    {K : Type} [CommRing K] [Nontrivial K]
    (leaf : PairLeaf K) (valid : OutputValid .withdrawal leaf) :
    ¬ leaf.SelectedSlotIsSpendable true := by
  simp [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied,
    withdrawal_output_second_empty leaf valid]

theorem private_transfer_output_second_sentinel_ne_zero
    {K : Type} [CommRing K] [Nontrivial K]
    (leaf : PairLeaf K) (valid : OutputValid .privateTransfer leaf) :
    leaf.secondSentinel ≠ 0 := by
  exact valid_occupied_second_sentinel_ne_zero leaf valid.1
    (private_transfer_output_second_occupied leaf valid)

#print axioms residual_zero_iff_expected
#print axioms private_transfer_output_second_occupied
#print axioms withdrawal_output_second_empty
#print axioms withdrawal_output_second_commitment_zero
#print axioms withdrawal_output_second_not_spendable
#print axioms private_transfer_output_second_sentinel_ne_zero

end AspisPool.V7PairOutputOccupancy
