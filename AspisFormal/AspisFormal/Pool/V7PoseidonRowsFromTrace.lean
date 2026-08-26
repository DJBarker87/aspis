import AspisFormal.Pool.V7OpenedColumnsFromTrace
import AspisFormal.V5AcceptedSpendRelation

/-!
# Exact Tag-73 Poseidon rows from the physical trace

The deployed state-only trace contains 49 permutation blocks of sixteen rows.
For each block, local rows `0..10` hold the inputs to eleven consecutive
two-round transitions, local row 11 holds the final state, and local row 12
holds the rate-eight absorption added to row zero.  The first transition also
applies Poseidon2's leading external linear layer through `gateStep rc 0`.

This file gives that layout a literal Boolean-row meaning.  Its four-by-four
lane family is the base-field decomposition of the four packed Poseidon lanes
consumed by Tag 73.  Vanishing of every deployed row constructs a
`TwoRoundPermutationRows` witness for every one of the 49 blocks.  No hash
equation, permutation correctness assumption, or arbitrary Poseidon-row
function is introduced here.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7PoseidonRowsFromTrace

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.V7OpenedColumnsFromTrace
open AspisV5AcceptedSpendRelation

abbrev PoseidonBlock := Fin 49
abbrev PoseidonPair := Fin 11

/-- The Boolean trace row for one active two-round transition. -/
def poseidonRow (block : PoseidonBlock) (pair : PoseidonPair) : Fin 1024 :=
  ⟨16 * block.val + pair.val, by omega⟩

/-- The committed sixteen-lane state at one physical row. -/
def stateAt (trace : PhysicalTrace) (row : Fin 1024) : State :=
  fun lane => trace row lane

/-- Row zero after adding the rate-eight absorption stored at local row 12. -/
def absorbedBlockInput
    (trace : PhysicalTrace) (block : PoseidonBlock) : State :=
  fun lane =>
    if rateLane : lane.val < 8 then
      trace ⟨16 * block.val, by omega⟩ lane +
        trace ⟨16 * block.val + 12, by omega⟩ lane
    else
      trace ⟨16 * block.val, by omega⟩ lane

/-- The eleven pair inputs followed by the final state.  Pair zero is the
absorbed row-zero state; later entries are literal physical rows 1 through 11. -/
def blockPairState
    (trace : PhysicalTrace) (block : PoseidonBlock) : Nat → State
  | 0 => absorbedBlockInput trace block
  | pair + 1 => stateAt trace
      ⟨(16 * block.val + pair + 1) % 1024, Nat.mod_lt _ (by decide)⟩

def blockFinalState
    (trace : PhysicalTrace) (block : PoseidonBlock) : State :=
  stateAt trace ⟨16 * block.val + 11, by omega⟩

/-- One exact base-field successor residual. -/
def poseidonPairResidual
    (rc : RoundConstants) (trace : PhysicalTrace)
    (block : PoseidonBlock) (pair : PoseidonPair) (lane : Fin 16) : F :=
  blockPairState trace block (pair.val + 1) lane -
    gateStep rc (2 * pair.val + 1)
      (gateStep rc (2 * pair.val) (blockPairState trace block pair.val)) lane

/-- The lane selected by one of the four packed groups and four tower slots. -/
def packedLane (group slot : Fin 4) : Fin 16 :=
  ⟨4 * group.val + slot.val, by omega⟩

def laneGroup (lane : Fin 16) : Fin 4 :=
  ⟨lane.val / 4, by omega⟩

def laneSlot (lane : Fin 16) : Fin 4 :=
  ⟨lane.val % 4, Nat.mod_lt _ (by decide)⟩

@[simp] theorem packedLane_laneGroup_laneSlot (lane : Fin 16) :
    packedLane (laneGroup lane) (laneSlot lane) = lane := by
  apply Fin.ext
  simp only [packedLane, laneGroup, laneSlot]
  omega

/-- Literal Boolean-row Poseidon family.  Rows outside the 49-by-11 active
rectangle are structural zeros, matching the deployed selector. -/
def deployedPoseidonRows
    (rc : RoundConstants) (trace : PhysicalTrace) :
    Fin 1024 → Fin 4 → Fin 4 → F :=
  fun row group slot =>
    if blockActive : row.val / 16 < 49 then
      if pairActive : row.val % 16 < 11 then
        poseidonPairResidual rc trace
          ⟨row.val / 16, blockActive⟩
          ⟨row.val % 16, pairActive⟩
          (packedLane group slot)
      else 0
    else 0

theorem poseidonRow_div
    (block : PoseidonBlock) (pair : PoseidonPair) :
    (poseidonRow block pair).val / 16 = block.val := by
  simp only [poseidonRow]
  omega

theorem poseidonRow_mod
    (block : PoseidonBlock) (pair : PoseidonPair) :
    (poseidonRow block pair).val % 16 = pair.val := by
  simp only [poseidonRow]
  omega

@[simp] theorem deployedPoseidonRows_at_active_row
    (rc : RoundConstants) (trace : PhysicalTrace)
    (block : PoseidonBlock) (pair : PoseidonPair)
    (group slot : Fin 4) :
    deployedPoseidonRows rc trace (poseidonRow block pair) group slot =
      poseidonPairResidual rc trace block pair (packedLane group slot) := by
  unfold deployedPoseidonRows
  rw [poseidonRow_div, poseidonRow_mod]
  simp

def DeployedPoseidonRowsVanish
    (rc : RoundConstants) (trace : PhysicalTrace) : Prop :=
  ∀ row group slot, deployedPoseidonRows rc trace row group slot = 0

/-- All sixteen base-field successor residuals vanish at every active row. -/
theorem poseidonPairResidual_zero_of_deployed_rows_vanish
    (rc : RoundConstants) (trace : PhysicalTrace)
    (vanish : DeployedPoseidonRowsVanish rc trace)
    (block : PoseidonBlock) (pair : PoseidonPair) (lane : Fin 16) :
    poseidonPairResidual rc trace block pair lane = 0 := by
  have selected := vanish (poseidonRow block pair) (laneGroup lane) (laneSlot lane)
  rw [deployedPoseidonRows_at_active_row,
    packedLane_laneGroup_laneSlot] at selected
  exact selected

/-- Vanishing of the exact deployed Boolean-row family constructs the
normalized eleven-pair gate object used by the spend-relation proof. -/
def twoRoundPermutationRowsOfVanish
    (rc : RoundConstants) (trace : PhysicalTrace)
    (vanish : DeployedPoseidonRowsVanish rc trace)
    (block : PoseidonBlock) :
    TwoRoundPermutationRows rc (absorbedBlockInput trace block)
      (blockFinalState trace block) where
  row := blockPairState trace block
  startResidual := by
    funext lane
    simp [blockPairState]
  pairResidual := by
    intro pair pairBound
    funext lane
    change poseidonPairResidual rc trace block ⟨pair, by omega⟩ lane = 0
    exact poseidonPairResidual_zero_of_deployed_rows_vanish
      rc trace vanish block ⟨pair, by omega⟩ lane
  finishResidual := by
    funext lane
    have rowBound : 16 * block.val + 10 + 1 < 1024 := by omega
    simp [blockPairState, blockFinalState, stateAt,
      Nat.mod_eq_of_lt rowBound]

theorem exact_poseidon_block_and_pair_count :
    Fintype.card PoseidonBlock = 49 ∧ Fintype.card PoseidonPair = 11 := by
  decide

#print axioms deployedPoseidonRows_at_active_row
#print axioms poseidonPairResidual_zero_of_deployed_rows_vanish
#print axioms twoRoundPermutationRowsOfVanish

end AspisPool.V7PoseidonRowsFromTrace
