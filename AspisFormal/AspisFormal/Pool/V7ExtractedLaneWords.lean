import AspisFormal.Pool.V7MerkleQueryExtractor
import AspisFormal.Pool.V7PackedFibreDecoder
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

/-!
# Complete Tag-73 Merkle words to 29 exact field-valued lanes

The query-graph extractor returns two complete lists of raw packed leaves.
This module gives those bytes their exact initial-domain meaning:

* leaf `q`, slot `s` is initial coordinate `4*q+s`;
* C1 lanes 0--25 are canonical M31 values embedded in QM31;
* C2 lanes 26--28 are the literal `(c0.a,c0.b,c1.a,c1.b)` QM31 values;
* any unopened non-canonical raw symbol is mapped to zero, producing a total
  received word. Accepted openings still use the successful-decoding lemmas
  below, so this default cannot hide an invalid queried symbol.

This is reconstruction, not inversion of the gamma-batched word.
-/

set_option autoImplicit false

namespace AspisPool.V7ExtractedLaneWords

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7PackedFibreTowerBridge
open AspisV5ComponentCQM31TowerExact

def fibreIndex (index : Fin 1048576) : Fin 262144 :=
  ⟨index.val / 4, by omega⟩

def fibreSlot (index : Fin 1048576) : Fin 4 :=
  ⟨index.val % 4, Nat.mod_lt _ (by omega)⟩

def initialIndex (fibre : Fin 262144) (slot : Fin 4) : Fin 1048576 :=
  ⟨4 * fibre.val + slot.val, by omega⟩

theorem initial_index_decomposition (index : Fin 1048576) :
    4 * (fibreIndex index).val + (fibreSlot index).val = index.val := by
  change 4 * (index.val / 4) + index.val % 4 = index.val
  simpa [Nat.add_comm] using Nat.mod_add_div index.val 4

@[simp] theorem fibreIndex_initialIndex
    (fibre : Fin 262144) (slot : Fin 4) :
    fibreIndex (initialIndex fibre slot) = fibre := by
  apply Fin.ext
  change (4 * fibre.val + slot.val) / 4 = fibre.val
  rw [Nat.mul_add_div (by omega)]
  simp [Nat.div_eq_of_lt slot.isLt]

@[simp] theorem fibreSlot_initialIndex
    (fibre : Fin 262144) (slot : Fin 4) :
    fibreSlot (initialIndex fibre slot) = slot := by
  apply Fin.ext
  change (4 * fibre.val + slot.val) % 4 = slot.val
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt slot.isLt

def extractedC1Leaf (words : ExtractedWords) (fibre : Fin 262144) : C1Leaf :=
  (words.c1[fibre.val]?).getD defaultC1Leaf

def extractedC2Leaf (words : ExtractedWords) (fibre : Fin 262144) : C2Leaf :=
  (words.c2[fibre.val]?).getD defaultC2Leaf

theorem extractedC1Leaf_of_projection
    (words : ExtractedWords) (fibre : Fin 262144) (leaf : C1Leaf)
    (projection : words.c1[fibre.val]? = some leaf) :
    extractedC1Leaf words fibre = leaf := by
  simp [extractedC1Leaf, projection]

theorem extractedC2Leaf_of_projection
    (words : ExtractedWords) (fibre : Fin 262144) (leaf : C2Leaf)
    (projection : words.c2[fibre.val]? = some leaf) :
    extractedC2Leaf words fibre = leaf := by
  simp [extractedC2Leaf, projection]

/-- Literal base-field embedding used by the Rust gamma accumulator. -/
def embedM31Exact (value : M31Exact) : QM31Exact :=
  ⟨⟨value, 0⟩, 0⟩

def c1Received (words : ExtractedWords) (column : Fin 26) :
    InitialWord QM31Exact :=
  fun index =>
    ((decodeC1EntryExact (extractedC1Leaf words (fibreIndex index)).value
      (fibreSlot index) column).map embedM31Exact).getD 0

def c2Received (words : ExtractedWords) (helper : Fin 3) :
    InitialWord QM31Exact :=
  fun index =>
    (decodeC2EntryExact (extractedC2Leaf words (fibreIndex index)).value
      helper (fibreSlot index)).getD 0

def c1LaneIndex (column : Fin 26) : Fin 29 :=
  ⟨column.val, by omega⟩

def c2LaneIndex (helper : Fin 3) : Fin 29 :=
  ⟨26 + helper.val, by omega⟩

/-- The complete 29-lane received object consumed by component decoding. -/
def extractedWidth29InitialWords (words : ExtractedWords) :
    Fin 29 → InitialWord QM31Exact :=
  fun lane =>
    if h : lane.val < 26 then
      c1Received words ⟨lane.val, h⟩
    else
      c2Received words ⟨lane.val - 26, by omega⟩

@[simp] theorem extractedWidth29_c1_lane
    (words : ExtractedWords) (column : Fin 26) :
    extractedWidth29InitialWords words (c1LaneIndex column) =
      c1Received words column := by
  simp [extractedWidth29InitialWords, c1LaneIndex]

@[simp] theorem extractedWidth29_c2_lane
    (words : ExtractedWords) (helper : Fin 3) :
    extractedWidth29InitialWords words (c2LaneIndex helper) =
      c2Received words helper := by
  simp [extractedWidth29InitialWords, c2LaneIndex]

theorem width29_lane_partition (lane : Fin 29) :
    (∃ column : Fin 26, lane = c1LaneIndex column) ∨
      ∃ helper : Fin 3, lane = c2LaneIndex helper := by
  by_cases hcolumn : lane.val < 26
  · left
    exact ⟨⟨lane.val, hcolumn⟩, Fin.ext rfl⟩
  · right
    refine ⟨⟨lane.val - 26, by omega⟩, Fin.ext ?_⟩
    simp [c2LaneIndex]
    omega

theorem c1_received_of_exact_projection
    (words : ExtractedWords) (index : Fin 1048576) (column : Fin 26)
    (leaf : C1Leaf) (decoded : M31Exact)
    (projection : words.c1[(fibreIndex index).val]? = some leaf)
    (decodeSuccess : decodeC1EntryExact leaf.value (fibreSlot index) column =
      some decoded) :
    c1Received words column index = embedM31Exact decoded := by
  simp [c1Received, extractedC1Leaf, projection, decodeSuccess]

theorem c2_received_of_exact_projection
    (words : ExtractedWords) (index : Fin 1048576) (helper : Fin 3)
    (leaf : C2Leaf) (decoded : QM31Exact)
    (projection : words.c2[(fibreIndex index).val]? = some leaf)
    (decodeSuccess : decodeC2EntryExact leaf.value helper (fibreSlot index) =
      some decoded) :
    c2Received words helper index = decoded := by
  simp [c2Received, extractedC2Leaf, projection, decodeSuccess]

theorem disclosed_opening_projects_both_raw_fibres
    (words : ExtractedWords) (opening : PairedOpening)
    (projection : openingIsProjection words opening) :
    (extractedC1Leaf words opening.position).value = opening.c1Value ∧
      (extractedC2Leaf words opening.position).value = opening.c2Value := by
  exact ⟨by
      rw [extractedC1Leaf_of_projection words opening.position
        ⟨opening.c1Value, opening.sharedSalt⟩ projection.1],
    by
      rw [extractedC2Leaf_of_projection words opening.position
        ⟨opening.c2Value, opening.sharedSalt⟩ projection.2]⟩

#print axioms initial_index_decomposition
#print axioms fibreIndex_initialIndex
#print axioms fibreSlot_initialIndex
#print axioms extractedWidth29_c1_lane
#print axioms extractedWidth29_c2_lane
#print axioms width29_lane_partition
#print axioms c1_received_of_exact_projection
#print axioms c2_received_of_exact_projection
#print axioms disclosed_opening_projects_both_raw_fibres

end AspisPool.V7ExtractedLaneWords
