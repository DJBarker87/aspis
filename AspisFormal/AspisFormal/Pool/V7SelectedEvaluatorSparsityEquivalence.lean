import AspisFormal.V5GoodGateDotBatching
import AspisFormal.V5M31RawMulReduction
import Mathlib

/-!
# Algebraic closure for the selected V7 evaluator sparsity rewrites

This module proves the field identities used by the final Tag-73/eight-lane
CU configuration.  It does not alter the relation, transcript, query count,
digest width, work schedule, or proof claims.  Source correspondence for the
literal Rust tables and loop bounds is a separate Aeneas obligation.

The covered rewrites are:

* factoring shared selectors over packed range residuals;
* grouping equality-basis products by their low selector coordinate;
* grouping the seven frozen active-row masks;
* separating Copy tags from dynamic tuple patterns;
* grouping dynamic tuple patterns by pattern identifier;
* preserving each of the four gamma outputs under block/slot loop
  interchange;
* batching the four selected Copy-finish dot widths; and
* the exact four-canonical-product `u64` bound used by Copy tag dots.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace AspisPool.V7SelectedEvaluatorSparsityEquivalence

/-! ## Shared-selector and selector-tensor identities -/

variable {K : Type*} [CommRing K]

theorem selector_mul_pair_sum (selector left right : K) :
    selector * (left + right) = selector * left + selector * right := by
  ring

theorem selector_mul_four_sum
    (selector x0 x1 x2 x3 : K) :
    selector * (x0 + x1 + x2 + x3) =
      selector * x0 + selector * x1 + selector * x2 + selector * x3 := by
  ring

/-- Literal equality-selector contraction over sparse events. -/
def literalSelectorTensor
    {Block Local Event : Type*}
    [Fintype Event]
    (block : Event → Block) (localOf : Event → Local)
    (high : Block → K) (low : Local → K) (residual : Event → K) : K :=
  ∑ event, high (block event) * low (localOf event) * residual event

/-- The selected source first accumulates by high block inside each low-local
coordinate, then contracts the low selector once.  The `if` is the exact
finite-fibre partition; absent coordinates contribute zero. -/
def groupedSelectorTensor
    {Block Local Event : Type*}
    [Fintype Local] [Fintype Event] [DecidableEq Local]
    (block : Event → Block) (localOf : Event → Local)
    (high : Block → K) (low : Local → K) (residual : Event → K) : K :=
  ∑ localCoordinate, low localCoordinate *
    ∑ event, if localOf event = localCoordinate then
      high (block event) * residual event else 0

/-- Grouping sparse equality-selector events by their low coordinate is exact
over every commutative ring. -/
theorem groupedSelectorTensor_eq_literal
    {Block Local Event : Type*}
    [Fintype Local] [Fintype Event] [DecidableEq Local]
    (block : Event → Block) (localOf : Event → Local)
    (high : Block → K) (low : Local → K) (residual : Event → K) :
    groupedSelectorTensor block localOf high low residual =
      literalSelectorTensor block localOf high low residual := by
  classical
  simp only [groupedSelectorTensor, literalSelectorTensor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro event _
  simp [mul_comm, mul_left_comm]

/-- The packed public-digest tensor is the preceding identity with the event
residual already containing the unchanged four-limb pack. -/
theorem packedDigestSelectorTensor_eq_literal
    {Block Local Event : Type*}
    [Fintype Local] [Fintype Event] [DecidableEq Local]
    (block : Event → Block) (localOf : Event → Local)
    (high : Block → K) (low : Local → K) (packedResidual : Event → K) :
    groupedSelectorTensor block localOf high low packedResidual =
      literalSelectorTensor block localOf high low packedResidual :=
  groupedSelectorTensor_eq_literal block localOf high low packedResidual

/-- The exact three low coordinates present in the deployed public-digest
binding grammar. -/
def packedDigestLocal : Fin 3 → Fin 16 := ![0, 11, 12]

theorem packedDigestLocal_injective : Function.Injective packedDigestLocal := by
  decide

/-! ## Seven-mask active-row basis -/

/-- The seven and only seven masks in the selected 64-block Copy active-row
schedule.  The source bridge must prove that every generated block maps to one
of these values. -/
def copyActiveMask : Fin 7 → Fin 65536 :=
  ![6144, 6145, 4097, 2048, 2049, 26214, 1749]

theorem copyActiveMask_injective : Function.Injective copyActiveMask := by
  decide

/-- Once each block is classified by its exact mask, summing high selectors
inside a mask class and evaluating the low mask once is the literal active-row
sum. -/
theorem activeMaskBasis_eq_literal
    {Block Mask : Type*}
    [Fintype Block] [Fintype Mask] [DecidableEq Mask]
    (maskOf : Block → Mask) (high : Block → K) (lowMask : Mask → K) :
    (∑ mask, lowMask mask *
        ∑ block, if maskOf block = mask then high block else 0) =
      ∑ block, high block * lowMask (maskOf block) := by
  simpa [groupedSelectorTensor, literalSelectorTensor, mul_assoc,
    mul_comm, mul_left_comm] using
    (groupedSelectorTensor_eq_literal
      (K := K) (fun block : Block => block) maskOf high lowMask
        (fun _ => (1 : K)))

/-! ## Copy tag/pattern basis -/

/-- Splitting the compressed endpoint value into its static tag and dynamic
tuple-pattern parts preserves the original endpoint sum. -/
theorem endpointTagPatternSplit
    {Event : Type*} [Fintype Event]
    (selector tag pattern : Event → K) :
    (∑ event, selector event * (tag event + pattern event)) =
      (∑ event, selector event * tag event) +
      ∑ event, pattern event * selector event := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro event _
  exact mul_comm _ _

/-- Grouping dynamic pattern terms by pattern identifier is exact. -/
theorem patternBasisGrouping
    {Pattern Event : Type*}
    [Fintype Pattern] [Fintype Event] [DecidableEq Pattern]
    (patternOf : Event → Pattern)
    (selector : Event → K) (patternValue : Pattern → K) :
    (∑ pattern, patternValue pattern *
        ∑ event, if patternOf event = pattern then selector event else 0) =
      ∑ event, selector event * patternValue (patternOf event) := by
  simpa [groupedSelectorTensor, literalSelectorTensor, mul_assoc,
    mul_comm, mul_left_comm] using
    (groupedSelectorTensor_eq_literal
      (K := K) (fun event : Event => event) patternOf selector patternValue
        (fun _ => (1 : K)))

/-! ## Gamma loop interchange -/

/-- Seven fixed reduction chunks: six four-column blocks and the final
two-column tail.  `chunkTerm slot chunk` denotes the already reduced M31/QM31
contribution, so retaining this term verbatim retains every reduction
boundary. -/
def gammaSlotMajor
    (chunkTerm : Fin 4 → Fin 7 → K) : Fin 4 → K :=
  fun slot => ∑ chunk, chunkTerm slot chunk

/-- The block-major implementation writes the same per-slot accumulator. -/
def gammaBlockMajor
    (chunkTerm : Fin 4 → Fin 7 → K) : Fin 4 → K :=
  fun slot => ∑ chunk, chunkTerm slot chunk

theorem gammaBlockMajor_eq_slotMajor
    (chunkTerm : Fin 4 → Fin 7 → K) :
    gammaBlockMajor chunkTerm = gammaSlotMajor chunkTerm := by
  rfl

/-- If the four outputs are viewed together, changing the traversal order is
the standard finite double-sum interchange. -/
theorem gamma_slot_block_total_interchange
    (chunkTerm : Fin 4 → Fin 7 → K) :
    (∑ slot, ∑ chunk, chunkTerm slot chunk) =
      ∑ chunk, ∑ slot, chunkTerm slot chunk := by
  exact Finset.sum_comm

/-! ## Selected Copy-finish dot chunkings -/

def finishDot9 (term : Fin 9 → K) : K :=
  (term 0 + term 1 + term 2 + term 3) +
  (term 4 + term 5 + term 6 + term 7) + term 8

def finishDot6 (term : Fin 6 → K) : K :=
  (term 0 + term 1 + term 2 + term 3) + (term 4 + term 5)

def finishDot11 (term : Fin 11 → K) : K :=
  (term 0 + term 1 + term 2 + term 3) +
  (term 4 + term 5 + term 6 + term 7) +
  (term 8 + term 9 + term 10)

def finishDot4 (term : Fin 4 → K) : K :=
  term 0 + term 1 + term 2 + term 3

theorem finishDot9_eq_sum (term : Fin 9 → K) :
    finishDot9 term = ∑ index, term index := by
  simp [finishDot9, Fin.sum_univ_succ]
  ring

theorem finishDot6_eq_sum (term : Fin 6 → K) :
    finishDot6 term = ∑ index, term index := by
  simp [finishDot6, Fin.sum_univ_succ]
  ring

theorem finishDot11_eq_sum (term : Fin 11 → K) :
    finishDot11 term = ∑ index, term index := by
  simp [finishDot11, Fin.sum_univ_succ]
  ring

theorem finishDot4_eq_sum (term : Fin 4 → K) :
    finishDot4 term = ∑ index, term index := by
  simp [finishDot4, Fin.sum_univ_four]

/-! ## Exact `u64` safety and residue for four tag products -/

open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31TowerExact
open AspisV5GoodGateDotBatching
open AspisV5M31RawMulReduction

/-- One raw four-product channel in `copy_tag_coordinate_dot`. -/
def copyTagRaw4 (left right : Fin 4 → Nat) : Nat :=
  ∑ index, left index * right index

theorem copy_tag_four_max_products_lt_u64 :
    4 * (P - 1) ^ 2 < 2 ^ 64 :=
  four_max_products_lt_u64

private theorem canonical_product_le_max
    {x y : Nat} (hx : x < P) (hy : y < P) :
    x * y ≤ (P - 1) ^ 2 := by
  have hx' : x ≤ P - 1 := Nat.le_pred_of_lt hx
  have hy' : y ≤ P - 1 := Nat.le_pred_of_lt hy
  simpa [pow_two] using Nat.mul_le_mul hx' hy'

theorem copyTagRaw4_lt_u64
    (left right : Fin 4 → Nat)
    (hleft : ∀ index, left index < P)
    (hright : ∀ index, right index < P) :
    copyTagRaw4 left right < 2 ^ 64 := by
  have h0 := canonical_product_le_max (hleft 0) (hright 0)
  have h1 := canonical_product_le_max (hleft 1) (hright 1)
  have h2 := canonical_product_le_max (hleft 2) (hright 2)
  have h3 := canonical_product_le_max (hleft 3) (hright 3)
  rw [copyTagRaw4, Fin.sum_univ_four]
  have hmax := copy_tag_four_max_products_lt_u64
  omega

/-- Reducing one four-product tag channel yields exactly its M31 dot. -/
theorem copyTagRaw4_reduce_exact
    (left right : Fin 4 → Nat)
    (hleft : ∀ index, left index < P)
    (hright : ∀ index, right index < P) :
    ((rawReduceU64 (copyTagRaw4 left right) : Nat) : M31Exact) =
      ∑ index : Fin 4,
        (left index : M31Exact) * (right index : M31Exact) := by
  rw [rawReduceU64_residue _ (copyTagRaw4_lt_u64 left right hleft hright)]
  rw [copyTagRaw4, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [Nat.cast_mul]

#print axioms selector_mul_four_sum
#print axioms groupedSelectorTensor_eq_literal
#print axioms activeMaskBasis_eq_literal
#print axioms endpointTagPatternSplit
#print axioms patternBasisGrouping
#print axioms gammaBlockMajor_eq_slotMajor
#print axioms gamma_slot_block_total_interchange
#print axioms finishDot9_eq_sum
#print axioms finishDot6_eq_sum
#print axioms finishDot11_eq_sum
#print axioms finishDot4_eq_sum
#print axioms copyTagRaw4_lt_u64
#print axioms copyTagRaw4_reduce_exact

end AspisPool.V7SelectedEvaluatorSparsityEquivalence
