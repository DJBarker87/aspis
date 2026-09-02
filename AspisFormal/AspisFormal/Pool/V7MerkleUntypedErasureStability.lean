import AspisFormal.Pool.V7MerkleCompletePrefixStability
import AspisFormal.Pool.V7MerkleRawCollisionPredicate

/-!
# Order-preserving erasure of non-Merkle SHA queries

The restored Tag-73 fibre changes a small set of routed transcript queries,
but an adversary may place those queries anywhere in its chronological SHA
log.  Prefix locality is therefore insufficient: we need to erase the routed
queries in place while retaining every intervening Merkle query.

This module starts that stronger proof with the two facts used at every
recursive traversal node:

* deleting the pivot in `pre ++ pivot :: suffix` is exactly `pre ++ suffix`;
* in a collision-free log, an untyped pivot cannot have the digest of a typed
  Merkle preimage in the same log.

The later traversal theorem can consequently shift indices across the erased
pivot without assuming that the pivot occurred after the prover's Merkle
queries or that the verifier exposed it first.
-/

set_option autoImplicit false

namespace AspisPool.V7MerkleUntypedErasureStability

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleCompletePrefixStability
open AspisPool.V7MerkleRawCollisionPredicate

/-- Erasing the distinguished pivot preserves the exact order of all other
queries. -/
theorem eraseIdx_pivot_append
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput) :
    (pre ++ pivot :: suffix).eraseIdx pre.length = pre ++ suffix := by
  rw [List.eraseIdx_eq_take_drop_succ]
  simp

/-- Absence of the executable collision event makes the truncated digest
function injective on members of the audited log. -/
theorem truncate_injective_on_log_of_no_collision
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (noCollision : hasRawTruncatedCollision truncateSha256 log = false)
    {left right : RawHashInput}
    (leftMem : left ∈ log) (rightMem : right ∈ log)
    (digestExact : truncateSha256 left = truncateSha256 right) :
    left = right := by
  by_contra distinct
  have collision : RawLogTruncatedDigestCollision truncateSha256 log :=
    ⟨left, leftMem, right, rightMem, distinct, digestExact⟩
  exact ((no_raw_truncated_collision_iff truncateSha256 log).mp noCollision)
    collision

/-- A routed non-Merkle query cannot shadow any typed Merkle query under a
collision-free 208-bit view.  This is the precise replacement for the false
assumption that all routed queries form a suffix. -/
theorem untyped_pivot_digest_ne_typed_member
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot typed : RawHashInput)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false)
    (pivotUntyped : parseTypedPreimage pivot = none)
    (typedMem : typed ∈ pre ++ pivot :: suffix)
    (typedExact : parseTypedPreimage typed ≠ none) :
    truncateSha256 pivot ≠ truncateSha256 typed := by
  intro digestExact
  have pivotMem : pivot ∈ pre ++ pivot :: suffix := by simp
  have inputExact := truncate_injective_on_log_of_no_collision truncateSha256
    (pre ++ pivot :: suffix) noCollision pivotMem typedMem digestExact
  subst typed
  exact typedExact pivotUntyped

/-- The previous result in the orientation used by `resolveFirst`: a target
digest known to come from a typed log member cannot match the erased pivot. -/
theorem untyped_pivot_ne_typed_target
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot typed : RawHashInput)
    (target : Digest208)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false)
    (pivotUntyped : parseTypedPreimage pivot = none)
    (typedMem : typed ∈ pre ++ pivot :: suffix)
    (typedExact : parseTypedPreimage typed ≠ none)
    (targetExact : truncateSha256 typed = target) :
    truncateSha256 pivot ≠ target := by
  rw [← targetExact]
  exact untyped_pivot_digest_ne_typed_member truncateSha256 pre suffix pivot
    typed noCollision pivotUntyped typedMem typedExact

/-! ## Exact index transport across one erased query -/

/-- Embed an index of the shortened log back into the original log. -/
def liftErasedIndex (pivot index : Nat) : Nat :=
  if index < pivot then index else index + 1

/-- `resolveFirstAux` is equivariant under a uniform change of its absolute
index offset. -/
theorem resolveFirstAux_offset_add
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208) :
    ∀ (log : OrderedRawQueryLog) (offset delta : Nat),
      resolveFirstAux truncateSha256 target (offset + delta) log =
        (resolveFirstAux truncateSha256 target offset log).map
          (fun index => index + delta) := by
  intro log
  induction log with
  | nil => intro offset delta; simp [resolveFirstAux]
  | cons head tail ih =>
      intro offset delta
      by_cases hit : truncateSha256 head = target
      · simp [resolveFirstAux, hit, Nat.add_comm]
      · rw [resolveFirstAux_cons_miss truncateSha256 target (offset + delta)
          head tail hit]
        rw [resolveFirstAux_cons_miss truncateSha256 target offset head tail hit]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (offset + 1) delta

/-- Removing one query which misses the target preserves `resolveFirstAux`,
with the unique expected index shift after the pivot. -/
theorem resolveFirstAux_erase_miss
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208) :
    ∀ (offset : Nat) (pre suffix : OrderedRawQueryLog)
      (pivot : RawHashInput),
      truncateSha256 pivot ≠ target →
      resolveFirstAux truncateSha256 target offset
          (pre ++ pivot :: suffix) =
        (resolveFirstAux truncateSha256 target offset (pre ++ suffix)).map
          (liftErasedIndex (offset + pre.length)) := by
  intro offset pre
  induction pre generalizing offset with
  | nil =>
      intro suffix pivot miss
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      rw [resolveFirstAux_cons_miss truncateSha256 target offset pivot suffix
        miss]
      rw [resolveFirstAux_offset_add truncateSha256 target suffix offset 1]
      cases resolved : resolveFirstAux truncateSha256 target offset suffix with
      | none => simp
      | some index =>
          have bound := resolveFirstAux_some_bounds truncateSha256 target offset
            suffix index resolved
          simp [liftErasedIndex]
          omega
  | cons head tail ih =>
      intro suffix pivot miss
      simp only [List.cons_append, List.length_cons]
      by_cases hit : truncateSha256 head = target
      · simp [resolveFirstAux, hit, liftErasedIndex]
      · rw [resolveFirstAux_cons_miss truncateSha256 target offset head
          (tail ++ pivot :: suffix) hit]
        rw [resolveFirstAux_cons_miss truncateSha256 target offset head
          (tail ++ suffix) hit]
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ih (offset + 1) suffix pivot miss

/-- Root-index form of the erasure theorem. -/
theorem resolveFirst_erase_miss
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput)
    (miss : truncateSha256 pivot ≠ target) :
    resolveFirst truncateSha256 target (pre ++ pivot :: suffix) =
      (resolveFirst truncateSha256 target (pre ++ suffix)).map
        (liftErasedIndex pre.length) := by
  simpa [resolveFirst] using resolveFirstAux_erase_miss truncateSha256 target
    0 pre suffix pivot miss

#print axioms eraseIdx_pivot_append
#print axioms truncate_injective_on_log_of_no_collision
#print axioms untyped_pivot_digest_ne_typed_member
#print axioms untyped_pivot_ne_typed_target
#print axioms resolveFirstAux_offset_add
#print axioms resolveFirstAux_erase_miss
#print axioms resolveFirst_erase_miss

end AspisPool.V7MerkleUntypedErasureStability
