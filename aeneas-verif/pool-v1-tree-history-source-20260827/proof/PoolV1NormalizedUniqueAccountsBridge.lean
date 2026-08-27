import PoolV1NormalizedUnique.Funs

/-!
# Pool V1 normalized account-key uniqueness bridge

The production uniqueness gate reads only account keys.  This extraction-only
projection retains its exact two nested ranges and first-duplicate rejection.
The theorem below pins the critical inner-loop behavior directly to translated
Rust.  Full recursion-to-pairwise composition remains a separate theorem.
-/

set_option autoImplicit false

namespace PoolV1NormalizedUniqueAccountsBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open pool_v1_tree_history_source_harness

theorem inner_loop_body_rejects_equal_selected_keys
    (keys : Slice (Array Std.U8 32#usize))
    (left right : Std.Usize)
    (iter nextIter : core.ops.range.Range Std.Usize)
    (leftKey rightKey : Array Std.U8 32#usize)
    (nextRun : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter = .ok (.some right, nextIter))
    (leftRun : Slice.index_usize keys left = .ok leftKey)
    (rightRun : Slice.index_usize keys right = .ok rightKey)
    (equalRun : core.array.equality.PartialEqArray.eq
      core.cmp.PartialEqU8 leftKey rightKey = .ok true) :
    normalized_require_unique_account_keys_loop0_loop0.body
      keys left iter = .ok (done (.some false)) := by
  unfold normalized_require_unique_account_keys_loop0_loop0.body
  rw [nextRun]
  simp (config := { zeta := true }) only [bind_tc_ok]
  rw [leftRun]
  simp only [bind_tc_ok]
  change (do
    let selected ← Slice.index_usize keys right
    let equal ← core.array.equality.PartialEqArray.eq
      core.cmp.PartialEqU8 leftKey selected
    if equal then ok (done (some false)) else ok (cont nextIter)) =
      .ok (done (some false))
  rw [rightRun]
  simp only [bind_tc_ok]
  rw [equalRun]
  rfl

#print axioms inner_loop_body_rejects_equal_selected_keys

end PoolV1NormalizedUniqueAccountsBridge
