import ASQ8NextLane.Funs

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.ASQ8NextLaneSourceBridge

open ASQ8NextLane

abbrev Lane :=
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
abbrev TerminalResult :=
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1

def exactNextLane (lane : Lane) (result : TerminalResult) : Lane :=
  { lane with tree := {
      next_leaf_index := result.verified_afterstate.next_pair_index
      root := result.verified_afterstate.next_root
      frontier := result.verified_afterstate.next_frontier
    } }

/-- The translated production helper returns exactly the ASR8 afterstate while
preserving the selected lane's master/lane identity.  The loop premise is the
literal generated canonical-empty-frontier check, exposed separately so this
source theorem does not assume Poseidon or incremental-tree semantics. -/
theorem translated_next_lane_success_is_exact_asr8_afterstate
    (lane : Lane) (result : TerminalResult)
    (raw : core.slice.iter.Iter (Array aspis_core.field.M31 8#usize))
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (Array aspis_core.field.M31 8#usize)))
    (added : U64.checked_add lane.tree.next_leaf_index 1#u64 =
      some result.verified_afterstate.next_pair_index)
    (iterExact :
      core.slice.Slice.iter (Array.to_slice result.verified_afterstate.next_frontier) =
        .ok raw)
    (enumerateExact :
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter
          (Array aspis_core.field.M31 8#usize)) raw = .ok iter)
    (frontierCanonical :
      pair_forest.next_pair_forest_lane_v1_loop result iter = .ok none) :
    pair_forest.next_pair_forest_lane_v1 lane result =
      .ok (.Ok (exactNextLane lane result)) := by
  simp [pair_forest.next_pair_forest_lane_v1, added,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    lift, iterExact, enumerateExact, frontierCanonical,
    exactNextLane]

#print axioms translated_next_lane_success_is_exact_asr8_afterstate

end AspisPool.ASQ8NextLaneSourceBridge
