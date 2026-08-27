import Aeneas
import PoolV1NormalizedNewPageData.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1NormalizedNewPageData

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-! Exact executable model of shared-slice `Iterator::any`. -/
def core.slice.iter.Iter.anyAux
    {T F : Type} (predicate : core.ops.function.FnMut F T Bool) :
    Nat → core.slice.iter.Iter T → F →
      Result (Bool × core.slice.iter.Iter T × F)
  | 0, iter, state => .ok (false, iter, state)
  | fuel + 1, iter, state => do
      let (item, next) ← core.slice.iter.IteratorSliceIter.next iter
      match item with
      | none => .ok (false, next, state)
      | some value =>
        let (found, state') ← predicate.call_mut state value
        if found then .ok (true, next, state')
        else core.slice.iter.Iter.anyAux predicate fuel next state'

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type} (predicate : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T)
  | iter, state => do
      let (found, final, _) ← core.slice.iter.Iter.anyAux predicate
        (iter.slice.len - iter.i + 1) iter state
      .ok (found, final)

@[rust_const
  "aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES"]
def aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES :
    Result Std.Usize :=
  .ok 8256#usize
