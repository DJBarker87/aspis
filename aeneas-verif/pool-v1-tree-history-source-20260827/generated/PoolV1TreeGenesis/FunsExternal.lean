import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import PoolV1TreeGenesis.Types

/-!
Executable interpretations of the standard-library and constant operations
left external by the focused Pool V1 genesis extraction.  The Poseidon parent
remains the one deliberately opaque cryptographic primitive.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeGenesisGenerated

set_option autoImplicit false

@[rust_fun "core::array::from_fn"]
def core.array.from_fn
    {T F : Type} (N : Std.Usize)
    (fnMutInst : core.ops.function.FnMut F Std.Usize T) :
    F → Result (Array T N)
  | closure => do
    if hN : N = 20#usize then
      let (v0, closure) ← fnMutInst.call_mut closure 0#usize
      let (v1, closure) ← fnMutInst.call_mut closure 1#usize
      let (v2, closure) ← fnMutInst.call_mut closure 2#usize
      let (v3, closure) ← fnMutInst.call_mut closure 3#usize
      let (v4, closure) ← fnMutInst.call_mut closure 4#usize
      let (v5, closure) ← fnMutInst.call_mut closure 5#usize
      let (v6, closure) ← fnMutInst.call_mut closure 6#usize
      let (v7, closure) ← fnMutInst.call_mut closure 7#usize
      let (v8, closure) ← fnMutInst.call_mut closure 8#usize
      let (v9, closure) ← fnMutInst.call_mut closure 9#usize
      let (v10, closure) ← fnMutInst.call_mut closure 10#usize
      let (v11, closure) ← fnMutInst.call_mut closure 11#usize
      let (v12, closure) ← fnMutInst.call_mut closure 12#usize
      let (v13, closure) ← fnMutInst.call_mut closure 13#usize
      let (v14, closure) ← fnMutInst.call_mut closure 14#usize
      let (v15, closure) ← fnMutInst.call_mut closure 15#usize
      let (v16, closure) ← fnMutInst.call_mut closure 16#usize
      let (v17, closure) ← fnMutInst.call_mut closure 17#usize
      let (v18, closure) ← fnMutInst.call_mut closure 18#usize
      let (v19, _) ← fnMutInst.call_mut closure 19#usize
      let output : Array T N := hN.symm ▸
        (Array.make 20#usize
          [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9,
           v10, v11, v12, v13, v14, v15, v16, v17, v18, v19] :
          Array T 20#usize)
      .ok output
    else
      .fail .panic

@[rust_const "aspis_core::field::{aspis_core::field::M31}::ZERO"]
def aspis_core.field.M31.ZERO : Result aspis_core.field.M31 :=
  .ok 0#u32

@[rust_const "aspis_statement::pool_v1::format::POOL_V1_TREE_DEPTH"]
def aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH : Result Std.Usize :=
  .ok 20#usize

/-- Exact boundary deliberately excluded from this implementation lane:
the deployed Poseidon/M31 compression primitive. -/
@[rust_fun "aspis_statement::pool_v1::format::pool_v1_tree_parent"]
opaque aspis_statement.pool_v1.format.pool_v1_tree_parent :
  Array aspis_core.field.M31 8#usize →
    Array aspis_core.field.M31 8#usize →
      Result (Array aspis_core.field.M31 8#usize)
