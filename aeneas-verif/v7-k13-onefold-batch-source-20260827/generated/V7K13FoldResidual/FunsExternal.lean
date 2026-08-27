import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7K13FoldResidual.Types

/-!
Executable interpretation of the only standard-library operation left
external by the focused fold/residual extraction.  The production caller uses
`core::array::from_fn` at the fixed length sixteen; every other length fails
closed in this focused interpretation.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7K13FoldResidualGenerated

set_option autoImplicit false

@[rust_fun "core::array::from_fn"]
def core.array.from_fn
    {T F : Type} (N : Std.Usize)
    (fnMutInst : core.ops.function.FnMut F Std.Usize T) :
    F → Result (Array T N)
  | closure =>
    if hN : N = 16#usize then do
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
      let (v15, _) ← fnMutInst.call_mut closure 15#usize
      let output : Array T N := hN.symm ▸
        (Array.make 16#usize
          [v0, v1, v2, v3, v4, v5, v6, v7,
           v8, v9, v10, v11, v12, v13, v14, v15] :
          Array T 16#usize)
      .ok output
    else
      .fail .panic
