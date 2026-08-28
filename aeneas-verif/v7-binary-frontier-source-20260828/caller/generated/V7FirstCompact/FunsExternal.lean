import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7BinaryFrontier.FunsExternal
import V7FirstCompact.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V7FirstCompactSource

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 4096

/-! Transparent executable models of the Rust library operations reachable
from the literal first-cap-203 caller extraction. -/

@[rust_fun "core::num::{u32}::is_power_of_two"]
def core.num.U32.is_power_of_two (value : Std.U32) : Result Bool :=
  .ok value.val.isPowerOfTwo

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, closure => do
      let mapped ← inst.call_once closure error
      .ok (.Err mapped)

@[rust_fun
  "alloc::vec::{core::convert::TryFrom<[@T; @N], alloc::vec::Vec<@T>, alloc::vec::Vec<@T>>}::try_from"]
def Array.Insts.CoreConvertTryFromVecVec.try_from
    {T : Type} (_allocator : Type) (size : Std.Usize)
    (value : alloc.vec.Vec T) :
    Result (core.result.Result (Array T size) (alloc.vec.Vec T)) :=
  if lengthExact : value.val.length = size.val then
    .ok (.Ok ⟨value.val, lengthExact⟩)
  else
    .ok (.Err value)
