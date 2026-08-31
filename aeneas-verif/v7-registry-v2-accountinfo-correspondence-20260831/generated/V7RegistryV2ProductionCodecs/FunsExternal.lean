import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7RegistryV2ProductionCodecs.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

open V7RegistryV2ProductionCodecsGenerated

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::ne"]
def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Std.Usize}
    (cmpPartialEqInst : core.cmp.PartialEq T U)
    (slice : Slice T) (array : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.ne cmpPartialEqInst slice
    (Array.to_slice array)
