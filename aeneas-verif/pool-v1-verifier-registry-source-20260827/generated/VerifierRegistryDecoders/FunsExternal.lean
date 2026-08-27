-- Transparent completion of the sole standard-library function left external
-- by the focused production decoder extraction.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import VerifierRegistryDecoders.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open VerifierRegistryDecodersGenerated

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::ne"]
def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Std.Usize}
    (cmpPartialEqInst : core.cmp.PartialEq T U)
    (slice : Slice T) (array : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.ne cmpPartialEqInst slice
    (Array.to_slice array)
