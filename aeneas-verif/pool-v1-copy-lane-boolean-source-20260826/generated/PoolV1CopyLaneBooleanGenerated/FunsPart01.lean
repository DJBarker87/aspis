-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart00
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 28:0-28:28
    Name pattern: [aspis_core::field::reduce_u64] -/
@[rust_fun "aspis_core::field::reduce_u64"]
def aspis_core.field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← Std.lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← Std.lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← Std.lift (UScalar.cast .U64 aspis_core.field.P)
  let i4 ← Std.lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← Std.lift (UScalar.cast .U32 x2)
  if x3 >= aspis_core.field.P
  then x3 - aspis_core.field.P
  else ok x3

end PoolV1CopyLaneBooleanGenerated
