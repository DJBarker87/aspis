-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart04
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 77:4-77:37
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::mul]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::mul"]
def aspis_core.field.M31.mul
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← Std.lift (UScalar.cast .U64 self)
  let i1 ← Std.lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← aspis_core.field.reduce_u64 i2
  ok i3

end PoolV1CopyLaneBooleanGenerated
