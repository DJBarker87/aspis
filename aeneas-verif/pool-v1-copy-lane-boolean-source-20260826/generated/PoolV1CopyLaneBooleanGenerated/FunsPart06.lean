-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart05
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 95:4-95:40
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::reduce_u64]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::reduce_u64"]
def aspis_core.field.M31.reduce_u64
  (value : Std.U64) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.reduce_u64 value
  ok i

end PoolV1CopyLaneBooleanGenerated
