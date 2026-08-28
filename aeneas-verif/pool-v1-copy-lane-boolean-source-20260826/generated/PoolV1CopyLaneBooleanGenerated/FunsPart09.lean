-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart08
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::CM31}::from_m31]:
    Source: 'crates/aspis-core/src/field.rs', lines 212:4-212:35
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::from_m31]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::from_m31"]
def aspis_core.field.CM31.from_m31
  (a : aspis_core.field.M31) : Result aspis_core.field.CM31 := do
  ok { a, b := aspis_core.field.M31.ZERO }

end PoolV1CopyLaneBooleanGenerated
