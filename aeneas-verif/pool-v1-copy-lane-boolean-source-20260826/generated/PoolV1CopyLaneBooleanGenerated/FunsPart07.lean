-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart06
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 123:4-123:30
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::double]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::double"]
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  aspis_core.field.M31.add self self

end PoolV1CopyLaneBooleanGenerated
