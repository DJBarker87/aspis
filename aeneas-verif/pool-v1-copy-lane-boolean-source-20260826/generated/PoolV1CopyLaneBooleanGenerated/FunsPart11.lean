-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart10
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::CM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 225:4-225:39
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::sub]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::sub"]
def aspis_core.field.CM31.sub
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.sub self.a rhs.a
  let m1 ← aspis_core.field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

end PoolV1CopyLaneBooleanGenerated
