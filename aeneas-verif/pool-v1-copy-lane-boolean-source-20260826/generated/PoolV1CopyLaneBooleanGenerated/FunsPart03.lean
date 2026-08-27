-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart02
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::M31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 56:4-56:37
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::add]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::add"]
def aspis_core.field.M31.add
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let s ← self + rhs
  if s >= aspis_core.field.P
  then let s1 ← s - aspis_core.field.P
       ok s1
  else ok s

end PoolV1CopyLaneBooleanGenerated
