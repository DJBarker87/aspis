-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart19
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::QM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 857:4-857:39
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::mul]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::mul"]
def aspis_core.field.QM31.mul
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let m0 ← aspis_core.field.CM31.mul self.c0 rhs.c0
  let m1 ← aspis_core.field.CM31.mul self.c1 rhs.c1
  let c ← aspis_core.field.CM31.add self.c0 self.c1
  let c1 ← aspis_core.field.CM31.add rhs.c0 rhs.c1
  let m2 ← aspis_core.field.CM31.mul c c1
  let c2 ← aspis_core.field.mul_by_r m1
  let c3 ← aspis_core.field.CM31.add m0 c2
  let c4 ← aspis_core.field.CM31.sub m2 m0
  let c5 ← aspis_core.field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

end PoolV1CopyLaneBooleanGenerated
