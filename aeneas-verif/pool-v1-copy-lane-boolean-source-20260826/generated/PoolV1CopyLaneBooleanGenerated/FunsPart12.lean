-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart11
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::CM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 242:4-242:39
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::mul]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::mul"]
def aspis_core.field.CM31.mul
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m0 ← aspis_core.field.M31.mul self.a rhs.a
  let m1 ← aspis_core.field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← Std.lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← Std.lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← Std.lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← Std.lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← aspis_core.field.M31.reduce_u64 i10
  let m ← aspis_core.field.M31.sub m0 m1
  let m3 ← aspis_core.field.M31.sub m2 m0
  let m4 ← aspis_core.field.M31.sub m3 m1
  ok { a := m, b := m4 }

end PoolV1CopyLaneBooleanGenerated
