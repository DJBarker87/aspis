import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk04

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::params::CIRCLE_LOG_ORDER]
    Source: 'crates/aspis-core/src/params.rs', lines 20:0-20:31
    Name pattern: [aspis_core::params::CIRCLE_LOG_ORDER]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::params::CIRCLE_LOG_ORDER"]
def aspis_core.params.CIRCLE_LOG_ORDER : Std.U32 := 31#u32

/-- [aspis_core::circle_fri::CIRCLE_INDEX_MASK]
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 28:0-28:28
    Name pattern: [aspis_core::circle_fri::CIRCLE_INDEX_MASK] -/
@[global_simps, irreducible, rust_const
  "aspis_core::circle_fri::CIRCLE_INDEX_MASK"]
def aspis_core.circle_fri.CIRCLE_INDEX_MASK : Result Std.U64 := do
  let i ← 1#u64 <<< aspis_core.params.CIRCLE_LOG_ORDER
  i - 1#u64

/-- [aspis_core::circle_fri::{aspis_core::circle_fri::BaseCirclePoint}::add]:
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 40:4-40:35
    Name pattern: [aspis_core::circle_fri::{aspis_core::circle_fri::BaseCirclePoint}::add] -/
@[rust_fun
  "aspis_core::circle_fri::{aspis_core::circle_fri::BaseCirclePoint}::add"]
def aspis_core.circle_fri.BaseCirclePoint.add
  (self : aspis_core.circle_fri.BaseCirclePoint)
  (rhs : aspis_core.circle_fri.BaseCirclePoint) :
  Result aspis_core.circle_fri.BaseCirclePoint
  := do
  let m ← aspis_core.field.M31.mul self.x rhs.x
  let m1 ← aspis_core.field.M31.mul self.y rhs.y
  let m2 ← aspis_core.field.M31.sub m m1
  let m3 ← aspis_core.field.M31.mul self.x rhs.y
  let m4 ← aspis_core.field.M31.mul self.y rhs.x
  let m5 ← aspis_core.field.M31.add m3 m4
  ok { x := m2, y := m5 }

/-- [aspis_core::params::CIRCLE_GEN]
    Source: 'crates/aspis-core/src/params.rs', lines 14:0-14:26
    Name pattern: [aspis_core::params::CIRCLE_GEN]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::params::CIRCLE_GEN"]
def aspis_core.params.CIRCLE_GEN : aspis_core.field.CM31 :=
  { a := 2#u32, b := 1268011823#u32 }

/-- [aspis_core::field::{aspis_core::field::CM31}::ONE]
    Source: 'crates/aspis-core/src/field.rs', lines 201:4-201:23
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::ONE]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::CM31}::ONE"]
def aspis_core.field.CM31.ONE : aspis_core.field.CM31 :=
  { a := 1#u32, b := 0#u32 }

/-- [aspis_core::field::{aspis_core::field::CM31}::pow]: loop body 0:
    Source: 'crates/aspis-core/src/field.rs', lines 315:8-321:9
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::pow]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::field::{aspis_core::field::CM31}::pow"]
def aspis_core.field.CM31.pow_loop.body
  (exp : Std.U64) (base : aspis_core.field.CM31) (acc : aspis_core.field.CM31)
  :
  Result (ControlFlow (Std.U64 × aspis_core.field.CM31 ×
    aspis_core.field.CM31) aspis_core.field.CM31)
  := do
  if exp > 0#u64
  then
    let i ← lift (exp &&& 1#u64)
    let acc1 ←
      if i = 1#u64
      then aspis_core.field.CM31.mul acc base
      else ok acc
    let base1 ← aspis_core.field.CM31.square base
    let exp1 ← exp >>> 1#i32
    ok (cont (exp1, base1, acc1))
  else ok (done acc)

/-- [aspis_core::field::{aspis_core::field::CM31}::pow]: loop 0:
    Source: 'crates/aspis-core/src/field.rs', lines 315:8-321:9
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::pow]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::field::{aspis_core::field::CM31}::pow"]
def aspis_core.field.CM31.pow_loop
  (exp : Std.U64) (base : aspis_core.field.CM31) (acc : aspis_core.field.CM31)
  :
  Result aspis_core.field.CM31
  := do
  loop
    (fun (exp1, base1, acc1) => aspis_core.field.CM31.pow_loop.body exp1 base1
      acc1)
    (exp, base, acc)

/-- [aspis_core::field::{aspis_core::field::CM31}::pow]:
    Source: 'crates/aspis-core/src/field.rs', lines 312:4-312:42
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::pow]
    Visibility: public -/
@[reducible, rust_fun "aspis_core::field::{aspis_core::field::CM31}::pow"]
def aspis_core.field.CM31.pow
  (self : aspis_core.field.CM31) (exp : Std.U64) :
  Result aspis_core.field.CM31
  := do
  aspis_core.field.CM31.pow_loop exp self aspis_core.field.CM31.ONE

/-- [aspis_core::circle_fri::point_from_group_index]:
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 224:0-224:56
    Name pattern: [aspis_core::circle_fri::point_from_group_index] -/
@[rust_fun "aspis_core::circle_fri::point_from_group_index"]
def aspis_core.circle_fri.point_from_group_index
  (index : Std.U64) : Result aspis_core.circle_fri.BaseCirclePoint := do
  let i ← aspis_core.circle_fri.CIRCLE_INDEX_MASK
  let i1 ← lift (index &&& i)
  let point ← aspis_core.field.CM31.pow aspis_core.params.CIRCLE_GEN i1
  ok { x := point.a, y := point.b }

/-- [aspis_core::circle_fri::bit_reverse_index]:
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 696:0-696:86
    Name pattern: [aspis_core::circle_fri::bit_reverse_index]
    Visibility: public -/
@[rust_fun "aspis_core::circle_fri::bit_reverse_index"]
def aspis_core.circle_fri.bit_reverse_index
  (index : Std.Usize) (log_size : Std.U32) :
  Result (core.result.Result Std.Usize aspis_core.circle_fri.CircleFriError)
  := do
  let o ← core.num.Usize.checked_shl 1#usize log_size
  let r ←
    core.option.Option.ok_or o
      aspis_core.circle_fri.CircleFriError.InvalidBitReverseLength
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    if index >= val
    then
      ok (core.result.Result.Err
        aspis_core.circle_fri.CircleFriError.BitReverseIndexOutOfRange)
    else
      if log_size = 0#u32
      then ok (core.result.Result.Ok 0#usize)
      else
        let i ← core.num.Usize.reverse_bits index
        let i1 ← core.num.Usize.BITS - log_size
        let i2 ← i >>> i1
        ok (core.result.Result.Ok i2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Std.Usize (core.convert.FromSame aspis_core.circle_fri.CircleFriError)
      residual

/-- [aspis_core::circle_fri::half_odds_step_index]:
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 533:0-533:45
    Name pattern: [aspis_core::circle_fri::half_odds_step_index] -/
@[rust_fun "aspis_core::circle_fri::half_odds_step_index"]
def aspis_core.circle_fri.half_odds_step_index
  (log_size : Std.U32) : Result Std.U64 := do
  let i ← aspis_core.params.CIRCLE_LOG_ORDER - log_size
  1#u64 <<< i

/-- [aspis_core::circle_fri::half_odds_initial_index]:
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 528:0-528:48
    Name pattern: [aspis_core::circle_fri::half_odds_initial_index] -/
@[rust_fun "aspis_core::circle_fri::half_odds_initial_index"]
def aspis_core.circle_fri.half_odds_initial_index
  (log_size : Std.U32) : Result Std.U64 := do
  let i ← log_size + 2#u32
  let i1 ← aspis_core.params.CIRCLE_LOG_ORDER - i
  1#u64 <<< i1


end V7Tag73CurrentHelpersOpaque
