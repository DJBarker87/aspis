import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk03
import V7Tag73CurrentHelpersOpaque.CircleTable_V6_CIRCLE_HIGH6_WINDOW_Chunk03

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::circle_fri::V6_CIRCLE_HIGH6_WINDOW]
    Source: '/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/target-normalized-r2/x86_64-unknown-linux-gnu/debug/build/aspis-core-4e5313882daeed0f/out/circle_tables.rs', lines 36310:0-36310:48
    Name pattern: [aspis_core::circle_fri::V6_CIRCLE_HIGH6_WINDOW]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::circle_fri::V6_CIRCLE_HIGH6_WINDOW"]
def aspis_core.circle_fri.V6_CIRCLE_HIGH6_WINDOW
  : Array (Array Std.U32 2#usize) 64#usize :=
  staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk00) (staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk01)) (staged_circle_tables.append16 (staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk02) (staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk03))

/-- [aspis_core::field::{aspis_core::field::M31}::is_zero]:
    Source: 'crates/aspis-core/src/field.rs', lines 170:4-170:32
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::is_zero]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::is_zero"]
def aspis_core.field.M31.is_zero
  (self : aspis_core.field.M31) : Result Bool := do
  ok (self = 0#u32)

/-- [aspis_core::field::{aspis_core::field::CM31}::is_zero]:
    Source: 'crates/aspis-core/src/field.rs', lines 342:4-342:32
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::is_zero]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::is_zero"]
def aspis_core.field.CM31.is_zero
  (self : aspis_core.field.CM31) : Result Bool := do
  let b ← aspis_core.field.M31.is_zero self.a
  if b
  then aspis_core.field.M31.is_zero self.b
  else ok false

/-- [aspis_core::field::{aspis_core::field::QM31}::is_zero]:
    Source: 'crates/aspis-core/src/field.rs', lines 899:4-899:32
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::is_zero]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::is_zero"]
def aspis_core.field.QM31.is_zero
  (self : aspis_core.field.QM31) : Result Bool := do
  let b ← aspis_core.field.CM31.is_zero self.c0
  if b
  then aspis_core.field.CM31.is_zero self.c1
  else ok false

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 16:0-16:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

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

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 123:4-123:30
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::double]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::double"]
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  aspis_core.field.M31.add self self

/-- [aspis_core::field::{aspis_core::field::M31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 62:4-62:37
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::sub]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::sub"]
def aspis_core.field.M31.sub
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← self + aspis_core.field.P
  let s ← i - rhs
  if s >= aspis_core.field.P
  then let s1 ← s - aspis_core.field.P
       ok s1
  else ok s

/-- [aspis_core::field::mul_by_r]:
    Source: 'crates/aspis-core/src/field.rs', lines 788:0-788:28
    Name pattern: [aspis_core::field::mul_by_r] -/
@[rust_fun "aspis_core::field::mul_by_r"]
def aspis_core.field.mul_by_r
  (x : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.double x.a
  let m1 ← aspis_core.field.M31.sub m x.b
  let m2 ← aspis_core.field.M31.double x.b
  let m3 ← aspis_core.field.M31.add x.a m2
  ok { a := m1, b := m3 }

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 28:0-28:28
    Name pattern: [aspis_core::field::reduce_u64] -/
@[rust_fun "aspis_core::field::reduce_u64"]
def aspis_core.field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= aspis_core.field.P
  then x3 - aspis_core.field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 77:4-77:37
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::mul]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::mul"]
def aspis_core.field.M31.mul
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← aspis_core.field.reduce_u64 i2
  ok i3

/-- [aspis_core::field::{aspis_core::field::M31}::neg]:
    Source: 'crates/aspis-core/src/field.rs', lines 68:4-68:27
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::neg]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::neg"]
def aspis_core.field.M31.neg
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  if self = 0#u32
  then ok 0#u32
  else let i ← aspis_core.field.P - self
       ok i

/-- [aspis_core::field::{aspis_core::field::CM31}::inv_with]:
    Source: 'crates/aspis-core/src/field.rs', lines 332:4-332:58
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::inv_with]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::inv_with"]
def aspis_core.field.CM31.inv_with
  (self : aspis_core.field.CM31)
  (inverse : aspis_core.field.M31 → Result aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.mul self.a self.a
  let m1 ← aspis_core.field.M31.mul self.b self.b
  let norm ← aspis_core.field.M31.add m m1
  let inv_norm ← inverse norm
  let m2 ← aspis_core.field.M31.mul self.a inv_norm
  let m3 ← aspis_core.field.M31.neg self.b
  let m4 ← aspis_core.field.M31.mul m3 inv_norm
  ok { a := m2, b := m4 }

/-- [aspis_core::field::square_n]: loop body 0:
    Source: 'crates/aspis-core/src/field.rs', lines 45:4-47:5
    Name pattern: [aspis_core::field::square_n] -/
@[rust_loop_body, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n_loop.body
  (iter : core.ops.range.Range Std.Usize) (value : aspis_core.field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.field.M31) aspis_core.field.M31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done value)
  | some _ =>
    let value1 ← aspis_core.field.M31.mul value value
    ok (cont (iter1, value1))

/-- [aspis_core::field::square_n]: loop 0:
    Source: 'crates/aspis-core/src/field.rs', lines 45:4-47:5
    Name pattern: [aspis_core::field::square_n] -/
@[rust_loop, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n_loop
  (iter : core.ops.range.Range Std.Usize) (value : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  loop
    (fun (iter1, value1) => aspis_core.field.square_n_loop.body iter1 value1)
    (iter, value)

/-- [aspis_core::field::square_n]:
    Source: 'crates/aspis-core/src/field.rs', lines 44:0-44:48
    Name pattern: [aspis_core::field::square_n] -/
@[reducible, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n
  (value : aspis_core.field.M31) (count : Std.Usize) :
  Result aspis_core.field.M31
  := do
  aspis_core.field.square_n_loop { start := 0#usize, «end» := count } value

/-- [aspis_core::field::{aspis_core::field::M31}::inv]:
    Source: 'crates/aspis-core/src/field.rs', lines 151:4-151:27
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::inv]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::inv"]
def aspis_core.field.M31.inv
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  massert (self != 0#u32)
  let m ← aspis_core.field.M31.mul self self
  let t2 ← aspis_core.field.M31.mul m self
  let m1 ← aspis_core.field.square_n t2 2#usize
  let t4 ← aspis_core.field.M31.mul m1 t2
  let m2 ← aspis_core.field.square_n t4 4#usize
  let t8 ← aspis_core.field.M31.mul m2 t4
  let m3 ← aspis_core.field.square_n t8 8#usize
  let t16 ← aspis_core.field.M31.mul m3 t8
  let m4 ← aspis_core.field.square_n t16 8#usize
  let t24 ← aspis_core.field.M31.mul m4 t8
  let m5 ← aspis_core.field.square_n t24 4#usize
  let t28 ← aspis_core.field.M31.mul m5 t4
  let m6 ← aspis_core.field.M31.mul t28 t28
  let t29 ← aspis_core.field.M31.mul m6 self
  let t30 ← aspis_core.field.M31.mul t29 t29
  let m7 ← aspis_core.field.M31.mul t30 t30
  aspis_core.field.M31.mul m7 self

/-- [aspis_core::field::{aspis_core::field::CM31}::inv]:
    Source: 'crates/aspis-core/src/field.rs', lines 326:4-326:28
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::inv]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::inv"]
def aspis_core.field.CM31.inv
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  aspis_core.field.CM31.inv_with self (aspis_core.field.M31.inv)

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 95:4-95:40
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::reduce_u64]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::reduce_u64"]
def aspis_core.field.M31.reduce_u64
  (value : Std.U64) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.reduce_u64 value
  ok i

/-- [aspis_core::field::{aspis_core::field::CM31}::square]:
    Source: 'crates/aspis-core/src/field.rs', lines 261:4-261:31
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::square]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::square"]
def aspis_core.field.CM31.square
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i7 ← i5 + i6
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← i7 - i8
  let i10 ← i4 * i9
  let m ← aspis_core.field.M31.reduce_u64 i10
  let m1 ← aspis_core.field.M31.mul self.a self.b
  let m2 ← aspis_core.field.M31.double m1
  ok { a := m, b := m2 }

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
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← aspis_core.field.M31.reduce_u64 i10
  let m ← aspis_core.field.M31.sub m0 m1
  let m3 ← aspis_core.field.M31.sub m2 m0
  let m4 ← aspis_core.field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_core::field::{aspis_core::field::CM31}::neg]:
    Source: 'crates/aspis-core/src/field.rs', lines 233:4-233:28
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::neg]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::neg"]
def aspis_core.field.CM31.neg
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.neg self.a
  let m1 ← aspis_core.field.M31.neg self.b
  ok { a := m, b := m1 }

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

/-- [aspis_core::field::{aspis_core::field::QM31}::try_inv]:
    Source: 'crates/aspis-core/src/field.rs', lines 918:4-918:40
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::try_inv]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::try_inv"]
def aspis_core.field.QM31.try_inv
  (self : aspis_core.field.QM31) : Result (Option aspis_core.field.QM31) := do
  let b ← aspis_core.field.QM31.is_zero self
  if b
  then ok none
  else
    let c ← aspis_core.field.CM31.square self.c0
    let c1 ← aspis_core.field.CM31.square self.c1
    let c2 ← aspis_core.field.mul_by_r c1
    let norm ← aspis_core.field.CM31.sub c c2
    let inverse_norm ← aspis_core.field.CM31.inv norm
    let c3 ← aspis_core.field.CM31.mul self.c0 inverse_norm
    let c4 ← aspis_core.field.CM31.neg self.c1
    let c5 ← aspis_core.field.CM31.mul c4 inverse_norm
    ok (some { c0 := c3, c1 := c5 })

/-- [aspis_core::field::{aspis_core::field::CM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 217:4-217:39
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::add]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::add"]
def aspis_core.field.CM31.add
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.add self.a rhs.a
  let m1 ← aspis_core.field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 282:4-282:31
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::double]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::double"]
def aspis_core.field.CM31.double
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  aspis_core.field.CM31.add self self

/-- [aspis_core::field::{aspis_core::field::QM31}::square]:
    Source: 'crates/aspis-core/src/field.rs', lines 871:4-871:31
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::square]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::square"]
def aspis_core.field.QM31.square
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let c0_square ← aspis_core.field.CM31.square self.c0
  let c1_square ← aspis_core.field.CM31.square self.c1
  let c ← aspis_core.field.mul_by_r c1_square
  let c1 ← aspis_core.field.CM31.add c0_square c
  let c2 ← aspis_core.field.CM31.mul self.c0 self.c1
  let c3 ← aspis_core.field.CM31.double c2
  ok { c0 := c1, c1 := c3 }

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

/-- [aspis_core::field::{aspis_core::field::QM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 832:4-832:39
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::sub]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::sub"]
def aspis_core.field.QM31.sub
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.sub self.c0 rhs.c0
  let c1 ← aspis_core.field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 824:4-824:39
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::add]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::add"]
def aspis_core.field.QM31.add
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.add self.c0 rhs.c0
  let c1 ← aspis_core.field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::ONE]
    Source: 'crates/aspis-core/src/field.rs', lines 807:4-807:23
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ONE]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ONE"]
def aspis_core.field.QM31.ONE : aspis_core.field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::circle::secure_circle_point_from_parameter]:
    Source: 'crates/aspis-core/src/circle.rs', lines 34:0-36:48
    Name pattern: [aspis_core::circle::secure_circle_point_from_parameter]
    Visibility: public -/
@[rust_fun "aspis_core::circle::secure_circle_point_from_parameter"]
def aspis_core.circle.secure_circle_point_from_parameter
  (parameter1 : aspis_core.field.QM31) :
  Result (core.result.Result aspis_core.circle.SecureCirclePoint
    aspis_core.circle.CirclePointError)
  := do
  let square ← aspis_core.field.QM31.square parameter1
  let q ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE square
  let o ← aspis_core.field.QM31.try_inv q
  let r ←
    core.option.Option.ok_or o
      aspis_core.circle.CirclePointError.SingularParameter
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let q1 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE square
    let q2 ← aspis_core.field.QM31.mul q1 val
    let q3 ← aspis_core.field.QM31.add parameter1 parameter1
    let q4 ← aspis_core.field.QM31.mul q3 val
    ok (core.result.Result.Ok { x := q2, y := q4 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.circle.SecureCirclePoint (core.convert.FromSame
      aspis_core.circle.CirclePointError) residual

/-- [aspis_core::field::{aspis_core::field::CM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 197:4-197:24
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::CM31}::ZERO"]
def aspis_core.field.CM31.ZERO : aspis_core.field.CM31 :=
  { a := 0#u32, b := 0#u32 }

/-- [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::M31> for aspis_core::field::M31}::eq]:
    Source: 'crates/aspis-core/src/field.rs', lines 19:22-19:31
    Name pattern: [aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq"]
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : aspis_core.field.M31) (other : aspis_core.field.M31) :
  Result Bool
  := do
  ok (self = other)

/-- [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::CM31> for aspis_core::field::CM31}::eq]:
    Source: 'crates/aspis-core/src/field.rs', lines 190:22-190:31
    Name pattern: [aspis_core::field::{core::cmp::PartialEq<aspis_core::field::CM31, aspis_core::field::CM31>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::CM31, aspis_core::field::CM31>}::eq"]
def aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  (self : aspis_core.field.CM31) (other : aspis_core.field.CM31) :
  Result Bool
  := do
  let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.a other.a
  if b
  then aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.b other.b
  else ok false

/-- [aspis_core::circle::secure_ood_circle_point_from_parameter]:
    Source: 'crates/aspis-core/src/circle.rs', lines 55:0-57:48
    Name pattern: [aspis_core::circle::secure_ood_circle_point_from_parameter]
    Visibility: public -/
@[rust_fun "aspis_core::circle::secure_ood_circle_point_from_parameter"]
def aspis_core.circle.secure_ood_circle_point_from_parameter
  (parameter1 : aspis_core.field.QM31) :
  Result (core.result.Result aspis_core.circle.SecureCirclePoint
    aspis_core.circle.CirclePointError)
  := do
  let r ← aspis_core.circle.secure_circle_point_from_parameter parameter1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let b ←
      aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq parameter1.c1
        aspis_core.field.CM31.ZERO
    if b
    then
      ok (core.result.Result.Err
        aspis_core.circle.CirclePointError.ParameterInCm31Subfield)
    else ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.circle.SecureCirclePoint (core.convert.FromSame
      aspis_core.circle.CirclePointError) residual

/-- [aspis_core::circle::double_x]:
    Source: 'crates/aspis-core/src/circle.rs', lines 69:0-69:32
    Name pattern: [aspis_core::circle::double_x]
    Visibility: public -/
@[rust_fun "aspis_core::circle::double_x"]
def aspis_core.circle.double_x
  (x : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let square ← aspis_core.field.QM31.square x
  let q ← aspis_core.field.QM31.add square square
  aspis_core.field.QM31.sub q aspis_core.field.QM31.ONE


end V7Tag73CurrentHelpersOpaque
