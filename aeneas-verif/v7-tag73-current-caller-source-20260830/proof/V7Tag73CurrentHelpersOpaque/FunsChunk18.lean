import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk17

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop 3:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 606:16-608:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop2
  (iter : core.ops.range.Range Std.Usize) (signed : Array Std.U64 4#usize)
  (limbs : Array Std.U32 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, signed1) =>
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop2.body
      limbs iter1 signed1)
    (iter, signed)

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop body 5:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 623:16-625:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3_loop0.body
  (limbs : Array Std.U32 4#usize) (coefficient : Std.U64)
  (iter : core.ops.range.Range Std.Usize) (products : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done products)
  | some limb =>
    let i ← Array.index_usize limbs limb
    let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i)
    let i2 ← i1 * coefficient
    let i3 ← Array.index_usize products limb
    let i4 ← i3 + i2
    let a ← Array.update products limb i4
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop 5:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 623:16-625:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3_loop0
  (iter : core.ops.range.Range Std.Usize) (products : Array Std.U64 4#usize)
  (limbs : Array Std.U32 4#usize) (coefficient : Std.U64) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, products1) =>
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3_loop0.body
      limbs coefficient iter1 products1)
    (iter, products)

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop body 4:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 591:4-629:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3.body
  (products : Array Std.U64 4#usize) (limbs : Array Std.U32 4#usize)
  (coefficient : Std.U64) (iter : core.ops.range.Range Std.Usize)
  (reduced_products : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) ((Array Std.U64 4#usize) × (Array Std.U64 4#usize) × Std.U64))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let products1 := Array.repeat 4#usize 0#u64
    let products2 ←
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3_loop0
        { start := 0#usize, «end» := 4#usize } products1 limbs coefficient
    let product_coefficient_sum ← 0#u64 + coefficient
    ok (done (products2, reduced_products, product_coefficient_sum))
  | some limb =>
    let i ← Array.index_usize products limb
    let m ← aspis_core.field.M31.reduce_u64 i
    let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from m)
    let i2 ← Array.index_usize reduced_products limb
    let i3 ← i2 + i1
    let a ← Array.update reduced_products limb i3
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop 4:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 591:4-629:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3
  (iter : core.ops.range.Range Std.Usize) (products : Array Std.U64 4#usize)
  (reduced_products : Array Std.U64 4#usize) (limbs : Array Std.U32 4#usize)
  (coefficient : Std.U64) :
  Result ((Array Std.U64 4#usize) × (Array Std.U64 4#usize) × Std.U64)
  := do
  loop
    (fun (iter1, reduced_products1) =>
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3.body
      products limbs coefficient iter1 reduced_products1)
    (iter, reduced_products)

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop body 6:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 623:16-625:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop4.body
  (limbs : Array Std.U32 4#usize) (coefficient : Std.U64)
  (iter : core.ops.range.Range Std.Usize) (products : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done products)
  | some limb =>
    let i ← Array.index_usize limbs limb
    let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i)
    let i2 ← i1 * coefficient
    let i3 ← Array.index_usize products limb
    let i4 ← i3 + i2
    let a ← Array.update products limb i4
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop 6:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 623:16-625:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop4
  (iter : core.ops.range.Range Std.Usize) (products : Array Std.U64 4#usize)
  (limbs : Array Std.U32 4#usize) (coefficient : Std.U64) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, products1) =>
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop4.body
      limbs coefficient iter1 products1)
    (iter, products)

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 591:4-645:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0.body
  (selectors : Slice aspis_core.field.QM31)
  (iter : core.slice.iter.Iter (Std.U8 × Std.U32))
  (signed : Array Std.U64 4#usize) (products : Array Std.U64 4#usize)
  (reduced_products : Array Std.U64 4#usize)
  (product_coefficient_sum : Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter (Std.U8 × Std.U32)) × (Array
    Std.U64 4#usize) × (Array Std.U64 4#usize) × (Array Std.U64 4#usize) ×
    Std.U64) (aspis_core.field.CM31 × aspis_core.field.CM31))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none =>
    if product_coefficient_sum != 0#u64
    then
      let reduced_products1 ←
        aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop0
          { start := 0#usize, «end» := 4#usize } products reduced_products
      let i ← Array.index_usize signed 0#usize
      let i1 ← Array.index_usize reduced_products1 0#usize
      let i2 ← i + i1
      let m ← aspis_core.field.M31.reduce_u64 i2
      let i3 ← Array.index_usize signed 1#usize
      let i4 ← Array.index_usize reduced_products1 1#usize
      let i5 ← i3 + i4
      let m1 ← aspis_core.field.M31.reduce_u64 i5
      let c ← aspis_core.field.CM31.new m m1
      let i6 ← Array.index_usize signed 2#usize
      let i7 ← Array.index_usize reduced_products1 2#usize
      let i8 ← i6 + i7
      let m2 ← aspis_core.field.M31.reduce_u64 i8
      let i9 ← Array.index_usize signed 3#usize
      let i10 ← Array.index_usize reduced_products1 3#usize
      let i11 ← i9 + i10
      let m3 ← aspis_core.field.M31.reduce_u64 i11
      let c1 ← aspis_core.field.CM31.new m2 m3
      ok (done (c, c1))
    else
      let i ← Array.index_usize signed 0#usize
      let i1 ← Array.index_usize reduced_products 0#usize
      let i2 ← i + i1
      let m ← aspis_core.field.M31.reduce_u64 i2
      let i3 ← Array.index_usize signed 1#usize
      let i4 ← Array.index_usize reduced_products 1#usize
      let i5 ← i3 + i4
      let m1 ← aspis_core.field.M31.reduce_u64 i5
      let c ← aspis_core.field.CM31.new m m1
      let i6 ← Array.index_usize signed 2#usize
      let i7 ← Array.index_usize reduced_products 2#usize
      let i8 ← i6 + i7
      let m2 ← aspis_core.field.M31.reduce_u64 i8
      let i9 ← Array.index_usize signed 3#usize
      let i10 ← Array.index_usize reduced_products 3#usize
      let i11 ← i9 + i10
      let m3 ← aspis_core.field.M31.reduce_u64 i11
      let c1 ← aspis_core.field.CM31.new m2 m3
      ok (done (c, c1))
  | some p =>
    let (index, coefficient) := p
    let i ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from index)
    let selector ← Slice.index_usize selectors i
    let i1 := selector.c0.a
    let i2 := selector.c0.b
    let i3 := selector.c1.a
    let i4 := selector.c1.b
    match coefficient with
    | 1#uscalar =>
      let signed1 ←
        aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop1
          { start := 0#usize, «end» := 4#usize } signed
          (Array.make 4#usize [ i1, i2, i3, i4 ])
      ok (cont (iter1, signed1, products, reduced_products,
        product_coefficient_sum))
    | _ =>
      let i5 ← aspis_core.field.P - 1#u32
      if coefficient = i5
      then
        let signed1 ←
          aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop2
            { start := 0#usize, «end» := 4#usize } signed
            (Array.make 4#usize [ i1, i2, i3, i4 ])
        ok (cont (iter1, signed1, products, reduced_products,
          product_coefficient_sum))
      else
        let coefficient1 ←
          Aeneas.Std.lift (core.convert.num.FromU64U32.from coefficient)
        let i6 ←
          aspis_statement.atomic_state_only_terminal.routing_linear_form.MAX_PRODUCT_COEFFICIENT_SUM
        let i7 ← i6 - coefficient1
        if product_coefficient_sum > i7
        then
          let (products1, reduced_products1, product_coefficient_sum1) ←
            aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop3
              { start := 0#usize, «end» := 4#usize } products
              reduced_products (Array.make 4#usize [ i1, i2, i3, i4 ])
              coefficient1
          ok (cont (iter1, signed, products1, reduced_products1,
            product_coefficient_sum1))
        else
          let products1 ←
            aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop4
              { start := 0#usize, «end» := 4#usize } products
              (Array.make 4#usize [ i1, i2, i3, i4 ]) coefficient1
          let product_coefficient_sum1 ←
            product_coefficient_sum + coefficient1
          ok (cont (iter1, signed, products1, reduced_products,
            product_coefficient_sum1))


end V7Tag73CurrentHelpersOpaque
