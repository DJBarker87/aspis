import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk16

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 566:4-572:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot"]
def aspis_statement.atomic_state_only_terminal.atomic_pattern_masked_dot_loop
  (routing : Slice aspis_core.field.QM31)
  (pattern_values : Array aspis_core.field.QM31 15#usize) (support : Std.U16)
  (selected_routing : Array aspis_core.field.QM31 15#usize)
  (selected_patterns : Array aspis_core.field.QM31 15#usize)
  (selected : Std.Usize) :
  Result ((Array aspis_core.field.QM31 15#usize) × (Array
    aspis_core.field.QM31 15#usize) × Std.Usize)
  := do
  loop
    (fun (support1, selected_routing1, selected_patterns1, selected1) =>
      aspis_statement.atomic_state_only_terminal.atomic_pattern_masked_dot_loop.body
      routing pattern_values support1 selected_routing1 selected_patterns1
      selected1)
    (support, selected_routing, selected_patterns, selected)

/-- [aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 557:0-561:9
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot"]
def aspis_statement.atomic_state_only_terminal.atomic_pattern_masked_dot
  (routing : Slice aspis_core.field.QM31)
  (pattern_values : Array aspis_core.field.QM31 15#usize) (support : Std.U16) :
  Result aspis_core.field.QM31
  := do
  let i := Slice.len routing
  massert (i >=
    aspis_statement.atomic_state_only_terminal.ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS)
  let selected_routing := Array.repeat 15#usize aspis_core.field.QM31.ZERO
  let selected_patterns := Array.repeat 15#usize aspis_core.field.QM31.ZERO
  let (selected_routing1, selected_patterns1, selected) ←
    aspis_statement.atomic_state_only_terminal.atomic_pattern_masked_dot_loop
      routing pattern_values support selected_routing selected_patterns 0#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      selected_routing1 { «end» := selected }
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      selected_patterns1 { «end» := selected }
  aspis_core.field.qm31_dot s s1

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form::MAX_PRODUCT_COEFFICIENT_SUM]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 590:4-590:42
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form::MAX_PRODUCT_COEFFICIENT_SUM] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::routing_linear_form::MAX_PRODUCT_COEFFICIENT_SUM"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form.MAX_PRODUCT_COEFFICIENT_SUM
  : Result Std.U64 := do
  let i ← Aeneas.Std.lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← i - 1#u64
  core.num.U64.MAX / i1

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop body 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 631:8-633:9
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop0.body
  (products : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (reduced_products : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done reduced_products)
  | some limb =>
    let i ← Array.index_usize products limb
    let m ← aspis_core.field.M31.reduce_u64 i
    let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from m)
    let i2 ← Array.index_usize reduced_products limb
    let i3 ← i2 + i1
    let a ← Array.update reduced_products limb i3
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 631:8-633:9
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (products : Array Std.U64 4#usize)
  (reduced_products : Array Std.U64 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, reduced_products1) =>
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop0.body
      products iter1 reduced_products1)
    (iter, reduced_products)

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop body 2:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 601:16-603:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop1.body
  (limbs : Array Std.U32 4#usize) (iter : core.ops.range.Range Std.Usize)
  (signed : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done signed)
  | some limb =>
    let i ← Array.index_usize limbs limb
    let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i)
    let i2 ← Array.index_usize signed limb
    let i3 ← i2 + i1
    let a ← Array.update signed limb i3
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop 2:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 601:16-603:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop1
  (iter : core.ops.range.Range Std.Usize) (signed : Array Std.U64 4#usize)
  (limbs : Array Std.U32 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, signed1) =>
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop1.body
      limbs iter1 signed1)
    (iter, signed)

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop body 3:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 606:16-608:17
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def
  aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0_loop2.body
  (limbs : Array Std.U32 4#usize) (iter : core.ops.range.Range Std.Usize)
  (signed : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done signed)
  | some limb =>
    let i ← Aeneas.Std.lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i1 ← Array.index_usize limbs limb
    let i2 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i1)
    let i3 ← i - i2
    let i4 ← Array.index_usize signed limb
    let i5 ← i4 + i3
    let a ← Array.update signed limb i5
    ok (cont (iter1, a))


end V7Tag73CurrentHelpersOpaque
