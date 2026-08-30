import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk11

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 205:4-213:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16"]
def
  aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_16_loop.body
  (values : Array aspis_core.field.QM31 16#usize) (complement : Bool)
  (mask : Std.U16) (sum : aspis_core.field.QM31) :
  Result (ControlFlow (Std.U16 × aspis_core.field.QM31) aspis_core.field.QM31)
  := do
  if mask != 0#u16
  then
    let i ← core.num.U16.trailing_zeros mask
    let index ← lift (UScalar.cast .Usize i)
    let sum1 ←
      if complement
      then
        do
        let q ← Array.index_usize values index
        aspis_core.field.QM31.sub sum q
      else
        do
        let q ← Array.index_usize values index
        aspis_core.field.QM31.add sum q
    let i1 ← mask - 1#u16
    let mask1 ← lift (mask &&& i1)
    ok (cont (mask1, sum1))
  else ok (done sum)

/-- [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 205:4-213:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16"]
def aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_16_loop
  (values : Array aspis_core.field.QM31 16#usize) (mask : Std.U16)
  (complement : Bool) (sum : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (mask1, sum1) =>
      aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_16_loop.body
      values complement mask1 sum1)
    (mask, sum)

/-- [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 199:0-199:74
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_16"]
def aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_16
  (values : Array aspis_core.field.QM31 16#usize) (mask : Std.U16) :
  Result aspis_core.field.QM31
  := do
  let i ← core.num.U16.count_ones mask
  let (mask1, complement) ←
    if i > 8#u32
    then do
         let mask2 ← lift (~~~ mask)
         ok (mask2, true)
    else ok (mask, false)
  let sum ←
    if complement
    then ok aspis_core.field.QM31.ONE
    else ok aspis_core.field.QM31.ZERO
  aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_16_loop
    values mask1 complement sum

/-- [aspis_statement::atomic_state_only_terminal::projected_row_index]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 220:4-224:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::projected_row_index] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::projected_row_index"]
def aspis_statement.atomic_state_only_terminal.projected_row_index_loop.body
  (row : Std.Usize) (bit_mask : Std.U16)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.I32))
  (output : Std.Usize) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.I32)) × Std.Usize) Std.Usize)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepI32)
      iter
  match o with
  | none => ok (done output)
  | some bit =>
    let i ← 1#u16 <<< bit
    let i1 ← lift (bit_mask &&& i)
    if i1 != 0#u16
    then
      let i2 ← output <<< 1#i32
      let i3 ← row >>> bit
      let i4 ← lift (i3 &&& 1#usize)
      let output1 ← lift (i2 ||| i4)
      ok (cont (iter1, output1))
    else ok (cont (iter1, output))

/-- [aspis_statement::atomic_state_only_terminal::projected_row_index]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 220:4-224:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::projected_row_index] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::projected_row_index"]
def aspis_statement.atomic_state_only_terminal.projected_row_index_loop
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.I32))
  (row : Std.Usize) (bit_mask : Std.U16) (output : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, output1) =>
      aspis_statement.atomic_state_only_terminal.projected_row_index_loop.body
      row bit_mask iter1 output1)
    (iter, output)

/-- [aspis_statement::atomic_state_only_terminal::projected_row_index]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 218:0-218:58
    Name pattern: [aspis_statement::atomic_state_only_terminal::projected_row_index] -/
@[rust_fun "aspis_statement::atomic_state_only_terminal::projected_row_index"]
def aspis_statement.atomic_state_only_terminal.projected_row_index
  (row : Std.Usize) (bit_mask : Std.U16) : Result Std.Usize := do
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepI32)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepI32)
      { start := 0#i32, «end» := 10#i32 }
  aspis_statement.atomic_state_only_terminal.projected_row_index_loop iter row
    bit_mask 0#usize

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand]: loop body 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 235:12-240:13
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand"]
def
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0.body
  {N : Std.Usize} (prepared : aspis_core.field.PreparedQm31Multiplier)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (weights : Array aspis_core.field.QM31 N) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Array aspis_core.field.QM31 N)) (Array
    aspis_core.field.QM31 N))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done weights)
  | some index =>
    let parent ← Array.index_usize weights index
    let right ← aspis_core.field.PreparedQm31Multiplier.mul prepared parent
    let q ← aspis_core.field.QM31.sub parent right
    let i ← 2#usize * index
    let weights1 ← Array.update weights i q
    let i1 ← i + 1#usize
    let a ← Array.update weights1 i1 right
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand]: loop 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 235:12-240:13
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand"]
def
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (weights : Array aspis_core.field.QM31 N)
  (prepared : aspis_core.field.PreparedQm31Multiplier) :
  Result (Array aspis_core.field.QM31 N)
  := do
  loop
    (fun (iter1, weights1) =>
      aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0.body
      prepared iter1 weights1)
    (iter, weights)


end V7Tag73CurrentHelpersOpaque
