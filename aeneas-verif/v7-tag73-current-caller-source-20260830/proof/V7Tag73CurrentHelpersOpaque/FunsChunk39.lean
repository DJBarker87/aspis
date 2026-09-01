import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk38

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::external_linear_lazy]: loop body 1:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 156:8-172:9
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy"]
def aspis_statement.state_only_poseidon.external_linear_lazy_loop0_loop0.body
  (start : Std.Usize) (input : Array (Array Std.U32 4#usize) 4#usize)
  (state : Array aspis_core.field.QM31 16#usize) (output : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 16#usize) × Std.Usize)
    (Array aspis_core.field.QM31 16#usize))
  := do
  if output < 4#usize
  then
    let raw1 ←
      core.array.from_fn 4#usize
        aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        (input, output)
    let q ← aspis_statement.state_only_poseidon.extension_from_raw_limbs raw1
    let i ← start + output
    let a ← Array.update state i q
    let output1 ← output + 1#usize
    ok (cont (a, output1))
  else ok (done state)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy]: loop 1:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 156:8-172:9
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy"]
def aspis_statement.state_only_poseidon.external_linear_lazy_loop0_loop0
  (state : Array aspis_core.field.QM31 16#usize) (start : Std.Usize)
  (input : Array (Array Std.U32 4#usize) 4#usize) (output : Std.Usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (state1, output1) =>
      aspis_statement.state_only_poseidon.external_linear_lazy_loop0_loop0.body
      start input state1 output1)
    (state, output)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 146:4-174:5
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy"]
def aspis_statement.state_only_poseidon.external_linear_lazy_loop0.body
  (state : Array aspis_core.field.QM31 16#usize) (group : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 16#usize) × Std.Usize)
    (Array aspis_core.field.QM31 16#usize))
  := do
  if group < 4#usize
  then
    let start ← 4#usize * group
    let q ← Array.index_usize state start
    let i ← start + 1#usize
    let q1 ← Array.index_usize state i
    let i1 ← start + 2#usize
    let q2 ← Array.index_usize state i1
    let i2 ← start + 3#usize
    let q3 ← Array.index_usize state i2
    let input ←
      core.array.Array.map (BuiltinFnMut aspis_core.field.QM31 (Array Std.U32
        4#usize)) (Array.make 4#usize [ q, q1, q2, q3 ])
        (aspis_statement.state_only_poseidon.extension_limbs)
    let state1 ←
      aspis_statement.state_only_poseidon.external_linear_lazy_loop0_loop0
        state start input 0#usize
    let group1 ← group + 1#usize
    ok (cont (state1, group1))
  else ok (done state)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 146:4-174:5
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy"]
def aspis_statement.state_only_poseidon.external_linear_lazy_loop0
  (state : Array aspis_core.field.QM31 16#usize) (group : Std.Usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (state1, group1) =>
      aspis_statement.state_only_poseidon.external_linear_lazy_loop0.body
      state1 group1)
    (state, group)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy]: loop body 2:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 184:4-190:5
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy"]
def aspis_statement.state_only_poseidon.external_linear_lazy_loop1.body
  (sums : Array (Array Std.U64 4#usize) 4#usize)
  (state : Array aspis_core.field.QM31 16#usize) (index : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 16#usize) × Std.Usize)
    (Array aspis_core.field.QM31 16#usize))
  := do
  if index < aspis_statement.poseidon2.POSEIDON2_WIDTH
  then
    let q ← Array.index_usize state index
    let limbs ← aspis_statement.state_only_poseidon.extension_limbs q
    let a ←
      core.array.from_fn 4#usize
        aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        (limbs, sums, index)
    let q1 ← aspis_statement.state_only_poseidon.extension_from_raw_limbs a
    let a1 ← Array.update state index q1
    let index1 ← index + 1#usize
    ok (cont (a1, index1))
  else ok (done state)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy]: loop 2:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 184:4-190:5
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy"]
def aspis_statement.state_only_poseidon.external_linear_lazy_loop1
  (state : Array aspis_core.field.QM31 16#usize)
  (sums : Array (Array Std.U64 4#usize) 4#usize) (index : Std.Usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (state1, index1) =>
      aspis_statement.state_only_poseidon.external_linear_lazy_loop1.body sums
      state1 index1)
    (state, index)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 144:0-144:60
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy] -/
@[rust_fun "aspis_statement::state_only_poseidon::external_linear_lazy"]
def aspis_statement.state_only_poseidon.external_linear_lazy
  (state : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let state1 ←
    aspis_statement.state_only_poseidon.external_linear_lazy_loop0 state
      0#usize
  let sums ←
    core.array.from_fn 4#usize
      aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
      state1
  aspis_statement.state_only_poseidon.external_linear_lazy_loop1 state1 sums
    0#usize

/-- [aspis_statement::state_only_poseidon::full_round]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 336:4-338:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round] -/
@[rust_loop_body, rust_fun "aspis_statement::state_only_poseidon::full_round"]
def aspis_statement.state_only_poseidon.full_round_loop.body
  (constants1 : Array aspis_core.field.QM31 16#usize)
  (iter : core.ops.range.Range Std.Usize)
  (state : Array aspis_core.field.QM31 16#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 16#usize)) (Array aspis_core.field.QM31 16#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some lane =>
    let q ← Array.index_usize state lane
    let q1 ← Array.index_usize constants1 lane
    let q2 ← aspis_core.field.QM31.add q q1
    let q3 ← aspis_statement.state_only_poseidon.pow5 q2
    let a ← Array.update state lane q3
    ok (cont (iter1, a))


end V7Tag73CurrentHelpersOpaque
