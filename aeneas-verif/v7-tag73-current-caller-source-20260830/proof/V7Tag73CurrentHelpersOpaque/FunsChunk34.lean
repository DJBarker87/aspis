import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk33

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::internal_linear_lazy]: loop 1:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 312:8-315:9
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy"]
def aspis_statement.state_only_poseidon.internal_linear_lazy_loop0_loop0
  (part_sum : Array Std.U64 4#usize) (limbs : Array Std.U32 4#usize)
  (limb : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (part_sum1, limb1) =>
      aspis_statement.state_only_poseidon.internal_linear_lazy_loop0_loop0.body
      limbs part_sum1 limb1)
    (part_sum, limb)

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 309:4-317:5
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy"]
def aspis_statement.state_only_poseidon.internal_linear_lazy_loop0.body
  (state : Array aspis_core.field.QM31 16#usize)
  (part_sum : Array Std.U64 4#usize) (lane : Std.Usize) :
  Result (ControlFlow ((Array Std.U64 4#usize) × Std.Usize) (Array Std.U64
    4#usize))
  := do
  if lane < aspis_statement.poseidon2.POSEIDON2_WIDTH
  then
    let q ← Array.index_usize state lane
    let limbs ← aspis_statement.state_only_poseidon.extension_limbs q
    let part_sum1 ←
      aspis_statement.state_only_poseidon.internal_linear_lazy_loop0_loop0
        part_sum limbs 0#usize
    let lane1 ← lane + 1#usize
    ok (cont (part_sum1, lane1))
  else ok (done part_sum)

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 309:4-317:5
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy"]
def aspis_statement.state_only_poseidon.internal_linear_lazy_loop0
  (state : Array aspis_core.field.QM31 16#usize)
  (part_sum : Array Std.U64 4#usize) (lane : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (part_sum1, lane1) =>
      aspis_statement.state_only_poseidon.internal_linear_lazy_loop0.body state
      part_sum1 lane1)
    (part_sum, lane)

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy]: loop body 2:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 323:4-328:5
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy"]
def aspis_statement.state_only_poseidon.internal_linear_lazy_loop1.body
  (full_sum : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
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
    let limbs ← aspis_statement.state_only_poseidon.extension_limbs q
    let a ←
      core.array.from_fn 4#usize
        aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        (full_sum, limbs, lane)
    let q1 ← aspis_statement.state_only_poseidon.extension_from_raw_limbs a
    let a1 ← Array.update state lane q1
    ok (cont (iter1, a1))

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy]: loop 2:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 323:4-328:5
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy"]
def aspis_statement.state_only_poseidon.internal_linear_lazy_loop1
  (iter : core.ops.range.Range Std.Usize)
  (state : Array aspis_core.field.QM31 16#usize)
  (full_sum : Array Std.U64 4#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (iter1, state1) =>
      aspis_statement.state_only_poseidon.internal_linear_lazy_loop1.body
      full_sum iter1 state1)
    (iter, state)

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 304:0-304:60
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy] -/
@[rust_fun "aspis_statement::state_only_poseidon::internal_linear_lazy"]
def aspis_statement.state_only_poseidon.internal_linear_lazy
  (state : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let q ← Array.index_usize state 0#usize
  let old_zero ← aspis_statement.state_only_poseidon.extension_limbs q
  let part_sum := Array.repeat 4#usize 0#u64
  let part_sum1 ←
    aspis_statement.state_only_poseidon.internal_linear_lazy_loop0 state
      part_sum 1#usize
  let full_sum ←
    core.array.from_fn 4#usize
      aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      (part_sum1, old_zero)
  let a ←
    core.array.from_fn 4#usize
      aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      (part_sum1, old_zero)
  let q1 ← aspis_statement.state_only_poseidon.extension_from_raw_limbs a
  let a1 ← Array.update state 0#usize q1
  aspis_statement.state_only_poseidon.internal_linear_lazy_loop1
    { start := 1#usize, «end» := aspis_statement.poseidon2.POSEIDON2_WIDTH }
    a1 full_sum

/-- [aspis_statement::state_only_poseidon::pow5]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 124:0-124:28
    Name pattern: [aspis_statement::state_only_poseidon::pow5] -/
@[rust_fun "aspis_statement::state_only_poseidon::pow5"]
def aspis_statement.state_only_poseidon.pow5
  (value : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let square ← aspis_core.field.QM31.square value
  let q ← aspis_core.field.QM31.square square
  aspis_core.field.QM31.mul q value

/-- [aspis_statement::state_only_poseidon::internal_round]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 383:0-383:83
    Name pattern: [aspis_statement::state_only_poseidon::internal_round] -/
@[rust_fun "aspis_statement::state_only_poseidon::internal_round"]
def aspis_statement.state_only_poseidon.internal_round
  (state : Array aspis_core.field.QM31 16#usize)
  (constant1 : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let q ← Array.index_usize state 0#usize
  let q1 ← aspis_core.field.QM31.add q constant1
  let q2 ← aspis_statement.state_only_poseidon.pow5 q1
  let state1 ← Array.update state 0#usize q2
  aspis_statement.state_only_poseidon.internal_linear_lazy state1


end V7Tag73CurrentHelpersOpaque
