import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk36

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::external_local_packed_raw]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 217:0-217:58
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw] -/
@[rust_fun "aspis_statement::state_only_poseidon::external_local_packed_raw"]
def aspis_statement.state_only_poseidon.external_local_packed_raw
  (input : Array aspis_core.field.QM31 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  let input1 ←
    core.array.Array.map (BuiltinFnMut aspis_core.field.QM31 (Array Std.U32
      4#usize)) input (aspis_statement.state_only_poseidon.extension_limbs)
  let local1 ←
    core.array.from_fn 4#usize
      aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
      input1
  let all_local_limbs_bounded ←
    aspis_statement.state_only_poseidon.external_local_packed_raw_loop0 local1
      true 0#usize
  massert all_local_limbs_bounded
  let bound ←
    aspis_statement.state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  let a ← Array.index_usize local1 0#usize
  let i ← Array.index_usize a 0#usize
  let i1 ← 5#u64 * bound
  let i2 ← i + i1
  let a1 ← Array.index_usize local1 1#usize
  let i3 ← Array.index_usize a1 1#usize
  let i4 ← i2 - i3
  let a2 ← Array.index_usize local1 2#usize
  let i5 ← Array.index_usize a2 2#usize
  let i6 ← 2#u64 * i5
  let i7 ← i4 + i6
  let i8 ← Array.index_usize a2 3#usize
  let i9 ← i7 - i8
  let a3 ← Array.index_usize local1 3#usize
  let i10 ← Array.index_usize a3 2#usize
  let i11 ← i9 - i10
  let i12 ← Array.index_usize a3 3#usize
  let i13 ← 2#u64 * i12
  let i14 ← i11 - i13
  let i15 ← Array.index_usize a 1#usize
  let i16 ← Array.index_usize a1 0#usize
  let i17 ← i15 + i16
  let i18 ← Array.index_usize a2 2#usize
  let i19 ← i17 + i18
  let i20 ← Array.index_usize a2 3#usize
  let i21 ← 2#u64 * i20
  let i22 ← i19 + i21
  let i23 ← Array.index_usize a3 2#usize
  let i24 ← 2#u64 * i23
  let i25 ← i22 + i24
  let i26 ← i25 + bound
  let i27 ← Array.index_usize a3 3#usize
  let i28 ← i26 - i27
  let i29 ← Array.index_usize a 2#usize
  let i30 ← 2#u64 * bound
  let i31 ← i29 + i30
  let i32 ← Array.index_usize a1 3#usize
  let i33 ← i31 - i32
  let i34 ← Array.index_usize a2 0#usize
  let i35 ← i33 + i34
  let i36 ← Array.index_usize a3 1#usize
  let i37 ← i35 - i36
  let i38 ← Array.index_usize a 3#usize
  let i39 ← Array.index_usize a1 2#usize
  let i40 ← i38 + i39
  let i41 ← Array.index_usize a2 1#usize
  let i42 ← i40 + i41
  let i43 ← Array.index_usize a3 0#usize
  let i44 ← i42 + i43
  let i45 ←
    Array.index_usize (Array.make 4#usize [ i14, i28, i37, i44 ]) 0#usize
  let i46 ← 8#u64 * bound
  massert (i45 < i46)
  let i47 ←
    Array.index_usize (Array.make 4#usize [ i14, i28, i37, i44 ]) 1#usize
  massert (i47 < i46)
  let i48 ←
    Array.index_usize (Array.make 4#usize [ i14, i28, i37, i44 ]) 2#usize
  let i49 ← 4#u64 * bound
  massert (i48 < i49)
  let i50 ←
    Array.index_usize (Array.make 4#usize [ i14, i28, i37, i44 ]) 3#usize
  massert (i50 < i49)
  ok (Array.make 4#usize [ i14, i28, i37, i44 ])

/-- [aspis_statement::state_only_poseidon::external_local_packed]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 265:0-265:50
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed] -/
@[rust_fun "aspis_statement::state_only_poseidon::external_local_packed"]
def aspis_statement.state_only_poseidon.external_local_packed
  (input : Array aspis_core.field.QM31 4#usize) :
  Result aspis_core.field.QM31
  := do
  let a ← aspis_statement.state_only_poseidon.external_local_packed_raw input
  aspis_statement.state_only_poseidon.extension_from_raw_limbs a

/-- [aspis_statement::state_only_poseidon::external_linear_packed]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 284:4-294:5
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_packed] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_packed"]
def aspis_statement.state_only_poseidon.external_linear_packed_loop.body
  (state : Array aspis_core.field.QM31 16#usize)
  (local_packed : Array aspis_core.field.QM31 4#usize) (group : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 4#usize) × Std.Usize)
    (Array aspis_core.field.QM31 4#usize))
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
    let q4 ←
      aspis_statement.state_only_poseidon.external_local_packed
        (Array.make 4#usize [ q, q1, q2, q3 ])
    let a ← Array.update local_packed group q4
    let group1 ← group + 1#usize
    ok (cont (a, group1))
  else ok (done local_packed)

/-- [aspis_statement::state_only_poseidon::external_linear_packed]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 284:4-294:5
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_packed] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::external_linear_packed"]
def aspis_statement.state_only_poseidon.external_linear_packed_loop
  (state : Array aspis_core.field.QM31 16#usize)
  (local_packed : Array aspis_core.field.QM31 4#usize) (group : Std.Usize) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  loop
    (fun (local_packed1, group1) =>
      aspis_statement.state_only_poseidon.external_linear_packed_loop.body
      state local_packed1 group1)
    (local_packed, group)

/-- [aspis_statement::state_only_poseidon::external_linear_packed]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 281:0-281:70
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_packed] -/
@[rust_fun "aspis_statement::state_only_poseidon::external_linear_packed"]
def aspis_statement.state_only_poseidon.external_linear_packed
  (state : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let local_packed := Array.repeat 4#usize aspis_core.field.QM31.ZERO
  let local_packed1 ←
    aspis_statement.state_only_poseidon.external_linear_packed_loop state
      local_packed 0#usize
  let q ← Array.index_usize local_packed1 0#usize
  let q1 ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO q
  let q2 ← Array.index_usize local_packed1 1#usize
  let q3 ← aspis_core.field.QM31.add q1 q2
  let q4 ← Array.index_usize local_packed1 2#usize
  let q5 ← aspis_core.field.QM31.add q3 q4
  let q6 ← Array.index_usize local_packed1 3#usize
  let sum ← aspis_core.field.QM31.add q5 q6
  core.array.Array.map
    aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
    local_packed1 sum

/-- [aspis_statement::state_only_poseidon::full_round_packed]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 364:4-366:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round_packed] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::full_round_packed"]
def aspis_statement.state_only_poseidon.full_round_packed_loop.body
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

/-- [aspis_statement::state_only_poseidon::full_round_packed]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 364:4-366:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round_packed] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::full_round_packed"]
def aspis_statement.state_only_poseidon.full_round_packed_loop
  (iter : core.ops.range.Range Std.Usize)
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (iter1, state1) =>
      aspis_statement.state_only_poseidon.full_round_packed_loop.body
      constants1 iter1 state1)
    (iter, state)

/-- [aspis_statement::state_only_poseidon::full_round_packed]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 360:0-363:45
    Name pattern: [aspis_statement::state_only_poseidon::full_round_packed] -/
@[rust_fun "aspis_statement::state_only_poseidon::full_round_packed"]
def aspis_statement.state_only_poseidon.full_round_packed
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let state1 ←
    aspis_statement.state_only_poseidon.full_round_packed_loop
      { start := 0#usize, «end» := aspis_statement.poseidon2.POSEIDON2_WIDTH
      } state constants1
  aspis_statement.state_only_poseidon.external_linear_packed state1


end V7Tag73CurrentHelpersOpaque
