import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk40

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::full_round_m31_constants]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 351:4-354:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round_m31_constants] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::full_round_m31_constants"]
def aspis_statement.state_only_poseidon.full_round_m31_constants_loop.body
  (constants1 : Array Std.U32 16#usize) (iter : core.ops.range.Range Std.Usize)
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
    let i ← Array.index_usize constants1 lane
    let m ← aspis_core.field.M31.add q.c0.a i
    let (q1, index_mut_back) ← Array.index_mut_usize state lane
    let state1 := index_mut_back { q1 with c0 := { q1.c0 with a := m } }
    let q2 ← Array.index_usize state1 lane
    let q3 ← aspis_statement.state_only_poseidon.pow5 q2
    let a ← Array.update state1 lane q3
    ok (cont (iter1, a))

/-- [aspis_statement::state_only_poseidon::full_round_m31_constants]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 351:4-354:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round_m31_constants] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::full_round_m31_constants"]
def aspis_statement.state_only_poseidon.full_round_m31_constants_loop
  (iter : core.ops.range.Range Std.Usize)
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (iter1, state1) =>
      aspis_statement.state_only_poseidon.full_round_m31_constants_loop.body
      constants1 iter1 state1)
    (iter, state)

/-- [aspis_statement::state_only_poseidon::full_round_m31_constants]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 347:0-350:28
    Name pattern: [aspis_statement::state_only_poseidon::full_round_m31_constants] -/
@[rust_fun "aspis_statement::state_only_poseidon::full_round_m31_constants"]
def aspis_statement.state_only_poseidon.full_round_m31_constants
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let state1 ←
    aspis_statement.state_only_poseidon.full_round_m31_constants_loop
      { start := 0#usize, «end» := aspis_statement.poseidon2.POSEIDON2_WIDTH
      } state constants1
  aspis_statement.state_only_poseidon.external_linear_lazy state1

/-- [aspis_statement::poseidon2::RATE]
    Source: 'crates/aspis-statement/src/poseidon2.rs', lines 57:0-57:21
    Name pattern: [aspis_statement::poseidon2::RATE]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_statement::poseidon2::RATE"]
def aspis_statement.poseidon2.RATE : Std.Usize := 8#usize

/-- [aspis_statement::state_only_poseidon::leading_pair_packed]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 405:4-407:5
    Name pattern: [aspis_statement::state_only_poseidon::leading_pair_packed] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::leading_pair_packed"]
def aspis_statement.state_only_poseidon.leading_pair_packed_loop.body
  (a : Array aspis_core.field.QM31 16#usize)
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
    let q1 ← Array.index_usize a lane
    let q2 ← aspis_core.field.QM31.add q q1
    let a1 ← Array.update state lane q2
    ok (cont (iter1, a1))

/-- [aspis_statement::state_only_poseidon::leading_pair_packed]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 405:4-407:5
    Name pattern: [aspis_statement::state_only_poseidon::leading_pair_packed] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::leading_pair_packed"]
def aspis_statement.state_only_poseidon.leading_pair_packed_loop
  (iter : core.ops.range.Range Std.Usize)
  (a : Array aspis_core.field.QM31 16#usize)
  (state : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (iter1, state1) =>
      aspis_statement.state_only_poseidon.leading_pair_packed_loop.body a iter1
      state1)
    (iter, state)

/-- [aspis_statement::state_only_poseidon::leading_pair_packed]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 401:0-403:45
    Name pattern: [aspis_statement::state_only_poseidon::leading_pair_packed] -/
@[rust_fun "aspis_statement::state_only_poseidon::leading_pair_packed"]
def aspis_statement.state_only_poseidon.leading_pair_packed
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let state ←
    aspis_statement.state_only_poseidon.leading_pair_packed_loop
      { start := 0#usize, «end» := aspis_statement.poseidon2.RATE }
      openings.xor12_z openings.z
  let state1 ← aspis_statement.state_only_poseidon.external_linear_lazy state
  let a ←
    Array.index_usize aspis_statement.poseidon2.EXTERNAL_INITIAL 0#usize
  let a1 ←
    aspis_statement.state_only_poseidon.full_round_m31_constants state1 a
  let a2 ←
    Array.index_usize aspis_statement.poseidon2.EXTERNAL_INITIAL 1#usize
  aspis_statement.state_only_poseidon.full_round_m31_constants_packed a1 a2

/-- [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 585:0-588:45
    Name pattern: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected]
    Visibility: public -/
@[rust_fun
  "aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors)
  :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let leading_low ← Array.index_usize selectors.«local» 0#usize
  let ii ←
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      (Array.make 3#usize [ 1#usize, 9#usize, 10#usize ])
  let full_low ←
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
      aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
      ii aspis_core.field.QM31.ZERO selectors
  let ri ← core.ops.range.RangeInclusive.new 2#usize 8#usize
  let internal_low ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold
      core.iter.range.StepUsize
      aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
      ri aspis_core.field.QM31.ZERO selectors
  let leading ←
    aspis_statement.state_only_poseidon.leading_pair_packed openings
  let full ←
    aspis_statement.state_only_poseidon.interpolated_full_pair_packed
      openings.z selectors.«local»
  let internal ←
    aspis_statement.state_only_poseidon.interpolated_internal_pair openings.z
      selectors.«local»
  let prepared_weights ←
    core.array.Array.map (BuiltinFnMut aspis_core.field.QM31
      aspis_core.field.PreparedQm31Multiplier)
      (Array.make 3#usize [ leading_low, full_low, internal_low ])
      (aspis_core.field.PreparedQm31Multiplier.new)
  let prepared_block ←
    aspis_core.field.PreparedQm31Multiplier.new selectors.block
  core.array.from_fn 4#usize
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    (openings, internal, prepared_block, prepared_weights, leading, full)


end V7Tag73CurrentHelpersOpaque
