import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk09

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 207:0-212:53
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings]
    Visibility: public -/
@[rust_fun "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings"]
def aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (queries : Array Std.U32 16#usize)
  (powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers) :
  Result (core.result.Result (Array (Array aspis_core.field.QM31 4#usize)
    16#usize) aspis_core.v6_onefold.V6WireError)
  := do
  let order ←
    core.array.from_fn 16#usize
      aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnMutTupleUsizePairU32Usize
      queries
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut order)
  let s1 ←
    core.slice.Slice.sort_unstable_by_key
      aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
      core.cmp.OrdU32 s ()
  let order1 := to_slice_mut_back s1
  let i ← aspis_core.v6_onefold.V6_QUERY_COUNT - 1#usize
  let (i1, _) ← Array.index_usize order1 i
  let i2 ← 1#u32 <<< 18#i32
  if i1 >= i2
  then
    ok (core.result.Result.Err
      aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule)
  else
    let s2 ← lift (Array.to_slice order1)
    let w ← core.slice.Slice.windows s2 2#usize
    let (b, _) ←
      core.iter.traits.iterator.Iterator.any.default
        (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
        (Std.U32 × Std.Usize))
        aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool
        w ()
    if b
    then
      ok (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule)
    else
      let a := Array.repeat 4#usize aspis_core.field.QM31.ZERO
      let combined := Array.repeat 16#usize a
      let entries :=
        alloc.vec.Vec.with_capacity (Std.U32 × (Array Std.U8 26#usize) ×
          (Array Std.U8 26#usize)) aspis_core.v6_onefold.V6_QUERY_COUNT
      let iter ←
        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter order1
      aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings_loop wire iter
        hash powers combined entries

/-- [aspis_statement::atomic_state_only_terminal::TRACE_ROWS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 28:0-28:23
    Name pattern: [aspis_statement::atomic_state_only_terminal::TRACE_ROWS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::TRACE_ROWS"]
def aspis_statement.atomic_state_only_terminal.TRACE_ROWS : Std.Usize :=
  1024#usize

/-- [aspis_statement::atomic_state_only_terminal::C1_COLUMNS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 29:0-29:23
    Name pattern: [aspis_statement::atomic_state_only_terminal::C1_COLUMNS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::C1_COLUMNS"]
def aspis_statement.atomic_state_only_terminal.C1_COLUMNS : Std.Usize :=
  16#usize

/-- [aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_TERMINAL_COLUMNS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 33:0-33:45
    Name pattern: [aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_TERMINAL_COLUMNS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_TERMINAL_COLUMNS"]
def aspis_statement.atomic_state_only_terminal.ATOMIC_SELECTED_TERMINAL_COLUMNS
  : Result Std.Usize := do
  let i ←
    aspis_statement.atomic_state_only_terminal.C1_COLUMNS +
      aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  i + 2#usize

/-- [aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_H1_COLUMN]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 36:0-36:38
    Name pattern: [aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_H1_COLUMN] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_H1_COLUMN"]
def aspis_statement.atomic_state_only_terminal.ATOMIC_SELECTED_H1_COLUMN
  : Result Std.Usize :=
  aspis_statement.atomic_state_only_terminal.C1_COLUMNS +
    aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS

/-- [aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_G_COLUMN]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 37:0-37:37
    Name pattern: [aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_G_COLUMN] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::ATOMIC_SELECTED_G_COLUMN"]
def aspis_statement.atomic_state_only_terminal.ATOMIC_SELECTED_G_COLUMN
  : Result Std.Usize := do
  let i ←
    aspis_statement.atomic_state_only_terminal.ATOMIC_SELECTED_H1_COLUMN
  i + 1#usize

/-- [aspis_statement::atomic_state_only_terminal::ATOMIC_RETAINED_INITIAL_BLOCK_INDICES]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 38:0-38:55
    Name pattern: [aspis_statement::atomic_state_only_terminal::ATOMIC_RETAINED_INITIAL_BLOCK_INDICES] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::ATOMIC_RETAINED_INITIAL_BLOCK_INDICES"]
def
  aspis_statement.atomic_state_only_terminal.ATOMIC_RETAINED_INITIAL_BLOCK_INDICES
  : Array Std.Usize 4#usize :=
  Array.make 4#usize [ 0#usize, 1#usize, 22#usize, 23#usize ]

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_PATTERNS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 23:0-23:66
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_PATTERNS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_PATTERNS"]
def aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_PATTERNS
  :
  Array aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern
    15#usize
  :=
  staged_atomic_patterns.patterns

end V7Tag73CurrentHelpersOpaque
