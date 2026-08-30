import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk19

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_DESTINATIONS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 49:0-49:59
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_DESTINATIONS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_DESTINATIONS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_DESTINATIONS
  : Array Std.U8 74#usize :=
  Array.make 74#usize [
    0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 3#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 2#u8, 2#u8, 3#u8, 3#u8, 3#u8, 5#u8, 5#u8, 5#u8, 7#u8, 8#u8,
    9#u8, 10#u8, 13#u8, 28#u8, 38#u8, 13#u8, 38#u8, 15#u8, 32#u8, 45#u8, 15#u8,
    32#u8, 17#u8, 17#u8, 17#u8, 20#u8, 18#u8, 18#u8, 18#u8, 22#u8, 37#u8,
    56#u8, 28#u8, 34#u8, 34#u8, 34#u8, 36#u8, 34#u8, 36#u8, 34#u8, 35#u8,
    35#u8, 35#u8, 35#u8, 35#u8, 35#u8, 36#u8, 39#u8, 40#u8, 45#u8, 46#u8,
    48#u8, 50#u8, 51#u8, 62#u8, 51#u8, 52#u8, 52#u8, 55#u8, 62#u8
    ]

/-- [aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 771:4-776:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations"]
def
  aspis_statement.atomic_state_only_terminal.add_atomic_copy_routing_destinations_loop.body
  (product : aspis_core.field.QM31) (destinations : Array Std.U8 74#usize)
  (destination_end : Std.Usize)
  (matrices : alloc.vec.Vec aspis_core.field.QM31)
  (destination_index : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.QM31))
  := do
  if destination_index < destination_end
  then
    let i ← Array.index_usize destinations destination_index
    let matrix_index ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from i)
    let q ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.QM31) matrices matrix_index
    let updated ← aspis_core.field.QM31.add q product
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.QM31) matrices matrix_index
    let matrices1 := index_mut_back updated
    let destination_index1 ← destination_index + 1#usize
    ok (cont (matrices1, destination_index1))
  else ok (done matrices)

/-- [aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 771:4-776:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations"]
def
  aspis_statement.atomic_state_only_terminal.add_atomic_copy_routing_destinations_loop
  (matrices : alloc.vec.Vec aspis_core.field.QM31)
  (product : aspis_core.field.QM31) (destinations : Array Std.U8 74#usize)
  (destination_index : Std.Usize) (destination_end : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  loop
    (fun (matrices1, destination_index1) =>
      aspis_statement.atomic_state_only_terminal.add_atomic_copy_routing_destinations_loop.body
      product destinations destination_end matrices1 destination_index1)
    (matrices, destination_index)

/-- [aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 762:0-767:14
    Name pattern: [aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::add_atomic_copy_routing_destinations"]
def
  aspis_statement.atomic_state_only_terminal.add_atomic_copy_routing_destinations
  (matrices : alloc.vec.Vec aspis_core.field.QM31)
  (product : aspis_core.field.QM31) (start : Std.Usize) (len : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  let destination_end ← start + len
  aspis_statement.atomic_state_only_terminal.add_atomic_copy_routing_destinations_loop
    matrices product
    aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_DESTINATIONS
    start destination_end

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_PAIR_TERMS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 48:0-48:72
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_PAIR_TERMS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_PAIR_TERMS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_PAIR_TERMS
  : Array (Std.U8 × Std.U8 × Std.U16 × Std.U8) 61#usize :=
  Array.make 61#usize [
    (0#u8, 0#u8, 0#u16, 1#u8), (1#u8, 1#u8, 1#u16, 1#u8), (2#u8, 2#u8, 2#u16,
    1#u8), (3#u8, 3#u8, 3#u16, 1#u8), (4#u8, 4#u8, 4#u16, 1#u8), (5#u8, 5#u8,
    5#u16, 2#u8), (6#u8, 0#u8, 7#u16, 1#u8), (7#u8, 6#u8, 8#u16, 1#u8), (8#u8,
    7#u8, 9#u16, 1#u8), (9#u8, 3#u8, 10#u16, 1#u8), (10#u8, 8#u8, 11#u16,
    1#u8), (11#u8, 4#u8, 12#u16, 1#u8), (12#u8, 9#u8, 13#u16, 1#u8), (13#u8,
    4#u8, 14#u16, 1#u8), (14#u8, 10#u8, 15#u16, 1#u8), (15#u8, 11#u8, 16#u16,
    1#u8), (16#u8, 3#u8, 17#u16, 1#u8), (14#u8, 12#u8, 18#u16, 1#u8), (17#u8,
    10#u8, 19#u16, 1#u8), (18#u8, 3#u8, 20#u16, 1#u8), (19#u8, 4#u8, 21#u16,
    1#u8), (20#u8, 3#u8, 22#u16, 1#u8), (21#u8, 3#u8, 23#u16, 1#u8), (22#u8,
    3#u8, 24#u16, 1#u8), (23#u8, 0#u8, 25#u16, 1#u8), (24#u8, 0#u8, 26#u16,
    3#u8), (25#u8, 3#u8, 29#u16, 2#u8), (26#u8, 0#u8, 31#u16, 3#u8), (27#u8,
    3#u8, 34#u16, 2#u8), (28#u8, 0#u8, 36#u16, 1#u8), (29#u8, 3#u8, 37#u16,
    1#u8), (30#u8, 10#u8, 38#u16, 2#u8), (31#u8, 0#u8, 40#u16, 1#u8), (32#u8,
    3#u8, 41#u16, 1#u8), (33#u8, 10#u8, 42#u16, 1#u8), (34#u8, 3#u8, 43#u16,
    3#u8), (35#u8, 3#u8, 46#u16, 1#u8), (36#u8, 13#u8, 47#u16, 1#u8), (37#u8,
    0#u8, 48#u16, 1#u8), (38#u8, 14#u8, 49#u16, 2#u8), (39#u8, 4#u8, 51#u16,
    2#u8), (40#u8, 3#u8, 53#u16, 1#u8), (41#u8, 15#u8, 54#u16, 1#u8), (42#u8,
    0#u8, 55#u16, 1#u8), (43#u8, 16#u8, 56#u16, 1#u8), (44#u8, 17#u8, 57#u16,
    1#u8), (45#u8, 3#u8, 58#u16, 1#u8), (46#u8, 4#u8, 59#u16, 1#u8), (47#u8,
    3#u8, 60#u16, 1#u8), (48#u8, 3#u8, 61#u16, 1#u8), (49#u8, 3#u8, 62#u16,
    1#u8), (50#u8, 3#u8, 63#u16, 1#u8), (51#u8, 0#u8, 64#u16, 1#u8), (52#u8,
    12#u8, 65#u16, 1#u8), (53#u8, 12#u8, 66#u16, 1#u8), (54#u8, 0#u8, 67#u16,
    2#u8), (55#u8, 3#u8, 69#u16, 1#u8), (56#u8, 0#u8, 70#u16, 1#u8), (57#u8,
    3#u8, 71#u16, 1#u8), (58#u8, 3#u8, 72#u16, 1#u8), (59#u8, 3#u8, 73#u16,
    1#u8)
    ]

/-- [aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 788:4-798:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing"]
def
  aspis_statement.atomic_state_only_terminal.accumulate_atomic_copy_routing_loop.body
  (left_values : alloc.vec.Vec aspis_core.field.QM31)
  (right_prepared : alloc.vec.Vec aspis_core.field.PreparedQm31Multiplier)
  (pair_terms : Array (Std.U8 × Std.U8 × Std.U16 × Std.U8) 61#usize)
  (matrices : alloc.vec.Vec aspis_core.field.QM31) (pair_index : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.QM31))
  := do
  let s ← Aeneas.Std.lift (Array.to_slice pair_terms)
  let i := Slice.len s
  if pair_index < i
  then
    let t ← Array.index_usize pair_terms pair_index
    let (left, _, _, _) := t
    let (_, right, _, _) := t
    let (_, _, matrix_start, _) := t
    let (_, _, _, matrix_len) := t
    let i1 ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from right)
    let pqm ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.PreparedQm31Multiplier) right_prepared i1
    let i2 ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from left)
    let q ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.QM31) left_values i2
    let product ← aspis_core.field.PreparedQm31Multiplier.mul pqm q
    let i3 ← Aeneas.Std.lift (core.convert.num.FromUsizeU16.from matrix_start)
    let i4 ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from matrix_len)
    let matrices1 ←
      aspis_statement.atomic_state_only_terminal.add_atomic_copy_routing_destinations
        matrices product i3 i4
    let pair_index1 ← pair_index + 1#usize
    ok (cont (matrices1, pair_index1))
  else ok (done matrices)

/-- [aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 788:4-798:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing"]
def
  aspis_statement.atomic_state_only_terminal.accumulate_atomic_copy_routing_loop
  (left_values : alloc.vec.Vec aspis_core.field.QM31)
  (right_prepared : alloc.vec.Vec aspis_core.field.PreparedQm31Multiplier)
  (pair_terms : Array (Std.U8 × Std.U8 × Std.U16 × Std.U8) 61#usize)
  (matrices : alloc.vec.Vec aspis_core.field.QM31) (pair_index : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  loop
    (fun (matrices1, pair_index1) =>
      aspis_statement.atomic_state_only_terminal.accumulate_atomic_copy_routing_loop.body
      left_values right_prepared pair_terms matrices1 pair_index1)
    (matrices, pair_index)

/-- [aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 781:0-784:14
    Name pattern: [aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::accumulate_atomic_copy_routing"]
def aspis_statement.atomic_state_only_terminal.accumulate_atomic_copy_routing
  (left_values : alloc.vec.Vec aspis_core.field.QM31)
  (right_prepared : alloc.vec.Vec aspis_core.field.PreparedQm31Multiplier) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  let i ←
    2#usize +
      aspis_statement.atomic_state_only_terminal.ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS
  let i1 ← 4#usize * i
  let matrices ←
    alloc.vec.from_elem aspis_core.field.QM31.Insts.CoreCloneClone
      aspis_core.field.QM31.ZERO i1
  aspis_statement.atomic_state_only_terminal.accumulate_atomic_copy_routing_loop
    left_values right_prepared
    aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_PAIR_TERMS
    matrices 0#usize


end V7Tag73CurrentHelpersOpaque
