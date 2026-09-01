import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk15

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::poseidon]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 415:4-415:52
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::poseidon] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::poseidon"]
def aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.poseidon
  (self : aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors) :
  Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors
  := do
  ok { block := self.poseidon_block, «local» := self.semantic_local }

/-- [aspis_statement::atomic_state_only_terminal::{impl aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView for aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::path_block]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 469:4-469:32
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::path_block] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::path_block"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.path_block
  (self : aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors) :
  Result aspis_core.field.QM31
  := do
  ok self.path_block

/-- [aspis_statement::atomic_state_only_terminal::{impl aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView for aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::row]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 464:4-464:37
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::row] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::row"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.row
  (self : aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors)
  (row : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.row self row

/-- [aspis_statement::atomic_state_only_terminal::{impl aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView for aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::block]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 459:4-459:41
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::block] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::block"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.block
  (self : aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors)
  (block : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.block self
    block

/-- [aspis_statement::atomic_state_only_terminal::{impl aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView for aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::local]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 454:4-454:34
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::local] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>}::local"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.local
  (self : aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  ok self.semantic_local

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{impl aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView for aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 452:0-452:56
    Name pattern: [aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>] -/
@[reducible, rust_trait_impl
  "aspis_statement::atomic_state_only_terminal::AtomicSemanticSelectorView<aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView
  : aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors := {
  «local» :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.local
  block :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.block
  row :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.row
  path_block :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView.path_block
}

/-- [aspis_statement::atomic_state_only_terminal::lift]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 475:0-475:27
    Name pattern: [aspis_statement::atomic_state_only_terminal::lift] -/
@[rust_fun "aspis_statement::atomic_state_only_terminal::lift"]
def aspis_statement.atomic_state_only_terminal.lift
  (value : aspis_core.field.M31) : Result aspis_core.field.QM31 := do
  let c ← aspis_core.field.CM31.from_m31 value
  aspis_core.field.QM31.from_cm31 c

/-- [aspis_statement::atomic_state_only_terminal::atomic_copy_pattern_values]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 479:0-482:53
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_copy_pattern_values] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_copy_pattern_values"]
def aspis_statement.atomic_state_only_terminal.atomic_copy_pattern_values
  (openings : Array aspis_core.field.QM31 16#usize)
  (powers : Slice aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 15#usize)
  := do
  let i := Slice.len powers
  massert (i >= 9#usize)
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      aspis_core.field.QM31) powers { «end» := 8#usize }
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      openings { «end» := 8#usize }
  let a ← aspis_core.field.qm31_dot s s1
  let s2 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      openings { start := 1#usize, «end» := 9#usize }
  let c ← aspis_core.field.qm31_dot s s2
  let s3 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      aspis_core.field.QM31) powers { «end» := 6#usize }
  let s4 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      openings { start := 8#usize, «end» := 14#usize }
  let bd_prefix ← aspis_core.field.qm31_dot s3 s4
  let q ← Slice.index_usize powers 6#usize
  let q1 ← Slice.index_usize powers 7#usize
  let q2 ← Array.index_usize openings 14#usize
  let q3 ← Array.index_usize openings 15#usize
  let q4 ←
    aspis_core.field.qm31_sum_products2 (Array.make 2#usize [ q, q1 ])
      (Array.make 2#usize [ q2, q3 ])
  let b ← aspis_core.field.QM31.add bd_prefix q4
  let q5 ← Array.index_usize openings 0#usize
  let q6 ← Array.index_usize openings 1#usize
  let q7 ←
    aspis_core.field.qm31_sum_products2 (Array.make 2#usize [ q, q1 ])
      (Array.make 2#usize [ q5, q6 ])
  let d ← aspis_core.field.QM31.add bd_prefix q7
  let s5 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      openings { start := 2#usize, «end» := 10#usize }
  let e ← aspis_core.field.qm31_dot s s5
  let lambda ← Slice.index_usize powers 0#usize
  let x0 ← aspis_core.field.QM31.mul lambda q5
  let q8 ← Array.index_usize openings 11#usize
  let x11 ← aspis_core.field.QM31.mul lambda q8
  let q9 ← Array.index_usize openings 12#usize
  let x12 ← aspis_core.field.QM31.mul lambda q9
  let lambda8_b ← aspis_core.field.QM31.mul q1 b
  let cap ←
    Array.index_usize
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_PATTERNS
      14#usize
  let i1 ← Array.index_usize cap.offsets 8#usize
  let q10 ← aspis_core.field.QM31.add a lambda8_b
  let q11 ← aspis_core.field.QM31.add b lambda8_b
  let q12 ← aspis_core.field.QM31.mul q1 e
  let q13 ← aspis_core.field.QM31.add a q12
  let q14 ← aspis_core.field.QM31.mul q1 d
  let q15 ← aspis_core.field.QM31.add a q14
  let q16 ← Slice.index_usize powers 8#usize
  let q17 ← Array.index_usize openings 8#usize
  let q18 ← aspis_core.field.QM31.mul q16 q17
  let q19 ← aspis_core.field.QM31.add a q18
  let q20 ← aspis_core.field.QM31.mul lambda a
  let q21 ← aspis_core.field.QM31.mul lambda c
  let q22 ← aspis_core.field.QM31.add lambda q21
  let q23 ← aspis_core.field.QM31.sub q22 x0
  let q24 ← aspis_core.field.QM31.mul lambda b
  let q25 ← aspis_core.field.QM31.add lambda q24
  let q26 ← aspis_core.field.QM31.mul_m31 q16 i1
  let q27 ← aspis_core.field.QM31.add q25 q26
  ok
    (Array.make 15#usize [
      q10, a, c, b, d, q11, q13, q15, x11, x0, x12, q19, q20, q23, q27
      ])

/-- [aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 566:4-572:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_pattern_masked_dot"]
def
  aspis_statement.atomic_state_only_terminal.atomic_pattern_masked_dot_loop.body
  (routing : Slice aspis_core.field.QM31)
  (pattern_values : Array aspis_core.field.QM31 15#usize) (support : Std.U16)
  (selected_routing : Array aspis_core.field.QM31 15#usize)
  (selected_patterns : Array aspis_core.field.QM31 15#usize)
  (selected : Std.Usize) :
  Result (ControlFlow (Std.U16 × (Array aspis_core.field.QM31 15#usize) ×
    (Array aspis_core.field.QM31 15#usize) × Std.Usize) ((Array
    aspis_core.field.QM31 15#usize) × (Array aspis_core.field.QM31 15#usize)
    × Std.Usize))
  := do
  if support != 0#u16
  then
    let i ← core.num.U16.trailing_zeros support
    let pattern ← Aeneas.Std.lift (UScalar.cast .Usize i)
    let q ← Slice.index_usize routing pattern
    let a ← Array.update selected_routing selected q
    let q1 ← Array.index_usize pattern_values pattern
    let a1 ← Array.update selected_patterns selected q1
    let selected1 ← selected + 1#usize
    let i1 ← support - 1#u16
    let support1 ← Aeneas.Std.lift (support &&& i1)
    ok (cont (support1, a, a1, selected1))
  else ok (done (selected_routing, selected_patterns, selected))


end V7Tag73CurrentHelpersOpaque
