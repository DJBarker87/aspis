import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk28

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'_0, '_1, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1182:56-1182:62
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1182:56-1182:62
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1182:56-1182:62
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl]: loop body 2:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1181:4-1196:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0_loop0.body
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (low_lanes_selector : aspis_core.field.QM31)
  (high_lanes_selector : aspis_core.field.QM31)
  (iter : core.ops.range.Range Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 20#usize)) (Array aspis_core.field.QM31 20#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done packed)
  | some group =>
    let residuals ←
      core.array.from_fn 4#usize
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (group, openings)
    let selector ←
      if group < 2#usize
      then ok low_lanes_selector
      else ok high_lanes_selector
    let i ← 4#usize + group
    let q ← Array.index_usize packed i
    let s ← Aeneas.Std.lift (Array.to_slice residuals)
    let q1 ← aspis_core.field.qm31_pack_base4 s
    let q2 ← aspis_core.field.QM31.mul selector q1
    let q3 ← aspis_core.field.QM31.add q q2
    let a ← Array.update packed i q3
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl]: loop 2:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1181:4-1196:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0_loop0
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (iter : core.ops.range.Range Std.Usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (packed : Array aspis_core.field.QM31 20#usize)
  (low_lanes_selector : aspis_core.field.QM31)
  (high_lanes_selector : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  loop
    (fun (iter1, packed1) =>
      aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0_loop0.body
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
      openings low_lanes_selector high_lanes_selector iter1 packed1)
    (iter, packed)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl]: loop body 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1155:4-1262:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0.body
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : S) (trace : F) (domain_sum : aspis_core.field.QM31)
  (length_sum : aspis_core.field.QM31)
  (initial_selector : aspis_core.field.QM31)
  (iter : core.ops.range.Range Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 20#usize)) (Array aspis_core.field.QM31 20#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let q ← Array.index_usize packed 2#usize
    let a ← AtomicSemanticSelectorViewInst.«local» selectors
    let q1 ← Array.index_usize a 0#usize
    let s ←
      Aeneas.Std.lift (Array.to_slice
        (Array.make 4#usize [
          domain_sum, length_sum, aspis_core.field.QM31.ZERO,
          aspis_core.field.QM31.ZERO
          ]))
    let q2 ← aspis_core.field.qm31_pack_base4 s
    let q3 ← aspis_core.field.QM31.mul q1 q2
    let q4 ← aspis_core.field.QM31.sub q q3
    let a1 ← Array.update packed 2#usize q4
    let (_, trace1) ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.SemanticInitial
    let absorption_low ← Array.index_usize a 12#usize
    let q5 ← AtomicSemanticSelectorViewInst.block selectors 3#usize
    let q6 ← AtomicSemanticSelectorViewInst.block selectors 48#usize
    let q7 ← aspis_core.field.QM31.add q5 q6
    let low_lanes_selector ← aspis_core.field.QM31.mul absorption_low q7
    let q8 ← AtomicSemanticSelectorViewInst.block selectors 1#usize
    let q9 ← AtomicSemanticSelectorViewInst.block selectors 44#usize
    let q10 ← aspis_core.field.QM31.add q8 q9
    let q11 ← AtomicSemanticSelectorViewInst.block selectors 45#usize
    let q12 ← aspis_core.field.QM31.add q10 q11
    let q13 ← AtomicSemanticSelectorViewInst.block selectors 46#usize
    let q14 ← aspis_core.field.QM31.add q12 q13
    let q15 ← aspis_core.field.QM31.add q14 q6
    let high_lanes_selector ← aspis_core.field.QM31.mul absorption_low q15
    let packed1 ←
      aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0_loop0
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
        { start := 0#usize, «end» := 4#usize } openings a1 low_lanes_selector
        high_lanes_selector
    let (_, trace2) ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace1
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.SemanticAbsorption
    let (_, trace3) ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace2
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.SemanticMerkle
    let q16 ← AtomicSemanticSelectorViewInst.row selectors 864#usize
    let q17 ← AtomicSemanticSelectorViewInst.row selectors 866#usize
    let q18 ← Array.index_usize (Array.make 2#usize [ q16, q17 ]) 0#usize
    let q19 ← Array.index_usize (Array.make 2#usize [ q16, q17 ]) 1#usize
    let range_selector ← aspis_core.field.QM31.add q18 q19
    let q20 ← Array.index_usize openings.z 10#usize
    let q21 ← Array.index_usize openings.succ_z 10#usize
    let i ← 1#u32 <<< 10#i32
    let q22 ← aspis_core.field.QM31.mul_m31 q21 i
    let q23 ← aspis_core.field.QM31.add q20 q22
    let q24 ← Array.index_usize openings.xor12_z 10#usize
    let i1 ← 1#u32 <<< 20#i32
    let q25 ← aspis_core.field.QM31.mul_m31 q24 i1
    let triple_value ← aspis_core.field.QM31.add q23 q25
    let range_residuals ←
      core.array.from_fn 34#usize
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (openings, triple_value)
    let packed2 ←
      aspis_statement.atomic_state_only_terminal.atomic_accumulate packed1
        32#usize range_residuals range_selector
    let q26 ← Array.index_usize openings.z 11#usize
    let q27 ← Array.index_usize openings.z 12#usize
    let q28 ← aspis_core.field.QM31.sub q26 q27
    let q29 ←
      aspis_statement.atomic_state_only_terminal.lift statement.spend.fee
    let q30 ← aspis_core.field.QM31.sub q28 q29
    let q31 ← aspis_core.field.QM31.mul q18 q30
    let packed3 ←
      aspis_statement.atomic_state_only_terminal.atomic_add_preweighted packed2
        66#usize (Array.make 1#usize [ q31 ])
    let (_, trace4) ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace3
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.SemanticRange
    let a2 ←
      core.array.from_fn 8#usize
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (openings, statement)
    let a3 ←
      core.array.from_fn 8#usize
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (openings, statement)
    let a4 ←
      core.array.from_fn 8#usize
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (openings, statement)
    let a5 ←
      core.array.from_fn 8#usize
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (openings, statement)
    let public_selectors ←
      core.array.Array.map
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (Array.make 4#usize [ 23#usize, 43#usize, 45#usize, 48#usize ])
        selectors
    let packed4 ←
      aspis_statement.atomic_state_only_terminal.atomic_accumulate4 packed3
        67#usize (Array.make 4#usize [ a2, a3, a4, a5 ]) public_selectors
    let assets ←
      core.array.from_fn 2#usize
        (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst)
        (selectors, openings, statement)
    let packed5 ←
      aspis_statement.atomic_state_only_terminal.atomic_add_preweighted packed4
        75#usize assets
    let _ ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace4
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.SemanticPublic
    ok (done packed5)
  | some group =>
    let i ← 4#usize * group
    let i1 ← i + 4#usize
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
        openings.z { start := i, «end» := i1 }
    let q ← aspis_core.field.qm31_pack_base4 s
    let q1 ← aspis_core.field.QM31.mul initial_selector q
    let a ← Array.update packed group q1
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl]: loop 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1155:4-1262:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (iter : core.ops.range.Range Std.Usize)
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : S) (trace : F) (packed : Array aspis_core.field.QM31 20#usize)
  (domain_sum : aspis_core.field.QM31) (length_sum : aspis_core.field.QM31)
  (initial_selector : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  loop
    (fun (iter1, packed1) =>
      aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0.body
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
      statement openings selectors trace domain_sum length_sum initial_selector
      iter1 packed1)
    (iter, packed)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1151:4-1262:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0.body
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : S) (trace : F) (domain_sum : aspis_core.field.QM31)
  (length_sum : aspis_core.field.QM31)
  (initial_selector : aspis_core.field.QM31)
  (initial_or_path_selector : aspis_core.field.QM31)
  (iter : core.ops.range.Range Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 20#usize)) (Array aspis_core.field.QM31 20#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let packed1 ←
      aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0_loop0
        AtomicSemanticSelectorViewInst
        coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
        { start := 2#usize, «end» := 4#usize } statement openings selectors
        trace packed domain_sum length_sum initial_selector
    ok (done packed1)
  | some group =>
    let i ← 4#usize * group
    let i1 ← i + 4#usize
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
        openings.z { start := i, «end» := i1 }
    let q ← aspis_core.field.qm31_pack_base4 s
    let q1 ← aspis_core.field.QM31.mul initial_or_path_selector q
    let a ← Array.update packed group q1
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1151:4-1262:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (iter : core.ops.range.Range Std.Usize)
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : S) (trace : F) (packed : Array aspis_core.field.QM31 20#usize)
  (domain_sum : aspis_core.field.QM31) (length_sum : aspis_core.field.QM31)
  (initial_selector : aspis_core.field.QM31)
  (initial_or_path_selector : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  loop
    (fun (iter1, packed1) =>
      aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0.body
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
      statement openings selectors trace domain_sum length_sum initial_selector
      initial_or_path_selector iter1 packed1)
    (iter, packed)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1130:0-1138:47
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl"]
def aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : S) (trace : F) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  let packed := Array.repeat 20#usize aspis_core.field.QM31.ZERO
  let (initial_high_sum, domain_sum, length_sum) ←
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums
      AtomicSemanticSelectorViewInst selectors
  let a ← AtomicSemanticSelectorViewInst.«local» selectors
  let q ← Array.index_usize a 0#usize
  let initial_selector ← aspis_core.field.QM31.mul q initial_high_sum
  let q1 ← Array.index_usize a 0#usize
  let q2 ← AtomicSemanticSelectorViewInst.path_block selectors
  let path_initial_selector ← aspis_core.field.QM31.mul q1 q2
  let initial_or_path_selector ←
    aspis_core.field.QM31.add initial_selector path_initial_selector
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl_loop0
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
    { start := 0#usize, «end» := 2#usize } statement openings selectors trace
    packed domain_sum length_sum initial_selector initial_or_path_selector


end V7Tag73CurrentHelpersOpaque
