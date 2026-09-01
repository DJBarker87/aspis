import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk18
import V7Tag73CurrentHelpersOpaque.LateIteratorExternal

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 591:4-645:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0
  (iter : core.slice.iter.Iter (Std.U8 × Std.U32))
  (selectors : Slice aspis_core.field.QM31) (signed : Array Std.U64 4#usize)
  (products : Array Std.U64 4#usize) (reduced_products : Array Std.U64 4#usize)
  (product_coefficient_sum : Std.U64) :
  Result (aspis_core.field.CM31 × aspis_core.field.CM31)
  := do
  loop
    (fun (iter1, signed1, products1, reduced_products1,
      product_coefficient_sum1) =>
      aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0.body
      selectors iter1 signed1 products1 reduced_products1
      product_coefficient_sum1)
    (iter, signed, products, reduced_products, product_coefficient_sum)

/-- [aspis_statement::atomic_state_only_terminal::routing_linear_form]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 580:0-580:73
    Name pattern: [aspis_statement::atomic_state_only_terminal::routing_linear_form] -/
@[rust_fun "aspis_statement::atomic_state_only_terminal::routing_linear_form"]
def aspis_statement.atomic_state_only_terminal.routing_linear_form
  (entries : Slice (Std.U8 × Std.U32))
  (selectors : Slice aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let signed := Array.repeat 4#usize 0#u64
  let products := Array.repeat 4#usize 0#u64
  let reduced_products := Array.repeat 4#usize 0#u64
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      entries
  let (c, c1) ←
    aspis_statement.atomic_state_only_terminal.routing_linear_form_loop0 iter
      selectors signed products reduced_products 0#u64
  ok { c0 := c, c1 }

/-- [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{impl core::ops::function::FnMut<(&'_ (u16, u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 730:13-730:28
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU16U8QM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure)
  (tupled_args : (Std.U16 × Std.U8)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure)
  := do
  let (s, s1) := c
  let (start, len) := tupled_args
  let start1 ← Aeneas.Std.lift (core.convert.num.FromUsizeU16.from start)
  let i ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from len)
  let i1 ← start1 + i
  let s2 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      (Std.U8 × Std.U32)) s { start := start1, «end» := i1 }
  let q ←
    aspis_statement.atomic_state_only_terminal.routing_linear_form s2 s1
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{impl core::ops::function::FnOnce<(&'_ (u16, u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 730:13-730:28
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairU16U8QM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure)
  (p : (Std.U16 × Std.U8)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU16U8QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{impl core::ops::function::FnOnce<(&'_ (u16, u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 730:13-730:28
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairU16U8QM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure
  (Std.U16 × Std.U8) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairU16U8QM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::{impl core::ops::function::FnMut<(&'_ (u16, u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 730:13-730:28
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms::closure<'0, '1>, (&'_ (u16, u8)), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU16U8QM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure
  (Std.U16 × Std.U8) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairU16U8QM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU16U8QM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 723:0-727:14
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_routing_linear_forms"]
def aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms
  (factors : Slice (Std.U16 × Std.U8)) (entries : Slice (Std.U8 × Std.U32))
  (selectors : Slice aspis_core.field.QM31) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  let i ← core.slice.Slice.iter factors
  let m ←
    core.iter.traits.iterator.Iterator.map.default
      (core.iter.traits.iterator.IteratorSliceIter (Std.U16 × Std.U8))
      aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU16U8QM31
      i (entries, selectors)
  core.iter.traits.iterator.Iterator.collect.default
    (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    (core.iter.traits.iterator.IteratorSliceIter (Std.U16 × Std.U8))
    aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTupleSharedPairU16U8QM31)
    (core.iter.traits.collect.FromIteratorVec aspis_core.field.QM31) m

/-- [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{impl core::ops::function::FnMut<((&'_ (u16, u8), &'_ u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 750:13-750:39
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTuplePairSharedPairU16U8SharedU8QM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure)
  (tupled_args : ((Std.U16 × Std.U8) × Std.U8)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure)
  := do
  let (v, s) := c
  let ((start, len), direct) := tupled_args
  if direct != core.num.U8.MAX
  then
    let i ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from direct)
    let q ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.QM31) v i
    ok (q, c)
  else
    let start1 ← Aeneas.Std.lift (core.convert.num.FromUsizeU16.from start)
    let i ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from len)
    let i1 ← start1 + i
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        (Std.U8 × Std.U32)) s { start := start1, «end» := i1 }
    let s2 := alloc.vec.Vec.deref v
    let q ←
      aspis_statement.atomic_state_only_terminal.routing_linear_form s1 s2
    ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{impl core::ops::function::FnOnce<((&'_ (u16, u8), &'_ u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 750:13-750:39
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTuplePairSharedPairU16U8SharedU8QM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure)
  (p : ((Std.U16 × Std.U8) × Std.U8)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTuplePairSharedPairU16U8SharedU8QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{impl core::ops::function::FnOnce<((&'_ (u16, u8), &'_ u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 750:13-750:39
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTuplePairSharedPairU16U8SharedU8QM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure
  ((Std.U16 × Std.U8) × Std.U8) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTuplePairSharedPairU16U8SharedU8QM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::{impl core::ops::function::FnMut<((&'_ (u16, u8), &'_ u8),), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 750:13-750:39
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms::closure<'0, '1>, ((&'_ (u16, u8), &'_ u8)), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTuplePairSharedPairU16U8SharedU8QM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure
  ((Std.U16 × Std.U8) × Std.U8) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnOnceTuplePairSharedPairU16U8SharedU8QM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTuplePairSharedPairU16U8SharedU8QM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 738:0-744:14
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_factorized_routing_linear_forms"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms
  (basis_factors : Slice (Std.U16 × Std.U8))
  (reconstruction_factors : Slice (Std.U16 × Std.U8))
  (direct_basis : Slice Std.U8) (entries : Slice (Std.U8 × Std.U32))
  (selectors : Slice aspis_core.field.QM31) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  let left_val := Slice.len reconstruction_factors
  let right_val := Slice.len direct_basis
  massert (left_val = right_val)
  let basis ←
    aspis_statement.atomic_state_only_terminal.evaluate_routing_linear_forms
      basis_factors entries selectors
  let i ← core.slice.Slice.iter reconstruction_factors
  let z ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.traits.iterator.IteratorSliceIter (Std.U16 × Std.U8))
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter Std.U8) i
      direct_basis
  let m ←
    core.iter.traits.iterator.Iterator.map.default
      (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (core.iter.traits.iterator.IteratorSliceIter (Std.U16 × Std.U8))
      (core.iter.traits.iterator.IteratorSliceIter Std.U8))
      aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTuplePairSharedPairU16U8SharedU8QM31
      z (basis, entries)
  core.iter.traits.iterator.Iterator.collect.default
    (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
    (core.iter.traits.iterator.IteratorSliceIter (Std.U16 × Std.U8))
    (core.iter.traits.iterator.IteratorSliceIter Std.U8))
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms.closure.Insts.CoreOpsFunctionFnMutTuplePairSharedPairU16U8SharedU8QM31)
    (core.iter.traits.collect.FromIteratorVec aspis_core.field.QM31) m


end V7Tag73CurrentHelpersOpaque
