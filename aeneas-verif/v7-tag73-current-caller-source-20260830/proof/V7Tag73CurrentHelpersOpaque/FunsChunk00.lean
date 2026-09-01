import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsExternal
import V7Tag73CurrentHelpersOpaque.CircleTable_RATE512_CIRCLE_LOW8_WINDOW_Chunk15
import V7Tag73CurrentHelpersOpaque.AtomicPatternChunk14
import V7Tag73CurrentHelpersOpaque.LateScalarExternal

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque

/-- Trait implementation: [core::array::iter::{impl core::iter::traits::iterator::Iterator<T> for core::array::iter::IntoIter<T, N>}]
    Source: '/rustc/library/core/src/array/iter.rs', lines 238:0-238:51
    Name pattern: [core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>"]
impl_def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator (T :
  Type) (N : Std.Usize) : core.iter.traits.iterator.Iterator
  (core.array.iter.IntoIter T N) T := {
  next := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N)
}

/-- Trait implementation: [core::array::iter::{impl core::iter::traits::double_ended::DoubleEndedIterator<T> for core::array::iter::IntoIter<T, N>}]
    Source: '/rustc/library/core/src/array/iter.rs', lines 295:0-295:62
    Name pattern: [core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>"]
def
  core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
  (T : Type) (N : Std.Usize) :
  core.iter.traits.double_ended.DoubleEndedIterator (core.array.iter.IntoIter T
  N) T := {
  iteratorInst := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
    T N
  next_back :=
    core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
}

/-- Trait implementation: [core::fmt::{impl core::fmt::Debug for [T]}]
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 3121:0-3121:28
    Name pattern: [core::fmt::Debug<[@T]>] -/
@[reducible, rust_trait_impl "core::fmt::Debug<[@T]>"]
def Slice.Insts.CoreFmtDebug {T : Type} (DebugInst : core.fmt.Debug T) :
  core.fmt.Debug (Slice T) := {
  fmt := Slice.Insts.CoreFmtDebug.fmt DebugInst
}

/-- Trait implementation: [core::iter::adapters::filter_map::{impl core::iter::traits::iterator::Iterator<B> for core::iter::adapters::filter_map::FilterMap<I, F>}]
    Source: '/rustc/library/core/src/iter/adapters/filter_map.rs', lines 56:0-58:35
    Name pattern: [core::iter::traits::iterator::Iterator<core::iter::adapters::filter_map::FilterMap<@I, @F>, @B>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::filter_map::FilterMap<@I, @F>, @B>"]
impl_def
  core.iter.adapters.filter_map.FilterMap.Insts.CoreIterTraitsIteratorIterator
  {B : Type} {I : Type} {F : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I
  Clause0_Item) (opsfunctionFnMutFTupleClause0_ItemOptionInst :
  core.ops.function.FnMut F Clause0_Item (Option B)) :
  core.iter.traits.iterator.Iterator (core.iter.adapters.filter_map.FilterMap I
  F) B := {
  next :=
    core.iter.adapters.filter_map.FilterMap.Insts.CoreIterTraitsIteratorIterator.next
    traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemOptionInst
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.adapters.filter_map.FilterMap.Insts.CoreIterTraitsIteratorIterator
    traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemOptionInst)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.adapters.filter_map.FilterMap.Insts.CoreIterTraitsIteratorIterator
    traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemOptionInst)
}

/-- Trait implementation: [core::iter::adapters::map::{impl core::iter::traits::iterator::Iterator<B> for core::iter::adapters::map::Map<I, F>}]
    Source: '/rustc/library/core/src/iter/adapters/map.rs', lines 99:0-101:27
    Name pattern: [core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>"]
impl_def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator {B :
  Type} {I : Type} {F : Type} {Clause0_Item : Type} (traitsiteratorIteratorInst
  : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F
  Clause0_Item B) : core.iter.traits.iterator.Iterator
  (core.iter.adapters.map.Map I F) B := {
  next := core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
    traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemBInst
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemBInst)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemBInst)
}

/-- Trait implementation: [core::iter::adapters::zip::{impl core::iter::traits::iterator::Iterator<(Clause0_Item, Clause1_Item)> for core::iter::adapters::zip::Zip<A, B>}]
    Source: '/rustc/library/core/src/iter/adapters/zip.rs', lines 74:0-77:16
    Name pattern: [core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>"]
impl_def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair {A
  : Type} {B : Type} {Clause0_Item : Type} {Clause1_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A
  Clause0_Item) (traitsiteratorIteratorInst1 :
  core.iter.traits.iterator.Iterator B Clause1_Item) :
  core.iter.traits.iterator.Iterator (core.iter.adapters.zip.Zip A B)
  (Clause0_Item × Clause1_Item) := {
  next :=
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    traitsiteratorIteratorInst traitsiteratorIteratorInst1
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
    traitsiteratorIteratorInst traitsiteratorIteratorInst1)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
    traitsiteratorIteratorInst traitsiteratorIteratorInst1)
}

/-- Trait implementation: [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a mut T> for core::slice::iter::IterMut<'a, T>}]
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 153:8-153:45
    Name pattern: [core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>"]
impl_def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (T :
  Type) : core.iter.traits.iterator.Iterator (core.slice.iter.IterMut T) T := {
  next := core.slice.iter.IteratorIterMut.next_without_writeback
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
}

/-- Trait implementation: [core::slice::iter::{impl core::iter::traits::double_ended::DoubleEndedIterator<&'_ T> for core::slice::iter::Iter<'a, T>}]
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 436:8-436:56
    Name pattern: [core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>"]
def
  core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
  (T : Type) : core.iter.traits.double_ended.DoubleEndedIterator
  (core.slice.iter.Iter T) T := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  next_back :=
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
}

/-- Trait implementation: [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a [T]> for core::slice::iter::Windows<'a, T>}]
    Source: '/rustc/library/core/src/slice/iter.rs', lines 1350:0-1350:39
    Name pattern: [core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>"]
impl_def
  core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice (T :
  Type) : core.iter.traits.iterator.Iterator (core.slice.iter.Windows T) (Slice
  T) := {
  next :=
    core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
    T)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
    T)
}

/-- Trait implementation: [alloc::boxed::{impl core::fmt::Debug for alloc::boxed::Box<T>}]
    Source: '/rustc/library/alloc/src/boxed.rs', lines 2234:0-2234:67
    Name pattern: [core::fmt::Debug<Box<@T>>] -/
@[reducible, rust_trait_impl "core::fmt::Debug<Box<@T>>"]
def Box.Insts.CoreFmtDebug {T : Type} (A : Type) (corefmtDebugInst :
  core.fmt.Debug T) : core.fmt.Debug T := {
  fmt := Box.Insts.CoreFmtDebug.fmt A corefmtDebugInst
}

/-- Trait implementation: [alloc::vec::{impl core::iter::traits::collect::IntoIterator<&'a T, core::slice::iter::Iter<'a, T>> for &'a alloc::vec::Vec<T>}]
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3977:0-3977:56
    Name pattern: [core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter (T : Type)
  (A : Type) : core.iter.traits.collect.IntoIterator (alloc.vec.Vec T) T
  (core.slice.iter.Iter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  into_iter :=
    SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter A
}

/-- [aspis_core::circle_fri::RATE512_CIRCLE_LOW8_WINDOW]
    Source: '/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/target-normalized-r2/x86_64-unknown-linux-gnu/debug/build/aspis-core-4e5313882daeed0f/out/circle_tables.rs', lines 36151:0-36151:53
    Name pattern: [aspis_core::circle_fri::RATE512_CIRCLE_LOW8_WINDOW]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::circle_fri::RATE512_CIRCLE_LOW8_WINDOW"]
def aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
  : Array (Array Std.U32 2#usize) 256#usize :=
  staged_circle_tables.append128 (staged_circle_tables.append64 (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk00) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk01)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk02) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk03))) (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk04) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk05)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk06) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk07)))) (staged_circle_tables.append64 (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk08) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk09)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk10) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk11))) (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk12) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk13)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk14) (staged_circle_tables.RATE512_CIRCLE_LOW8_WINDOW_chunk15))))


end V7Tag73CurrentHelpersOpaque
