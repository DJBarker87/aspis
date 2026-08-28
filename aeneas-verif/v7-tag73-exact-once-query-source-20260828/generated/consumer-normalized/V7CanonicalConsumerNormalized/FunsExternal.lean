import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7CanonicalConsumerNormalized.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CanonicalConsumerNormalizedGenerated

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-! Executable interpretations of Rust-library functions left external by
the focused extraction.  The final two definitions are deterministic hash
and Merkle control-flow models.  They are not used to prove cryptographic
correctness: the direct, unnormalized LLBC deliberately retains the real
cryptographic functions opaque.  They merely make the validation-control
translation executable and axiom-free. -/

@[rust_fun
  "core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter"]
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T : Type} {N : Std.Usize} (array : Array T N) :
    Result (core.array.iter.IntoIter T N) :=
  .ok { array := array }

@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    {T : Type} {N : Std.Usize}
    (iterator : core.array.iter.IntoIter T N) :
    Result (Option T × core.array.iter.IntoIter T N) :=
  if h : iterator.index < iterator.array.val.length then
    .ok (some iterator.array.val[iterator.index],
      { iterator with index := iterator.index + 1 })
  else
    .ok (none, iterator)

namespace V7CanonicalConsumerNormalizedExternal

def fromFnList
    {T F : Type} (fnMut : core.ops.function.FnMut F Std.Usize T) :
    Nat → Std.Usize → F → Result (List T)
  | 0, _, _ => .ok []
  | remaining + 1, index, closure => do
      let (value, closure) ← fnMut.call_mut closure index
      let nextIndex ← index + 1#usize
      let tail ← fromFnList fnMut remaining nextIndex closure
      .ok (value :: tail)

end V7CanonicalConsumerNormalizedExternal

@[rust_fun "core::array::from_fn"]
def core.array.from_fn
    {T F : Type} (N : Std.Usize)
    (fnMut : core.ops.function.FnMut F Std.Usize T) :
    F → Result (Array T N)
  | closure => do
      let values ←
        V7CanonicalConsumerNormalizedExternal.fromFnList
          fnMut N.val 0#usize closure
      dite (values.length = N.val)
        (fun h => .ok ⟨values, h⟩)
        (fun _ => .fail .panic)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def core.iter.traits.iterator.Iterator.any.default
    {Self F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (fnMutInst : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self) :=
  fun iterator closure => do
    let result : Bool × Self × F ← loop
      (fun (iterator, closure) => do
        let (item, iterator) ← iteratorInst.next iterator
        match item with
        | none => .ok (.done (false, iterator, closure))
        | some value => do
          let (found, closure) ← fnMutInst.call_mut closure value
          if found then
            .ok (.done (true, iterator, closure))
          else
            .ok (.cont (iterator, closure)))
      (iterator, closure)
    .ok (result.1, result.2.1)

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} :
    Option T → Result
      (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  | some value => .ok (.Continue value)
  | none => .ok (.Break none)

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible → Result (Option T)
  | none => .ok none
  | some impossible => nomatch impossible

@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T E : Type} :
    core.result.Result T E → Result (Option T)
  | .Ok value => .ok (some value)
  | .Err _ => .ok none

def core.slice.iter.Windows.windowAt {T : Type}
    (slice : Slice T) (index width : Nat) : Slice T :=
  ⟨(slice.val.drop index).take width, by
    calc
      ((slice.val.drop index).take width).length ≤
          (slice.val.drop index).length := List.length_take_le' _ _
      _ = slice.val.length - index := List.length_drop
      _ ≤ slice.val.length := Nat.sub_le _ _
      _ ≤ Usize.max := slice.property⟩

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    {T : Type} (iterator : core.slice.iter.Windows T) :
    Result (Option (Slice T) × core.slice.iter.Windows T) :=
  if iterator.index + iterator.width.val ≤ iterator.slice.val.length then
    .ok (some (core.slice.iter.Windows.windowAt iterator.slice iterator.index
      iterator.width.val), { iterator with index := iterator.index + 1 })
  else
    .ok (none, iterator)

@[rust_fun "core::slice::{[@T]}::windows"]
def core.slice.Slice.windows {T : Type} :
    Slice T → Std.Usize → Result (core.slice.iter.Windows T)
  | slice, width =>
    if width = 0#usize then .fail .panic
    else .ok { slice := slice, width := width, index := 0 }

namespace V7CanonicalConsumerNormalizedExternal

def insertByKey
    {T K F : Type} (fnMut : core.ops.function.FnMut F T K)
    (ord : core.cmp.Ord K) (value : T) :
    List T → F → Result (List T × F)
  | [], closure => .ok ([value], closure)
  | head :: tail, closure => do
      let (valueKey, closure) ← fnMut.call_mut closure value
      let (headKey, closure) ← fnMut.call_mut closure head
      let ordering ← ord.cmp valueKey headKey
      match ordering with
      | .lt => .ok (value :: head :: tail, closure)
      | .eq =>
          let (rest, closure) ← insertByKey fnMut ord value tail closure
          .ok (head :: rest, closure)
      | .gt =>
          let (rest, closure) ← insertByKey fnMut ord value tail closure
          .ok (head :: rest, closure)

def sortListByKey
    {T K F : Type} (fnMut : core.ops.function.FnMut F T K)
    (ord : core.cmp.Ord K) : List T → F → Result (List T × F)
  | [], closure => .ok ([], closure)
  | head :: tail, closure => do
      let (sortedTail, closure) ← sortListByKey fnMut ord tail closure
      insertByKey fnMut ord head sortedTail closure

end V7CanonicalConsumerNormalizedExternal

@[rust_fun "core::slice::{[@T]}::sort_unstable_by_key"]
def core.slice.Slice.sort_unstable_by_key
    {T K F : Type} (fnMut : core.ops.function.FnMut F T K)
    (ord : core.cmp.Ord K) : Slice T → F → Result (Slice T)
  | slice, closure => do
      let (values, _) ←
        V7CanonicalConsumerNormalizedExternal.sortListByKey
          fnMut ord slice.val closure
      dite (values.length ≤ Usize.max)
        (fun h => .ok ⟨values, h⟩)
        (fun _ => .fail .panic)

@[rust_const "aspis_core::field::P"]
def field.P : Result Std.U32 := .ok 2147483647#u32

@[rust_const "aspis_core::field::{aspis_core::field::QM31}::ZERO"]
def field.QM31.ZERO : Result field.QM31 :=
  .ok ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩

@[rust_fun "aspis_core::v7_merkle208::private_leaf_hash_v7"]
def v7_merkle208.private_leaf_hash_v7 :
    (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) → Std.U8 →
      Slice Std.U8 → Array Std.U8 32#usize →
      Result (Array Std.U8 26#usize) :=
  fun _ _ _ _ => .ok (Array.repeat 26#usize 0#u8)

@[rust_fun "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes"]
def v7_merkle208.verify_two_minimal_subtrees_v7_bytes :
    (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) →
      (Array Std.U8 26#usize × Array Std.U8 26#usize) → Std.U32 →
      Slice (Std.U32 × Array Std.U8 26#usize × Array Std.U8 26#usize) →
      (Slice Std.U8 × Slice Std.U8) →
      alloc.vec.Vec (Std.U32 × Array Std.U8 26#usize × Array Std.U8 26#usize) →
      alloc.vec.Vec (Std.U32 × Array Std.U8 26#usize × Array Std.U8 26#usize) →
      Result (Bool ×
        alloc.vec.Vec (Std.U32 × Array Std.U8 26#usize × Array Std.U8 26#usize) ×
        alloc.vec.Vec (Std.U32 × Array Std.U8 26#usize × Array Std.U8 26#usize)) :=
  fun _ _ _ _ _ level next => .ok (true, level, next)
