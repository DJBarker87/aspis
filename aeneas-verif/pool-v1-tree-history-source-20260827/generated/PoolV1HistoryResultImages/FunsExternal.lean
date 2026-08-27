import Aeneas
import PoolV1HistoryResultImages.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1HistoryResultImages

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::ne"]
def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Std.Usize} (partialEq : core.cmp.PartialEq T U) :
    Slice T → Array U N → Result Bool :=
  fun slice array =>
    core.slice.cmp.PartialEqSlice.ne partialEq slice (Array.to_slice array)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
axiom core.iter.traits.iterator.Iterator.any.default
    {Self F Item : Type} (iterator :
      core.iter.traits.iterator.Iterator Self Item)
    (predicate : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self)

def core.slice.iter.Iter.anyAux
    {T F : Type} (predicate : core.ops.function.FnMut F T Bool) :
    Nat → core.slice.iter.Iter T → F →
      Result (Bool × core.slice.iter.Iter T × F)
  | 0, iter, state => .ok (false, iter, state)
  | fuel + 1, iter, state => do
      let (item, next) ← core.slice.iter.IteratorSliceIter.next iter
      match item with
      | none => .ok (false, next, state)
      | some value =>
        let (found, state') ← predicate.call_mut state value
        if found then .ok (true, next, state')
        else core.slice.iter.Iter.anyAux predicate fuel next state'

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type} (predicate : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T)
  | iter, state => do
      let (found, final, _) ← core.slice.iter.Iter.anyAux predicate
        (iter.slice.len - iter.i + 1) iter state
      .ok (found, final)

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (mapper : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, closure => do
      let mapped ← mapper.call_once closure error
      .ok (.Err mapped)

@[rust_fun
  "alloc::boxed::convert::{core::convert::TryFrom<Box<[@T; @N]>, Box<[@T]>, Box<[@T]>>}::try_from"]
def BoxArray.Insts.CoreConvertTryFromBoxSliceBoxSlice.try_from
    {T : Type} (N : Std.Usize) (slice : Slice T) :
    Result (core.result.Result (Array T N) (Slice T)) :=
  if h : slice.val.length = N.val then .ok (.Ok ⟨slice.val, h⟩)
  else .ok (.Err slice)

@[rust_fun "alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref"]
def Box.Insts.CoreConvertAsRef.as_ref
    {T : Type} (_allocator : Type) (value : T) : Result T := .ok value

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::into_boxed_slice"]
def alloc.vec.Vec.into_boxed_slice
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T) :
    Result (Slice T) := .ok ⟨value.val, value.property⟩

/-!
The canonical digest codec is source-closed in the dedicated persistence and
read/round-trip extractions in this bundle.  This broader routing extraction
keeps the two exact production symbols as named composition boundaries.
-/
@[rust_fun "aspis_statement::atomic_statement::encode_digest_canonical"]
axiom aspis_statement.atomic_statement.encode_digest_canonical :
  Array aspis_core.field.M31 8#usize → Result (Array Std.U8 32#usize)

@[rust_fun "aspis_statement::atomic_statement::decode_digest_canonical"]
axiom aspis_statement.atomic_statement.decode_digest_canonical :
  Array Std.U8 32#usize → Result (core.result.Result
    (Array aspis_core.field.M31 8#usize)
    aspis_statement.atomic_statement.AtomicStatementError)

@[rust_fun
  "solana_pubkey::{core::cmp::PartialEq<solana_pubkey::Pubkey, solana_pubkey::Pubkey>}::eq"]
def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq
    (left right : solana_pubkey.Pubkey) : Result Bool :=
  .ok (decide (left.val = right.val))

@[rust_fun "solana_pubkey::{solana_pubkey::Pubkey}::new_from_array"]
def solana_pubkey.Pubkey.new_from_array
    (bytes : Array Std.U8 32#usize) : Result solana_pubkey.Pubkey := .ok bytes

/-! Solana PDA derivation remains the exact named runtime primitive boundary. -/
@[rust_fun "solana_pubkey::{solana_pubkey::Pubkey}::find_program_address"]
axiom solana_pubkey.Pubkey.find_program_address :
  Slice (Slice Std.U8) → solana_pubkey.Pubkey →
    Result (solana_pubkey.Pubkey × Std.U8)

@[rust_fun "solana_pubkey::{solana_pubkey::Pubkey}::to_bytes"]
def solana_pubkey.Pubkey.to_bytes
    (key : solana_pubkey.Pubkey) : Result (Array Std.U8 32#usize) := .ok key

@[rust_fun
  "solana_pubkey::{core::convert::AsRef<solana_pubkey::Pubkey, [u8]>}::as_ref"]
def solana_pubkey.Pubkey.Insts.CoreConvertAsRefSliceU8.as_ref
    (key : solana_pubkey.Pubkey) : Result (Slice Std.U8) := .ok key.to_slice
