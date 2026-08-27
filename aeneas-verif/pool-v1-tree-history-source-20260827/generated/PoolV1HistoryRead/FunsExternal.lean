import Aeneas
import PoolV1HistoryRead.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1HistoryRead

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-!
Transparent interpretations of the two standard-library combinators used by
the focused retained-root source extraction.
-/

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, closure => do
      let mapped ← inst.call_once closure error
      .ok (.Err mapped)

def m31Prime : Nat := 2147483647

def u32 (value : Nat) (bound : value < 2 ^ 32 := by omega) : Std.U32 :=
  Std.U32.ofNatCore value bound

def word32 (bytes : List Std.U8) : Std.U32 :=
  u32 ((bytes.getD 0 0#u8).val +
    256 * (bytes.getD 1 0#u8).val +
    65536 * (bytes.getD 2 0#u8).val +
    16777216 * (bytes.getD 3 0#u8).val) (by
      have h0 := U8.lt_succ_max (bytes.getD 0 0#u8)
      have h1 := U8.lt_succ_max (bytes.getD 1 0#u8)
      have h2 := U8.lt_succ_max (bytes.getD 2 0#u8)
      have h3 := U8.lt_succ_max (bytes.getD 3 0#u8)
      omega)

def wordAt (bytes : List Std.U8) (index : Nat) : Std.U32 :=
  word32 (bytes.drop (4 * index))

def canonicalWord (bytes : List Std.U8) (index : Nat) : Option Std.U32 :=
  let value := wordAt bytes index
  if value.val < m31Prime then some value else none

def decodeDigest (bytes : List Std.U8) :
    Option (Array Std.U32 8#usize) :=
  if hall : ∀ index : Fin 8, (canonicalWord bytes index).isSome then
    some ⟨List.ofFn (fun index : Fin 8 =>
      (canonicalWord bytes index).get (hall index)), by simp⟩
  else none

@[rust_fun "aspis_statement::atomic_statement::decode_digest_canonical"]
def aspis_statement.atomic_statement.decode_digest_canonical
    (bytes : Array Std.U8 32#usize) : Result (core.result.Result
      (Array aspis_core.field.M31 8#usize)
      aspis_statement.atomic_statement.AtomicStatementError) :=
  match decodeDigest bytes.val with
  | some words => .ok (.Ok words)
  | none => .ok (.Err
      aspis_statement.atomic_statement.AtomicStatementError.NonCanonicalDigest)
