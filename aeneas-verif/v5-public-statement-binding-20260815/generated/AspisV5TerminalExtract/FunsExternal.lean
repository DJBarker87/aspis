import Aeneas.Std
import AspisV5TerminalExtract.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V5PublicStatementGenerated

/-!
Transparent models for the standard-library calls and the small codec helpers
which Charon leaves opaque when `decode_statement` is selected as the sole
production entry point.  The statement encoder below spells out the same
fixed-width layout as `aspis-statement`; it is intentionally not an axiom.
-/

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::ne"]
def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Std.Usize} (partialEq : core.cmp.PartialEq T U)
    (slice : Slice T) (array : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.ne partialEq slice (Array.to_slice array)

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
    {T E : Type} : Option T -> E -> Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (function : core.ops.function.FnOnce O E F) :
    core.result.Result T E -> O -> Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, state => do
      let mapped <- function.call_once state error
      ok (.Err mapped)

def unwrapCopySlice {T : Type} :
    core.result.Result T core.array.TryFromSliceError -> Result T
  | .Ok value => ok value
  | .Err _ => fail .panic

def m31Prime : Nat := 2147483647

def u8 (value : Nat) (bound : value < 256 := by omega) : Std.U8 :=
  Std.U8.ofNatCore value bound

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

@[rust_const "aspis_core::field::{aspis_core::field::QM31}::ZERO"]
def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 :=
  ok { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::from_le_bytes"]
def aspis_core.field.QM31.from_le_bytes
    (bytes : Slice Std.U8) : Result (Option aspis_core.field.QM31) :=
  if hlen : bytes.val.length = 16 then
    match canonicalWord bytes.val 0, canonicalWord bytes.val 1,
        canonicalWord bytes.val 2, canonicalWord bytes.val 3 with
    | some a, some b, some c, some d =>
        ok (some { c0 := { a, b }, c1 := { a := c, b := d } })
    | _, _, _, _ => ok none
  else ok none

@[rust_const "aspis_statement::atomic_statement::ATOMIC_PAYMENT_TREE_DEPTH"]
def aspis_statement.atomic_statement.ATOMIC_PAYMENT_TREE_DEPTH :
    Result Std.Usize := ok 20#usize

@[rust_const "aspis_statement::atomic_statement::ATOMIC_PAYMENT_STATEMENT_VERSION"]
def aspis_statement.atomic_statement.ATOMIC_PAYMENT_STATEMENT_VERSION :
    Result Std.U8 := ok 4#u8

@[rust_const "aspis_statement::atomic_statement::ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES"]
def aspis_statement.atomic_statement.ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES :
    Result Std.Usize := ok 216#usize

@[rust_fun "aspis_statement::atomic_statement::decode_digest_canonical"]
def aspis_statement.atomic_statement.decode_digest_canonical
    (bytes : Array Std.U8 32#usize) : Result (core.result.Result
      (Array aspis_core.field.M31 8#usize)
      aspis_statement.atomic_statement.AtomicStatementError) :=
  match decodeDigest bytes.val with
  | some words => ok (.Ok words)
  | none => ok (.Err
      aspis_statement.atomic_statement.AtomicStatementError.NonCanonicalDigest)

@[rust_fun "aspis_statement::atomic_statement::decode_asset_id_canonical"]
def aspis_statement.atomic_statement.decode_asset_id_canonical
    (value : Std.U32) : Result (core.result.Result aspis_core.field.M31
      aspis_statement.atomic_statement.AtomicStatementError) :=
  if value.val < m31Prime then ok (.Ok value)
  else ok (.Err
    aspis_statement.atomic_statement.AtomicStatementError.NonCanonicalAssetId)

def digestBytes (digest : Array aspis_core.field.M31 8#usize) : List Std.U8 :=
  digest.val.flatMap (fun value => (core.num.U32.to_le_bytes value).val)

def statementBytes
    (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4) :
    List Std.U8 :=
  [4#u8, 20#u8] ++ List.replicate 6 0#u8 ++ statement.pool.val ++
    (core.num.U64.to_le_bytes statement.sequence).val ++
    digestBytes statement.spend.anchor ++
    digestBytes statement.spend.nullifier ++
    digestBytes statement.spend.output_commitment ++
    digestBytes statement.output_anchor ++
    (core.num.U32.to_le_bytes statement.spend.asset_id).val ++
    (core.num.U32.to_le_bytes statement.spend.fee).val ++
    statement.deployment_domain.val

theorem digestBytes_length
    (digest : Array aspis_core.field.M31 8#usize) :
    (digestBytes digest).length = 32 := by
  simp [digestBytes]

theorem statementBytes_length
    (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4) :
    (statementBytes statement).length = 216 := by
  simp [statementBytes, digestBytes_length]

@[rust_fun "aspis_statement::atomic_statement::encode_atomic_payment_statement_v4"]
def aspis_statement.atomic_statement.encode_atomic_payment_statement_v4
    (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4) :
    Result (core.result.Result (Array Std.U8 216#usize)
      aspis_statement.atomic_statement.AtomicStatementError) :=
  if statement.spend.asset_id.val >= m31Prime then
    ok (.Err
      aspis_statement.atomic_statement.AtomicStatementError.NonCanonicalAssetId)
  else if statement.spend.fee.val >= 2 ^ 30 then
    ok (.Err aspis_statement.atomic_statement.AtomicStatementError.FeeOutOfRange)
  else
    ok (.Ok ⟨statementBytes statement, statementBytes_length statement⟩)
