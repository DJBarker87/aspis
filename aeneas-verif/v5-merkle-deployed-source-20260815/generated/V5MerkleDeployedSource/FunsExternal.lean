import Aeneas.Std
import RuntimeScheduleMerkleReuse
import V5MerkleDeployedSource.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5MerkleDeployedSource

/-- Exact low-32-bit coercion used for a Rust `usize` shift count. -/
def usizeShiftCount (value : Std.Usize) : Std.U32 :=
  ⟨value.bv.setWidth 32⟩

def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

def core.option.OptionShared0T.copied {T : Type}
    (_markerCopyInst : core.marker.Copy T) :
    Option T → Result (Option T) :=
  fun value => ok value

def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} :
    Option T → Result (core.ops.control_flow.ControlFlow
      (Option core.convert.Infallible) T)
  | none => ok (.Break none)
  | some value => ok (.Continue value)

def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible → Result (Option T)
  | none => ok none
  | some impossible => nomatch impossible

def core.result.Result.map_err
    {T E F O : Type} (function : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, state => do
      let mapped ← function.call_once state error
      ok (.Err mapped)

def alloc.vec.Vec.as_slice {T : Type} (A : Type)
    (value : alloc.vec.Vec T) : Result (Slice T) :=
  let _ := A
  ok ⟨value.val, value.property⟩

def alloc.vec.Vec.clear {T : Type} (A : Type)
    (_value : alloc.vec.Vec T) : Result (alloc.vec.Vec T) :=
  let _ := A
  ok (alloc.vec.Vec.new T)

def alloc.vec.Vec.is_empty {T : Type} (A : Type)
    (value : alloc.vec.Vec T) : Result Bool :=
  let _ := A
  ok (value.val = [])

def mapQueryError :
    _root_.V5MerkleQueryReuse.circle_line_merkle.CircleLineMerkleError →
      aspis_core.circle_line_merkle.CircleLineMerkleError
  | .EmptyQueries => .EmptyQueries
  | .QueryOutOfRange index => .QueryOutOfRange index
  | .CountMismatch tag expected actual => .CountMismatch tag expected actual
  | .UnexpectedEnd tag offset needed => .UnexpectedEnd tag offset needed
  | .TrailingBytes offset remaining => .TrailingBytes offset remaining
  | .LengthOverflow => .LengthOverflow
  | .NonCanonicalLeaf tag query component =>
      .NonCanonicalLeaf tag query component
  | .MerkleMismatch tag => .MerkleMismatch tag
  | .PrefixRootMissing tag => .PrefixRootMissing tag
  | .InvalidLayer layer => .InvalidLayer layer
  | .QueryNotOpened query => .QueryNotOpened query
  | .LeafIndexNotFound layer index => .LeafIndexNotFound layer index

def mapQueryIndices
    (indices : _root_.V5MerkleQueryReuse.circle_line_merkle.CircleLineQueryIndices) :
    aspis_core.circle_line_merkle.CircleLineQueryIndices where
  layer0 := indices.layer0
  later := indices.later

def aspis_core.circle_line_merkle.CIRCLE_LINE_TAGS :
    Result (Array Std.U8 3#usize) :=
  ok (Array.make 3#usize [65#u8, 66#u8, 67#u8])

def aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
    (queries : Slice Std.U32) (queryCount : Std.Usize) :
    Result (core.result.Result
      aspis_core.circle_line_merkle.CircleLineQueryIndices
      aspis_core.circle_line_merkle.CircleLineMerkleError) := do
  let result ←
    _root_.V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count
      queries queryCount
  match result with
  | .Ok indices => ok (.Ok (mapQueryIndices indices))
  | .Err error => ok (.Err (mapQueryError error))

def aspis_core.circle_merkle.CIRCLE_C1_LAYER0_TAG : Result Std.U8 :=
  ok 64#u8

def aspis_core.circle_merkle.CIRCLE_C2_LAYER0_TAG : Result Std.U8 :=
  ok 192#u8

/-- The sole remaining executable boundary. Every theorem using this constant
must explicitly assume its equality to Solana SHA-256 over the concatenated
input slices. -/
axiom merkle.fixed_hashv :
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

end V5MerkleDeployedSource
