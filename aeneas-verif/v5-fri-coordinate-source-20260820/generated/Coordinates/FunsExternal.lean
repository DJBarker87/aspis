-- Implementations of the four standard-library/constant declarations left
-- external by the coordinate extraction.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Coordinates.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open V5FriCoordinateAdapter

@[rust_fun "core::num::{usize}::reverse_bits"]
def core.num.Usize.reverse_bits (value : Std.Usize) : Result Std.Usize :=
  ok ⟨value.bv.reverse⟩

@[rust_fun "core::slice::{[@T]}::first"]
def core.slice.Slice.first {T : Type} (value : Slice T) : Result (Option T) :=
  ok value.val.head?

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def alloc.vec.Vec.is_empty
    {T : Type} (A : Type) (value : alloc.vec.Vec T) : Result Bool :=
  let _ := A
  ok (value.val = [])

@[rust_const "aspis_core::params::CIRCLE_LOG_ORDER"]
def aspis_core.params.CIRCLE_LOG_ORDER : Result Std.U32 :=
  ok 31#u32
