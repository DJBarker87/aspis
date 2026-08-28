import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option linter.dupNamespace false

/-! Transparent model of Rust's overlapping slice-window iterator. -/

@[rust_type "core::slice::iter::Windows"]
structure core.slice.iter.Windows (T : Type) where
  slice : Slice T
  width : Std.Usize
  index : Nat
