import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
Transparent representations of the two Rust standard-library iterator types
left external by the focused query-batch extraction.
-/

@[rust_type "core::array::iter::IntoIter"]
structure core.array.iter.IntoIter (T : Type) (N : Std.Usize) where
  array : Array T N
  index : Nat := 0

@[rust_type "core::slice::iter::Windows"]
structure core.slice.iter.Windows (T : Type) where
  slice : Slice T
  width : Std.Usize
  index : Nat
