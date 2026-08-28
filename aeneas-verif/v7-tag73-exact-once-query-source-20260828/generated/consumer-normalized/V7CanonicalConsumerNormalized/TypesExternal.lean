import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option linter.dupNamespace false

/-! Transparent representations of the three types left external by the
focused extraction.  The prepared multiplier is not inspected by the
validation-only normalization; `Unit` therefore models exactly its erased
data role in this extraction, without adding an axiom. -/

@[rust_type "core::array::iter::IntoIter"]
structure core.array.iter.IntoIter (T : Type) (N : Std.Usize) where
  array : Array T N
  index : Nat := 0

@[rust_type "core::slice::iter::Windows"]
structure core.slice.iter.Windows (T : Type) where
  slice : Slice T
  width : Std.Usize
  index : Nat

def field.PreparedQm31Multiplier : Type := Unit
