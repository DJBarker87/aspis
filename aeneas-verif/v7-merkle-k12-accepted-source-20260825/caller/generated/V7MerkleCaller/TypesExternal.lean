-- Executable interpretation of the Rust-library iterator type unique to the
-- transparent caller extraction.  The shared `Windows` type is reused from
-- the already checked V7 Merkle extraction so both generated roots can be
-- imported into one Lean environment without duplicate declarations.
import V7MerkleK12.TypesExternal
open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-- Rust's owned fixed-array iterator, represented by the array and cursor. -/
@[rust_type "core::array::iter::IntoIter"]
structure core.array.iter.IntoIter (T : Type) (N : Std.Usize) where
  array : Array T N
  index : Nat := 0
