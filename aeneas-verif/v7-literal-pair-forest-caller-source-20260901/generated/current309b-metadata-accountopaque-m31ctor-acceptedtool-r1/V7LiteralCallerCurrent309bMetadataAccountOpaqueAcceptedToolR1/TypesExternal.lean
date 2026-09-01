import Aeneas
import V7LiteralCallerReadonlyMetadataHelperCurrent309bR1.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-!
Executable replacements for the seven external type templates in the accepted
whole-caller translation.  Only `AccountInfo` participates in the metadata
bridge below.  Four iterator/container types remain opaque-to-this-root carrier
types, represented as empty inductives rather than logical axioms.  `Windows`
is now its exact finite logical state so its ordinary slice-library operations
can be executable.
-/
@[rust_type "core::array::iter::IntoIter"]
inductive core.array.iter.IntoIter (T : Type) (N : Std.Usize) : Type

@[rust_type "core::iter::adapters::flatten::Flatten"]
inductive core.iter.adapters.flatten.Flatten (I : Type) (Clause0_Item : Type)
    (Clause1_Item : Type) (Clause1_IntoIter : Type) : Type

@[rust_type "core::iter::adapters::filter_map::FilterMap"]
inductive core.iter.adapters.filter_map.FilterMap (I : Type) (F : Type) : Type

/-!
The current production caller only obtains shared, read-only views from
`core::cell::Ref`; it never writes through a data guard.  In the focused
borrow-ready entry-state model below, the guard carries exactly the viewed
value.  The literal `RefCell` dynamic-borrow check remains an explicit Solana
entry-state/platform boundary; it is not silently translated as infallible for
arbitrary host calls.
-/
@[reducible, rust_type "core::cell::Ref"]
def core.cell.Ref (T : Type) := T

@[rust_type "core::slice::iter::Windows"]
structure core.slice.iter.Windows (T : Type) where
  slice : Slice T
  width : Std.Usize
  index : Nat

@[reducible, rust_type "solana_account_info::AccountInfo" (mutRegions := #[0])]
def solana_account_info.AccountInfo :=
  V7LiteralCallerReadonlyMetadataHelperCurrent309bR1.solana_account_info.AccountInfo

/- `solana_pubkey.Pubkey` is supplied by the imported literal helper model. -/
