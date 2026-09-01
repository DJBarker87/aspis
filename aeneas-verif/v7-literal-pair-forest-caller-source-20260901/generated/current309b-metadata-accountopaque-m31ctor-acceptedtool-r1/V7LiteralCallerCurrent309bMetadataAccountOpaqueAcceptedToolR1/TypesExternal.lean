import Aeneas
import V7LiteralCallerReadonlyMetadataHelperCurrent309bR1.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-!
Executable replacements for the seven external type templates in the accepted
whole-caller translation.  Only `AccountInfo` participates in the metadata
bridge below; the five iterator/container types are opaque-to-this-root carrier
types, represented as empty inductives rather than logical axioms.
-/
@[rust_type "core::array::iter::IntoIter"]
inductive core.array.iter.IntoIter (T : Type) (N : Std.Usize) : Type

@[rust_type "core::iter::adapters::flatten::Flatten"]
inductive core.iter.adapters.flatten.Flatten (I : Type) (Clause0_Item : Type)
    (Clause1_Item : Type) (Clause1_IntoIter : Type) : Type

@[rust_type "core::iter::adapters::filter_map::FilterMap"]
inductive core.iter.adapters.filter_map.FilterMap (I : Type) (F : Type) : Type

@[rust_type "core::cell::Ref"]
inductive core.cell.Ref (T : Type) : Type

@[rust_type "core::slice::iter::Windows"]
inductive core.slice.iter.Windows (T : Type) : Type

@[reducible, rust_type "solana_account_info::AccountInfo" (mutRegions := #[0])]
def solana_account_info.AccountInfo :=
  V7LiteralCallerReadonlyMetadataHelperCurrent309bR1.solana_account_info.AccountInfo

/- `solana_pubkey.Pubkey` is supplied by the imported literal helper model. -/
