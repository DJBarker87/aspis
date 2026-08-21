import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std

/-- Rust's `Copied<I>` has exactly the iterator state of `I`; copying changes
the yielded item, not the iterator representation. -/
@[reducible, rust_type "core::iter::adapters::copied::Copied"]
def core.iter.adapters.copied.Copied (I : Type) : Type := I

end Aeneas.Std
