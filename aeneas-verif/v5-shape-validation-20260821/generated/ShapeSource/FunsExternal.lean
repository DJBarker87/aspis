import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import ShapeSource.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::copied"]
def core.iter.traits.iterator.Iterator.copied.default
    {Self : Type} {T : Type} {Clause2_Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self T)
    (_copy : core.marker.Copy T)
    (_copiedIterator : core.iter.traits.iterator.Iterator Self Clause2_Item) :
    Self → Result (core.iter.adapters.copied.Copied Self) :=
  fun self => .ok self

@[rust_fun
  "core::iter::adapters::copied::{core::iter::traits::iterator::Iterator<core::iter::adapters::copied::Copied<@I>, @T>}::next"]
def core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.next
    {I : Type} {T : Type}
    (iterator : core.iter.traits.iterator.Iterator I T)
    (_copy : core.marker.Copy T) :
    core.iter.adapters.copied.Copied I →
      Result (Option T × core.iter.adapters.copied.Copied I) :=
  iterator.next

end Aeneas.Std

namespace V5ShapeValidationSource

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

end V5ShapeValidationSource
