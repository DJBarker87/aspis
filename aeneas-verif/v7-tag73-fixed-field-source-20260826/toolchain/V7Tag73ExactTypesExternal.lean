import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error

@[rust_type "core::array::iter::IntoIter"]
structure core.array.iter.IntoIter (T : Type) (N : Std.Usize) where
  array : Array T N
  index : Nat := 0

@[rust_type "core::iter::adapters::filter_map::FilterMap"]
structure core.iter.adapters.filter_map.FilterMap (I : Type) (F : Type) where
  iter : I
  f : F

@[rust_type "core::mem::maybe_uninit::MaybeUninit"]
inductive core.mem.maybe_uninit.MaybeUninit (T : Type) where
  | uninit
  | init (value : T)

@[rust_type "core::slice::iter::Windows"]
structure core.slice.iter.Windows (T : Type) where
  slice : Slice T
  width : Std.Usize
  index : Nat
