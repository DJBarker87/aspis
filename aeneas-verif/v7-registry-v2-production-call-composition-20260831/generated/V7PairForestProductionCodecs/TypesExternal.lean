-- Transparent model for the sole Rust core-library adapter type left outside
-- the focused production ASQ8/ASR8 extraction.
import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-- Logical state of Rust's `Flatten<I>`.  `outer` is the source iterator and
`inner` is the currently active iterator, if an outer item has already been
converted with `IntoIterator`.  The two item parameters are phantom in Rust as
well; retaining them gives the generated declaration its exact type. -/
@[rust_type "core::iter::adapters::flatten::Flatten"]
structure core.iter.adapters.flatten.Flatten
    (I : Type) (_Clause0Item : Type) (_Clause1Item : Type)
    (Clause1IntoIter : Type) where
  outer : I
  inner : Option Clause1IntoIter
