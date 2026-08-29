# Shared Box dereference compatibility fix

The translated production caller constructs a `Box<[[QM31; 29]; 3]>`, lends
it to the semantic-terminal callback, and later passes a coerced shared
reference to the relation continuation. Rustc's built MIR represents the
second coercion with `copy (*_77)`, where `_77` is a shared reference to the
Box. This is a compiler-generated dereference operation, not a source-level
`Box: Copy` operation.

Pinned Aeneas `d860ac47` rejects every concrete `TBuiltin TBox` encountered by
its `Copy` operand interpreter before checking the boxed value. The patch
permits only this value-model copy when the boxed type is primitively copyable
and the concrete Box contains no borrows. The ordinary Rust `Box` type is not
made `Copy`; mutable, borrowed, or non-copyable contents still fail. No LLBC,
Rust source, generated result branch, or protocol value is changed.

The pre-patch failure is frozen in `evidence/aeneas-box-debug`: source line
1125 is logged as `copy (*_77)`, `_77` is a shared `&Box`, and the box contains
the canonical 3-by-29 QM31 point-claim array.
