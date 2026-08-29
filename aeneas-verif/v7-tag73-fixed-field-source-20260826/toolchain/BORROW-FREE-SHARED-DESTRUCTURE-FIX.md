# Borrow-free shared-value destructuring identity

The production `WeightAccumulator::weight_at` caller reached Aeneas's Pure
backend but failed because a nested-loop input contained an unregistered fresh
`Vec<WeightComponent>` symbolic value.

The value was introduced while `destructure_abs` flattened an immutable nested
shared loan. After `list_values` removed nested loans, the value contained no
borrow. Freshening its symbolic ids therefore created no new alias or write-back
obligation; it only introduced a bookkeeping identity in a context where the
fixed-point pass deliberately performs no synthesis.

`aeneas-d860ac47-borrow-free-shared-destructure-identity.patch` preserves the
existing symbolic identity only when `tvalue_has_borrows` is false. Values which
still contain shared or mutable borrows retain the original freshening rule.
Production Rust, the Tag-73 relation, transcript ordering, field arithmetic and
generated result semantics are unchanged.

The focused frozen caller LLBC has SHA-256
`f3a0a653484cb6d372910ad43d6e7442bbeb0ae485d81d6ebee6a0b81b98e89a`.
With the patch it completed Rust-to-Lean generation in 9.48 seconds at
295,772 KiB peak RSS with zero swap. The generated `Types`, `FunsExternal` and
`Funs` modules then compiled with Lean 4.31.0 against the pinned Aeneas runtime.
