# Exact V5 FRI transition decoders

This bundle universally checks the two unchanged production decoders used by
the later FRI layers against loop-free Rust reference functions.  The
references preserve the production decoder's complete result and validation
order, but can also be translated by Charon/Aeneas and proved against exact
field semantics in Lean.

The Kani checks cover every 64-byte leaf, every layer byte, and every selected
slot below four.  They are not tests of the released proof fixture.

The production functions are:

- `decode_later_leaf`; and
- `decode_selected_later_slot`.

The production source is unchanged.  The small `formal_decode_*` functions in
`aspis-core` only expose those private functions when the
`formal-verification` feature is enabled; the deployed verifier does not
enable that feature.

## Pinned subject and tools

- `circle_query.rs` Git blob: `085f0d082d9d2fe61d46ceb69f4a2b06bc6a0727`
- Kani: `cargo-kani 0.67.0`
- Bitwuzla: `0.9.1`

Run `./verify.sh` from this directory.  The proof relies on the correctness of
Rust-to-MIR compilation, Kani/CBMC translation, and Bitwuzla.  That is an
explicit toolchain boundary, not a cryptographic probability assumption.
