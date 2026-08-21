# Exact V5 FRI 16-column dot-product check

This bundle checks the one production FRI arithmetic helper that the pinned
Charon/Aeneas toolchain cannot translate because its iterator loans do not
currently join.

The subject is the unchanged production function
`qm31_m31_dot4_prepared_limbs_4b_bytes::<16>` in
`crates/aspis-core/src/field.rs`. The check covers every prepared-limb array in
the stated M31 range and every 256-byte input, not only the released proof.

Three separate harnesses establish:

1. the complete production `Option<[QM31; 4]>` equals the fixed-index
   `indexed_dot16` result for every input;
2. the production function accepts exactly when all 64 input words are
   canonical M31 encodings, with all safety and unwind checks enabled; and
3. the fixed-index function has the same exact acceptance condition, with all
   safety and unwind checks enabled.

The fixed-index function is deliberately ordinary Rust that can also be
translated by Charon/Aeneas. It is therefore the bridge between the unchanged
production helper and the Lean arithmetic proof; it is not a replacement
production implementation.

## Pinned subject and tools

- production `field.rs` Git blob: `a28ff94de05265102ca819849805a7f73c675800`
- production `field.rs` SHA-256: `dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836`
- Kani: `cargo-kani 0.67.0`
- Bitwuzla: `0.9.1`
- Kissat: `4.0.4`

Run `./verify.sh` from this directory. The proof relies on the correctness of
Rust-to-MIR compilation, Kani/CBMC translation, and the named SAT/SMT solvers.
That is an explicit toolchain boundary; it is not a cryptographic assumption or
a probability term.
