# Source identity

- workspace HEAD: `27e8265d28de88e7967626a2d2432ef161fb4f49`
- exact status: ` M crates/aspis-prover/src/v5_sumcheck_mask.rs`
- source SHA-256: `26ed8e873da039503976fe08dcd26894b847c75007497d290fa74c4c9296319a`
- current source diff SHA-256: `5e54d5bf9ad5095e94eebe277fe868a66384063b7af9e42700da5039af8f6c1f`
- `crates/aspis-prover/src/v5_mask.rs` SHA-256:
  `a1516a5ab348d1e374d908844545054f1fd5647ea12ff56cff273cb1b2b7d05c`
- exact status: ` M crates/aspis-prover/src/v5_mask.rs`
- diff SHA-256: `4170850921b8d54eca1456313de5553a07a75caf20e3e21cd6cea2070eee1de6`
- `crates/aspis-core/src/state_only_sumcheck.rs` SHA-256:
  `5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9`
- exact status: clean
- diff SHA-256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `crates/aspis-core/src/field.rs` SHA-256:
  `dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836`
- exact status: clean
- diff SHA-256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- Charon checkout and binary commit:
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas checkout and binary commit:
  `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust: `nightly-2026-06-01`
- generated backend: Lean 4.31; retained compatibility replay: Lean 4.32.0

The LLBC embeds and replay-compares the exact two owning-package sources
`v5_sumcheck_mask.rs` and `v5_mask.rs`.  Charon records source filenames and
exact spans, but null contents, for cross-crate `state_only_sumcheck.rs` and
`field.rs`; replay therefore binds those two files by the hashes above without
claiming embedded-byte identity.
