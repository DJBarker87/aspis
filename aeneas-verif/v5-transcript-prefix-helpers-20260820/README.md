# V5 transcript-prefix helper source proofs

This bundle removes four helper-call assumptions from the production V5
transcript-prefix proof.

Charon extracts the unchanged Rust helpers and the patched Aeneas translator
produces Lean definitions. The Lean proofs establish the exact successful
behavior of:

- the layer-zero commitment-root absorb;
- the second commitment-root absorb;
- the masked-sumcheck claim absorb and nonzero challenge; and
- the 37-bit batch-work check followed by its nonce absorb.

The proofs cover exact labels, byte order, root/salt concatenation, the
`(degree = 27, rounds = 10)` mask-claim header, little-endian nonce bytes, and
the check-before-absorb control flow. They are universal source proofs, not
tests of the released proof.

The transcript methods themselves use explicit observation definitions here.
Their real hash inputs and state changes are proved separately in
`../v5-transcript-primitives-20260820/`. SHA-256 security is not claimed by
this bundle.

Two prefix helpers remain to be joined: the zerocheck challenge setup and the
ten-round semantic sumcheck. The extraction harness already exposes the
zerocheck entry point; its mutable-array loop currently needs one more Aeneas
translation fix.
