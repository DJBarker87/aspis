# aspis-verifier

The on-chain program: `wire.rs` (frozen instruction tags), `dispatch.rs`
(entrypoint; production accepts tags 0/1/59/60/62/63/64/65, everything else
fails closed), `lifecycle.rs` (proof-account create/upload/finalize/close),
`verify.rs` (statement decode and verify closures), and
`atomic_payment.rs` (the tag-65 verify-and-apply state transition;
validation and complete proof verification precede every write, and the
transition is atomic with the proof-account rent refund).

Build with `cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml`.

Concept-to-file index: [docs/code-map.md](../../docs/code-map.md).
