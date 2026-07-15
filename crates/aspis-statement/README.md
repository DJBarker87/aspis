# aspis-statement

The shielded-spend relation and its public statement encoding: the
`AtomicPaymentStatementV3` binding, spend semantics (commitments,
nullifiers, value limit), the Poseidon2 permutation, the generated terminal
evaluators, and the complete proof verifier
(`state_only_spend::verify_atomic_state_only_spend_v3_with_inverse`) that
the on-chain program calls. Host-only modules (trace, constraints, LogUp
construction) build and check the same relation off-chain.

Concept-to-file index: [docs/code-map.md](../../docs/code-map.md).
