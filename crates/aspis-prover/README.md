# aspis-prover

Host-only prover and security calculators: the production proof builder,
grinding (CPU here, Metal GPU miner under `tools/`), the GoodSpend
predicate, the hiding rank certificates, and the soundness/hiding ledger
calculator (`examples/spend_soundness_epro_ledger.rs`).

`fixtures/` holds the release-certified proof and statement;
`tests/spend_release_kat.rs` verifies them end-to-end through the production
verifier and is run by CI.

Concept-to-file index: [docs/code-map.md](../../docs/code-map.md).
