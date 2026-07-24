# aspis-verifier

The default on-chain program exposes the frozen q18/g37 routes and the V5
Tag-67 production route:

- `wire.rs`: append-only instruction tags;
- `dispatch.rs`: minimal production entrypoint;
- `lifecycle.rs`: proof-account create, upload, finalize, and close;
- `verify.rs`: q18/g37 statement decode and verification;
- `v5_cu_probe.rs`: strict V5 Mode-9 verifier used by production Tag 67;
- `v5_full_transaction.rs`: Tag-67 public-input decode and atomic wrapper; and
- `atomic_payment.rs`: verify-before-write pool/nullifier transition.

The default build accepts tags 0/1/59/60/62/63/64/65/67. Tag 66 and every
other diagnostic or historical tag fail before account access. Tag 65 closes
and refunds its proof account; Tag 67 retains the sealed proof account.

Build with `cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml`.

Concept-to-file index: [docs/code-map.md](../../docs/code-map.md).
The exact V5 binary, mainnet CU policy, provenance, and formal gate are
recorded in [the production freeze](../../release/preflight/v5-production-freeze.md).
