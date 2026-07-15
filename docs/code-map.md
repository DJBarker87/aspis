# Code map

Where each concept lives. File names are stable; functions are named so
`rg`/IDE search lands directly.

## The spend transaction, end to end

| Step | Code |
| --- | --- |
| SBF entrypoint and tag dispatch | `programs/aspis-verifier/src/dispatch.rs` — `process_spend_production_instruction`; the accepted wire tags are documented on the function |
| Wire format (frozen instruction tags) | `programs/aspis-verifier/src/wire.rs` — `AspisInstruction`; variant order is the wire encoding and is frozen |
| Proof-account lifecycle (create, upload, finalize, close) | `programs/aspis-verifier/src/lifecycle.rs` |
| Verify-and-apply (tag 65): ordering, atomicity, refund | `programs/aspis-verifier/src/atomic_payment.rs` — `verify_and_apply_atomic_payment_state_with_proof_refund`; validation and complete proof verification precede every write |
| Statement decode and verify closures (tags 59/60/65) | `programs/aspis-verifier/src/verify.rs` |
| Complete proof verifier | `crates/aspis-statement/src/state_only_spend.rs` — `verify_atomic_state_only_spend_v3_with_inverse` |

## Cryptographic core (`crates/aspis-core`)

| Concept | Code |
| --- | --- |
| M31 / CM31 / QM31 field tower | `field.rs` |
| SHA-256 Fiat–Shamir transcript (byte-exact host/SBF) | `transcript.rs` — `absorb`, `squeeze_block`, `challenge_queries_without_replacement`, `grinding_ok` |
| Frozen protocol constants | `params.rs` |
| Circle-domain point math | `circle.rs` |
| Proof envelope (fixed layout) | `proof.rs` |
| Parser and transcript-prefix schedule | `circle_prefix.rs`, `state_only_prefix.rs` |
| Fold arithmetic and query fibers | `circle_fri.rs` — `derive_query_fold_inverses_for_circle`; `circle_query.rs`, `state_only_spend_query.rs` |
| Merkle openings (five-tree, salted, private) | `merkle.rs`, `circle_merkle.rs`, `circle_line_merkle.rs`, `state_only_private_merkle.rs`, `state_only_private_openings.rs`, `state_only_spend_openings.rs` |
| Zerocheck sumcheck wires | `sumcheck.rs`, `statement_sumcheck.rs`, `state_only_sumcheck.rs` |
| Masking algebra (hiding) | `state_only_hiding.rs`, `statement_hiding.rs`, `state_only_masked_switch.rs` |
| Zero-factor D-lane relation | `state_only_spend_relation.rs` |

## Statement and relation (`crates/aspis-statement`)

| Concept | Code |
| --- | --- |
| Public statement binding | `atomic_statement.rs` — `AtomicPaymentStatementV3`, `atomic_payment_statement_digest_v3` |
| Spend semantics: commitments, nullifiers, value limit | `spend.rs` |
| Poseidon2 permutation (width 16, 22 rounds) | `poseidon2.rs` |
| Generated terminal/routing evaluators and constants | `state_only_terminal.rs`, `atomic_state_only_terminal.rs` and their `*_constants` includes |
| Range/lookup argument construction (host) | `logup.rs` |
| Host trace and constraint system | `state_only_trace.rs`, `state_only_constraints.rs`, `atomic_state_only_trace.rs`, `atomic_state_only_registry.rs` |

## Prover and security calculators (`crates/aspis-prover`)

| Concept | Code |
| --- | --- |
| Production proof builder | `src/state_only_spend.rs` — `build_hiding_atomic_state_only_spend_proof_v3` |
| Grinding (batch/fold/final work) | `src/pow.rs` — `find_grinding_nonce`; GPU miner in `tools/aspis-pow-metal.swift` |
| GoodSpend predicate and selector | `src/state_only_good_spend.rs` |
| Hiding rank certificates (affine-image simulator) | `src/state_only_hiding_rank/` |
| Soundness/hiding ledger calculator | `examples/spend_soundness_epro_ledger.rs` (`-- --calculation-only`) |
| Release proof + statement fixtures and end-to-end KAT | `fixtures/`, `tests/spend_release_kat.rs` |

## Release and deployment (`xtask`)

| Concept | Code |
| --- | --- |
| Release certificate gates | `src/spend_release.rs` — `evaluate`; command `spend-release` |
| Local-validator measurement | `src/spend_measure.rs`; command `spend-measure` |
| Devnet / mainnet executors, cleanup, journal, loader | `src/spend_devnet*.rs`, `src/spend_mainnet*.rs` |
| Statement digests and sidecar schema | `src/spend_statement.rs` |

## Naming conventions

- **spend** — the released protocol (internally numbered during research;
  the archived trees keep the old numbering).
- **state_only** — the relation family that proves the atomic public state
  transition (anchor, nullifier, sequence) under a shared private Merkle
  path.
- **v3** — the third and current atomic statement layout.
- **GoodSpend** — the machine-checked public predicate over the Fiat–Shamir
  schedule whose rank conditions certify the hiding simulator.
- **q18 / g37** — 18 queries per fold branch; 37-bit batch grinding.
- **Wire tags** — append-only instruction bytes; production accepts
  0/1/59/60/62/63/64/65 and everything else fails closed before account
  access.
