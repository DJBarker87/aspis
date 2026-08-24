# Code map

This map follows the current V5 path from the private-spend rules to
the finalized mainnet transaction. Paths are relative to the repository root.

## Follow the evidence

| Question | Start here |
| --- | --- |
| What does a valid private spend mean? | `crates/aspis-statement/src/spend.rs`, `crates/aspis-statement/src/atomic_statement.rs` |
| Where is the mathematics checked? | `AspisFormal/README.md`, then the modules under `AspisFormal/AspisFormal/` |
| Where is selected production Rust connected to Lean? | `aeneas-verif/README.md` and the pinned packages it indexes |
| What exactly does an accepted V5 execution call? | `docs/v5-accepted-source-map.md` |
| Where is the V5 Solana path? | `programs/aspis-verifier/src/dispatch.rs`, `v5_full_transaction.rs`, and `v5_cu_probe.rs` |
| Where is the exact V5 program recorded? | `release/aspis-v5-tag67-frozen-candidate-v1/` |
| Where is the finalized V5 mainnet lifecycle recorded? | `release/aspis-v5-tag67-mainnet-v1/` and `docs/v5-mainnet-demo.md` |

## Mathematical construction

| Concept | Code or proof |
| --- | --- |
| Public statement, deployment binding, and digest | `crates/aspis-statement/src/atomic_statement.rs` |
| Spend semantics, commitments, nullifier, and value rule | `crates/aspis-statement/src/spend.rs` |
| Poseidon2 permutation | `crates/aspis-statement/src/poseidon2.rs` |
| Maintained Lean development | `AspisFormal/AspisFormal/` |
| Lean theorem and assumption status | `AspisFormal/README.md` |
| Current formal result and security boundary | `paper/aspis-formalization/` |
| Earlier construction and deployment paper | `paper/aspis-spend/` |

## Proof system and prover

| Concept | Code |
| --- | --- |
| M31/CM31/QM31 fields and circle domain | `crates/aspis-core/src/field.rs`, `circle.rs` |
| Fiat–Shamir transcript and grinding predicate | `crates/aspis-core/src/transcript.rs` |
| Proof format and parser | `crates/aspis-core/src/proof.rs`, `circle_prefix.rs`, `state_only_prefix.rs` |
| Circle folds and query paths | `crates/aspis-core/src/circle_fri.rs`, `circle_query.rs` |
| Merkle openings | `crates/aspis-core/src/*merkle*.rs`, `state_only_*openings.rs` |
| Sumcheck and relation arithmetic | `crates/aspis-core/src/*sumcheck*.rs`, `state_only_spend_relation.rs` |
| V5 production proof builder | `xtask/src/v5_cu_probe.rs`, `build_v5_runtime_bound_production_demo_proof_body` |
| V5 mainnet proof orchestration and grinding | `xtask/src/spend_devnet/v5.rs` |
| Historical q18/g37 prover and grinding | `crates/aspis-prover/src/state_only_spend.rs`, `pow.rs` |
| Security and hiding calculators | `crates/aspis-prover/examples/spend_soundness_epro_ledger.rs`, `crates/aspis-prover/src/state_only_hiding_rank/` |

## Selected Rust-to-Lean connection

| V5 scope | Principal record |
| --- | --- |
| Current theorem map and pinned extraction packages | `aeneas-verif/README.md` |
| One successful production proof-checker execution | `aeneas-verif/v5-result-aware-source-link-20260821/` |
| Exact transcript operations and six work checks | `aeneas-verif/v5-result-aware-source-link-20260821/proof/` |
| Five private-opening trees and FRI checks | `aeneas-verif/v5-merkle-unchanged-full-20260820/`, `aeneas-verif/v5-fri-consumer-exact-20260815/` |
| Four relation rounds and final check | `aeneas-verif/v5-relation-acceptance-20260815/`, `aeneas-verif/v5-relation-full-source-20260820/` |
| Plain-language scope and remaining boundaries | `docs/formal-verification.md` |

The current accepted-path work starts with a successful translated call to
the production proof checker. It derives the parser, transcript, work, query,
private-opening, FRI, decoded claim table, initial relation value, and
relation tail used by the mathematical security argument from that same
execution. The general and compact final-dot equalities still have to be
proved before the outer theorem is complete. This is not a proof of every
Rust function, the compiler, or the Solana runtime.

## V5 Solana transaction

| Step | Production code |
| --- | --- |
| Entrypoint and instruction dispatch | `programs/aspis-verifier/src/dispatch.rs`, `process_spend_production_instruction` |
| Instruction encoding | `programs/aspis-verifier/src/wire.rs`, `AspisInstruction` |
| Proof-account create, upload, seal, and close | `programs/aspis-verifier/src/lifecycle.rs` |
| V5 account checks and atomic state update | `programs/aspis-verifier/src/v5_full_transaction.rs`, `process_v5_full_cu_transaction_with_verifier` |
| Complete V5 verifier used by the dispatcher | `programs/aspis-verifier/src/v5_cu_probe.rs`, `verify_uploaded_v5_mode9_cu_fixture` |
| Shared account-distinctness and state guards | `programs/aspis-verifier/src/atomic_payment.rs` |

The production path validates account order, signer/writable requirements,
owners, distinctness, pool state, and the program-derived nullifier account before writing.
It verifies the proof and then rechecks mutable state before committing.

## Mainnet execution and cleanup

| Operation | Tooling |
| --- | --- |
| V5 artifact and read-only readiness gates | `xtask/src/spend_devnet/v5.rs`; `v5-mainnet-artifact`, `v5-mainnet-readiness` |
| Crash-resumable executor | `xtask/src/spend_devnet/v5.rs`; `v5-mainnet-execute` |
| Hash-chained signed-wire journal | `xtask/src/spend_mainnet_journal.rs` |
| Retained proof-account close | `xtask/src/spend_mainnet_v5_close.rs`; `v5-mainnet-proof-close` |
| ProgramData close to pinned recipient | `xtask/src/spend_mainnet_cleanup.rs`; `spend-mainnet-cleanup` |
| Final payer sweep | `xtask/src/v5_mainnet_refund.rs`; `v5-mainnet-payer-sweep` |

The frozen program and build provenance are in
`release/aspis-v5-tag67-frozen-candidate-v1/`. The sanitized proof, statement,
receipts, and refund reconciliation are in
`release/aspis-v5-tag67-mainnet-v1/`.

## Tests and review entry points

| Review target | Start here |
| --- | --- |
| Malicious account aliasing and state mutation | `programs/aspis-verifier/src/atomic_payment.rs` test modules |
| V5 dispatch and atomic behavior | `programs/aspis-verifier/src/dispatch.rs`, `v5_full_transaction.rs` tests |
| Proof-account lifecycle | `programs/aspis-verifier/src/lifecycle.rs` tests |
| Mainnet recovery rules | `xtask/src/spend_mainnet_journal.rs`, `spend_devnet/v5.rs` tests |
| Security assumptions | `docs/assumptions-ledger.md` |
| Release preflight and runtime envelope | `release/preflight/v5-production-freeze.md` |

## Repository directories

| Directory | Purpose |
| --- | --- |
| `AspisFormal/` | Lean mathematical development |
| `aeneas-verif/` | Charon/Aeneas output and bridge proofs |
| `crates/` | Shared proof system, statement, and prover |
| `programs/` | Solana verifier program |
| `xtask/` | Release, deployment, recovery, and cleanup tooling |
| `release/` | Frozen and finalized public bundles |
| `results/` | Measurements and build/runtime evidence |
| `docs/` | Explanations, reviews, assumptions, and history |
| `paper/` | Full construction and security argument |

## Historical q18/g37 path

The earlier Tag-65 implementation remains available for historical
reproduction in `release/aspis-spend-q18-g37-mainnet-v1/` and
`docs/mainnet-demo.md`. Its principal verify-and-refund path is
`programs/aspis-verifier/src/atomic_payment.rs`. V5 is the current release and
the organizing path of this map.
