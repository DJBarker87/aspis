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
| Full construction and reductions | `paper/aspis-spend/` |

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
| Component A/B/C integration | `aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean` |
| Component-C runtime rounds and public output | `aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean` |
| V5 work-byte reads and ordered checks | `aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean` |
| Plain-language scope and remaining boundaries | `docs/formal-verification.md` |

The final composition theorem is
`FormalClosureStream1.current_source_combined_capstone`. It packages the listed
selected paths under successful-call, valid-input, and explicit
execution/model hypotheses. It is neither a proof of every Rust function nor
a theorem that arbitrary verifier acceptance implies the complete spend
relation.

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
