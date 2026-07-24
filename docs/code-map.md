# Code map

Where each concept lives. File names are stable; functions are named so
`rg`/IDE search lands directly.

## Follow the evidence

| Question | Where to look |
| --- | --- |
| What rules define a valid private spend? | `crates/aspis-statement/src/{spend,atomic_statement}.rs` and the relation modules listed in `AspisFormal/README.md` |
| Where are those rules and release calculations formally checked? | `AspisFormal/`; start with `AspisFormal/README.md` |
| Where is the proof created? | `crates/aspis-prover/src/state_only_spend.rs` |
| Where is the proof checked and state updated on Solana? | `programs/aspis-verifier/src/{dispatch,v5_full_transaction,v5_cu_probe}.rs` |
| Where is selected production Rust translated into Lean? | The pinned Charon/Aeneas extraction snapshots under `aeneas-verif/` |
| Where are the Rust-to-model proofs recorded? | `aeneas-verif/README.md` and the theorem packages it links |
| Where is the exact compiled V5 program recorded? | `release/aspis-v5-tag67-frozen-candidate-v1/` |
| Where is the finalized mainnet execution recorded? | `release/aspis-spend-q18-g37-mainnet-v1/`; the V5 release remains a frozen candidate until its mainnet transaction is recorded |

## The spend transaction, end to end

| Step | Code |
| --- | --- |
| SBF entrypoint and tag dispatch | `programs/aspis-verifier/src/dispatch.rs`, `process_spend_production_instruction`; the accepted instruction tags are documented on the function |
| Instruction byte format | `programs/aspis-verifier/src/wire.rs`, `AspisInstruction`; the variant order defines the frozen byte encoding |
| Proof-account lifecycle (create, upload, finalize, close) | `programs/aspis-verifier/src/lifecycle.rs` |
| Verify-and-apply (tag 65): ordering, atomicity, refund | `programs/aspis-verifier/src/atomic_payment.rs`, `verify_and_apply_atomic_payment_state_with_proof_refund`; validation and complete proof verification precede every write |
| V5 verify-and-apply (tag 67): retained proof, atomic state transition | `programs/aspis-verifier/src/v5_full_transaction.rs`, `process_v5_full_cu_transaction_with_verifier`; the production dispatcher supplies the strict Mode-9 verifier from `v5_cu_probe.rs` |
| Statement decode and verification (tags 59/60/65) | `programs/aspis-verifier/src/verify.rs` |
| q18/g37 complete proof verifier | `crates/aspis-statement/src/state_only_spend.rs`, `verify_atomic_state_only_spend_v4_with_inverse` |
| V5 complete proof verifier | `programs/aspis-verifier/src/v5_cu_probe.rs`, `verify_uploaded_v5_mode9_cu_fixture` |
| Account-distinctness matrix (production guard) | `programs/aspis-verifier/src/atomic_payment.rs`, `validate_accounts_and_state`; pairwise distinctness over {proof, pool, nullifier, payer}, PDA-seed and owner checks, and the post-verification recheck |

### Tests for malicious reuse of accounts

The verifier rejects malicious reuse of one account in multiple roles, often
called account aliasing, before any state write. The tests live in
`programs/aspis-verifier/src/atomic_payment.rs`, test module
`tests::adversarial_account_aliasing` (`rg adversarial_account_aliasing`). Each
test builds one hostile arrangement and asserts the exact error with an
unchanged pool, nullifier, and (on the refund path) lamports. Covered cases:

| Case | Test | Rejecting error |
| --- | --- | --- |
| proof == pool | `rejects_proof_account_aliased_to_pool_without_mutation` | `InvalidArgument` |
| proof == nullifier PDA | `rejects_proof_account_aliased_to_nullifier_pda_without_mutation` | `InvalidArgument` |
| proof == refund destination (payer) | `rejects_proof_account_aliased_to_refund_destination_without_mutation` | `InvalidArgument` |
| pool == nullifier PDA | `rejects_pool_state_aliased_to_nullifier_pda_without_mutation` | `InvalidArgument` |
| payer == pool (writable state) | `rejects_payer_aliased_to_pool_state_without_mutation` | `InvalidArgument` |
| payer == nullifier PDA | `rejects_payer_aliased_to_nullifier_pda_without_mutation` | `InvalidArgument` |
| correct PDA seeds, foreign owner | `rejects_nullifier_pda_with_correct_seeds_but_foreign_owner_without_mutation` | `IncorrectProgramId` |
| nullifier pre-created System-owned with data | `rejects_nullifier_pda_pre_created_system_owned_with_data_without_mutation` | `IncorrectProgramId` |
| pool: correct owner, wrong discriminator | `rejects_pool_state_with_correct_owner_but_wrong_discriminator_without_mutation` | `InvalidAccountData` |
| nullifier: correct owner, wrong discriminator | `rejects_nullifier_marker_with_correct_owner_but_wrong_discriminator_without_mutation` | `InvalidAccountData` |
| nullifier pre-seeded with a foreign marker | `rejects_nullifier_pda_pre_seeded_with_foreign_marker_without_mutation` | `InvalidAccountData` |
| sequence overflow | `rejects_pool_sequence_overflow_before_verification_without_mutation` | `ArithmeticOverflow` |
| pool changed between snapshot and commit | `rejects_pool_mutation_during_verification_via_recheck_without_commit` | `ATOMIC_ERROR_ANCHOR_MISMATCH` |
| nullifier appears between snapshot and commit | `rejects_nullifier_marker_appearing_during_verification_via_recheck_without_commit` | `ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT` |

Refund-recipient substitution after proof sealing is covered separately by
`tests::spend_refund_requires_writable_proof_signer_and_checked_balance`: a rent
drain requires the proof account's own signature, so the recipient cannot be
redirected without it.

## Cryptographic core (`crates/aspis-core`)

| Concept | Code |
| --- | --- |
| M31 / CM31 / QM31 field tower | `field.rs` |
| SHA-256 Fiat–Shamir transcript (byte-exact host/SBF) | `transcript.rs`, `absorb`, `squeeze_block`, `challenge_queries_without_replacement`, `grinding_ok` |
| Frozen protocol constants | `params.rs` |
| Circle-domain point math | `circle.rs` |
| Proof envelope (fixed layout) | `proof.rs` |
| Parser and transcript-prefix schedule | `circle_prefix.rs`, `state_only_prefix.rs` |
| Fold arithmetic and query fibers | `circle_fri.rs`, `derive_query_fold_inverses_for_circle`; `circle_query.rs`, `state_only_spend_query.rs` |
| Merkle openings (five-tree, salted, private) | `merkle.rs`, `circle_merkle.rs`, `circle_line_merkle.rs`, `state_only_private_merkle.rs`, `state_only_private_openings.rs`, `state_only_spend_openings.rs` |
| Zerocheck sumcheck wires | `sumcheck.rs`, `statement_sumcheck.rs`, `state_only_sumcheck.rs` |
| Masking algebra (hiding) | `state_only_hiding.rs`, `statement_hiding.rs`, `state_only_masked_switch.rs` |
| Zero-factor D-lane relation | `state_only_spend_relation.rs` |

## Statement and relation (`crates/aspis-statement`)

| Concept | Code |
| --- | --- |
| Public statement binding | `atomic_statement.rs`, `AtomicPaymentStatementV4`, `atomic_payment_statement_digest_v4` |
| Deployment-domain derivation | `atomic_statement.rs`, `atomic_deployment_domain`; stored per pool at tag-63 init, compared fail-closed by tags 59/60/65 |
| Spend semantics: commitments, nullifiers, value limit | `spend.rs` |
| Poseidon2 permutation (width 16, 22 rounds) | `poseidon2.rs` |
| Generated terminal/routing evaluators and constants | `state_only_terminal.rs`, `atomic_state_only_terminal.rs` and their `*_constants` includes |
| Range/lookup argument construction (host) | `logup.rs` |
| Host trace and constraint system | `state_only_trace.rs`, `state_only_constraints.rs`, `atomic_state_only_trace.rs`, `atomic_state_only_registry.rs` |

## Prover and security calculators (`crates/aspis-prover`)

| Concept | Code |
| --- | --- |
| Production proof builder | `src/state_only_spend.rs`, `build_hiding_atomic_state_only_spend_proof_v3` |
| Grinding (batch/fold/final work) | `src/pow.rs`, `find_grinding_nonce`; GPU miner in `tools/aspis-pow-metal.swift` |
| GoodSpend predicate and selector | `src/state_only_good_spend.rs` |
| Hiding rank certificates (affine-image simulator) | `src/state_only_hiding_rank/` |
| Soundness and hiding calculator | `examples/spend_soundness_epro_ledger.rs` (`-- --calculation-only`) |
| Release proof + statement fixtures and end-to-end KAT | `fixtures/`, `tests/spend_release_kat.rs` |

## Release and deployment (`xtask`)

| Concept | Code |
| --- | --- |
| Release certificate gates | `src/spend_release.rs`, `evaluate`; command `spend-release` |
| Local-validator measurement | `src/spend_measure.rs`; command `spend-measure` |
| V5 mainnet proof, read-only gate, and one-shot executor | `src/spend_devnet/v5.rs`; commands `v5-mainnet-artifact`, `v5-mainnet-readiness`, and `v5-mainnet-execute` |
| q18/g37 devnet/mainnet executor, cleanup, journal, loader | `src/spend_devnet*.rs`, `src/spend_mainnet*.rs` |
| Statement digests and sidecar schema | `src/spend_statement.rs` |

## Formal proof and Rust connection

| Claim layer | Proof entry point |
| --- | --- |
| q18/g37 algebra, finite security calculation, masking, and theft-resistance composition | `AspisFormal/`; status and theorem map in `AspisFormal/README.md` |
| Current Rust-to-Lean proof map | `aeneas-verif/README.md` |
| V5 final A/B/C and Tag-67 integration theorem | `aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`, `FormalClosureStream1.current_source_combined_capstone` |
| Component-C actual four-round evaluator and public packed output | `aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean`, `generated_public_run_output_matches_deployed` |
| Tag-67 work bytes and six-step verifier theorem | `aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean`, `AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure` |
| V5 release SBF, mainnet-runner CU policy, and build record | `release/preflight/v5-production-freeze.md` and `results/spend/v5-production-tag67-freeze-stream3-20260722/` |
| V5 replay on the current mainnet runtime | `results/spend/v5-mainnet-runtime-4.1.0-20260723/` |

## Naming conventions

- **spend**: the released protocol (internally numbered during research;
  the archived trees keep the old numbering).
- **state_only**: the relation family that proves the atomic public state
  transition (anchor, nullifier, sequence) under a shared private Merkle
  path.
- **v4**: the current atomic statement layout (v3 plus the
  deployment-domain field).
- **GoodSpend**: the machine-checked public predicate over the Fiat–Shamir
  schedule whose rank conditions certify the hiding simulator.
- **q18 / g37**: 18 queries per fold branch; 37-bit batch grinding.
- **Instruction tags**: append-only instruction bytes; the default production build
  accepts 0/1/59/60/62/63/64/65/67. Tag 66 and every other diagnostic or
  historical tag fail before account access.
