# Code map

Where each concept lives. File names are stable; functions are named so
`rg`/IDE search lands directly.

## The spend transaction, end to end

| Step | Code |
| --- | --- |
| SBF entrypoint and tag dispatch | `programs/aspis-verifier/src/dispatch.rs`, `process_spend_production_instruction`; the accepted wire tags are documented on the function |
| Wire format (frozen instruction tags) | `programs/aspis-verifier/src/wire.rs`, `AspisInstruction`; variant order is the wire encoding and is frozen |
| Proof-account lifecycle (create, upload, finalize, close) | `programs/aspis-verifier/src/lifecycle.rs` |
| Verify-and-apply (tag 65): ordering, atomicity, refund | `programs/aspis-verifier/src/atomic_payment.rs`, `verify_and_apply_atomic_payment_state_with_proof_refund`; validation and complete proof verification precede every write |
| Statement decode and verify closures (tags 59/60/65) | `programs/aspis-verifier/src/verify.rs` |
| Complete proof verifier | `crates/aspis-statement/src/state_only_spend.rs`, `verify_atomic_state_only_spend_v4_with_inverse` |
| Account-distinctness matrix (production guard) | `programs/aspis-verifier/src/atomic_payment.rs`, `validate_accounts_and_state`; pairwise distinctness over {proof, pool, nullifier, payer}, PDA-seed and owner checks, and the post-verification recheck |

### Adversarial account aliasing

Explicit adversarial evidence that the atomic verifier rejects hostile account
arrangements before any state write lives in
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
| Soundness/hiding ledger calculator | `examples/spend_soundness_epro_ledger.rs` (`-- --calculation-only`) |
| Release proof + statement fixtures and end-to-end KAT | `fixtures/`, `tests/spend_release_kat.rs` |

## Release and deployment (`xtask`)

| Concept | Code |
| --- | --- |
| Release certificate gates | `src/spend_release.rs`, `evaluate`; command `spend-release` |
| Local-validator measurement | `src/spend_measure.rs`; command `spend-measure` |
| Devnet / mainnet executors, cleanup, journal, loader | `src/spend_devnet*.rs`, `src/spend_mainnet*.rs` |
| Statement digests and sidecar schema | `src/spend_statement.rs` |

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
- **Wire tags**: append-only instruction bytes; production accepts
  0/1/59/60/62/63/64/65 and everything else fails closed before account
  access.
