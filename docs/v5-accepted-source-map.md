# Accepted V5 execution: source and proof map

This page is the short review path through the production V5 spend. It exists
because the main verifier file is intentionally frozen and large. Refactoring
that deployed source would make it easier to read, but it would also break the
exact source and program identity recorded by the release.

The number `67` is only the instruction byte used by the dispatcher. It is not
a separate cryptographic idea. The rows below call it the **released V5
spend**.

## Fifteen review stops

| Order | Production function or call | What an accepted execution establishes | Proof or evidence to inspect |
| ---: | --- | --- | --- |
| 1 | `process_spend_production_instruction` → `process_v5_full_cu_transaction_with_verifier` | Selects the released V5 spend, decodes the exact 169-byte public input, and supplies the production proof checker as the callback. | `programs/aspis-verifier/src/dispatch.rs`, `v5_full_transaction.rs`; `V5CurrentInstructionAndClose.current_rust_success_requires_bump_255` records the current instruction model and its explicit Rust-equality boundary. |
| 2 | `verify_and_apply_atomic_payment_state_with_required_nullifier_bump` | Checks account roles, owners, signer and writable flags, pool state, distinct accounts, and the nullifier address with bump 255. It calls the proof checker before committing the marker and pool updates. | `programs/aspis-verifier/src/atomic_payment.rs`; `V5ProductionStateBridge.current_rust_success_is_exact` and the hostile-account tests. Compiler and Solana account semantics remain outside Lean. |
| 3 | `verify_uploaded_v5_mode9_cu_fixture` and `exact_uploaded_v5_proof_body` | Requires a sealed proof account and consumes exactly its declared proof body, with no trailing account padding. | `programs/aspis-verifier/src/v5_cu_probe.rs`; released-proof replay and lifecycle tests. The generated accepted-path extraction begins at the parser and composite verifier below. |
| 4 | `parse_probe_data` | Decodes the exact released proof-body layout and rejects an oversized body. | `V5AcceptedEntrySourceBridge.accepted_parse_builds_transcript_projection` and the generated `V5AcceptedEntryGenerated.v5_cu_probe.parse_probe_data`. |
| 5 | `verify_mode9_composite_with_live_statement` | Calls the prefix, terminal, transcript, query, FRI, and relation stages in production order and returns only if every stage succeeds. | `V5AcceptedEntrySourceBridge.accepted_composite_builds_call_chain`; the combined accepted-path replay checks this theorem against one extraction of the production source. |
| 6 | `verify_v5_wire_prefix` | Checks the fixed header, zero reserve, roots, live-statement digest, ten-round sumcheck, transcript prefix, batch work, and nonzero batching values. | `V5TranscriptPrefixExtractionBridge.normalized_generated_successful_prefix_trace_eq_typed_schedule` and `V5AcceptedPrefixWorkBridge.accepted_prefix_proves_batch_work`. |
| 7 | `verify_mode9_atomic_terminal_with_prefix` | Checks the private-spend terminal values against the live statement and the challenges returned by the prefix stage. | `V5AcceptedSpendRelation.lean` and the terminal bridge modules indexed by `AspisFormal/README.md`. The combined caller theorem exposes the exact production call and successful result. |
| 8 | `replay_real_v5_relation_rounds` | Replays four relation rounds, including two sampled points per round, each relation message, four fold-work checks, four fold challenges, and later roots. | The generated body in the combined accepted-path extraction, `V5TranscriptSourceAdapter`, and the accepted-work projection theorem. |
| 9 | `derive_v5_selected_good_queries_from_transcript` | Binds the final polynomial, checks final work, binds the selected schedule, derives 18 distinct query positions, and accepts only a schedule that passes the two public goodness checks. | `V5TranscriptConnection`, `V5QuerySamplerControl`, and the combined accepted-path work/query bridge. |
| 10 | `decode_v5_fri_alphas` | Decodes the four field challenges consumed by both the FRI and relation checks. | `V5AcceptedEntryAlphaDecode.decode_v5_fri_alphas_success_calls`. |
| 11 | `verify_mode9_fri_phase` | Calls private-opening authentication, prepares the four point claims, and runs the full FRI checker with the decoded challenges and final polynomial. | `V5AcceptedEntryFriPhaseBridge.accepted_fri_phase_builds_exact_call`. |
| 12 | `verify_v5_private_suffix` → `verify_v5_private_openings` | Authenticates the five opening sections against the five roots at the transcript-derived positions and checks that the returned C1/C2 records are the records consumed later. | `V5MerkleRustBridge.verifyV5_sourceEquality_implies_RustAcceptedOpeningYieldsForest` plus the exact caller bridge. SHA-256 collision resistance remains a cryptographic assumption. |
| 13 | `prepare_v5_pcs_claims` | Decodes the 4 × 19 claim table and combines each row with the exact powers of the transcript challenge. | `V5PreparedPointClaimsSourceBridge.sourcePreparedPointClaim_eq_sourcePointClaim` and the pinned preparation-loop replay. |
| 14 | `check_v5_fri_queries` | Checks all 18 layer-zero openings and every later fold through the four-coefficient final polynomial. | `V5FriProductionDecoderEquality.productionDecoderReferenceEquality`, the coordinate-source proofs, and `V5FriAcceptedForestChecks.accepted_production_execution_yields_released_forest_fri_checks`. |
| 15 | `verify_mode9_relation_phase` and return to the atomic state wrapper | Checks the four relation rounds against the same final polynomial. Only after the composite verifier returns success can the atomic wrapper write the nullifier marker and new pool state. | `V5RelationAcceptanceSourceProof.extracted_mode9_success_implies_final_polynomial_match`, `V5RelationFullSourceProof.generated_complete_relation_success_exact`, and the state bridge in row 2. |

## How to read the proof claims

There are three different kinds of support in the last column:

1. A **generated-source theorem** reasons about Lean produced from selected
   production Rust by Charon and Aeneas.
2. A **model theorem** proves the mathematics used by that code.
3. A **runtime or release check** covers behavior that is not proved in Lean,
   such as Solana account handling or the identity of the deployed program.

The end-to-end replay joins the generated-source and model theorems. It does
not prove Charon, Aeneas, Lean, `rustc`, LLVM, the Solana build tools, SHA-256,
Poseidon2, or the Solana runtime. Those remaining assumptions are listed in
[`assumptions-ledger.md`](assumptions-ledger.md).

## Primary files

- Production transaction shell:
  `programs/aspis-verifier/src/{dispatch,v5_full_transaction,atomic_payment}.rs`
- Production verifier:
  `programs/aspis-verifier/src/v5_cu_probe.rs`
- Full FRI loops:
  `programs/aspis-verifier/src/v5_fri_checks.rs`
- Combined generated accepted path and direct caller proofs:
  `aeneas-verif/v5-result-aware-source-link-20260821/`
- Mathematical proof project: `AspisFormal/`
- Exact Rust-to-Lean theorem index: `aeneas-verif/README.md`
