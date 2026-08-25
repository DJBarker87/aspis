# Documentation

Aspis V5 combines an end-to-end Lean proof of every successful execution of
the selected deployed verifier path with a reproducible Solana program and a
finalized mainnet archive. For each accepted call, the theorem follows that
single translated Rust execution through
the complete transcript, authentication, FRI, relation, and accumulator data
flow. Its clean Lean 4.32 replay passed on 24 August 2026 over 331 tracked
modules.

## Start here

1. [Formal verification](formal-verification.md) - the headline theorem,
   methodology, proof map, assumptions, and replay command.
2. [How Aspis works](how-it-works.md) - the spend statement, proof upload, and
   atomic state transition.
3. [Accepted V5 source map](v5-accepted-source-map.md) - 15 review stops from
   dispatch to the state update.
4. [V5 mainnet result](v5-mainnet-demo.md) - transaction, program, proof,
   compute, lifecycle, and cleanup identities.
5. [Assumptions ledger](assumptions-ledger.md) - the cryptographic,
   translation, compiler, and runtime interfaces used by the claims.
6. [Code map](code-map.md) - concepts and proof claims mapped to deployed
   files.
7. [Formalization paper](../paper/aspis-formalization/) - the arXiv/IACR
   manuscript and artifact manifest.
8. [Reproduction commands](../README.md#reproduce-the-result) - separate
   checks for Lean, the accepted Rust path, SBF identity, and chain evidence.

## Evidence map

| Result | Record |
| --- | --- |
| Private-spend mathematics and release arithmetic | [`AspisFormal/`](../AspisFormal/) |
| End-to-end selected accepted verifier path | [`aeneas-verif/`](../aeneas-verif/) |
| Exact V5 SBF and pinned build inputs | [V5 preflight](../release/preflight/v5-production-freeze.md) |
| Finalized V5 transaction and cleanup | [mainnet bundle](../release/aspis-v5-tag67-mainnet-v1/) |
| Reconstruction of closed proof and program accounts | [full payer RPC archive](../release/aspis-v5-tag67-mainnet-rpc-archive-v1/) |

The central theorem is
`AspisV5AcceptedOneRunDeterministicFinal.accepted_composite_security_conclusion_for_any_terminal_evaluator`.
It derives both final accumulator equalities internally from the same accepted
execution. The proof's trust boundary is summarized once in the
[assumptions ledger](assumptions-ledger.md).

## Publication records

The dated [24 August 2026 novelty scan](novelty-rescan-2026-08-24.md) records
the exact, qualified comparison used by the paper. Historical reviews under
[`docs/reviews/`](reviews/) preserve their original cutoffs and should be read
as snapshots rather than current status pages.

The earlier q18/g37 Tag-65 feasibility result remains in the
[historical mainnet record](mainnet-demo.md). V5 is the current publication
result.
