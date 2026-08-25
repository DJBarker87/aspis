# Documentation

Aspis combines the first publicly evidenced Solana mainnet result of its exact
kind, to our knowledge at the 24 August 2026 search cutoff, with an end-to-end
formal proof of the deployed successful verifier path. The transaction
directly verified a transparent, computationally hiding private-spend proof
and atomically recorded its nullifier and new pool state. For every successful
translated Rust call, Lean follows the same execution through the statement,
byte transcript, authentication, four low-degree folds, algebraic relation,
and both final accumulators. The clean Lean 4.32 replay covers 331 tracked
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

The central theorem derives both final accumulator equalities from the same
accepted execution. The [artifact guide](../paper/aspis-formalization/ARTIFACT.md)
maps the paper's theorem names to exact declarations and replay commands. The
proof's assumption boundary is summarized in the
[assumptions ledger](assumptions-ledger.md).

## Publication records

The dated [24 August 2026 novelty scan](novelty-rescan-2026-08-24.md) records
the exact, qualified comparison used by the paper. Historical reviews under
[`docs/reviews/`](reviews/) preserve their original cutoffs and should be read
as snapshots rather than current status pages.

The earlier feasibility result remains in the
[historical mainnet record](mainnet-demo.md). The later mainnet transaction and
end-to-end proof are the current publication result.
