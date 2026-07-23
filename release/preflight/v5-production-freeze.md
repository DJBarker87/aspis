# V5 Tag-67 production freeze

Status date: 2026-07-22
Decision: **GO for production-default and mainnet deployment readiness**

V5 Tag 67 is enabled in the default `aspis-verifier` feature set and routes
only through the atomic verify-and-apply wrapper. The plain manifest-default
SBF build is byte-identical to the frozen production-feature binary. This
record freezes the code, formal closure, runtime envelope, and deployment
handoff for that exact artefact.

V5 has not yet been deployed. The q18/g37 Tag-65 transaction finalized on
2026-07-16 is a separate release and remains frozen under
[`aspis-spend-q18-g37-mainnet-v1`](../aspis-spend-q18-g37-mainnet-v1/).

## Frozen artefact

| Item | Value |
| --- | --- |
| Canonical program ID | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` |
| SBF | `results/spend/v5-production-tag67-freeze-stream3-20260722/aspis_verifier_v5_production_tag67.so` |
| Size | 1,258,496 bytes |
| SHA-256 | `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40` |
| Provenance | `aspis_verifier_v5_production_tag67.provenance.json` |
| Provenance SHA-256 | `a7c9f7bea70d9805d8aff093fad309c911c752f2d47f6ad489c2f2eda1d7c3ec` |
| Source identities | 77/77 matched |
| Toolchain identities | 91/91 matched |
| Exact allocation minimum | 1,258,496 bytes |
| Suggested fresh allocation | 1,300,000 bytes, leaving 41,504 bytes |

The production-feature build and the later default-feature build produced the
same bytes. `v5-production-tag67` is therefore both the measured binary and the
default deployment binary.

## Accepted-input CU ceiling

The final accepted-grammar ceiling is **1,353,616 CU**, leaving **46,384 CU**
below Solana's 1.4 million limit.

| Selector | Measured missing-marker CU | Measured/max parent hashes | Conservative ceiling |
| ---: | ---: | ---: | ---: |
| 0 | 1,331,232 | 457 / 487 | 1,350,688 |
| 1 | 1,333,896 | 467 / 487 | 1,348,232 |
| 2 | 1,326,480 | 442 / 487 | **1,353,616** |

Each missing-marker measurement completed the real System Program
create-account CPI and repeated identically three times. The selector-0
present-marker control consumed 1,328,897 CU, also identically three times,
without a CPI.

The bound covers the complete frozen grammar:

- proof body: at most 77,278 bytes;
- sealed proof account: at most 77,318 bytes;
- pool: exactly 80 bytes;
- nullifier marker: exactly 72 bytes;
- instruction: exactly 169 bytes;
- five frontier sections: at most 338/338/284/230/176 nodes;
- total frontier nodes: at most 1,366;
- executed internal parent hashes: at most 487.

Every additional radix-4 parent is budgeted at 512 CU, above its measured
SHA-256 syscall, loop, and child-copy cost. The GoodA/GoodB control-flow
variation receives a separate 4,096-CU allowance. The missing-marker path
upper-bounds the present-marker path because it performs the same verification
plus the create-account CPI.

The machine-readable derivation is
[`v5_universal_accepted_topology_cu_policy.json`](../../results/spend/v5-production-tag67-freeze-stream3-20260722/v5_universal_accepted_topology_cu_policy.json),
SHA-256
`0da8ebbaee5b26bf82814bbc1cd7ebdfc1d542a8207bea30fb882ffb51c904cf`.

## Formal closure

The formal gate is green under Lean 4.32 default limits.

- **Component A:** maintained source correspondence and deployed-terminal
  applicability.
- **Component B:** deterministic sampler/evaluator/layout correspondence and
  maintained terminal capstone.
- **Component C:** actual-current sampler, encoder, arithmetic/folds, finish,
  packer, and public output. The final public theorem is
  `generated_public_run_output_matches_deployed`.
- **Tag 67:** generated wire guards and six actual LE64 reads construct the
  maintained work-wire view; the digest predicate and all six ordered
  batch/fold0/fold1/fold2/fold3/final steps are proved.
- **Combined capstone:**
  `FormalClosureStream1.current_source_combined_capstone` joins A, B, C
  operational/public output, and Tag-67 wire/verifier closure.

The combined theorem's only Tag-67 implementation/model premise is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

This is the exact pinned-Aeneas `HashFn` application boundary. No parser,
projection, digest-predicate, or six-step correspondence premise remains.
The audited capstones use only `{propext, Classical.choice, Quot.sound}`.

Principal entry points:

- `aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`
- `aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean`
- `aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean`
- `AspisFormal/AspisFormal/V5ProductionCap17RetryControl.lean`

## Production control flow

The host caller:

- attempts indices 0 through 16;
- draws fresh OS entropy for every attempt and witness component;
- fixes the canonical host hash;
- retries only `AllGoodCandidatesBad`;
- propagates every other error immediately;
- records the successful attempt index; and
- fails closed after 17 unsuccessful attempts.

Fixture RNG, selector overrides, and deterministic fallback are excluded from
the production path.

The production dispatcher exposes Tag 67 and no Tag-66 diagnostic arm. It
requires five ordered accounts, checks ownership/signer/writable flags,
re-derives the canonical nullifier PDA, requires the executable System
Program, rejects account aliasing, verifies before the first write or CPI, and
rejects a reused nullifier.

## Validation record

- `cargo check --workspace --release --locked`: green.
- Verifier Tag-67 tests: 22 passed.
- Dispatch tests: 3 passed.
- Focused production retry, entropy, PoW, layout, account-size, and
  duplicate-spend tests: green.
- Component-C and combined Lean 4.32 replays: green.
- Rust formatting, diff hygiene, JSON validation, provenance checks, and
  targeted credential scan: green.
- Manifest-default SBF versus frozen production SBF: byte-identical.

## Deployment handoff

The exact binary is ready for a fresh deployment with at least 1,258,496 bytes
of ProgramData allocation. An upgrade must first compare that requirement with
the actual on-chain ProgramData allocation. The deployment operator supplies
the RPC URL, program identity, payer, funding, and signing authorization, then
publishes the resulting signature alongside the SBF and provenance hashes.

No devnet or mainnet transaction was submitted during this freeze.

The publication-side deployment checklist and post-deploy evidence contract
are recorded in the
[V5 mainnet deployment handoff](../../docs/reviews/v5-mainnet-deployment-handoff.html).

## Evidence layout

`main` retains the final production SBF, provenance, three selector proofs and
measurements, marker-mode controls, statement, and universal CU policy under
`results/spend/v5-production-tag67-freeze-stream3-20260722/`. Duplicate SBF
paths are relative symlinks to the canonical binary.

Regenerable LLBC, raw/versioned Aeneas output, build logs, intermediate
feature-only SBFs, and the temporary-suffixed devnet build are preserved at
[`research-archive-v5-production-closure-2026-07-22`](https://github.com/DJBarker87/aspis/tree/research-archive-v5-production-closure-2026-07-22).
