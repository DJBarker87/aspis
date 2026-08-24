# Documentation

Aspis V5 is the current release. It records a private-spend construction,
Lean proofs, selected production verifier paths translated with Charon and
Aeneas, a byte-reproducible Solana program, and a finalized mainnet-beta state
transition. The Rust-to-model connection is complete through the initial
relation value and decoded relation tail. The complete general dot product and
the compact accumulator's component calculations are proved; the compact
state composition and outer theorem are still being joined.

## Start here

1. [How Aspis works](how-it-works.md) — the private-spend statement, proof
   upload, atomic transaction, and cleanup
2. [From mathematics to mainnet](../README.md#from-mathematics-to-mainnet) —
   the four-stage path
3. [What has been formally checked](formal-verification.md) — what Lean
   checks, how selected Rust is connected, and what remains trusted
4. [V5 mainnet result](v5-mainnet-demo.md) — finalized execution first, then
   exact deployment, lifecycle, compute, and refund evidence
5. [Verify and reproduce the
   evidence](../README.md#reproduce-the-evidence) — separate checks for the
   proof layers, program identity, and mainnet bundle
6. [Security assumptions](assumptions-ledger.md) — cryptographic,
   translation, compiler, and runtime boundaries
7. [Accepted V5 source map](v5-accepted-source-map.md) — the 15 review stops
   from instruction dispatch through proof checks and the state update
8. [Code map](code-map.md) — broader concept-to-file navigation
9. [Formalization report](../paper/aspis-formalization/) — mathematical,
   Rust-to-Lean, security, and trusted-boundary record
10. [Construction paper](../paper/aspis-spend/) — earlier protocol and
   deployment description
11. [Design history and previous releases](design-history.md) — evolution of
   the current V5 result and the earlier q18/g37 record

## Evidence by layer

| Layer | Record |
| --- | --- |
| Maintained mathematical models and Lean proofs | [`AspisFormal/`](../AspisFormal/) and its [proof-status table](../AspisFormal/README.md) |
| Selected production Rust translated and bridged to Lean | [`aeneas-verif/`](../aeneas-verif/) |
| Exact V5 SBF and reproducible build inputs | [V5 preflight](../release/preflight/v5-production-freeze.md) and [frozen candidate bundle](../release/aspis-v5-tag67-frozen-candidate-v1/) |
| Finalized V5 mainnet transaction and cleanup | [mainnet lifecycle bundle](../release/aspis-v5-tag67-mainnet-v1/) |

Run the V5 lifecycle verifier from a repository checkout:

```bash
./release/aspis-v5-tag67-mainnet-v1/verify.sh
python3 tools/check_release_facts.py
```

The [V5 evidence-chain publication
review](reviews/v5-evidence-chain-publication-review.html) records the resolved
framing and release-integrity findings and the boundaries that remain open to
outside review.

The [14 August formal-security extension
review](reviews/v5-formal-security-extension-20260814.html) explains the new
false-acceptance and theft proofs in plain English, including what they still
do not establish for the deployed program.

## History

The earlier q18/g37 Tag-65 feasibility result is retained separately in the
[historical mainnet record](mainnet-demo.md) and
[`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/).
It is not the current top-level release.

Design evolution and archived research are indexed in
[design history](design-history.md) and the [archive](../archive/README.md).
