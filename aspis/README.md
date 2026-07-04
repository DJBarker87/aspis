# Aspis — transparent shielded spend on Solana (Stage 0 substrate)

Aspis is a staged project toward the first transparent, trusted-setup-free,
plausibly-post-quantum verifier of a real private-payment statement running as
a program on Solana. This subrepo is **Stage 0**: the native WHIR-style M31
PCS substrate ("native v0"), consolidated with the measured Phase 2 kernel
winners built in from the first line.

**Status**: Stage 0, **conditionally closed**. Host prove/verify parity is
10/10 on every profile/packaging variant; all host corruption classes reject.
The gate-focused SBF run on Agave `2.3.0` accepts the capacity lr12
raw/minimal profile at `1,063,093` CU. Johnson q80 exceeds the cap and stays
research-track. The lr14 profile also exceeds the cap, but it is now recorded
as a narrow-layout diagnostic rather than the statement target; the real
target is lr10/k64/q32/g32 as a Stage 1 hypothesis. The measured projection is
`887,776` CU after PCS + wide-leaf/RLC overhead + the existing 30K sumcheck
estimate, leaving `302,224` CU against the 1.19M target. See
`docs/stage0-conclusion.md` and `docs/stage0-gate.md`. Every soundness label
in this tree is `heuristic` until the Stage 1 soundness note exists.

## What this is (and is not)

- A **WHIR-style multilinear PCS substrate**, not paper WHIR. Do not call it
  WHIR in any public claim: what v0 verifies is transcript-bound local fold
  consistency of a committed evaluation table down to an explicit final
  polynomial, with grinding, bound to a statement digest. Out-of-domain
  samples, sumcheck/fold interleaving, and external evaluation claims are
  Stage 1 work.
- Hashing on-chain and in the proof's own Merkle/transcript structure is
  SHA-256 via the Solana syscall (the two-hash rule: the in-circuit algebraic
  hash arrives with the Stage 2 statement layer, never on this path).
- Field tower: M31 → CM31 → QM31, with the Phase 2 winning kernels:
  `reference_canonical` M31 reduction, Karatsuba extension multiplication,
  `late_lift_qm31` mixed-width kernels, `raw_fibers` fold payload,
  `minimal_subtree` Merkle multiproofs, and `round_batch_inversion`.
  `proof_carried_round_local` (bytes-for-CU trade) is implemented behind a
  flag and measured, not frozen.
- Evaluation domains are cosets of 2^k subgroups of the M31 circle group
  (unit circle in CM31, order 2^31); committed layer-0 values are CM31 and
  lift to QM31 only at the first fold challenge.

## Claim boundary

Verbatim from the staged design (this section ships with every artifact):

> **Strongest defensible positive claim.** For one pinned code revision, one
> pinned proof configuration, and one pinned Solana runtime setup, this repo
> implements a hiding, transparent, hash-based proof of a shielded-spend
> statement (Merkle membership under a public anchor, nullifier derivation,
> value range, public binding), generates and locally verifies those proofs,
> and accepts them on Solana devnet within the documented 1.4M CU
> per-transaction cap, with raw n = 100 devnet measurements published.
>
> **Strongest defensible negative claim.** After implementing and
> adversarially testing the statement layer on the hardened multilinear PCS,
> the resulting proof bytes, upload pressure, or on-chain verifier cost
> exceed the stated Solana constraints; a transparent shielded-spend atom is
> therefore not feasible within this pinned stack.
>
> **Explicitly out of scope**: production readiness, audits, mainnet
> deployment; relayer infrastructure, fee privacy, wallet UX; multi-asset
> pools, swaps, private DeFi composition; compliance / viewing-key machinery;
> recursion, aggregation, batching of spends; any claim of equivalence to
> paper WHIR; any "first" claim without the Stage 5 novelty re-check.

Stage 0 realizes none of the positive claim yet — it is the substrate the
later stages build on, and its own claims are limited to what
`results/stage0/` reproduces.

## Layout

```text
crates/aspis-core        no_std verifier core, byte-exact host + SBF (the seam artifact)
crates/aspis-prover      host-only prover
programs/aspis-verifier  SBF program: staged upload + verify; knows nothing about spends
xtask                    stage0-host / stage0-onchain measurement runners
docs/                    staged design, stage 0 gate note, audit notes, divergence note
results/stage0/          raw artifacts backing every number quoted anywhere
```

## Stage gates

| Stage | Goal | Current status |
| --- | --- | --- |
| Stage 0 | Consolidate the native WHIR-style M31 PCS substrate | **CONDITIONAL GO**: lr10/k64/q32/g32 target hypothesis; Johnson q80 and old lr14 target are RED |
| Stage 1 | Harden and budget the PCS soundness argument | next; must justify or kill q32/g32 |
| Stage 2 | Build the direct spend evaluator and statement layer | blocked until Stage 1 closes |
| Stage 3 | Add commitment and sumcheck/evaluation hiding | future |
| Stage 4 | Split verifier crate seam and demo shielded pool | future |
| Stage 5 | Freeze, devnet n=100 measurement, novelty re-check, writeup | future |

## Commands

```bash
cargo test                                     # parity + corruption + unit suites
cargo run --release -p aspis-xtask -- stage0-host     # host artifacts (results/stage0/host_summary.json)
cargo run --release -p aspis-xtask -- stage0-onchain-gate  # gate CU matrix, writes results/stage0/onchain_summary.json
cargo run --release -p aspis-xtask -- stage0-onchain-profile # native CU markers, writes onchain_profile.json
cargo run --release -p aspis-xtask -- stage0-layout-sweep    # synthetic (log_rows,k) sweep
cargo run --release -p aspis-xtask -- stage0-onchain-g32     # g32 query/grinding diagnostics
cargo run --release -p aspis-xtask -- stage0-onchain-layout-target # lr10 q40/q36/q32 target profiles
cargo run --release -p aspis-xtask -- stage0-onchain       # full packaging matrix; slow
```

## On-chain proof account layout

`aspis-verifier` keeps staged upload separate from proof verification. Upload
state is a program-owned account with:

```text
[0..4]   magic "ASPU"
[4..8]   proof_len u32 LE
[8..40]  upload authority pubkey
[40..]   proof bytes
```

`InitProof` requires both the proof account signer (first initialization only)
and the upload authority signer. `UploadChunk` requires the stored authority
signer. `Verify` only reads the uploaded proof and statement digest; it does
not know about spends and does not require the upload authority.

## Working rules (inherited from the staged design)

- No public number without a reproduction script and a soundness label.
- No stage begins before the previous gate document is written.
- Scope deviations are named as deviations — see `docs/stage0-gate.md`, which
  records the bootstrap-native deviation, gate-focused measurement deviation,
  and the lr14 target demotion.
