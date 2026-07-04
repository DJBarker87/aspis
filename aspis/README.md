# Aspis — transparent shielded spend on Solana (Stage 0 substrate)

Aspis is a staged project toward the first transparent, trusted-setup-free,
plausibly-post-quantum verifier of a real private-payment statement running as
a program on Solana. This subrepo is **Stage 0**: the native WHIR-style M31
PCS substrate ("native v0"), consolidated with the measured Phase 2 kernel
winners built in from the first line.

**Status**: Stage 0, host-complete. Host prove/verify parity 10/10 on every
profile/packaging variant; all corruption classes rejected. **No on-chain CU
number exists for this code yet** — `stage0-onchain` must run on a machine
with the Agave toolchain before the Stage 0 gate closes (see
`docs/stage0-gate.md`). Every soundness label in this tree is `heuristic`
until the Stage 1 soundness note exists.

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
docs/                    stage 0 gate note, whir-p3 divergence note
results/stage0/          raw artifacts backing every number quoted anywhere
```

## Commands

```bash
cargo test                                     # parity + corruption + unit suites
cargo run --release -p aspis-xtask -- stage0-host     # host artifacts (results/stage0/host_summary.json)
cargo run --release -p aspis-xtask -- stage0-onchain  # CU measurement; needs cargo-build-sbf + solana-test-validator
```

## Working rules (inherited from the staged design)

- No public number without a reproduction script and a soundness label.
- No stage begins before the previous gate document is written.
- Scope deviations are named as deviations — see `docs/stage0-gate.md`, which
  records two: this tree contained no pre-existing native v0 to port into,
  and on-chain measurement was environment-blocked at authoring time.
