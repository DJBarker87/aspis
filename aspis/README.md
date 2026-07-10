# Aspis — transparent shielded spend on Solana (Stage 2)

Aspis is a staged project toward the first transparent, trusted-setup-free,
plausibly-post-quantum verifier of a real private-payment statement running as
a program on Solana. This subrepo contains the native WHIR-style M31 PCS
substrate ("native v0") and its staged hardening, with the measured Phase 2
kernel winners built in from the first line.

**Status**: Stage 1 PCS milestone **closed; Stage 2 one-transaction feasibility
reopened by measured math kernels**. Stage 0 closed conditionally and the
soundness review retired q32/g32 in favor of q36/g32. The upstream T1/T2
constants are pinned, the challenge sampler is exact-uniform, and external
evaluation claims plus one OOD value per round are transcript-bound and
enforced by an interleaved degree-6 relation sumcheck. The v3 C2 interface
implements `C1 -> (lambda,chi) -> C2 -> claims -> gamma`, authenticates both
trees, and gamma-combines them before folding. False claims, false OOD
evaluations, challenge-order attacks, and corruption reject on host and SBF;
the same three ordering vectors accept under matching deliberately weakened
test-only schedules. On Agave `2.3.0`, the literal lr10/q36/g32 v3 verifier
accepts at `943,972` CU; the current PCS + wide-leaf/RLC + statement-sumcheck
projection is `1,175,086` CU, leaving only `14,914` CU against the 1.19M
target before unpriced constraint composition. The
conditional headline is t=100
capacity-conjectured (~102.98 system bits under the stated three-clause
assumption), with a proven Johnson floor of ~65.5 bits. See
`docs/aspis-soundness-note.md`, `docs/stage0-conclusion.md`, and
`docs/stage0-gate.md`. Stage 2 now has an executable SpendV0-min evaluator,
13 economic vectors replayed by both direct and six-limb lookup evaluators,
two lookup-specific teeth vectors, a Plonky3-pinned Poseidon2-M31
implementation, and isolated SBF composition/layout/hash measurements. The
first structured projection was `1,415,268` CU. Cached circle powers,
conjugate denominators,
specialized tower arithmetic, and lazy dots reduce the measured frozen binary
PCS to `714,111` CU. A fresh literal radix-4 q36/g32 proof measures `678,407`
CU. The lookup semantic oracle plus fixed-width q36/k80 RLC project the full
path to `1,041,944` CU, 29,056 below the strict slack ceiling. The LogUp proof
and wide RLC are not integrated into one payment proof, so split verification
remains the fallback; see `docs/stage2-feasibility.md` and
`docs/solmath-zk-candidates.md`.

## What this is (and is not)

- A **WHIR-style multilinear PCS substrate**, not paper WHIR. Do not call it
  WHIR in any public claim: the current verifier checks transcript-bound
  local fold consistency down to an explicit final polynomial, with grinding
  and statement binding. External `(z,v)` and per-round OOD evaluation
  relations are carried to the explicit final polynomial by an interleaved
  degree-6 sumcheck.
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

The current substrate still realizes none of the full positive spend claim;
its claims are limited to the PCS/soundness artifacts under `results/stage0/`
and `results/stage1/`.

## Layout

```text
crates/aspis-core        no_std verifier core, byte-exact host + SBF (the seam artifact)
crates/aspis-prover      host-only prover
programs/aspis-verifier  SBF program: staged upload + verify; knows nothing about spends
xtask                    stage0-host / stage0-onchain measurement runners
docs/                    staged design, stage 0 gate note, audit notes, divergence note
results/stage0,stage1/   raw artifacts backing every number quoted anywhere
```

## Stage gates

| Stage | Goal | Current status |
| --- | --- | --- |
| Stage 0 | Consolidate the native WHIR-style M31 PCS substrate | **CLOSED/CONDITIONAL (historical)**: admitted q32/g32 as a hypothesis; Stage 1 has since retired it |
| Stage 1 | Harden and budget the PCS soundness argument | **CLOSED/FROZEN**: q36/g32, v3 C2, relation enforcement, teeth tests, literal SBF measurement |
| Stage 2 | Build the direct spend evaluator and statement layer | **IN PROGRESS / CANDIDATE-GREEN PROJECTION**: direct + lookup evaluators complete; real radix-4 g32 PCS; projected 26.38% saving; LogUp/RLC/full-proof integration pending; split receipt retained |
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
cargo run --release -p aspis-xtask -- stage0-onchain-layout-target # literal lr10 q36/g32 + g16 diagnostics
cargo run --release -p aspis-xtask -- stage1-soundness-pin # pinned upstream T1/T2 artifact
cargo run --release -p aspis-xtask -- stage1-onchain-hardening # literal enforced q36/g32 + cached proof
cargo test -p aspis-prover --features insecure-test-ordering --test stage1_ordering # teeth proof against weakened schedules
cargo run --release -p aspis-xtask -- stage2-evaluator # economic corpus + real statement shape
cargo run --release -p aspis-xtask -- stage2-composition-probe # naive + structured SBF bracket
cargo run --release -p aspis-xtask -- stage2-layout-probe # k64/k80/k82 wide-layout delta
cargo run --release -p aspis-xtask -- stage2-poseidon2-probe # direct software hash cost
cargo run --release -p aspis-xtask -- stage2-zk-kernel-probe # field/tower/circle kernels + full PCS
cargo run --release -p aspis-xtask -- stage2-wide-rlc-probe # correct q-by-k gamma-power RLC
cargo run --release -p aspis-xtask -- stage2-merkle-arity-probe # binary vs radix-4 model
cargo run --release -p aspis-xtask -- stage2-radix4-g16 # real binary/radix-4 C2 comparison
cargo run --release -p aspis-xtask -- stage2-radix4-g32 # literal g32 proof + production SBF comparison
cargo run --release -p aspis-xtask -- stage2-variance-g16 # 16-seed transcript-draw variance vs pre-registered criterion
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
