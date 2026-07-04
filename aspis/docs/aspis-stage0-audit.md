# Aspis Stage 0 Audit

Date: 2026-07-04
Scope: `aspis/` workspace after the Stage 0 bootstrap pull.
Design reference: `docs/aspis-staged-design.md`.

## Summary

Stage 0 is substantially implemented as a bootstrap native WHIR-style M31 PCS
slice: field tower, transcript, Merkle packaging, prover, no_std verifier,
SBF verifier program, host measurement runner, on-chain measurement harness,
and gate notes all exist. The implementation already includes the Stage 0
kernel choices: `minimal_subtree`, `raw_fibers`, `round_batch_inversion`, and
`proof_carried_round_local` as a measured option.

Stage 0 is conditionally closed. The capacity lr12 raw/minimal profile accepts
on-chain, Johnson q80 exceeds the CU ceiling, and lr14 exceeds the CU ceiling
under a narrow-table diagnostic layout. The measured continuation target is
lr10/k64/q32/g32, with q32/g32 explicitly treated as a Stage 1 soundness
hypothesis rather than a claim.

## Scores

| Dimension | Score | Rationale |
| --- | --- | --- |
| Security | B- | Upload authority checks are now present; cryptographic soundness is still explicitly Stage 1. |
| Correctness | B | Host parity passes; lr12, g32, and lr10 target diagnostics accept on-chain; Johnson/lr14 failures are measured gate data. |
| Error handling | B | Proof parsing is length-checked; proof account short-data panics are covered. |
| Testing | B | Unit, host, and gate-focused on-chain artifacts exist; false-statement suites remain Stage 1. |
| Code organization | A- | Clean host/SBF seam; verifier core is `no_std`; spend logic is not mixed in. |
| Documentation | A- | Staged design, gate note, divergence note, and audit artifact are in-repo. |

Ready for mainnet: **no**. This repo is a measurement/research artifact until
Stages 1-5 complete.

## Findings

### High - Stage 0 only conditionally closes because q32/g32 is unproven

Status: conditionally closed for Stage 1 entry.

The original design text treated `log_rows=14` as the statement-sized target,
but that was a narrow-table sizing assumption. The wide-row layout machinery
trades row count against column count, so §13.8 now has to move forward into
Stage 0 before the gate can close. The gate-focused SBF artifact shows:

- `capacity_lr12_q40_g16` raw/minimal accepts at `1,063,093` CU.
- `capacity_lr12_q40_g16` carried/minimal accepts at `1,078,628` CU.
- `johnson_lr12_q80_g16` raw/carried both hit the CU ceiling.
- `capacity_lr14_q40_g16` raw/minimal hits the CU ceiling as a narrow-layout
  diagnostic.

Follow-up measurements:

- `capacity_lr12_q36_g32` accepts at `1,025,729` CU.
- `capacity_lr12_q32_g32` accepts at `894,891` CU.
- `capacity_lr10_q40_g16` accepts at `773,668` CU.
- `capacity_lr10_q36_g16` accepts at `742,795` CU.
- `capacity_lr10_q32_g16` accepts at `656,662` CU.
- The corrected synthetic layout sweep gives `201,114` CU for lr10/k64
  wide-leaf hashing plus gamma-RLC recombination.

Conclusion: the Stage 1 target is lr10/k64/q32/g32, projected at `887,776` CU
after PCS + measured wide-row overhead + the existing 30K sumcheck estimate.
If Stage 1 cannot justify q32/g32, q36 is the reserve target and q40 is too
tight for the current single-transaction statement plan.

### High - Staged upload lacked account authority checks

Status: fixed.

Before this audit pass, any transaction that supplied a program-owned proof
account could call `InitProof` or `UploadChunk`; the declared payer account
was not checked as a signer and no upload authority was stored in the account.
For the Stage 0 harness this is not a funds bug, but it is still the exact
class of Solana account-mutation issue the verifier seam should avoid before
being reused by a demo pool.

Fix applied:

- proof accounts now carry magic, proof length, and upload authority
- first initialization requires proof-account signer and authority signer
- chunk upload requires the stored authority signer
- verification remains read-only and statement/proof-only
- short account data rejects instead of indexing into `[0..4]`

Touched files:

- `programs/aspis-verifier/src/lib.rs`
- `xtask/src/onchain.rs`

### Medium - Host artifact corruption suite did not match gate-note claims

Status: fixed.

`docs/stage0-gate.md` said per-variant artifacts covered `mode_flag_replay`
and `profile_swap`, but `xtask::host::corruption_suite` only emitted seven
cases. The test suite had replay tests, but the JSON artifact did not.

Fix applied:

- `mode_flag_replay` is now recorded in `host_summary.json`
- `profile_swap` is now recorded in `host_summary.json`

Touched file: `xtask/src/host.rs`.

### Medium - Stage 1 soundness work is intentionally unimplemented

Status: open by design.

The substrate still proves transcript-bound local fold consistency, not paper
WHIR and not a complete opening scheme suitable for sumcheck claims. Missing
items include OOD samples, sumcheck/fold interleaving, explicit soundness
budgeting, external evaluation-claim binding, and RLC batched-opening
soundness.

Fix: complete Stage 1 before any statement-layer or public security claim.

### Medium - Stage 2/3 spend and hiding layers are intentionally absent

Status: open by design.

There is no shielded spend evaluator, Poseidon2-M31 statement circuit,
zerocheck/sumcheck layer, wide-leaf RLC opening, commitment hiding, or
evaluation hiding yet. This means the positive claim in the staged design is
not realized by the current code.

Fix: do not begin Stage 2 until the Stage 0 gate and Stage 1 soundness gate
close.

## Verified Commands

```bash
cargo test --manifest-path aspis/Cargo.toml
cargo run --release -p aspis-xtask -- stage0-host
cargo run --release -p aspis-xtask -- stage0-onchain-gate
cargo run --release -p aspis-xtask -- stage0-onchain-profile
cargo run --release -p aspis-xtask -- stage0-layout-sweep
cargo run --release -p aspis-xtask -- stage0-onchain-g32
cargo run --release -p aspis-xtask -- stage0-onchain-layout-target
```

Result: host tests passed (`8` core, `11` Stage 0 prover/verifier, `4`
verifier crate tests). Gate-focused SBF artifact was generated at
`results/stage0/onchain_summary.json`; profile, layout, and g32 diagnostic
artifacts were generated under `results/stage0/`.
