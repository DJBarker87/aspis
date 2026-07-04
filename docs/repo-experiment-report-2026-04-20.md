# Repo Experiment Report

Date: 2026-04-20

## Scope

This is a best-effort report of what has actually been tried in the current repo, based on the checked-in docs, `xtask` entrypoints, result summaries, raw result directories, and experiment subtrees present on disk on 2026-04-20.

It is not a claim that every abandoned shell command or unpublished local scratch file has been captured. It does cover the documented experiment tracks that have repo artifacts today.

## Executive Summary

The repo is no longer a single proof-system spike. It contains several distinct research tracks:

| Track | What was tried | Best concrete outcome | Current status |
| --- | --- | --- | --- |
| Phase 1 cost model | Solana CU measurement scaffold and additive scorer for transparent verifiers | Huber model over 186 records; real `verify_stark` baseline predicted within 0.44% | complete scaffold, still a model |
| Phase 1 follow-on | Security-qualified Circle and WHIR screens plus real-verifier calibration | No security-qualified Circle/WHIR spend-screen point fit under 1.4M CU | negative screen |
| Phase 2 WHIR proxy | SBF-measured WHIR-shaped verifier path with arithmetic, transcript, multiproof, and payload experiments | `whir-m31-capacity-v0` at 927,227 CU and 5,932 proof bytes | frozen shipping profile inside repo framing |
| Phase 2 real verifier | Actual Anchor/Winterfell `verify_stark` path in vendored stack | trace-8 baseline runs at 1,157,699 CU; recursive trace-64 variants hit the 1.4M cap | real-path measurement, not a WHIR replacement |
| Native WHIR M31 v0 | Fixed-profile host prover/verifier plus Solana verifier using SHA-256 syscall path | target profile verified on-chain at 326,021 CU with 18,316-byte proof | working vertical slice, but not full WHIR/SpendV0 |
| Official WHIR / whir-p3 comparison | Upstream comparison and schedule-level cross-validation | closest honest overlap is schedule derivation only; proof-level interop blocked | comparison infrastructure only |
| Circle / p3-circle | upstream fixture selection, host roundtrip, parameter sweep, Solana compile attempt | host parity ok, but projected CU remained structural-over-budget | negative result |
| WHIR-UD | upstream reference study, hash-only host roundtrip, SBF compile attempt | best measured lower bound 499,648 CU for hash-only path, with 163,680 bytes and 133 staged tx just for upload | amber, likely dead end |
| WHIR-JB | upstream reference evaluation plus exact host roundtrip against upstream bytes | exact host parity on two Goldilocks3 scenarios; 128-bit upstream proof still 96.9-180.5 KiB | proof-level parity exists, Solana viability not shown |
| ML-DSA via Winterfell on Solana | Yano baseline reproduction, ML-DSA Stage A/B spec and hash-path study, Winterfell feasibility projection | Stage B projection gave ~120,128-byte Winterfell proof proxy for ML-DSA-44 | red-stop negative result under current framing |

The two clearest repo-wide outcomes are:

1. A measured WHIR-shaped path can fit under the Solana 1.4M CU cap in this repo's current framing.
2. The original ML-DSA-on-Winterfell-on-Solana framing does not fit once the Stage B projection is written in actual Winterfell terms.

## 1. Phase 1 Cost-Model Scaffold

### What was tried

- Built the initial local Solana measurement harness around `programs/phase1-probe`, `crates/svm-cost-model`, and `cargo xtask phase1`.
- Measured isolated verifier-cost surfaces: hashing, Merkle paths, proof parsing, field-op proxies, heap, account I/O, upload path, and a synthetic verifier aggregate.
- Fit an additive CU model and preserved uncertainty bands.

### Measured outcome

- Model: `huber_irls` over 186 successful records.
- RMSE: 59,021.4 CU.
- MAE: 9,606.9 CU.
- Historical external baseline preserved: `verify_stark` mean 1,104,510 CU, max 1,190,982 CU.
- Safe-operating-region conclusion at this stage: Circle sweep had 0 feasible points; lowest predicted point was still 1,524,640.7 CU.

### What this established

- The repo gained a machine-calibrated measurement stack instead of hand-wavy verifier-cost estimates.
- This was explicitly a scaffold, not a production verifier.

### Artifacts

- `docs/phase1-cost-model.md`
- `crates/svm-cost-model/`
- `programs/phase1-probe/`
- `xtask/src/main.rs`

## 2. Phase 1 Follow-On Experiments

### What was tried

- Ran `cargo xtask phase1-next`.
- Compared the Phase 1 scorer to a real Winterfell verifier path.
- Added security-qualified spend screens for Circle and WHIR rather than low-query toy screens.
- Ran orthogonal upload, account-I/O, and inversion sweeps to refine coefficients.

### Measured outcome

- Real `verify_stark` baseline:
  - mean 1,104,506.47 CU
  - proof bytes 4,211
  - predicted verifier CU 1,099,681.6
  - absolute error 4,824.8 CU
- Base spend-screen scores:
  - Circle: 2,166,297.6 CU
  - WHIR: 1,749,910.3 CU
- Refined spend scores:
  - Circle: 1,942,566.3 CU
  - WHIR: 1,526,035.0 CU
- Security-qualified joint sweep:
  - 0 feasible points for every Circle and WHIR target bucket reported in the doc.

### What this established

- The scorer tracks the repo's real Winterfell verifier surprisingly closely.
- The early spend-shaped Circle/WHIR screens were negative even before the later WHIR-specific engineering work.

### Artifacts

- `docs/phase1-next-experiments.md`

## 3. Phase 2 WHIR Proxy Path

### What was tried

- Extended the Phase 1 scaffold into a WHIR-shaped verifier path using real SBF measurements.
- Measured arithmetic kernels, extension kernels, lift policy, fold representation, transcript inclusion, Merkle multiproof mode, payload format, multiplication taxonomy, round-0 reuse, and round-local structure.
- Used `xtask/src/phase2.rs` and the `results/phase2/` tree as the main experiment harness.

### Measured outcome

- Arithmetic winner: `reference_canonical`.
- Extension-kernel winner: `karatsuba`.
- Lift-policy winner: `late_lift_qm31`.
- Query-only to transcript-inclusive jump:
  - `whir_t128_capacity_full`: 603,811 CU -> 1,014,405 CU.
  - `whir_t128_johnson_full`: 1,103,645 CU -> 1,462,367 CU.
- Merkle `minimal_subtree` beat `separate_paths`.
- Canonical multiproof payload lost badly against flat nodes.
- `local_interpolant` did not beat `raw_fibers` on the measured full path.
- Round-batch inversion materially improved both capacity and Johnson cases.

### Frozen shipping profile

The repo's own state-of-play freezes:

- profile: `whir-m31-capacity-v0`
- scenario: `whir_t128_capacity_full`
- arithmetic: `reference_canonical`
- extension: `karatsuba`
- lift: `late_lift_qm31`
- fold mode: `raw_fibers`
- Merkle mode: `minimal_subtree`
- payload baseline: `flat_nodes`

Measured result:

- total: 927,227 CU
- verify: 914,591 CU
- upload: 12,636 CU
- proof bytes: 5,932
- margin vs 1.4M cap: 472,773 CU

### What this established

- Inside the repo's current WHIR-shaped framing, there is a measured under-cap path.
- The Johnson branch remains research, not shipping.
- The dominant remaining cost is still per-round queries, not parsing or upload.

### Artifacts

- `docs/phase2-experiments.md`
- `docs/whir-m31-capacity-v0.md`
- `docs/state-of-play.md`
- `results/phase2/summary.json`
- `results/phase2/whir-m31-capacity-v0/summary.json`
- `xtask/src/phase2.rs`

## 4. Phase 2 Real Winterfell Verifier Path

### What was tried

- Ran the actual Anchor/Winterfell `verify_stark` instruction present in the vendored stack.
- Used feature-gated `phase2_*` loader instructions only to stage the exact chat payload consumed by the production verifier path.
- Compared a baseline trace-8 proof against recursive trace-64 variants with and without row-interpolant sidecars.

### Measured outcome

- `trace8_raw_rows`:
  - verify 1,157,699 CU
  - pipeline total 1,177,074 CU
  - proof bytes 4,437
- `trace64_q30_raw_rows`:
  - verify hit 1,400,000 CU cap and failed to complete
  - pipeline total 1,457,359 CU
  - proof bytes 13,354
- `trace64_q30_raw_rows_plus_interpolants`:
  - also hit the 1,400,000 CU cap
  - pipeline total 1,465,704 CU
  - proof bytes 15,210

### What this established

- The repo contains a real measured Winterfell verifier path, not just a proxy.
- Recursive FRI growth quickly exhausts the transaction cap in the current setup.
- The row-interpolant sidecar was not a win on this real path.

### Artifacts

- `docs/phase2-real-experiments.md`
- `xtask/src/phase2_real.rs`

## 5. Native WHIR M31 v0

### What was tried

- Built a fixed-profile native multilinear opening prover/verifier slice over the M31 -> CM31 -> QM31 tower.
- Implemented host proving, host verification, and an exact-profile Solana verifier using SHA-256 syscalls.
- Fixed the scope to two profiles rather than an open parameter family.

### Measured outcome

- Dev profile `whir-m31-dev-v0`:
  - proof bytes 4,108
  - on-chain verify 96,118 CU
  - upload 9,694 CU
- Target profile `whir-m31-solana-v0`:
  - proof bytes 18,316
  - on-chain verify 326,021 CU
  - upload 38,965 CU
- Host verify and on-chain verify both succeeded for both profiles.
- Corruption tests rejected on both host and chain:
  - flipped Merkle sibling
  - flipped fold coefficient
  - flipped query opening
  - flipped statement digest

### What this established

- There is a working native vertical slice in this repo, with real on-chain verification, but it is still a fixed-profile v0.
- The remaining gap is semantic: it is not yet the full WHIR paper path or a full SpendV0 arithmetic relation.

### Artifacts

- `docs/native-whir-m31-v0.md`
- `results/native-whir/summary.json`
- `crates/whir-m31-core/`
- `crates/whir-m31-host/`
- `programs/whir-m31-verifier/`
- `xtask/src/native_whir.rs`

## 6. Native WHIR vs Official WHIR

### What was tried

- Compared the local native WHIR path against the pinned upstream `WizardOfMenlo/whir` CLI where the comparison was still honest.
- Recorded both local and upstream runs and preserved the exact upstream commit.

### Measured outcome

- For the small dev profile:
  - local proof bytes 4,108
  - local on-chain verify 96,118 CU
  - official proof size about 22.3 KiB
  - official run completed
- For the Solana target profile:
  - local proof bytes 18,316
  - local on-chain verify 326,021 CU
  - official run timed out after 180 seconds

### What this established

- The comparison is useful as a directional reference only.
- It is not an equivalence claim because the fields, hashes, verifier cost units, and stage counts differ.

### Artifacts

- `docs/native-whir-vs-official-whir.md`
- `xtask/src/official_whir_compare.rs`

## 7. whir-p3 Compatibility

### What was tried

- Investigated whether the repo's local WHIR path could be cross-checked against `whir-p3`.
- Checked both current-main and a buildable pinned pair.
- Built schedule-level cross-validation via a helper crate when proof-level interop was impossible.

### Measured outcome

- Current-main `whir-p3` did not build against its declared Plonky3 dependency set.
- Buildable pinned pair did build.
- Proof-level interop remained blocked by:
  - different field tower
  - different transcript/MMCS hash path
  - different proof serialization
- Structural schedule comparison still diverged:
  - `whir_t100_capacity_full`: 3 divergences
  - `whir_t128_capacity_full`: 5 divergences
  - `whir_t128_johnson_full`: 6 divergences

### What this established

- The first honest overlap is schedule derivation, not proof bytes.
- The repo should not claim proof-level validation against `whir-p3`.

### Artifacts

- `docs/whir-p3-compatibility.md`
- `results/whir-p3-cross-validation/summary.json`
- `xtask/src/whir_p3_cross_validate.rs`

## 8. Circle / p3-circle Workstream

### What was tried

- Chose a pinned upstream circle reference.
- Selected the byte-stable `uni_stark_circle_v1.postcard` compatibility fixture in `p3-circle`.
- Studied the actual Circle parameter surface, then ran a spike and a parameter sweep.
- Attempted Solana compilation for the local mirror path.

### Measured outcome

- Reference selection favored `p3-circle` over Stwo because p3-circle ships a checked-in byte fixture and uses Keccak in the selected path.
- Upstream fixture size was already 29,332 bytes.
- Spike gate:
  - host roundtrip divergences: 0
  - Solana compilation: failed
  - projected CU: 7,267,870
  - soundness lower bound at the gate point: 28 bits vs 100-bit target
- Parameter gate:
  - best configuration still projected 12,144,181 CU
  - proof bytes 43,149
  - soundness lower bound 58 bits, conjectured upper bound 100 bits

### What this established

- Byte-level host compatibility was the easy part.
- Under the measured Circle configuration space in this repo, the Solana gap is structural, not just a bad parameter pick.

### Artifacts

- `docs/circle-reference-selection.md`
- `docs/circle-parameter-space.md`
- `docs/circle-spike-gate.md`
- `docs/circle-parameter-gate.md`
- `crates/circle-p3-core/`
- `programs/circle-p3-verifier/`
- `xtask/src/circle_spike.rs`
- `xtask/src/circle_parameter_sweep.rs`

## 9. WHIR-UD Workstream

### What was tried

- Pinned and studied the upstream `WizardOfMenlo/whir` reference for the unique-decoding branch.
- Verified how WHIR-UD is actually selected in the current CLI and code path.
- Ran practical reachability probes and a local spike around the largest host-roundtripped trace reached.
- Attempted an SBF wrapper build.

### Measured outcome

- Upstream reference is buildable and exposes WHIR-UD explicitly enough to target.
- Practical tiny sanity:
  - Goldilocks2 UD tiny PCS proof about 24.3 KiB
  - Goldilocks3 UD tiny PCS proof about 24.2 KiB
- Spike gate chosen configuration:
  - `whir-ud-goldilocks2-t100-rate1over4-d18-e1-l0-i4-k4-affine3x5`
  - best hash-only lower bound 499,648 CU
  - raw bytes 163,680
  - at least 133 staged transactions just to upload bytes
- Direct SBF compilation failed for the wrapper program.

### What this established

- The branch is not dead by source availability, but it looks very weak as a Solana candidate.
- Even the favorable measured result was only a hash-only lower bound, not a full verifier.

### Artifacts

- `docs/whir-ud-reference.md`
- `docs/whir-ud-spike-gate.md`
- `results/whir-ud-spike/`
- `crates/whir-ud-host/`
- `programs/whir-ud-verifier/`
- `xtask/src/whir_ud_spike.rs`

## 10. WHIR-JB Workstream

### What was tried

- Pinned and studied the upstream `WizardOfMenlo/whir` reference for the Johnson-bound branch.
- Verified how JB is selected in the current upstream code.
- Swept fields, rates, and practical `num_variables` ranges against the upstream 60-bit PoW ceiling.
- Added an exact host-roundtrip harness that consumes the upstream `narg_string` and `hints` byte streams directly, then compares reference vs mirror verification and transcript traffic.

### Measured outcome

- JB is selected by omitting `--unique-decoding`; there is no separate capacity-bound selector in the pinned upstream.
- Key practical field result:
  - `Goldilocks2` is not a practical 128-bit JB field at meaningful trace sizes because PoW requirements hit the upstream ceiling.
  - `Goldilocks3` is the practical 128-bit JB branch.
- Upstream proof sizes for the viable Goldilocks3 branch:
  - 128-bit, `d=20`: 96.9 KiB to 180.5 KiB across rates 1/16 to 1/2
  - 100-bit, `d=18`: 60.7 KiB to 113.9 KiB
- Exact host roundtrip:
  - dev scenario proof bytes 18,920, parity exact, 4/4 mutation checks matched
  - gate scenario proof bytes 98,496, parity exact, 4/4 mutation checks matched
  - divergences: none

### What this established

- This is the repo's strongest exact-upstream parity result outside the vendored Winterfell path.
- It is still not a Solana-feasible path yet because proof sizes remain far outside the hoped-for envelope.

### Artifacts

- `docs/whir-jb-reference.md`
- `results/whir-jb-spike/host-roundtrip.md`
- `results/whir-jb-spike/raw/host-roundtrip.json`
- `crates/whir-jb-host/`
- `xtask/src/whir_jb_parity.rs`

## 11. ML-DSA on Solana via Winterfell

### What was tried

- Created a bounded research track for "Post-quantum ML-DSA signature verification on Solana via STARK, extending Yano 2025."
- Reproduced the Yano/Winterfell/Solana baseline.
- Wrote the claim boundary, source manifest, spec map, baseline note, Stage A gate, literature scan, Stage B SHAKE prototype, Stage B verify-hash-path prototype, and Stage B projection gate.
- Built small dedicated experiment crates under `experiments/mldsa-solana-stark/`.

### Measured baseline and prototypes

- Yano baseline:
  - local proof bytes 4,211
  - published `verify_stark` mean 1,104,510 CU over 100 runs
  - published `finalize_sig` mean 501,263 CU
- ML-DSA-44 `ExpandA` prototype:
  - 80 SHAKE128 permutations
  - 1,920 projected round rows
- ML-DSA-44 verify hash-path prototype:
  - exact pk/sig decode and SHAKE256 path
  - `tr` 10 permutations / 240 rows
  - `mu` 1 / 24
  - `ctilde'` 7 / 168
  - `SampleInBall` 1 / 24
  - total excluding `ExpandA`: 456 rows
  - four negative checks passed

### Winterfell feasibility finding

- Winterfell 0.12 field surface exposed:
  - `f64`
  - `f62`
  - `f128`
  - no binary fields exposed in the checked setup
- Winterfell trace width cap: 255 columns
- Stage B Keccak candidate under the width cap:
  - 35 columns
  - 4,608 rows per permutation
- Combined ML-DSA-44 projection:
  - exact active rows 485,888
  - padded trace length 524,288
  - synthetic Winterfell proof proxy 120,128 bytes
  - proxy generation time about 32.5 s

### Decision

- Stage B decision in repo artifacts: `RED-STOP`.
- Under the current project framing, no Stage C continuation is justified.

### What this established

- The repo has a documented negative result, not an abandoned spike.
- The failure is not just "too many hash rounds"; it is a Winterfell-shaped trace/proof-size result after writing down an actual width-compliant Keccak candidate and combining it with the arithmetic model.

### Artifacts

- `docs/mldsa-solana-stark-claim-boundary.md`
- `docs/mldsa-solana-stark-source-manifest.md`
- `docs/mldsa-solana-stark-spec-map.md`
- `docs/mldsa-solana-stark-yano-baseline.md`
- `docs/mldsa-solana-stark-stage-a-gate.md`
- `docs/mldsa-solana-stark-literature-scan.md`
- `docs/mldsa-solana-stark-stage-b-shake-gate.md`
- `docs/mldsa-solana-stark-stage-b-verify-hash-gate.md`
- `docs/mldsa-solana-stark-stage-b-keccak-framework-gate.md`
- `docs/mldsa-solana-stark-stage-b-projection-gate.md`
- `results/mldsa-solana-stark/`
- `experiments/mldsa-solana-stark/`

## 12. What The Repo Currently Supports

### Strongest measured under-cap Solana path

- `whir-m31-capacity-v0` in the Phase 2 WHIR-shaped path:
  - 927,227 CU total
  - 5,932 proof bytes

### Strongest real on-chain verifier slice built locally

- native WHIR M31 v0 target profile:
  - 326,021 CU verify
  - 18,316 proof bytes
  - host/on-chain accept-reject parity for the tested corruptions

### Strongest exact-upstream parity result

- WHIR-JB host roundtrip:
  - no divergences on the two exercised Goldilocks3 scenarios
  - exact transcript parity against upstream byte streams

### Clearest negative results

- Circle parameter sweep: structural over-budget result.
- ML-DSA via Winterfell: Stage B red-stop under the current framing.

## 13. What The Repo Does Not Yet Support

- A full SpendV0 arithmetic relation proved and verified end to end.
- Proof-level interoperability with `whir-p3`.
- A convincing Solana path for WHIR-UD.
- A Solana-feasible upstream-equivalent WHIR-JB deployment.
- An ML-DSA-44 Winterfell/Solana continuation beyond Stage B under the current assumptions.

## 14. Safe Claim Boundary

Based on the current repo state, the safest summary is:

- The repo contains a mature measurement harness for transparent-proof verification cost on Solana.
- It contains a measured under-cap WHIR-shaped verifier profile and a separate fixed-profile native M31 vertical slice with working on-chain verification.
- It contains exact host-level parity work against upstream WHIR-JB bytes.
- It contains two documented negative-result lines: Circle under the measured p3-circle parameter space, and ML-DSA-44 via Winterfell 0.12 under the current Solana framing.

Claims the repo should not make yet:

- proof-level validation against `whir-p3`
- full WHIR paper-path equivalence
- full SpendV0 semantics
- production readiness
- a viable ML-DSA-on-Winterfell-on-Solana path beyond Stage B

