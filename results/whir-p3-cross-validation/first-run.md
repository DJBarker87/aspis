# First Diagnostic Run

## What Was Attempted
1. Reuse or clone `whir-p3` into `/tmp/whir-p3-ref` and record current-main commit `a755a26ae41c52e3a1695ac4c443af627c96fe77`.
2. Run current-main preflight: `cargo check --manifest-path /tmp/whir-p3-ref/Cargo.toml --features cli`.
3. Pin a buildable `whir-p3` checkout at `ade33e7f5900a0f6c763d2793d7e1a5068d0b338` with Plonky3 `ccbffd6df66389f45d308a9df77c90bd53fdf81e`.
4. Run buildable-pair preflight: `cargo check --manifest-path /tmp/whir-p3-ade33e7/Cargo.toml --features cli`.
5. Select the first honest shared surface: the derived WHIR schedule trace from `WhirConfig`.
6. Run the trace helper: `cargo run --manifest-path /Users/dominic/ZK/target/whir-p3-cross-validation/trace-helper/Cargo.toml --quiet -- babybear5-poseidon2 /Users/dominic/ZK/results/whir-p3-cross-validation/raw/trace-helper.input.json`.

## Directional Results
- `whir-p3 proof -> local SBF verifier`: not attempted. Proof-byte interop is still blocked by hash and envelope mismatches.
- `local proof -> whir-p3 verifier`: not attempted. The proof objects are not serialized the same way, and the current comparison stayed at the schedule-trace layer.
- `local schedule derivation -> whir-p3 schedule derivation`: attempted.
  - `whir_t100_capacity_full`: 3 structural differences observed.
  - `whir_t128_capacity_full`: 5 structural differences observed.
  - `whir_t128_johnson_full`: 6 structural differences observed.

## Exact Observations
- Current-main preflight success: `false` with status code `Some(101)`.
- Current-main stderr:
```text
Updating crates.io index
    Updating git repository `https://github.com/Plonky3/Plonky3`
error: no matching package named `p3-interpolation` found
location searched: Git repository https://github.com/Plonky3/Plonky3?branch=main
required by package `whir-p3 v0.1.0 (/tmp/whir-p3-ref)`
```
- Buildable-pair preflight success: `true` with status code `Some(0)`.
- Structural helper success: `true` with status code `Some(0)`.
- `whir_t100_capacity_full` divergences: final_query_pow_bits_required differs: local=31 whir-p3=30; max_required_pow_bits differs: local=31 whir-p3=30; round[0].query_pow_bits_required differs: local=30 whir-p3=29.
- `whir_t128_capacity_full` divergences: starting_folding_pow_bits_required differs: local=3 whir-p3=2; final_query_pow_bits_required differs: local=31 whir-p3=30; max_required_pow_bits differs: local=31 whir-p3=30; round[0].query_pow_bits_required differs: local=30 whir-p3=29; round[0].folding_pow_bits_required differs: local=8 whir-p3=7.
- `whir_t128_johnson_full` divergences: starting_folding_pow_bits_required differs: local=13 whir-p3=36; final_query_pow_bits_required differs: local=32 whir-p3=31; max_required_pow_bits differs: local=32 whir-p3=38; pow_cap_satisfied differs: local=`true` whir-p3=`false`; round[0].query_pow_bits_required differs: local=32 whir-p3=31; round[0].folding_pow_bits_required differs: local=16 whir-p3=38.

## Compatibility Diagnosis
- The current whir-p3 main checkout does not build against its declared Plonky3 main dependency set, so there is no stable current-main prover/verifier binary to compare against yet.
- The local implementation uses SHA-256 through Solana's syscall path, while the checked-in whir-p3 surfaces are Poseidon-based and tests add Keccak only; transcript bytes and Merkle roots are therefore expected to diverge.
- The local proof is a fixed-layout `P2T1` envelope parsed by deterministic offsets, while whir-p3 serializes `WhirProof` via serde/bincode with nested vectors, enums, and options.
- The first trace comparison had to target the derived schedule rather than the proof bytes. Matching the local 155-bit Phase 2 screen required a generic `BabyBear` degree-5 helper, not the public M31 path advertised by the reference repository.

## Raw Artifacts
- `results/whir-p3-cross-validation/raw/whir-p3-current-main-git-head.txt`
- `results/whir-p3-cross-validation/raw/whir-p3-current-main-cargo-check.stdout.txt`
- `results/whir-p3-cross-validation/raw/whir-p3-current-main-cargo-check.stderr.txt`
- `results/whir-p3-cross-validation/raw/whir-p3-buildable-git-head.txt`
- `results/whir-p3-cross-validation/raw/whir-p3-buildable-plonky3-commit.txt`
- `results/whir-p3-cross-validation/raw/whir-p3-buildable-cargo-check.stdout.txt`
- `results/whir-p3-cross-validation/raw/whir-p3-buildable-cargo-check.stderr.txt`
- `results/whir-p3-cross-validation/raw/local-phase2-scenarios.json`
- `results/whir-p3-cross-validation/raw/trace-helper.input.json`
- `results/whir-p3-cross-validation/raw/trace-helper.babybear5.stdout.json`
- `results/whir-p3-cross-validation/raw/trace-helper.babybear5.stderr.txt`
- `results/whir-p3-cross-validation/raw/local-structural-traces.json`
- `results/whir-p3-cross-validation/raw/whir-p3-structural-traces.json`
- `results/whir-p3-cross-validation/raw/structural-comparison.json`
- `results/whir-p3-cross-validation/raw/summary.json`

This is one comparison at one set of parameters. It does not constitute validation.