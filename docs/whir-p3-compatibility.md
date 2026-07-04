# WHIR-p3 Compatibility Analysis

## Scope
This document characterizes whether the current Solana WHIR measurement path in this workspace can be cross-checked against `whir-p3` without modifying either implementation to force agreement.
- Reference repository: `https://github.com/tcoratger/whir-p3`.
- Current-main checkout: `/tmp/whir-p3-ref` @ `a755a26ae41c52e3a1695ac4c443af627c96fe77`.
- Buildable pinned pair: `/tmp/whir-p3-ade33e7` @ `ade33e7f5900a0f6c763d2793d7e1a5068d0b338` with Plonky3 `ccbffd6df66389f45d308a9df77c90bd53fdf81e`.

## Current-main API Findings
- Current `whir-p3` main was inspected at `src/lib.rs`, `src/bin/main.rs`, and `src/whir/proof.rs` in the checkout above.
- The checked-in CLI surface is KoalaBear4 + Poseidon2. It exposes `security_level`, `pow_bits`, `num_variables`, `rate`, `folding_factor`, `soundness_type`, and `rs_domain_initial_reduction_factor`.
- Query count is not a direct CLI input; the proof constructor derives it from the soundness model and rate.
- Proof bytes come from serde/bincode over `WhirProof`, not from a fixed-layout envelope.
- The current main `Cargo.toml` does not declare `p3-mersenne-31`, and the public examples are not M31-based.

## Buildability
- Current-main preflight: success=`false` status_code=`Some(101)` via `cargo check --manifest-path /tmp/whir-p3-ref/Cargo.toml --features cli`.
- Current-main stderr excerpt:
```text
Updating crates.io index
    Updating git repository `https://github.com/Plonky3/Plonky3`
error: no matching package named `p3-interpolation` found
location searched: Git repository https://github.com/Plonky3/Plonky3?branch=main
required by package `whir-p3 v0.1.0 (/tmp/whir-p3-ref)`
```
- Buildable pinned pair preflight: success=`true` status_code=`Some(0)`.

## Buildable-pair API Findings
- Buildable pair API checked at `src/bin/main.rs`, `src/parameters/mod.rs`, `src/whir/parameters.rs`, and `src/whir/proof.rs`.
- The checked-in CLI still hardcodes KoalaBear4 + Poseidon2, but the generic `WhirConfig`/`ProtocolParameters` surface is usable from an external helper crate.
- Round structure is exposed through `WhirConfig::round_parameters`, `final_queries`, `final_pow_bits`, and `final_sumcheck_rounds`.
- Proof serialization remains serde/bincode over `WhirProof`, so proof-byte interop with the local fixed-layout transcript is still unavailable.

## Local Phase 2 Targets
| Scenario | Security bits | Assumption | eval_domain_log2 | log_inv_rate | Grinding bits | Round query counts | Total explicit queries | Target proof bytes |
| --- | ---: | --- | ---: | ---: | ---: | --- | ---: | ---: |
| whir_t100_capacity_full | 100 | whir_capacity_full | 13 | 4 | 32 | [18, 10] | 28 | 12356 |
| whir_t128_capacity_full | 128 | whir_capacity_full | 13 | 4 | 32 | [25, 14] | 39 | 15468 |
| whir_t128_johnson_full | 128 | whir_johnson_full | 13 | 4 | 32 | [50, 28] | 78 | 26463 |

## Parameter Mapping Table
| Scenario | Local parameter | Local value | whir-p3 API / config | Observed compatibility |
| --- | --- | --- | --- | --- |
| whir_t100_capacity_full | field tower | M31 base field with CM31/QM31 extension arithmetic in the Solana verifier path | Current checked-in CLI/examples use `KoalaBear` + `BinomialExtensionField<KoalaBear, 4>`; generic `WhirConfig` can be instantiated from an external helper crate. | proof-level blocked; schedule-level comparison required a helper crate and a field-size-matched `BinomialExtensionField<BabyBear, 5>` surface because the local Phase 2 screen hard-codes 155 field bits |
| whir_t100_capacity_full | hash / transcript / MMCS | Solana SHA-256 via `solana_program::hash::hashv` / `sol_sha256` syscall path | Checked-in surfaces are Poseidon-based; tests add Keccak only. | blocked for proof bytes and transcript data |
| whir_t100_capacity_full | starting rate | log_inv_rate=4 (nominal rate 1/16) | `ProtocolParameters { starting_log_inv_rate, .. }` or CLI `-r/--rate` | maps directly |
| whir_t100_capacity_full | folding factor | first=4, later=4 | `FoldingFactor::ConstantFromSecondRound(first, later)` | maps for the schedule derivation |
| whir_t100_capacity_full | query schedule | total=28 with round_query_counts=[18, 10] | `WhirConfig::round_parameters[..].num_queries` plus `final_queries` after parameter derivation | derivable and compared structurally; not a direct CLI input |
| whir_t100_capacity_full | grinding / PoW bits | 32 | `ProtocolParameters { pow_bits, .. }` or CLI `-p/--pow-bits` | maps for the schedule derivation |
| whir_t100_capacity_full | soundness assumption | whir_capacity_full | `SecurityAssumption::{CapacityBound, JohnsonBound}` | maps directly |
| whir_t100_capacity_full | proof serialization | fixed-layout phase2 transcript proof, target_proof_bytes=12356 | `bincode::serialize(&proof)` over the serde `WhirProof<F, EF, MT>` object | blocked: byte layout and parser model differ completely, so direct proof interchange is not available |
| whir_t128_capacity_full | field tower | M31 base field with CM31/QM31 extension arithmetic in the Solana verifier path | Current checked-in CLI/examples use `KoalaBear` + `BinomialExtensionField<KoalaBear, 4>`; generic `WhirConfig` can be instantiated from an external helper crate. | proof-level blocked; schedule-level comparison required a helper crate and a field-size-matched `BinomialExtensionField<BabyBear, 5>` surface because the local Phase 2 screen hard-codes 155 field bits |
| whir_t128_capacity_full | hash / transcript / MMCS | Solana SHA-256 via `solana_program::hash::hashv` / `sol_sha256` syscall path | Checked-in surfaces are Poseidon-based; tests add Keccak only. | blocked for proof bytes and transcript data |
| whir_t128_capacity_full | starting rate | log_inv_rate=4 (nominal rate 1/16) | `ProtocolParameters { starting_log_inv_rate, .. }` or CLI `-r/--rate` | maps directly |
| whir_t128_capacity_full | folding factor | first=4, later=4 | `FoldingFactor::ConstantFromSecondRound(first, later)` | maps for the schedule derivation |
| whir_t128_capacity_full | query schedule | total=39 with round_query_counts=[25, 14] | `WhirConfig::round_parameters[..].num_queries` plus `final_queries` after parameter derivation | derivable and compared structurally; not a direct CLI input |
| whir_t128_capacity_full | grinding / PoW bits | 32 | `ProtocolParameters { pow_bits, .. }` or CLI `-p/--pow-bits` | maps for the schedule derivation |
| whir_t128_capacity_full | soundness assumption | whir_capacity_full | `SecurityAssumption::{CapacityBound, JohnsonBound}` | maps directly |
| whir_t128_capacity_full | proof serialization | fixed-layout phase2 transcript proof, target_proof_bytes=15468 | `bincode::serialize(&proof)` over the serde `WhirProof<F, EF, MT>` object | blocked: byte layout and parser model differ completely, so direct proof interchange is not available |
| whir_t128_johnson_full | field tower | M31 base field with CM31/QM31 extension arithmetic in the Solana verifier path | Current checked-in CLI/examples use `KoalaBear` + `BinomialExtensionField<KoalaBear, 4>`; generic `WhirConfig` can be instantiated from an external helper crate. | proof-level blocked; schedule-level comparison required a helper crate and a field-size-matched `BinomialExtensionField<BabyBear, 5>` surface because the local Phase 2 screen hard-codes 155 field bits |
| whir_t128_johnson_full | hash / transcript / MMCS | Solana SHA-256 via `solana_program::hash::hashv` / `sol_sha256` syscall path | Checked-in surfaces are Poseidon-based; tests add Keccak only. | blocked for proof bytes and transcript data |
| whir_t128_johnson_full | starting rate | log_inv_rate=4 (nominal rate 1/16) | `ProtocolParameters { starting_log_inv_rate, .. }` or CLI `-r/--rate` | maps directly |
| whir_t128_johnson_full | folding factor | first=4, later=4 | `FoldingFactor::ConstantFromSecondRound(first, later)` | maps for the schedule derivation |
| whir_t128_johnson_full | query schedule | total=78 with round_query_counts=[50, 28] | `WhirConfig::round_parameters[..].num_queries` plus `final_queries` after parameter derivation | derivable and compared structurally; not a direct CLI input |
| whir_t128_johnson_full | grinding / PoW bits | 32 | `ProtocolParameters { pow_bits, .. }` or CLI `-p/--pow-bits` | maps for the schedule derivation |
| whir_t128_johnson_full | soundness assumption | whir_johnson_full | `SecurityAssumption::{CapacityBound, JohnsonBound}` | maps directly |
| whir_t128_johnson_full | proof serialization | fixed-layout phase2 transcript proof, target_proof_bytes=26463 | `bincode::serialize(&proof)` over the serde `WhirProof<F, EF, MT>` object | blocked: byte layout and parser model differ completely, so direct proof interchange is not available |

## Selected Comparison Surface
- Surface: Derived WHIR schedule trace from whir-p3 `WhirConfig`.
- Rationale: The first honest overlap is the protocol schedule derivation: OOD sample counts, per-round query counts, per-round PoW requirements, and final-query/final-sumcheck structure. Exact proof bytes, transcript challenges, query indices, and Merkle roots are not compared because the local verifier is SHA-256 + fixed-layout `P2T1`, while whir-p3 is Poseidon/Keccak-capable + serde/bincode.
- Selected field profile: `babybear5-poseidon2`. The Phase 2 scenarios in this workspace hard-code a 155-bit screening assumption. The closest buildable whir-p3 generic surface for that exact field-size input is `BinomialExtensionField<BabyBear, 5>`. This is a schedule-level comparison only; it is not an M31 proof-equivalence claim.
- Compared fields:
  - soundness assumption
  - target security bits
  - field_size_bits
  - starting_log_inv_rate
  - max_pow_bits
  - num_variables
  - first/later folding factors
  - commitment OOD samples
  - starting folding PoW bits
  - per-round query counts
  - per-round OOD samples
  - per-round query/folding PoW bits
  - final queries
  - final query PoW bits
  - final sumcheck rounds
  - final folding PoW bits
  - total explicit query count
  - pow-cap satisfied
- Intentionally not compared:
  - proof bytes
  - proof object layout
  - Merkle roots
  - Fiat-Shamir challenge bytes
  - query indices
  - opened values
  - host-verifier accept/reject
  - SBF-verifier accept/reject

## Structural Trace Run
- Helper run success=`true` status_code=`Some(0)` via `cargo run --manifest-path /Users/dominic/ZK/target/whir-p3-cross-validation/trace-helper/Cargo.toml --quiet -- babybear5-poseidon2 /Users/dominic/ZK/results/whir-p3-cross-validation/raw/trace-helper.input.json`.
- The selected surface is the derived WHIR schedule, not proof bytes.
- The helper uses `BinomialExtensionField<BabyBear, 5>` because the local Phase 2 sweep hard-codes a 155-bit field-size assumption.
- Any exact match reported here is only a formula-level schedule agreement on this surface.

| Scenario | Exact structural match | Divergence count |
| --- | --- | ---: |
| whir_t100_capacity_full | false | 3 |
| whir_t128_capacity_full | false | 5 |
| whir_t128_johnson_full | false | 6 |

### whir_t100_capacity_full
- final_query_pow_bits_required differs: local=31 whir-p3=30
- max_required_pow_bits differs: local=31 whir-p3=30
- round[0].query_pow_bits_required differs: local=30 whir-p3=29

### whir_t128_capacity_full
- starting_folding_pow_bits_required differs: local=3 whir-p3=2
- final_query_pow_bits_required differs: local=31 whir-p3=30
- max_required_pow_bits differs: local=31 whir-p3=30
- round[0].query_pow_bits_required differs: local=30 whir-p3=29
- round[0].folding_pow_bits_required differs: local=8 whir-p3=7

### whir_t128_johnson_full
- starting_folding_pow_bits_required differs: local=13 whir-p3=36
- final_query_pow_bits_required differs: local=32 whir-p3=31
- max_required_pow_bits differs: local=32 whir-p3=38
- pow_cap_satisfied differs: local=`true` whir-p3=`false`
- round[0].query_pow_bits_required differs: local=32 whir-p3=31
- round[0].folding_pow_bits_required differs: local=16 whir-p3=38

## Proof Format Analysis
- Local Phase 2 transcript proofs are fixed-layout byte envelopes. The builder writes a `P2T1` header and then packs round plans, roots, query records, Merkle witnesses, and final records at deterministic offsets.
- The on-chain parser mirrors that layout exactly, which is good for SBF parsing cost but tightly binds the verifier to the byte format.
- `whir-p3` proof bytes are serde/bincode over the `WhirProof` Rust structure, which contains nested vectors, enums, and optional sections.
- Even if the same semantics were proven, those byte layouts are not directly interchangeable.

## Current Status
Comparison infrastructure exists at the schedule-trace level. Proof-level interop is still blocked by buildability drift on current main plus field/hash/proof-format differences. No validation claim should be inferred from the structural trace output.