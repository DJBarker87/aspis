# Circle Reference Selection

Status: Phase 1 complete. Phase 2 has not started. This document stops at reference selection, per the spike plan.

## Recommendation

Select `p3-circle` from `Plonky3` at commit `0f87f2b543a01880274965c410bf804c124f5046` as the Phase 2 validation target.

Use the upstream circle compatibility path in `uni-stark/tests/fib_air.rs` as the initial proof source:

- simple statement: 8-row Fibonacci trace
- trace width: 2 columns
- public values: 3
- max constraint degree: 2
- field: `Mersenne31`
- extension field: `BinomialExtensionField<Mersenne31, 3>`
- transcript/hash path: `Keccak256Hash`
- serialized proof bytes: upstream `postcard` fixture `uni_stark_circle_v1.postcard`

This is the best fit for the stated goal: accept upstream proofs unchanged at the byte level before doing any Solana engineering.

## Pinned Candidates

### Stwo

- repo: `https://github.com/starkware-libs/stwo`
- evaluated commit: `93dd93e04f42edba48d8984858c8c39ce9f30c8c`
- toolchain: `nightly-2025-07-14` from `rust-toolchain.toml`
- build status on current main:
  - `cargo check -p stwo-examples`: passed
  - `cargo test -p stwo-examples wide_fib_prove_with_blake -- --nocapture`: passed

### Plonky3 / p3-circle

- repo: `https://github.com/Plonky3/Plonky3`
- evaluated commit: `0f87f2b543a01880274965c410bf804c124f5046`
- toolchain: stable Rust per repo README, no pinned nightly file found
- build status on current main:
  - `cargo check -p p3-examples`: passed
  - `cargo test -p p3-uni-stark --test fib_air verify_circle_compat_fixture -- --exact --nocapture`: passed

Raw command output is preserved under `results/circle-spike/raw/phase1/`.

## Comparison Against Selection Criteria

| Criterion | Stwo | p3-circle |
| --- | --- | --- |
| 1. Proof format stable and documented enough to mirror-parse | Weak. Proof structs are `serde` serializable, but I did not find a canonical emitted byte encoding or checked-in fixture. The examples keep proofs in memory. | Strong. Upstream ships a checked-in `postcard` circle fixture and a verifier test that consumes those exact bytes. |
| 2. Can generate proofs for a simple statement | Moderate. `wide_fibonacci` is the simplest obvious shipped path, but it is still a fairly wide AIR: 100 trace columns and 98 recurrence constraints per row. | Strong. Upstream `fib_air.rs` has a minimal Fibonacci AIR with 2 columns, 3 public values, degree-2 constraints, and an 8-row circle fixture. |
| 3. Hash function alignment with Solana syscalls | Weak. The simple shipped paths use Blake2s or Poseidon252; neither has a Solana syscall equivalent. | Better. The selected fixture path uses `Keccak256Hash`, which maps naturally to Solana's Keccak syscall family. |
| 4. Maintained and buildable from current main | Good, but requires pinned nightly. | Good, and builds cleanly on stable. |

On the priority order given in the prompt, `p3-circle` wins clearly on criterion 1 and also on criterion 3.

## Candidate Details

### Stwo

#### Public API surface for a simple proof

The easiest working upstream path I found is the `wide_fibonacci` example/test flow in `crates/examples/src/wide_fibonacci/mod.rs`.

The proof flow is low-level and manual:

1. build a trace with `generate_trace::<FIB_SEQUENCE_LENGTH, _>(&inputs)`
2. build `PcsConfig`
3. precompute twiddles
4. build `CommitmentSchemeProver`
5. commit the preprocessed trace tree
6. commit the main trace tree
7. create a `WideFibonacciComponent`
8. call `stwo::prover::prove`
9. manually reconstruct verifier commitments
10. call `stwo::core::verifier::verify`

This is workable, but it is not a single canonical "emit proof bytes" API.

#### Simple statement profile

For the shipped `WideFibonacciEval<100>` example:

- trace width: 100 columns
- per-row recurrence constraints: 98
- trace height in upstream tests: `2^log_n_instances` with `log_n_instances` in `4..=8`
- default security params in most tests:
  - `pow_bits = 10`
  - `FriConfig::new(0, 1, 3, 1)`
  - effective security bits = `10 + 1*3 = 13`

Observed proof size estimates from upstream test logs:

- log size 4: about 4144-4384 bytes
- log size 5: about 4672-5088 bytes
- log size 6: about 5040-5776 bytes
- log size 7: about 5536-6096 bytes
- log size 8: about 5856-6384 bytes

Those numbers are attractive for Solana, but they come from an in-memory estimate, not a canonical upstream byte fixture.

#### Proof serialization format

`StarkProof<H>` wraps `CommitmentSchemeProof<H>` and derives `Serialize`/`Deserialize`. Structurally the proof contains:

- `commitments`
- `sampled_values`
- `decommitments`
- `queried_values`
- `proof_of_work`
- `fri_proof`
- `config`

Important limitation: I did not find a canonical upstream byte encoding such as `postcard`, `bincode`, or a checked-in proof fixture. That means the repo defines a proof object shape, but not a stable proof byte format I can mirror against without making an extra encoding choice.

For this spike, that is a serious problem.

#### Hash function

For the simple example paths:

- Blake path: `Blake2sM31Channel` + `Blake2sM31MerkleChannel`
- alternate path: `Poseidon252Channel` + `Poseidon252MerkleChannel`

Neither is a Solana syscall hash.

#### Field tower

Stwo uses the M31 tower directly:

- base field: `M31`
- complex extension: `CM31`
- secure extension: `QM31`

This matches the Circle-STARK M31 / CM31 / QM31 tower you called out.

#### User-configurable vs derived parameters

User-configurable:

- `PcsConfig { pow_bits, fri_config, lifting_log_size }`
- `FriConfig { log_last_layer_degree_bound, log_blowup_factor, n_queries, fold_step }`
- channel / Merkle backend choice
- AIR / component choice
- trace height and input instances

Derived:

- security bits from `pow_bits + log_blowup_factor * n_queries`
- twiddles from the chosen domain
- max degree bounds from the AIR and PCS config
- sample points, challenges, queries, commitments, and decommitments

### Plonky3 / p3-circle

#### Public API surface for a simple proof

There are two relevant upstream surfaces:

1. `examples/src/proofs.rs` provides a high-level helper `prove_m31_keccak(...)` for circle proofs over `Mersenne31`.
2. `uni-stark/tests/fib_air.rs` provides the simplest concrete compatibility target:
   - build a `CircleConfig`
   - generate an 8-row Fibonacci trace
   - call `p3_uni_stark::prove(&config, &FibonacciAir {}, trace, &pis)`
   - serialize with `postcard::to_allocvec`
   - verify with `p3_uni_stark::verify`

For this spike, the second path is the right starting point because it already has stable upstream bytes.

#### Simple statement profile

From `uni-stark/tests/fib_air.rs`:

- AIR: Fibonacci recurrence
- trace width: 2 columns
- public values: 3
- max constraint degree: 2
- trace length in the compatibility fixture: 8 rows
- selected circle config:
  - `log_blowup = 1`
  - `log_final_poly_len = 0`
  - `max_log_arity = 1`
  - `num_queries = 40`
  - `commit_proof_of_work_bits = 0`
  - `query_proof_of_work_bits = 8`

Observed upstream fixture size:

- `uni_stark_circle_v1.postcard`: `29332` bytes

This is already far above Solana's 1232-byte transaction limit, so staged upload is almost certainly required later. That is not a reason to reject it for Phase 2, but it is an early Solana risk signal.

#### Proof serialization format

This is the strongest part of the p3-circle option.

The proof is a `postcard` serialization of `p3_uni_stark::Proof<CircleConfig>`. At a high level it contains:

- `commitments`
  - `trace`
  - `quotient_chunks`
  - `random`
- `opened_values`
  - `trace_local`
  - `trace_next`
  - `preprocessed_local`
  - `preprocessed_next`
  - `quotient_chunks`
  - `random`
- `opening_proof`
  - `CirclePcsProof`
    - `first_layer_commitment`
    - `lambdas`
    - `fri_proof`
      - `commit_phase_commits`
      - `query_proofs`
      - `final_poly`
      - `pow_witness`

Evidence that this byte format is already an upstream compatibility target:

- upstream ships `uni-stark/tests/fixtures/uni_stark_circle_v1.postcard`
- upstream test `verify_circle_compat_fixture` deserializes those bytes and verifies them successfully

That is exactly the kind of byte-level anchor this spike needs.

#### Hash function

For the selected compatibility fixture path:

- transcript hash: `Keccak256Hash`
- Merkle/MMCS hashing and compression: `Keccak256Hash`-based serializing hasher/compression

This is the best Solana-aligned option among the two candidates.

#### Field tower

For the selected circle fixture path:

- base field: `Mersenne31`
- extension field: `BinomialExtensionField<Mersenne31, 3>`

This is not the Stwo `M31 / CM31 / QM31` tower. If we select p3-circle, the mirror verifier in Phase 2 must follow the p3 field choices exactly and not substitute the Stwo tower.

#### User-configurable vs derived parameters

User-configurable:

- `FriParameters { log_blowup, log_final_poly_len, max_log_arity, num_queries, commit_proof_of_work_bits, query_proof_of_work_bits }`
- choice of base field
- choice of extension field
- choice of hash / MMCS
- AIR
- trace rows and public inputs

Derived:

- `degree_bits`
- query indices and FRI folding schedule
- batching challenges and `lambdas`
- commitment/opening structure
- proof-of-work witnesses

## Why p3-circle is the better validation target

The spike is governed by "no protocol changes" and "accept upstream proofs unchanged at the byte level."

That makes the decisive question:

Can I point to an upstream-produced proof blob, keep its bytes unchanged, and verify those exact bytes with a mirror parser/verifier?

For `p3-circle`, the answer is already yes in upstream form:

- there is a checked-in proof blob
- there is a defined codec (`postcard`)
- there is an upstream verification test that consumes the blob unchanged

For `Stwo`, the answer is not yet yes:

- the proof object is serializable
- but I did not find an upstream-defined emitted byte format to lock onto
- I did not find a checked-in proof blob or a compatibility test that verifies fixed bytes

That is enough to prefer `p3-circle` for a validation-first spike.

## Risks Carried Forward

These are not reasons to reject the reference, but they should shape Phase 2 and Phase 3 expectations.

1. `p3-circle` proof size is already large for a tiny example.
2. The selected p3 field extension is not the Stwo M31 / CM31 / QM31 tower.
3. Even if byte-level roundtrip succeeds, Solana plausibility may still fail on proof size or CU cost.

## Decision

Selected reference: `p3-circle` in `Plonky3` commit `0f87f2b543a01880274965c410bf804c124f5046`.

Selected validation target inside that repo:

- `uni-stark/tests/fib_air.rs`
- fixture: `uni-stark/tests/fixtures/uni_stark_circle_v1.postcard`
- verification test: `verify_circle_compat_fixture`

## Stop Point

Per instruction, implementation has not started. Do not begin Phase 2 until this reference selection is confirmed.
