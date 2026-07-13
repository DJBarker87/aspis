# Profile 23 host Good predicate and q3 selector

**Status (`2026-07-13`): exact host predicate, q3 selector, cap-16
first-good builder, fixed-boundary proof/abort release, and complete-view
computational hiding are green in the declared SHA-256 ROM/EPRO fixed-channel
model. Profile 23 is now released as the default one-transaction production
path after all `30/30` release gates passed. This earlier host-schedule
artifact did not itself change or enable the production wire.**

`crates/aspis-prover/src/state_only_good23.rs` turns the frozen complete-Good
product into a strict schedule-only host API. A schedule is good only when all
three required blocks pass:

1. D-after-G root-neutral rank `1,404 / 1,404`;
2. remaining G/D raw query rank `256` and terminal Schur rank `12`; and
3. inactive-balanced H1 raw query rank `256` and terminal Schur rank `12`.

The runtime echelon minor fingerprints are diagnostic and may vary with the
schedule. They are not compared to the frozen anchor fingerprints. The
definition instead pins the schema/layout, width `29`, D index `28`, q16,
rate `1/512`, domain log `19`, q3/cap16, and the complete degree tuple
`(q,z,gamma,continuous)=(28544,41280,92436,133716)`. The definition
fingerprint is

```text
0x9cdd6a6c14b796760c8dd73329effbfc734a048ccecc4ce10f214bdae3a6af2a
```

## Public API

```text
evaluate_profile23_strong_good_schedule(schedule)

derive_profile23_query_candidate_schedules_host(...)
derive_profile23_query_candidate_schedules_host_unmined_for_diagnostics(...)

evaluate_profile23_candidate_schedules_host(&[schedule; 3])

evaluate_profile23_query_candidates_host(...)
evaluate_profile23_query_candidates_host_unmined_for_diagnostics(...)

build_hiding_atomic_state_only_profile23_first_good_v3(...)

Profile23FixedReleaseController::record_first_good_completion(...)
Profile23FixedReleaseController::release(...)
```

The q3 replay creates three independent transcript executions from the same
prefix. Each absorbs exactly one label-44 selector byte, `0`, `1`, or `2`;
selectors are never absorbed sequentially into one state. Before evaluating
Good, it asserts equality of the entire pre-query schedule: prefix including
`z/gamma/point_scale`, OOD points, `mu`, `alpha`, and
`state_before_grinding`. Only queries and `state_after_queries` may differ.

All three Good predicates are evaluated before selection, and the returned
selector is the least good index. The mock suite covers least-good selectors
0, 1 and 2, plus all-bad, and checks the evaluator was called exactly three
times. Selector `3` is rejected by the Profile-23 prefix parser.

## Frozen real replay

On `atomic_state_only_profile23_v3_unmined.bin`, all three selector branches
are good and the least selector is `0`:

| selector | root rank | G/D Schur | H1 Schur | dynamic product fingerprint |
|---:|---:|---:|---:|---:|
| 0 | 1,404 | 12 | 12 | `0xc73e789daa54c8dd` |
| 1 | 1,404 | 12 | 12 | `0xd5e21e461ef4e5d2` |
| 2 | 1,404 | 12 | 12 | `0x9d1bcf6c743771ff` |

The optimized release test took `60.89 s` for the three predicates, about
`20.30 s` per branch. A cap-16 worst case is therefore roughly 16.2 minutes of
Good-gate time before counting proof construction. This is a host-latency
concern, not verifier CU. The likely remedy is to cache the common encoder,
row maps and continuous schedule work across the three q branches.

Separately, the ignored selector integration test built and verified three
complete unmined proofs—one for each valid selector—in `237.52 s`. That is
proof construction plus opening verification, not Good-gate latency.

## Integrated production boundary

The production builder retains one common attempt's private trees and salts,
derives and evaluates all three post-final schedules, and serializes openings
only for the least good branch. An all-bad triple is retryable; schema,
transcript, layout and internal gate errors are fatal and collapse to the same
opaque public error. Every complete rejected attempt has already burned its
durable mask nonce and its scratch buffers are scrubbed. The attempt cap is
exactly 16.

The builder returns an opaque `Profile23FirstGoodCandidate`. The only public
edge is the shared fixed-release controller: at the caller-selected boundary
it publishes exactly one `Proof(bytes)` or payload-free `Abort`. It never
publishes the selector, retry count, rank reason, partial proof, nonce or
progress event. This closes the previously separate two-phase/release wiring;
it does not replace the wallet/process side-channel assumptions stated by the
release controller.

## Computational hiding closure

Good23 is the runtime premise that makes the complete non-hash field simulator
exact on every emitted schedule: `epsilon_aff=0`. Combined with the final
Profile-23 EPRO inventory `C=969,993`, cap 16, and `Q_H <= 2^128`, the declared
SHA-256 programmable-random-oracle real-vs-simulator bound is dominated by
`2^-104.11238518950232`. Passing through that simulator gives the conservative
pairwise-witness floor `103.11238518950232` bits. The fresh-attempt regression
also passes in `141.00 s`: more than half the public bytes change, every root
changes, opened salt sets are disjoint, and nonce reuse fails closed.

This is computational hiding in the explicitly declared ROM/EPRO and fixed
public `Proof`/`Abort` channel model. It is not statistical HVZK, not a
standard-model SHA-256 PRG claim, and not protection against local
filesystem/timing/power/thermal/memory or remote-prover/miner observables;
`epsilon_side=0` only because those channels are excluded. See
`docs/stage2-profile23-computational-hvzk-closure.md` and
`results/stage2/profile23_computational_hvzk_closure.json`.

## Current production release

The later production integration completed the gates outside this schedule
artifact's scope. `results/stage2/profile23_one_transaction_release.json`
records `released=true` with all `30/30` required gates green. The
certificate's one-transaction scope is atomic verification and mutation using
a finalized, pre-uploaded proof account. Production tags 59 and 60 require the
all-zero authority sentinel in bytes `8..40` of the unchanged 40-byte header;
proof-account creation, chunk upload, and `FinalizeProof` are excluded.
Append-only tag 62 seals the proof account, append-only tag 63 initializes the
pool, and the frozen program id is
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`. The
released mined proof is
`results/stage2/proofs/atomic_state_only_profile23_v3_mined.bin`, `61,599`
bytes, SHA-256
`35c4e79316bf4a2af1951e5d2f41b6ebb4ebb7bd1e91a3ba93c52e549bfe7949`.
The manifest-default production SBF is `6,870,048` bytes, SHA-256
`6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`.

Same-binary production tag 59 is `1,202,939 CU`. Literal production tag 60
measures `1,204,792 CU` for the program-owned zeroed mutation account and
`1,207,123 CU` for canonical System-owned account
creation. The latter leaves the worst-case measured headroom of exactly
`192,877 CU` below the `1,400,000 CU` cap. The released ledger's selected
Johnson soundness floor is `101.30230658283051` bits, with a Profile-23-own
whole-ledger-times-three/BCS32 sensitivity of `100.80652861422749` bits; the
complete-view pairwise-witness computational-hiding floor is
`103.11238518950232` bits in
the declared SHA-256 ROM/EPRO fixed-release-channel model, with a
`104.11238518950232`-bit real-vs-simulator bound. Release does not weaken or
broaden the theorem and model caveats above.

## Tests

```bash
NO_DNA=1 cargo test -p aspis-prover --lib state_only_good23::tests \
  -- --skip frozen_profile23_fixture_runs_exact_good23_on_all_selectors

NO_DNA=1 cargo test --release -p aspis-prover --lib \
  state_only_good23::tests::frozen_profile23_fixture_runs_exact_good23_on_all_selectors \
  -- --ignored --nocapture

NO_DNA=1 cargo test --release -p aspis-prover \
  --test profile23_zero_factor_integration \
  --features insecure-profile23-fixture \
  profile23_all_three_selectors_build_and_verify -- --ignored --nocapture
```

The Good23 suite is `5` fast tests plus `1` ignored exact-q3 test. The exact
q3 run is all-good/least-0 in `60.89 s`; the separate three-proof selector run
passes in `237.52 s`.

Machine-readable result:
`results/stage2/profile23_good_schedule_host.json`.
