# Profile 23 host Good predicate and q3 selector

**Status (`2026-07-14`): the exact q18 host predicate, q3 selector, cap-17
first-Good builder, fixed-boundary proof/abort controller, complete-Good
product, and complete-view computational hiding are green in the declared
SHA-256 ROM/EPRO fixed-channel model. The canonically mined q18 proof,
tag-59/tag-60 host/SBF evidence, and local one-transaction release are green
with `35/35` gates. The previous q16 certificate is historical evidence and
does not authorize q18.**

`crates/aspis-prover/src/state_only_good23.rs` turns the frozen complete-Good
product into a strict schedule-only host API. A schedule is good only when all
three required blocks pass:

1. D-after-G root-neutral rank `1,404 / 1,404`;
2. remaining G/D raw query rank `288` and terminal Schur rank `12`; and
3. inactive-balanced H1 raw query rank `288` and terminal Schur rank `12`.

The runtime echelon minor fingerprints are diagnostic and may vary with the
schedule. They are not compared to the frozen anchor fingerprints. The
definition instead pins the schema/layout, width `29`, D index `28`, q18,
rate `1/512`, domain log `19`, batch grinding g37, fold grinding
`[34,33,30,25]`, final grinding g32, q3/cap17, and the complete degree tuple
`(q,z,gamma,continuous)=(31320,41280,80688,121968)`. The root-neutral
minimum-degree basis contains exactly `1,068` degree-one and `336` degree-two
columns, so its q-individual degree is `1,740` and its q-total degree is
`31,320`. The definition
fingerprint is

```text
0x927920b10ba31373c1909ef9bfb7ae7cb9570c7e2536d294347834b3c83dcb26
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
| 0 | 1,404 | 12 | 12 | `0xfc0706f3a304ae26` |
| 1 | 1,404 | 12 | 12 | `0x1eb7a0d4a2b3f79f` |
| 2 | 1,404 | 12 | 12 | `0xa8e5683ced1e2d1c` |

The deterministic q18 fixture is `67,327` bytes, SHA-256
`a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238`.
The three predicates now run in parallel and retain fixed selector ordering.
The exact post-release audit of the mined proof took `40.64 s` wall time and
confirmed that all three branches are good and selector `0` is least. The
sumcheck opening path also stopped computing 96 values that it discarded:
the exact unmined build-plus-verify path fell from `167–194 s` to `44.09 s`
while reproducing the same 67,327-byte proof and SHA-256.

With the optimized Metal miner, the q18/g37 production proof published
successfully at `480.42 s` on its configured 480-second fixed boundary. The
complete runtime record is
`results/stage2/profile23_q18_g37_runtime.json`.

## Integrated production boundary

The production builder retains one common attempt's private trees and salts,
derives and evaluates all three post-final schedules, and serializes openings
only for the least good branch. An all-bad triple is retryable; schema,
transcript, layout and internal gate errors are fatal and collapse to the same
opaque public error. Every complete rejected attempt has already burned its
durable mask nonce and its scratch buffers are scrubbed. The attempt cap is
exactly 17. The complete-Good rank-exhaustion and public-abort floors are
respectively `105.21398677941984` and `105.21398677941983` bits.

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
Profile-23 EPRO inventory `C=969,993`, cap 17, and `Q_H <= 2^128`, the declared
SHA-256 programmable-random-oracle real-vs-simulator bound is dominated by
`2^-104.02492234825198`. Passing through that simulator gives the conservative
pairwise-witness floor `103.02492234825198` bits. The q18 public-byte inventory
is gap-free and overlap-free across all `67,327` bytes, all five sections bind
roots, values, salts and frontiers, and nonce reuse fails closed.

This is computational hiding in the explicitly declared ROM/EPRO and fixed
public `Proof`/`Abort` channel model. It is not statistical HVZK, not a
standard-model SHA-256 PRG claim, and not protection against local
filesystem/timing/power/thermal/memory or remote-prover/miner observables;
`epsilon_side=0` only because those channels are excluded. See
`docs/stage2-profile23-computational-hvzk-closure.md` and
`results/stage2/profile23_computational_hvzk_closure.json`.

## Exact q18 soundness ledger

The q18 proven-Johnson anchors are `107.31602011435538` bits for the batch,
`108.98543226575069` bits for the union of folds g34/g33/g30/g25, and
`110.18373913364348` bits for the g32 final check after the three-branch
selector union. Their event union is `106.7020334873029` bits. The explicit
work-normalized BCS formula uses `R=32`, `lambda=256`, and checks both
`T=1` and `T=2^128`; its selected endpoint floors are
`101.65763936794444` and `106.70203180861958` bits. The selected factor-40
diagnostic is `101.38010539241553` bits. Reconstructing the unselected event
union and applying the same BCS endpoint check followed by the whole-ledger
factor three gives the authorizing release floor `100.16144938287455` bits. The cap-17
three-candidate sampler term is far below these errors at
`550.9238900176506` bits.

## Local q18 production release

The deterministic unmined theorem fixture remains
`results/stage2/proofs/atomic_state_only_profile23_v3_unmined.bin`, `67,327`
bytes, SHA-256
`a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238`.
It is not a production proof and cannot authorize release.

The released production proof is 63,487 bytes with SHA-256
`0e6d33cec0e18842b37b5f3ec1883a6a9f8b52a8be774e10386400508c8708cb`;
its canonical statement sidecar has SHA-256
`520a0a86e1d1918a5270622ac27182b1f5b6df2b624d68bbd2a2b6f927eebb14`.
All three production Good23 branches accept and serialized selector `0` is
the least Good branch. The freshly built default SBF is 915,656 bytes with
SHA-256
`da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254`.
Production tag 59 costs `1,299,012 CU`; tag 60 costs `1,300,905 CU` on the
program-owned marker path and `1,303,236 CU` on canonical System creation.
The maximum leaves `96,764 CU` below 1.4M.

`results/stage2/profile23_one_transaction_release.json` records
`released=true`, `status=released_all_required_gates_green`, and `35/35`
passing gates. It binds the conservative release soundness floor
`100.16144938287455` bits and the declared-model
real-vs-simulator/pairwise hiding floors
`104.02492234825198`/`103.02492234825198` bits.

Production tags 59 and 60 continue to require the all-zero authority sentinel
in bytes `8..40` of the unchanged 40-byte finalized proof-account header;
proof-account creation, chunk upload, and `FinalizeProof` are outside the
one-transaction measurement. Append-only tag 62 seals the proof account and
append-only tag 63 initializes the pool. None of the old q16 proof size, CU,
SBF hash, or `30/30` release results is transferred to q18. The green q18
certificate is local release evidence, not a mainnet deployment or an
external security audit; those remain separate blockers.

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

The Good23 suite includes the fixed-order parallel manager and its
panic-collapse gate. The production post-release audit is all-good/least-0 in
`40.64 s`; the opening-equivalence test reproduces the unchanged unmined
proof after the `44.09 s` optimized build-plus-verify path.

Machine-readable result:
`results/stage2/profile23_good_schedule_host.json`.
