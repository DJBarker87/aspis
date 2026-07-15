# Profile 23 host Good predicate and q3 selector

**Status (`2026-07-14`): the exact q18 host predicate, q3 selector, cap-17
first-Good builder, fixed-boundary proof/abort controller, complete-Good
product, and complete-view computational hiding are green in the declared
SHA-256 ROM/EPRO fixed-channel model. The canonically mined q18 proof,
tag59/tag65 host/SBF evidence, and local one-transaction release are green
with `36/36` gates. The previous q16 certificate is historical evidence and
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
A historical isolated audit of the 63,487-byte predecessor mined proof
(SHA-256
`0e6d33cec0e18842b37b5f3ec1883a6a9f8b52a8be774e10386400508c8708cb`)
took `40.64 s` and found all three branches good with selector 0 least. For
that same predecessor artifact, an optimized-Metal fixed-boundary run returned
`Proof` at `480.42 s` under the configured 480-second schedule. Neither figure
is a timing for the current 64,447-byte release proof (SHA-256
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`);
this artifact records no current-proof wall time. The separate unmined-fixture
build-plus-verify benchmark is `44.09 s` for the 67,327-byte fixture above.
The complete predecessor benchmark record is
`results/stage2/profile23_q18_g37_predecessor_runtime.json`.

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

The released production proof is 64,447 bytes with SHA-256
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`;
its canonical statement sidecar has SHA-256
`947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2`.
Its canonical public-input digest is
`b2d150dfcb6432c1b6f2e3892ee45a9aa5f393809d97c8292fea975b3da35fa3`.
All three production Good23 branches accept and serialized selector `0` is
the least Good branch. The freshly built default SBF is 921,848 bytes with
SHA-256
`97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a`.
Production tag59 costs `1,303,642 CU`; tag65 costs `1,338,471 CU` on the
program-owned marker path and `1,340,803 CU` on canonical System creation.
The maximum leaves `59,197 CU` below 1.4M.

`results/stage2/profile23_one_transaction_release.json` records
`released=true`, `status=released_all_required_gates_green`, and `36/36`
passing gates. It binds the conservative release soundness floor
`100.16144938287455` bits and the declared-model
real-vs-simulator/pairwise hiding floors
`104.02492234825198`/`103.02492234825198` bits.

Production tag59 and tag65 continue to require the all-zero authority sentinel
in bytes `8..40` of the unchanged 40-byte finalized proof-account header;
proof-account creation, chunk upload, and `FinalizeProof` are outside the
one-transaction measurement. Append-only tag 62 seals the proof account and
append-only tag 63 initializes the pool. None of the old q16 proof size, CU,
SBF hash, or `30/30` release results is transferred to q18. The green q18
certificate is local release evidence, not mainnet or external-audit evidence.
The finalized mainnet execution and current audit status are recorded
separately in [`profile23-mainnet-demo.md`](profile23-mainnet-demo.md) and the
[prepublication security review](reviews/profile23-prepublication-security-review.html).

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
panic-collapse gate. The retained historical predecessor-audit result is
all-good/least-0 in `40.64 s`; no current-release timing is inferred from it.
The opening-equivalence test reproduces the unchanged 67,327-byte unmined
fixture after the `44.09 s` optimized build-plus-verify path.

Machine-readable result:
`results/stage2/profile23_good_schedule_host.json`.
