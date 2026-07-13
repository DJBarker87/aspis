# Profile 23 zero-factor integration

**Status (`2026-07-13`): released. The q16/rate-1/512 Johnson-sound
Profile-23 proof, complete Good23 gate, q3/cap16 worker, fixed release,
complete-view computational hiding in the declared SHA-256 ROM/EPRO
fixed-channel model, and one-transaction production SBF path are integrated.
The fail-closed release certificate is green on all 30/30 gates.**

Profile 23 appends one full-domain QM31 zero-factor lane `D` after `H26/G27`.
The generator order is `semantic0..15, mask16..25, H26, G27, D28`; the D
factor identifier is `0`, C2 has three columns, and the layout-factor
fingerprint is `0x233ba2ca68f94148`.

## Frozen diagnostic proof and transcript

The committed unmined diagnostic proof is:

| item | value |
|---|---:|
| bytes | 59,679 |
| SHA-256 | `07f8258f9297bd19d007b5bebdfbb710e8e44dcc2277f8cf7a6148db6ce902` |
| opening section bytes | `[16518, 12934, 9350, 7814, 6278]` |
| frontier nodes | `[292, 292, 244, 196, 148]` |
| query candidates | 3 |
| selected fixture branch | 0 |
| query count | 16 |

The D claims are absorbed under label 43. Exactly one selector byte is
absorbed under label 44 after the final nonce. The three candidate schedules
are independent clones of the same pre-query state; selectors are never
chained into one transcript.

## Good23 and bounded release

Every selector is evaluated against the complete product:

- root-neutral rank `1,404/1,404`;
- remaining G/D query rank `256` and terminal Schur rank `12`; and
- inactive-balanced H1 query rank `256` and terminal Schur rank `12`.

The complete degrees are `q=28,544`, `z=41,280`, `gamma=92,436`, and
continuous `133,716`. On the frozen proof all three schedules are good and
the least selector is 0. The exact three-branch gate took `60.89 s`.

One production attempt retains one set of commitments, trees, salts, folds
and PoW state. It derives all three schedules, serializes only the least good
opening, retries an all-bad triple, and treats schema/transcript/layout/gate
errors as fatal. The cap is 16; durable nonces are burned before selection and
rejected scratch is scrubbed. The output is opaque until the fixed boundary,
where exactly one proof or payload-free abort is published.

The cap-16 rank-exhaustion subterm is `105.41017865405837` bits. The refined
factor-40 soundness floor, applying the selector factor only to q16 miss, is
`101.30230658283051` bits. The coarser whole-ledger-times-three sensitivity
floor, recomputed from Profile 23's own changed terms and 32 BCS boundaries,
is `100.80652861422749` bits. The selected `101.30230658283051`-bit result is
the headline soundness floor; the coarse figure is a sensitivity check.

## Hiding teeth

The 59,679-byte public view has an exact gap/overlap-free inventory. All five
Merkle sections bind values, salts and frontiers; the transcript-order test
binds C1, C2, D claims, PoW work, round data and selector before their dependent
challenges; and the fixture contains no literal private witness block. These
are regression teeth, not a substitute for the affine/EPRO proof.

Four fast privacy tests pass. The fresh-attempt release run also passes in
`141.00 s`: more than half the public bytes change, all roots change, opened
salt sets are disjoint, and nonce reuse fails closed.

Good23 makes the complete non-hash affine simulator exact on every emitted
schedule (`epsilon_aff=0`). With `C=969,993`, cap 16 and `Q_H <= 2^128`, the
declared SHA-256 programmable-random-oracle/EPRO real-vs-simulator bound is
dominated by `2^-104.11238518950232`; the conservative pairwise-witness floor
is `103.11238518950232` bits. This closes complete-view computational hiding
for the fixed public `Proof(bytes)`/payload-free-`Abort` channel. It does not claim
statistical HVZK, standard-model SHA-256 PRG security, or local
filesystem/timing/power/thermal/memory/remote-prover side-channel protection;
`epsilon_side=0` only because those observables are excluded. See
`docs/stage2-profile23-computational-hvzk-closure.md` and
`results/stage2/profile23_computational_hvzk_closure.json`.

## One-transaction SBF measurement

The verifier was split into non-inlined boxed phases after the first SBF build
reported a 5,888-byte stack frame, 1,656 bytes over Solana's 4,096-byte limit.
The rebuilt program has no stack-overwrite diagnostics.

The historical diagnostic overlap-free ledgers reconcile exactly:

| path | CU | headroom below 1.4M |
|---|---:|---:|
| tag 59 read-only | 1,195,306 | 204,694 |
| tag 61, program-owned marker | 1,205,006 | 194,994 |
| tag 61, canonical System create | 1,207,339 | 192,661 |

Corrupt-proof rollback, exact state images, duplicate rejection, and the
two-signer System-path race are green. These rows use the committed unmined
proof and a diagnostic PoW bypass; production tag 60 correctly rejects that
historical unmined fixture.

The released path instead uses the canonically mined proof and the plain
manifest-default production SBF:

| released item | value |
|---|---:|
| mined proof bytes | 61,599 |
| mined proof SHA-256 | `35c4e79316bf4a2af1951e5d2f41b6ebb4ebb7bd1e91a3ba93c52e549bfe7949` |
| default SBF bytes | 6,870,048 |
| default SBF SHA-256 | `6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb` |
| production tag 59, same binary | 1,202,939 CU |
| production tag 60, program-owned zeroed marker | 1,204,792 CU |
| production tag 60, canonical System create | 1,207,123 CU |
| worst-path headroom below 1.4M | 192,877 CU |
| program id | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` |

The current release certificate is
`results/stage2/profile23_one_transaction_release.json`: `released=true`,
30/30 gates green. It binds the selected Johnson soundness floor
`101.30230658283051` bits, with a Profile-23-own coarse sensitivity of
`100.80652861422749` bits, and the complete-view pairwise-witness
computational-hiding floor `103.11238518950232` bits in the declared model;
the one-sided real-vs-simulator bound is `104.11238518950232` bits. The hiding
claim remains computational and model-scoped exactly as stated above.

The final `1,202,920 CU` diagnostic tag-59 acceptance measurement and the
`1,202,939 CU` same-binary production baseline differ by 19 CU.
They are separate measurement contexts: the acceptance artifact reconciles
its own twelve buckets, while each mutation artifact uses its same-run,
same-binary tag-59 baseline to price the signed tag-60 increment. The release
ledger does not treat the 19-CU difference as a saving, and no unsupported
instruction-level cause is assigned to it.

The historical prior-build comparison was `1,202,868` versus `1,202,876`, an
8-CU delta. It is retained only as superseded history and is not a current
production number.

The 59,679-byte diagnostic fixture and 61,599-byte production proof differ
because minimal-subtree frontier geometry is schedule-dependent. The selector
law is public and witness-independent, so this length variation is part of the
simulated public view rather than a witness-dependent release channel.

## Production proof and release reproduction

The harness reads a mined proof from `ASPIS_PROFILE23_PROOF` without replacing
the historical committed fixture. The released mined artifact is
`results/stage2/proofs/atomic_state_only_profile23_v3_mined.bin`. Run
acceptance first so mutation can require the same hash and PoW classification:

```bash
ASPIS_PROFILE23_PROOF=/absolute/path/profile23-mined.bin NO_DNA=1 \
  cargo run --release -p aspis-xtask -- stage2-atomic-profile23-acceptance

ASPIS_PROFILE23_PROOF=/absolute/path/profile23-mined.bin NO_DNA=1 \
  cargo run --release -p aspis-xtask -- stage2-atomic-profile23-mutation
```

For override bytes, historical fixture length/hash pins are deliberately
skipped; the full diagnostic host verifier must still accept, and production
host/SBF must agree on whether PoW is mined. The released KAT confirms that
tag 60 rejects unmined bytes and accepts the pinned mined bytes before the
atomic state write. The release scope is one atomic transaction consuming a
finalized, pre-uploaded proof account. Production tags 59 and 60 require the
all-zero authority sentinel in bytes `8..40` of the unchanged 40-byte header;
proof-account creation, chunk upload, and `FinalizeProof` remain outside that
transaction. Append-only tag 62 performs that irreversible seal, while
append-only tag 63 initializes a live pool. Finalization is a deterministic public transition and adds no
hidden input or EPRO term.

Machine-readable summary:
`results/stage2/profile23_zero_factor_integration.json`.
