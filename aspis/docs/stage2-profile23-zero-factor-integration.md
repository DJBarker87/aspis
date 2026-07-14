# Profile 23 zero-factor integration

**Status (`2026-07-14`): the q18/rate-1/512 Profile-23 zero-factor wire,
complete Good23 gate, q3/cap17 worker, proof-independent soundness ledger, and
declared-model complete-view computational hiding are integrated. The
canonically mined q18 proof, production host/SBF KATs, and local
one-transaction release certificate are green with `35/35` gates. The
`2026-07-13` q16/cap16 30/30 release certificate is superseded historical
evidence.**

Profile 23 appends one full-domain QM31 zero-factor lane `D` after `H26/G27`.
The generator order is `semantic0..15, mask16..25, H26, G27, D28`; the D
factor identifier is `0`, C2 has three columns, and the layout-factor
fingerprint is `0x233ba2ca68f94148`.

## Frozen diagnostic proof and transcript

The active committed q18 unmined diagnostic proof is:

| item | value |
|---|---:|
| bytes | 67,327 |
| SHA-256 | `a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238` |
| opening section bytes | `[18790, 14758, 10726, 8998, 7270]` |
| frontier nodes | `[335, 335, 281, 227, 173]` |
| query candidates | 3 |
| selected fixture branch | 0 |
| query count | 18 |

The D claims are absorbed under label 43. Exactly one selector byte is
absorbed under label 44 after the final nonce. The three candidate schedules
are independent clones of the same pre-query state; selectors are never
chained into one transcript.

## Good23 and bounded release

Every selector is evaluated against the complete product:

- root-neutral rank `1,404/1,404`;
- remaining G/D query rank `288` and terminal Schur rank `12`; and
- inactive-balanced H1 query rank `288` and terminal Schur rank `12`.

The minimum-q-degree basis has 1,068 degree-one and 336 degree-two selected q
columns. The complete degrees are `q=31,320`, `z=41,280`, `gamma=80,688`, and
continuous `121,968`. On the frozen proof all three schedules are good and the
least selector is 0. The three Good branches now run in parallel; the exact
post-release audit took `40.64 s`. Removing 96 discarded sumcheck opening
evaluations reduced the exact unmined build-plus-verify path to `44.09 s`
without changing its bytes or SHA-256. The complete measured runtime record is
`results/stage2/profile23_q18_g37_runtime.json`.

One production attempt retains one set of commitments, trees, salts, folds
and PoW state. It derives all three schedules, serializes only the least good
opening, retries an all-bad triple, and treats schema/transcript/layout/gate
errors as fatal. The cap is 17; durable nonces are burned before selection and
rejected scratch is scrubbed. The output is opaque until the fixed boundary,
where exactly one proof or payload-free abort is published.

The cap-17 rank-exhaustion subterm is `105.21398677941984` bits, and the full
public-abort floor is `105.21398677941983` bits. The explicit work-normalized
BCS calculation uses `R=32`, `lambda=256`, and checks `T=1` and `T=2^128`;
the conservative whole-ledger-times-three release floor is
`100.16144938287455` bits. These are active
q18 theorem values bound into the green local release certificate.

## Hiding teeth

The 67,327-byte q18 public view has an exact gap/overlap-free inventory. All
five Merkle sections bind values, salts and frontiers; the transcript-order test
binds C1, C2, D claims, PoW work, round data and selector before their dependent
challenges; and the fixture contains no literal private witness block. These
are regression teeth, not a substitute for the affine/EPRO proof.

The exact byte inventory and nonce-reuse regression are green. The q18
fresh-attempt rerandomization run remains pending and must not be inferred from
the historical q16 `141.00 s` run.

Good23 makes the complete non-hash affine simulator exact on every emitted
schedule (`epsilon_aff=0`). With `C=969,993`, cap 17 and `Q_H <= 2^128`, the
declared SHA-256 programmable-random-oracle/EPRO real-vs-simulator bound is
dominated by `2^-104.02492234825198`; the conservative pairwise-witness floor
is `103.02492234825198` bits. This closes the proof-independent complete-view
computational-hiding theorem for the fixed public
`Proof(bytes)`/payload-free-`Abort` channel. It does not claim
statistical HVZK, standard-model SHA-256 PRG security, or local
filesystem/timing/power/thermal/memory/remote-prover side-channel protection;
`epsilon_side=0` only because those observables are excluded. See
`docs/stage2-profile23-computational-hvzk-closure.md` and
`results/stage2/profile23_computational_hvzk_closure.json`.

## Green local q18 one-transaction SBF measurement

The verifier was split into non-inlined boxed phases after the first SBF build
reported a 5,888-byte stack frame, 1,656 bytes over Solana's 4,096-byte limit.
The rebuilt program has no stack-overwrite diagnostics.

The fresh q18 build and production-mined tag-59/tag-60 KAT are green:

| q18 release item | value |
|---|---:|
| mined proof bytes | 66,367 |
| mined proof SHA-256 | `f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53` |
| statement SHA-256 | `976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de` |
| canonical public-input digest | `21d73e39be93112f986f52c7d683f2ab478890360a306af81110852ffb16a30a` |
| default SBF bytes | 915,656 |
| default SBF SHA-256 | `da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254` |
| production tag 59 | 1,310,162 CU |
| tag 60, program-owned zeroed marker | 1,312,055 CU |
| tag 60, canonical System creation | 1,314,386 CU |
| worst-path headroom below 1.4M | 85,614 CU |

The verifier's boxed-phase stack fix remains in the active code. The q16
values below are retained only as historical evidence and are not repinned to
q18.

## Superseded q16 SBF evidence (`2026-07-13`)

The q16 diagnostic overlap-free ledgers reconciled exactly:

| path | CU | headroom below 1.4M |
|---|---:|---:|
| tag 59 read-only | 1,195,306 | 204,694 |
| tag 61, program-owned marker | 1,205,006 | 194,994 |
| tag 61, canonical System create | 1,207,339 | 192,661 |

In that q16 run, corrupt-proof rollback, exact state images, duplicate
rejection, and the two-signer System-path race were green. These rows used the
committed unmined proof and a diagnostic PoW bypass; production tag 60
correctly rejected that historical unmined fixture.

The superseded q16 released path used a canonically mined proof and the plain
manifest-default production SBF:

| historical q16 item | value |
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

The q16 certificate passed 30/30 gates and bound selected/coarse soundness
floors of `101.30230658283051` and `100.80652861422749` bits, plus
declared-model pairwise/one-sided hiding floors of `103.11238518950232` and
`104.11238518950232` bits. That certificate is superseded; the current q18
release JSON records `released=true` with `35/35` gates. None of these q16
numbers is a current q18 claim.

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

The q16 59,679-byte diagnostic fixture and 61,599-byte production proof differed
because minimal-subtree frontier geometry is schedule-dependent. The selector
law is public and witness-independent, so this length variation is part of the
simulated public view rather than a witness-dependent release channel.

## q18 proof and release reproduction

The harness reads a q18 mined proof from `ASPIS_PROFILE23_PROOF` and its
statement from `ASPIS_PROFILE23_STATEMENT` without replacing the committed
unmined fixture. The booked release used
`results/stage2/proofs/profile23_devnet_sequence0_q18_g37_production_authorizing_guarded_private.bin`
and its `.statement.json` sidecar. Run acceptance first so mutation can
require the same hash, statement, and PoW classification:

```bash
ASPIS_PROFILE23_PROOF=/absolute/path/profile23-q18-mined.bin \
ASPIS_PROFILE23_STATEMENT=/absolute/path/profile23-q18-mined.statement.json \
NO_DNA=1 \
  cargo run --release -p aspis-xtask -- stage2-atomic-profile23-acceptance

ASPIS_PROFILE23_PROOF=/absolute/path/profile23-q18-mined.bin \
ASPIS_PROFILE23_STATEMENT=/absolute/path/profile23-q18-mined.statement.json \
NO_DNA=1 \
  cargo run --release -p aspis-xtask -- stage2-atomic-profile23-mutation
```

For override bytes, fixture length/hash pins are deliberately
skipped; the full diagnostic host verifier must still accept, and production
host/SBF must agree on whether PoW is mined. The green q18 KAT confirms that
tags 59 and 60 reject the committed unmined bytes and accept the pinned mined
bytes before the atomic state write. The release scope remains one atomic
transaction consuming a
finalized, pre-uploaded proof account. Production tags 59 and 60 require the
all-zero authority sentinel in bytes `8..40` of the unchanged 40-byte header;
proof-account creation, chunk upload, and `FinalizeProof` remain outside that
transaction. Append-only tag 62 performs that irreversible seal, while
append-only tag 63 initializes a live pool. Finalization is a deterministic public transition and adds no
hidden input or EPRO term.

The green certificate is local release evidence, not a mainnet deployment or
an external security audit; those remain separate blockers. The q18
fresh-attempt rerandomization regression remains pending and is not inferred
from the production KAT.

Machine-readable summary:
`results/stage2/profile23_zero_factor_integration.json`.
