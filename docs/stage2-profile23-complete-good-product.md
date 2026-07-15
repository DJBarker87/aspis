# Profile 23 complete Good-product provenance

**Status (`2026-07-14`): the q18 complete-Good product and q3/cap17 first-Good
theorem gate are green, and the product is used by the closed complete-view
computational-hiding theorem in the declared SHA-256 ROM/EPRO fixed-channel
model. The local q18 release is green: the canonically mined production proof,
production host/SBF KATs, and one-transaction certificate pass all `36/36`
gates. The `2026-07-13` q16/cap16 certificate is superseded historical
evidence.**

The executable joins three independently selected nonzero minors:

1. the 1,404-row D-after-G root-neutral terminal-plus-compressed-sumcheck
   minor;
2. the 12-row terminal Schur complement of the remaining independent G/D raw
   direction; and
3. the 12-row terminal Schur complement of the inactive-balanced H1 padding
   direction.

For each raw certificate, the replay first eliminates all 288 M31 query
coordinates. It then records the stable source ID, terminal pivot row and
nonzero pre-normalization pivot value of every Schur-complement pivot. Source
IDs are `4` tower-coordinate blocks of `1,024` trace rows:

```text
source_id = tower_coordinate * 1024 + trace_row.
```

The active q18 certificate is:

| component | rank | fingerprint |
|---|---:|---:|
| root-neutral minor | 1,404 | `0x6b3838662fbf34db` |
| remaining G/D terminal Schur | 12 | `0x1f34525db611d292` |
| H1 inactive-padding terminal Schur | 12 | `0xe70215f0b4795f52` |
| bound product provenance | — | `0xfc0706f3a304ae26` |

Both raw query ranks are exactly `288`; both terminal Schur ranks are exactly
`12`; and every recorded pivot value is nonzero in M31. The full source,
pivot and value lists are frozen in
`results/stage2/profile23_complete_good_product.json`.

The product fingerprint additionally binds the degree tuple:

```text
q degree                         31,320
root-neutral z degree            41,040
remaining G/D terminal z degree     120
H1 terminal z degree                120
complete z degree                41,280
gamma-coordinate degree          80,688
continuous degree               121,968
```

This closes the executable premise in the q3/cap17 liveness bound. The runtime
gate evaluates all three branches of one retained attempt, selects the least
good selector, retries only an all-bad triple, and feeds an opaque candidate
to the fixed-boundary release controller. Selectors 0, 1 and 2 have each built
and verified as complete q18 proofs. The Good branches now run in parallel.
On the historical 63,487-byte predecessor proof (SHA-256
`0e6d33cec0e18842b37b5f3ec1883a6a9f8b52a8be774e10386400508c8708cb`),
the isolated all-selector audit took `40.64 s`, and a fixed-boundary run
returned `Proof` at `480.42 s` under the configured 480-second schedule.
These are predecessor-only engineering benchmarks; no corresponding wall time
is recorded for the current 64,447-byte release proof (SHA-256
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`).
Separately, the optimized unmined build-plus-verify path took `44.09 s` for the
67,327-byte fixture (SHA-256
`a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238`)
and reproduced that fixture exactly. The benchmark record is
`results/stage2/profile23_q18_g37_predecessor_runtime.json`.

The complete field-view simulator is exact on every schedule accepted by this
product (`epsilon_aff=0`). With the fixed release channel and EPRO inventory,
complete-view computational hiding is above 100 bits in the declared model;
see `docs/stage2-profile23-computational-hvzk-closure.md` and
`results/stage2/profile23_computational_hvzk_closure.json`. This is neither a
statistical nor standard-model claim. Its `epsilon_side=0` excludes local
filesystem/timing/power/thermal/memory channels and remote-prover traffic; it
is not a physical side-channel bound.

The root-neutral rank certificate is pinned to the 67,327-byte q18 unmined
fixture, SHA-256
`a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238`.
Its production transfer is explicit rather than proof-byte equality:
the rank maps depend on the frozen q18 layout and schedule, not the witness;
the release gate must match the layout fingerprint and Good23 definition
fingerprint to live code; and the production selector audit must be green on
all three branches. The fixture replay and mined-proof all-selector repin are
green. The released 64,447-byte production proof has SHA-256
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`;
it is not assumed byte-equal to the theorem fixture.

The superseded q16 unmined diagnostic SBF path was measured at `1,195,306 CU`
read-only and at most `1,207,339 CU` including atomic mutation. Those
measurements remain useful only as historical diagnostic evidence and do not
transfer to the q18 wire.

## Current local q18 release state

`results/stage2/profile23_one_transaction_release.json` currently records
`released=true`, `status=released_all_required_gates_green`, and `36/36`
passing gates. It binds the 64,447-byte proof above and its statement sidecar,
whose SHA-256 is
`947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2`.
The canonical public-input digest is
`b2d150dfcb6432c1b6f2e3892ee45a9aa5f393809d97c8292fea975b3da35fa3`.
The fresh default SBF is 921,848 bytes with SHA-256
`97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a`.
Production tag59 costs `1,303,642 CU`; tag65 costs `1,338,471 CU` on the
program-owned path and `1,340,803 CU` on canonical System creation. The
maximum leaves `59,197 CU` below 1.4M.

The proof-independent conservative Johnson/BCS release floor is
`100.16144938287455` bits. The
declared-model pairwise-witness computational-hiding floor is
`103.02492234825198` bits; the one-sided real-vs-simulator bound is
`104.02492234825198` bits.

The intended one-transaction scope remains atomic verification and mutation
using a finalized, pre-uploaded proof account. Production tag59 and tag65
require the all-zero authority sentinel in bytes `8..40` of the unchanged
40-byte header; proof-account creation, chunk upload, and `FinalizeProof` are
excluded. Append-only tag 62 seals the proof account, append-only tag 63
initializes the pool, and the configured local program id is
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`. That configured address is not
deployment evidence. This is a local release certificate, not mainnet or
external-audit evidence. The finalized mainnet execution and current audit
status are recorded separately in
[`profile23-mainnet-demo.md`](profile23-mainnet-demo.md) and the
[prepublication security review](reviews/profile23-prepublication-security-review.html).

## Superseded q16 release evidence (`2026-07-13`)

The earlier q16/cap16 release passed 30/30 gates. It used a 61,599-byte mined
proof with SHA-256
`35c4e79316bf4a2af1951e5d2f41b6ebb4ebb7bd1e91a3ba93c52e549bfe7949`
and a 6,870,048-byte default SBF with SHA-256
`6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`.
Its worst measured System-create path was `1,207,123 CU`, leaving `192,877
CU`; its selected/coarse soundness values were `101.30230658283051` and
`100.80652861422749` bits. These proof, binary, CU, and theorem numbers do not
transfer to q18 and must be labeled historical whenever retained.

## Reproduction

```bash
NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile23_complete_good_product
```

The executable asserts all ranks, degree bounds and the three frozen
fingerprints before printing the provenance.
