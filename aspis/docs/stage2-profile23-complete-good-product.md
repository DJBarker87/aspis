# Profile 23 complete Good-product provenance

**Status (`2026-07-13`): green, wired into the Profile-23 q3/cap16 first-Good
builder, and used by the closed complete-view computational-hiding theorem in
the declared SHA-256 ROM/EPRO fixed-channel model. Profile 23 is now released
as the default one-transaction production path after all `30/30` release gates
passed. This earlier provenance artifact did not itself change or enable the
production wire.**

The executable joins three independently selected nonzero minors:

1. the 1,404-row D-after-G root-neutral terminal-plus-compressed-sumcheck
   minor;
2. the 12-row terminal Schur complement of the remaining independent G/D raw
   direction; and
3. the 12-row terminal Schur complement of the inactive-balanced H1 padding
   direction.

For each raw certificate, the replay first eliminates all 256 M31 query
coordinates. It then records the stable source ID, terminal pivot row and
nonzero pre-normalization pivot value of every Schur-complement pivot. Source
IDs are `4` tower-coordinate blocks of `1,024` trace rows:

```text
source_id = tower_coordinate * 1024 + trace_row.
```

The frozen certificate is:

| component | rank | fingerprint |
|---|---:|---:|
| root-neutral minor | 1,404 | `0xb7472b1f2b1d03e7` |
| remaining G/D terminal Schur | 12 | `0x0a2dbf8f1a9059c0` |
| H1 inactive-padding terminal Schur | 12 | `0x5c61aee383dff271` |
| bound product provenance | — | `0x1d6697447b7a1448` |

Both raw query ranks are exactly `256`; both terminal Schur ranks are exactly
`12`; and every recorded pivot value is nonzero in M31. The full source,
pivot and value lists are frozen in
`results/stage2/profile23_complete_good_product.json`.

The product fingerprint additionally binds the degree tuple:

```text
q degree                         28,544
root-neutral z degree            41,040
remaining G/D terminal z degree     120
H1 terminal z degree                120
complete z degree                41,280
gamma-coordinate degree          92,436
continuous degree               133,716
```

This closes the executable premise in the q3/cap16 liveness bound. The runtime
gate evaluates all three branches of one retained attempt, selects the least
good selector, retries only an all-bad triple, and feeds an opaque candidate
to the fixed-boundary release controller. Selectors 0, 1 and 2 have each built
and verified as complete proofs.

The complete field-view simulator is exact on every schedule accepted by this
product (`epsilon_aff=0`). With the fixed release channel and EPRO inventory,
complete-view computational hiding is above 100 bits in the declared model;
see `docs/stage2-profile23-computational-hvzk-closure.md` and
`results/stage2/profile23_computational_hvzk_closure.json`. This is neither a
statistical nor standard-model claim. Its `epsilon_side=0` excludes local
filesystem/timing/power/thermal/memory channels and remote-prover traffic; it
is not a physical side-channel bound.

The root-neutral rank certificate was computed on the frozen Profile-22
fixture. Its production transfer is explicit rather than proof-byte equality:
the rank maps depend on the frozen layout and schedule, not the witness; the
release gate matches the Profile-23 layout fingerprint and Good23 definition
fingerprint to live code; and the independent production selector audit is
green on all three branches. Those three links are the basis on which the
fixture certificate is used for the production proof.

The historical unmined diagnostic SBF path is measured at `1,195,306 CU`
read-only and at most `1,207,339 CU` including atomic mutation. Those
measurements did not enable the default production tag and remain useful only
as diagnostic evidence; the subsequent mined production KATs and release
certificate are the enabling evidence.

## Current production release

`results/stage2/profile23_one_transaction_release.json` records
`released=true` with all `30/30` required gates green. The certificate's
one-transaction scope is atomic verification and mutation using a finalized,
pre-uploaded proof account. Production tags 59 and 60 require the all-zero
authority sentinel in bytes `8..40` of the unchanged 40-byte header;
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
`1,207,123 CU` for canonical System-owned account creation. The latter is the
worst measured production path and leaves exactly `192,877 CU` below the
`1,400,000 CU` cap. The release certificate pins the
selected Johnson soundness floor at `101.30230658283051` bits; the
Profile-23-own coarse whole-ledger sensitivity is `100.80652861422749` bits.
The complete-view pairwise-witness computational-hiding floor is
`103.11238518950232` bits in the declared SHA-256 ROM/EPRO
fixed-release-channel model. Its one-sided
real-vs-simulator bound is `104.11238518950232` bits. The hiding claim retains
the model and side-channel limitations stated above; production release does
not turn it into statistical or standard-model HVZK.

## Reproduction

```bash
NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile23_complete_good_product
```

The executable asserts all ranks, degree bounds and the three frozen
fingerprints before printing the provenance.
