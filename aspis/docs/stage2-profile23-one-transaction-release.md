# Profile 23 one-transaction release gate

Status on 2026-07-13: **released, 30/30 fail-closed gates green.** The frozen
61,599-byte mined proof is consumed only from a sealed proof account, and the
manifest-default production binary is the exact binary exercised by the
production KAT.

Run:

```text
NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-profile23-one-transaction-release
```

The command always writes
`results/stage2/profile23_one_transaction_release.json` after successfully
reading the five source artifacts. It exits nonzero when any release tooth is
false or absent; a stale proof, binary, source hash, mutable proof account, or
missing gate therefore cannot silently retain the released status.

## Exact scope

“One transaction” means one atomic Solana instruction path that:

1. consumes a finalized, pre-uploaded Profile 23 proof account;
2. verifies the complete proof; and
3. commits the nullifier marker and pool-state mutation atomically.

Proof-account creation, proof-account chunk uploads, and append-only tag 62
(`FinalizeProof`) are separate
transactions. Their compute and fees are not included in the tag-60 CU number,
and this release artifact does not describe them as free.

## Source artifacts

The released gate requires:

- `results/stage2/atomic_state_only_profile23_acceptance_production_mined.json`;
- `results/stage2/atomic_state_only_profile23_mutation_production_mined.json`;
- `results/stage2/profile23_d_after_g_soundness_epro.json`;
- `results/stage2/profile23_complete_good_product.json`; and
- `results/stage2/profile23_computational_hvzk_closure.json`.

It additionally hashes and checks `Cargo.toml`, `xtask/Cargo.toml`,
`programs/aspis-verifier/Cargo.toml`, and the literal default binary at
`target/deploy/aspis_verifier.so`. The release command removes that output and
invokes a plain manifest-default `cargo-build-sbf` before reading it; a stale
explicit-alias build cannot satisfy the default-binary tooth.

The output records the relative path, byte length, and raw-file SHA-256 for
every source. Soundness and complete-Good are proof-independent theorem
artifacts. They are bound into the release certificate by those hashes, by the
shared root-minor/product identities, and by checking the HVZK artifact's
layout and Good23 fingerprints against live code.

The concrete production proof is bound independently. Its exact SHA-256 and
byte length must agree across acceptance, mutation, and these required HVZK
fields:

```text
complete_public_view.proof_sha256_production
complete_public_view.proof_bytes_production
```

The old `proof_sha256_unmined_fixture` field is never accepted as a production
identity. The gate also resolves the shared acceptance/mutation `proof_path`
inside the workspace, reads and hashes those actual bytes, and records the
proof itself as a source artifact. Matching metadata for a missing, changed,
or path-escaped proof cannot release.

## Release conjunction

`released` becomes true only when all gates pass in the same evaluation:

- acceptance and mutation both classify the proof as mined and both record a
  real proof override;
- the production-only mined override was exercised;
- every proof account used by production tags 59 and 60 was irreversibly
  sealed by tag 62 before verification;
- production host classification and SBF tag 59 accept that exact proof;
- the isolated no-default host dependencies remain fail-closed, while a
  separately committed unmined proof is rejected by production tags 59 and 60
  with exact transaction rollback and no production PoW bypass;
- exactly the program-owned and canonical-system-owned production tag-60
  marker paths exist;
- both production paths pass acceptance, corruption rollback, state commit,
  nullifier, and duplicate teeth, while the canonical system path passes the
  exactly-one race tooth;
- the production-only binary exposes neither the tag-59 diagnostic selector
  nor tag 61;
- the mined tag-59 acceptance total equals the checked sum of all twelve
  overlap-free ledger buckets, the recorded reconciled total, and its exact
  headroom;
- both diagnostic mutation ledgers equal the checked sum of their eight
  buckets, and each recorded increment is exactly its tag-61 total minus that
  mined acceptance tag-59 total;
- on each production path, literal tag 59 equals the ledger's read-only
  baseline, the signed increment equals `tag60 - tag59`, and literal tag 60
  equals both ledger totals and its exact headroom; the maximum literal
  production total is at most 1,400,000 CU;
- the program manifest's default feature list is exactly
  `profile23-production`, that alias resolves exactly to
  `profile23-mutation-candidate`, and both the workspace and xtask host
  dependencies explicitly set `default-features = false`;
- the production-only KAT was built with exactly the explicit
  `profile23-production` alias, not the lower-level candidate feature or a
  diagnostic feature;
- compile-fail probes reject the production alias combined separately with
  every diagnostic feature and every Profile 20/21/22 candidate feature, plus
  one grouped all-forbidden union;
- the byte length and SHA-256 of the release-command-built plain default
  `target/deploy/aspis_verifier.so` exactly match the production-only SBF
  identity recorded by the mined mutation KAT;
- the proof-independent Johnson soundness artifact is bookable with its
  selected floor at least 100 bits, while its separately reported
  Profile-23-own whole-ledger-times-three/BCS32 coarse sensitivity is also at
  least 100 bits;
- complete-Good, q3, cap16, opaque failure, and fixed-boundary release gates
  are green; and
- complete-view computational hiding is at least 100 bits in its explicitly
  declared SHA-256 programmable-random-oracle/EPRO and fixed public
  Proof-or-Abort channel model, including the mined production repin.

The frozen wire also pins append-only tag 62 (`FinalizeProof`) and tag 63
(`InitializeAtomicPool`), and the production program id is
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`.

The exact release CU is the maximum of the two literal production tag-60
measurements. Headroom is computed as `1,400,000 - max_tag60_cu`; diagnostic
tag-61 measurements are not substituted into that number.

The mined diagnostic acceptance artifact records `1,202,920 CU` for tag 59,
while the final production-mutation run records a same-binary tag-59 baseline
of `1,202,939 CU`. This named 19-CU measurement-context distinction is
retained: acceptance
reconciles its twelve-bucket ledger internally, and each mutation path prices
its tag-60 increment from its own same-binary baseline. No causal explanation
for the 19 CU is assumed, and it is not booked as headroom. The earlier
`1,202,868` versus `1,202,876` comparison (8 CU) is superseded history from a
prior build, not the released measurement.

The 59,679-byte diagnostic fixture and 61,599-byte production proof have
different public query schedules and therefore different minimal-subtree
frontier sizes. The public selector law is witness-independent; schedule-
dependent serialization length is included in the complete-view simulator.

## Frozen release result

The frozen default SBF is 6,870,048 bytes with SHA-256
`6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`.
Same-binary tag 59 is 1,202,939 CU. Production tag 60 is 1,204,792 CU on the
program-owned marker path and 1,207,123 CU on canonical System creation; the
worst path leaves 192,877 CU below 1.4M. The negative release tests still force
unmined and unsealed classifications, so the fail-closed invariant remains
covered after release.
