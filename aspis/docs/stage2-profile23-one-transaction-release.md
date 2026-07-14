# Profile 23 one-transaction release gate

Status on 2026-07-14: **the local q18/cap17 release is green with `35/35`
gates.** The certificate binds the proof-independent Good23, soundness, and
declared-model hiding artifacts to a canonically mined q18 proof, production
host/SBF acceptance and mutation KATs, and a fresh default SBF. The 2026-07-13
q16/cap16 `30/30` certificate is superseded historical evidence, not the
current Profile-23 release.

Run:

```text
NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-profile23-one-transaction-release
```

The command writes
`results/stage2/profile23_one_transaction_release.json` only from the required
source artifacts and exits nonzero when a release tooth is false or absent. A
stale q16 proof, binary, source hash, mutable proof account, or missing q18 gate
therefore cannot silently retain released status. The current JSON records
`released=true`, `status=released_all_required_gates_green`, and no failed
gates. Any retained q16 fields are historical only and must not be read as q18
evidence.

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

The released q18 gate consumes current q18 instances of:

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

The concrete q18 production proof is bound independently. Its exact SHA-256
and byte length agree across acceptance, mutation, and these required HVZK
fields:

```text
complete_public_view.proof_sha256_production
complete_public_view.proof_bytes_production
```

The `proof_sha256_unmined_fixture` field is never accepted as a production
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
- the proof-independent Johnson soundness artifact is bookable only when its
  conservative whole-ledger-times-three/BCS32 release floor is at least 100
  bits;
- complete-Good, q3, cap17, opaque failure, and fixed-boundary release gates
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

## Green local q18 result

The release command reconstructed all theorem ledgers, directly hashed and
verified the mined proof and canonical statement, rebuilt the plain default
SBF, replayed the production KATs, and passed `35/35` gates:

| q18 release item | value |
|---|---:|
| mined proof bytes | 63,487 |
| mined proof SHA-256 | `0e6d33cec0e18842b37b5f3ec1883a6a9f8b52a8be774e10386400508c8708cb` |
| statement SHA-256 | `520a0a86e1d1918a5270622ac27182b1f5b6df2b624d68bbd2a2b6f927eebb14` |
| default SBF bytes | 915,656 |
| default SBF SHA-256 | `da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254` |
| production tag 59 | 1,299,012 CU |
| tag 60, program-owned marker | 1,300,905 CU |
| tag 60, canonical System creation | 1,303,236 CU |
| worst-path headroom below 1.4M | 96,764 CU |
| fixed production release boundary | 480 s |
| measured production wall time | 480.42 s |
| exact post-release host audit | 40.64 s |
| conservative authorizing soundness floor | 100.16144938287455 bits |
| declared-model real-vs-simulator hiding floor | 104.02492234825198 bits |
| declared-model pairwise-witness hiding floor | 103.02492234825198 bits |

The active unmined q18 theorem fixture is 67,327 bytes with SHA-256
`a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238`.
It is not production-mined and cannot satisfy the release proof gate.

This is a local one-transaction release certificate. It is not evidence of a
mainnet deployment or a substitute for an external security audit; those
remain separate blockers. Its scope still excludes proof-account creation,
chunk uploads, and `FinalizeProof`, as stated above.

## Superseded q16 release result (`2026-07-13`)

The q16 mined diagnostic acceptance artifact recorded `1,202,920 CU` for tag
59, while its final production-mutation run recorded a same-binary baseline of
`1,202,939 CU`. The 19-CU difference was retained as a measurement-context
distinction, without assigning a cause or booking it as headroom. The even
earlier `1,202,868` versus `1,202,876` comparison was already superseded.

The q16 59,679-byte diagnostic fixture and 61,599-byte production proof had
different public query schedules and minimal-subtree frontier sizes. That
historical observation remains relevant to the simulator's treatment of
schedule-dependent serialization, but those sizes are not q18 identities.

The q16 frozen default SBF was 6,870,048 bytes with SHA-256
`6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`.
Same-binary tag 59 was 1,202,939 CU. Production tag 60 was 1,204,792 CU on the
program-owned marker path and 1,207,123 CU on canonical System creation; the
worst path left 192,877 CU below 1.4M. The negative release tests forced
unmined and unsealed classifications in that historical artifact. None of its
proof, SBF, CU, or soundness values transfers to q18.
