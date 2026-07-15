# Profile 23 one-transaction release gate

Status on 2026-07-14: **the local q18/cap17 release is green with `36/36`
gates.** The certificate binds the proof-independent Good23, soundness, and
declared-model hiding artifacts to a canonically mined q18 proof, production
host/SBF acceptance and mutation KATs, and a fresh default SBF. The 2026-07-13
parameter search and superseded certificates are preserved in the
[`research-archive-2026-07-14`](https://github.com/DJBarker87/aspis/tree/research-archive-2026-07-14)
tag.

Run:

```text
NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-profile23-one-transaction-release
```

The frozen SBF was built with `solana-cargo-build-sbf 2.3.0`, platform-tools
`v1.48`, and its bundled Rust `1.84.1`. The release command deliberately fails
the binary-identity gate when a different build environment emits different
bytes.

The command writes
`results/stage2/profile23_one_transaction_release.json` only from the required
source artifacts and exits nonzero when a release tooth is false or absent. A
stale proof, mismatched binary, source hash, mutable proof account, or missing
gate therefore cannot silently retain released status. The current JSON records
`released=true`, `status=released_all_required_gates_green`, and no failed
gates.

## Exact scope

“One transaction” means one atomic Solana instruction path that:

1. consumes a finalized, pre-uploaded Profile 23 proof account;
2. verifies the complete proof; and
3. commits the nullifier marker and pool-state mutation atomically.

Proof-account creation, proof-account chunk uploads, and append-only tag 62
(`FinalizeProof`) are separate
transactions. Their compute and fees are not included in the tag65 CU number,
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
and byte length must agree across acceptance, mutation, the bytes read from
the shared workspace-relative path, and the reconstructed release instance.
Concrete-proof KAT fields in the proof-independent HVZK artifact are
non-authorizing regression metadata and are not used as the production
identity. The gate resolves the shared acceptance/mutation `proof_path` inside
the workspace, reads and hashes those actual bytes, and records the proof
itself as a source artifact. Matching metadata for a missing, changed, or
path-escaped proof cannot release.

## Release conjunction

`released` becomes true only when all gates pass in the same evaluation:

- acceptance and mutation both classify the proof as mined and both record a
  real proof override;
- the production-only mined override was exercised;
- every proof account used by production tag59 and tag65 was irreversibly
  sealed by tag 62 before verification;
- production host classification and SBF tag 59 accept that exact proof;
- the isolated no-default host dependencies remain fail-closed, while a
  separately committed unmined proof is rejected by production tag59 and tag65
  with exact transaction rollback and no production PoW bypass;
- exactly the program-owned and canonical-system-owned production tag65
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
  baseline, the signed increment equals `tag65 - tag59`, and literal tag65
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

The exact release CU is the maximum of the two literal production tag65
measurements. Headroom is computed as `1,400,000 - max_tag65_cu`; diagnostic
tag-61 measurements are not substituted into that number.

## Green local q18 result

The release command reconstructed all theorem ledgers, directly hashed and
verified the mined proof and canonical statement, rebuilt the plain default
SBF, replayed the production KATs, and passed `36/36` gates:

| q18 release item | value |
|---|---:|
| mined proof bytes | 64,447 |
| mined proof SHA-256 | `d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d` |
| statement SHA-256 | `947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2` |
| canonical public-input digest | `b2d150dfcb6432c1b6f2e3892ee45a9aa5f393809d97c8292fea975b3da35fa3` |
| default SBF bytes | 921,848 |
| default SBF SHA-256 | `97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a` |
| production tag 59 | 1,303,642 CU |
| tag65, program-owned marker | 1,338,471 CU |
| tag65, canonical System creation | 1,340,803 CU |
| worst-path headroom below 1.4M | 59,197 CU |
| production release boundary | caller-selected; 3,600 s default |
| conservative authorizing soundness floor | 100.16144938287455 bits |
| declared-model real-vs-simulator hiding floor | 104.02492234825198 bits |
| declared-model pairwise-witness hiding floor | 103.02492234825198 bits |

For comparison only, the historical 63,487-byte q18/g37 predecessor proof
(SHA-256
`0e6d33cec0e18842b37b5f3ec1883a6a9f8b52a8be774e10386400508c8708cb`)
returned `Proof` at `480.42 s` in a run using the configured 480-second
boundary, and its isolated all-selector host audit took `40.64 s`. Those
figures do not time the current 64,447-byte proof (SHA-256
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`);
no current-proof production-run or isolated-audit wall time is recorded.

The active unmined q18 theorem fixture is 67,327 bytes with SHA-256
`a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238`.
It is not production-mined and cannot satisfy the release proof gate.

This is a local one-transaction release certificate. By itself it is not
evidence of a mainnet deployment or a substitute for an external security
audit. The finalized mainnet execution is recorded separately in
[`profile23-mainnet-demo.md`](profile23-mainnet-demo.md); the implementation
remains externally unaudited. The certificate's scope still excludes
proof-account creation, chunk uploads, and `FinalizeProof`, as stated above.

## Finalized devnet execution (`2026-07-14`)

The exact q18 tag65 transaction finalized on Solana devnet at slot
`476282685` with signature
`4HRnTBPqSh9HW4Nw52rJgnd36fzR6CiKgiaL29WkeH4Gk4xLJVhGEt9CAStyUTpuajo9sw4iDLXQHWwFFQALWmto`
and consumed `1,340,749 CU`. The immutable execution evidence has SHA-256
`e761782d6067a667bd36fff24322d199400382e2b869aa78a54e92b18ce3f440`.
This is devnet-only execution evidence; it is not a mainnet deployment or an
external security audit. Proof-account creation, upload, and finalization
remain outside the one-transaction claim.
