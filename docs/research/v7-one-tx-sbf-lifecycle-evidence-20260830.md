# V7 one-transaction SBF and lifecycle evidence preflight

> **Superseded candidate note (later on 2026-08-30):** Pool source advanced to
> `da77d5f5a22681200cceec8e90fc69ac2cc81ad8` to create the canonical
> nullifier-marker atomically. That security fix changes the terminal account
> layouts and invalidates the `bcd03b12` Pool SBF hash and 997-byte worst-case
> packet quoted below. The deterministic eleven-case fixture successor is
> documented in `v7-one-tx-agave-fixture-freeze-20260830.md`. This file is
> retained as chronology, not as the active release candidate.

> **Toolchain provenance correction (2026-08-30):** the V5 91-file inventory
> cited below is a Darwin arm64 capture and cannot authenticate Linux builder
> bytes. It remains immutable historical evidence. The active `da77d5f5`
> replay uses the separate Linux x86_64 inventory frozen in
> `release/v7-one-tx-candidate-preflight-v1/`.

> **Later Linux derivation:** capped two-copy builds at `da77d5f5` produced
> byte-identical Linux Pool `82606a25...` (525,888 bytes) and verifier
> `c4396030...` (1,812,264 bytes), and the provenance-complete confirmation
> replay passed. It also found the Pool checkpoint planner over the SBF stack
> limit, so the Pool artifact is not mainnet-ready. The active status is in
> `v7-one-tx-agave-fixture-freeze-20260830.md`; the `4ee9...` verifier below is
> preserved only as the historical Darwin/runtime baseline.

Date: 2026-08-30

Status: reproducibility inputs frozen and replay rail implemented; Linux dual
build and eleven-case Agave execution remain unexecuted. This work authorizes
no signing, submission, deployment or public-cluster mutation.

## Outcome

The selected candidate is now bound to one exact source tree, exact feature
aliases, exact SBF toolchain bytes, exact measured artifact hashes and one
fail-closed replay command. The input audit passes. The release evidence is
not yet complete because the NUC was reserved by the Aeneas work, the local
host is Darwin arm64 rather than the required Linux x86_64 builder, no local
Agave 4.2+ validator is installed, and the authoritative TxV1 preflight commit
does not contain the eleven-case account bundle.

The latest executable baseline is the static-inactive-schedule candidate, not
the older four-shape activation sweep:

| Fact | Exact value |
| --- | ---: |
| frozen source | `bcd03b12293f2737dfa1da1436092a0a24a6ae24` |
| source tree | `bbdc231d9ef8e09c23292c5c6f5ba8cefc9f76bb` |
| Pool SBF reference | 524,328 B, `61f80ab33bff36b38716df944d7851a473be0ed065b2d57864082fd966ec8810` |
| verifier SBF reference | 1,700,384 B, `4ee9b4789533e049e2d9e1f43c84fa97f745a98151f9477ebd828de742b75e5c` |
| real combined current-source worst case | withdrawal rollover, 1,198,735 CU |
| exact TxV1 packet | 997 B |
| hard margins | 101,265 CU and 3,099 B |

The current-source measurement is a complete LiteSVM transaction:

```text
TxV1 -> Pool -> authenticated registry/release -> selected Tag-73 verifier
     -> 792-byte ASR8 -> lane/history/nullifier writes -> SPL withdrawal CPI
```

It is not a component sum. Its ledger proves simulation/execution equality,
the selected verifier CPI, exact lane/rollover/nullifier mutation, unchanged
checkpoint/master/proof/registry, and an exact 250-token vault-to-destination
move. It is still local LiteSVM evidence, not Agave or devnet evidence.

The four older transfer/withdrawal shape measurements remain useful
optimization chronology. They do not substitute for replaying all shapes with
the current `4ee9...` verifier binary.

## Frozen build inputs

`release/v7-one-tx-candidate-preflight-v1/manifest.json` binds:

- the exact commit, whole source tree, Pool/verifier subtrees and `Cargo.lock`;
- the default-off `v7-pair-forest-one-tx-candidate` feature on both programs;
- Pool/verifier output length and SHA-256;
- all five strict proof fixtures and the current-source worst-case ledger;
- the authoritative simulation preflight commit
  `c403c2f95734b271c3f5e0cae50d2a770640941a`;
- all eleven mandatory TxV1 lifecycle cases;
- `solana-cargo-build-sbf 2.3.0`, platform-tools v1.48 and SBF Rust 1.84.1;
- the existing 91-file platform-tools/SBF-SDK checksum inventory, whose own
  SHA-256 is
  `70f037278f587754d5ef9713644e6ae7b6d7788d9f6c01153ac5da89939e9609`;
- Linux x86_64 plus cgroup limits of MemoryHigh <= 4 GiB, MemoryMax <= 6 GiB
  and MemorySwapMax = 0.

No OCI image is asserted. The replay instead checks every byte of the pinned
compiler, platform-tools and SBF SDK before building, and records the Linux
kernel and `/etc/os-release` identity. This avoids describing an unpinned
container tag as reproducibility evidence.

## Replay implementation

`scripts/v7_one_tx_release_replay.sh` has three modes:

1. `check` performs the source/toolchain/fixture/evidence audit without a
   build;
2. `build` exports the frozen commit twice, uses separate source/output/target
   directories, builds Pool and verifier in each copy, and requires A/B byte
   equality plus equality to the measured reference hashes;
3. `build-and-simulate` additionally requires the bundle's Pool/verifier
   bytes to equal those reproducible outputs and invokes the authoritative
   eleven-case disposable-Agave runner.

The build path is offline, locked, single-job and deterministic-environment
scoped. It records four build logs, four GNU-time ledgers, maximum RSS, exact
toolchain identities, the cgroup controls, artifact hashes and a complete
`SHA256SUMS`. It refuses Darwin, uncapped cgroups, swap, different toolchain
bytes, source drift, A/B drift, measured-candidate drift, an incomplete case
bundle or Agave below 4.2.

The exact future Linux invocation is:

```sh
systemd-run --user --scope \
  --unit=aspis-v7-one-tx-release-replay \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=0 \
  env ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT=<frozen-toolchain-capture-root> \
  scripts/v7_one_tx_release_replay.sh build-and-simulate \
  <new-output-directory> <agave-4.2+-bin-directory> \
  <eleven-case-bundle-directory>
```

This command should run once after the NUC reservation and complete bundle are
available. An unchanged failed run must not be retried with a larger memory
cap.

## Actually executed checks

The static audit passed:

```sh
release/v7-one-tx-candidate-preflight-v1/verify-inputs.sh
scripts/v7_one_tx_release_replay.sh check
bash -n release/v7-one-tx-candidate-preflight-v1/verify-inputs.sh
bash -n scripts/v7_one_tx_release_replay.sh
```

The Darwin build guard was exercised and exited 1 before creating an output
directory:

```text
FAIL: release SBF reproduction requires Linux x86_64; this host is Darwin arm64
```

The signer-free public-devnet probe also passed as a read-only observation:

| Field | Observation |
| --- | --- |
| finalized slot | 490,505,494 |
| `solana-core` | `4.3.0-beta.2` |
| feature set | 2,409,014,235 |
| TxV1 RPC decoding | supported |
| TxV1 feature account | absent |
| activation slot | absent |
| execution activated | **false** |

The probe exited 0 in 28.95 seconds with 14,991,360 bytes reported maximum
RSS and zero swaps. Since execution activation was false, no simulation RPC
was sent. No transaction was built with a signer, signed, submitted or
deployed.

## Evidence classification

| Gate | State | Honest classification |
| --- | --- | --- |
| Frozen source/features/fixtures | PASS | static cryptographic input audit |
| Current-source worst-case transaction | PASS | real combined LiteSVM, 1,198,735 CU / 997 B |
| Two clean Linux SBF builds | NOT RUN | NUC unavailable to this task; Darwin build forbidden |
| Byte equality to measured binaries | NOT RUN | enforced by replay, no result yet |
| Eleven-case Agave 4.2+ suite | NOT RUN | runner exists; complete case bundle and Agave 4.2+ absent |
| Public-devnet TxV1 capability | FAIL CLOSED | read-only finalized probe; feature inactive |
| Public-devnet lifecycle | NOT RUN | no signing/submission authorized; feature gate inactive |

## Remaining release-evidence work

1. Produce the complete eleven-case bundle from the exact current-source
   programs and authenticated account fixtures. Do not weaken the runner's
   exact expected-log, post-state hash or rollback checks.
2. Run one capped Linux `build-and-simulate` replay and freeze its generated
   binaries, four resource ledgers and suite hash.
3. Repeat the four success shapes and all seven rejection/rollback cases under
   the reproducible hashes; never infer the result from the older four-shape
   LiteSVM ledgers.
4. Recheck public devnet. Only when the finalized feature account has an
   activation slot may the existing simulation-only rail send a simulation
   RPC. A later finalized lifecycle remains a separate explicitly authorized
   phase.
5. Compose these runtime artifacts with the still-active formal/source gates;
   local evidence alone does not make the candidate mainnet-ready.

The selected configuration remains **not mainnet-ready** at this preflight.
