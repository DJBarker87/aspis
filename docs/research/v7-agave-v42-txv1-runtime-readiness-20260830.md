# V7 official Agave v4.2.0 TxV1 runtime readiness

Date: 2026-08-30

Status: **runtime prerequisite green; Aspis lifecycle not run**.

## Outcome

The missing Agave 4.2+ runtime has been closed without building from source.
The exact official stable Linux artifact for Agave v4.2.0 was fetched from the
Anza GitHub release, checked against GitHub's asset digest, tied to the signed
release commit and extracted in a task-owned NUC directory. A disposable
loopback validator then proved that Transaction V1 is active locally.

This phase did not load either Aspis program, deploy anything, construct or
sign a transaction, submit a transaction, or execute any lifecycle case.

## Official provenance

| Fact | Frozen value |
| --- | --- |
| repository | `https://github.com/anza-xyz/agave` |
| release | stable `v4.2.0`, published 2026-08-07 |
| tag commit | `ac82b5d438b0c2303dc7169f52c748977713a111` |
| commit tree | `f73e1b374fb2cc492783f3c154d0820310329377` |
| GitHub verification | `verified=true`, reason `valid` |
| Linux archive | `solana-release-x86_64-unknown-linux-gnu.tar.bz2` |
| archive bytes | 86,392,960 |
| archive SHA-256 | `1f5eb13bcf3694dbd3cf634602aee5edcf8eab519acac75778391c979c3002b0` |
| channel manifest SHA-256 | `76faed5da7a1152d88f37c97c599f2bcccb6912f8596faebd33a5dc70088fc4c` |

The 98-byte channel manifest independently names tag `v4.2.0`, commit
`ac82b5d438b0c2303dc7169f52c748977713a111` and target
`x86_64-unknown-linux-gnu`.

## Materialized binaries

| Binary | Exact version | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `solana` | `solana-cli 4.2.0 (src:ac82b5d4; feat:21b0d33a, client:Agave)` | 32,607,160 | `b6134ccddcb3456e49c0c15bc028c2902184a8fef6f6e6e665d9f8ae5bea8d10` |
| `solana-test-validator` | `solana-test-validator 4.2.0 (src:ac82b5d4; feat:21b0d33a, client:Agave)` | 75,151,616 | `78ee817e9a4fade8a6606ee663060d39728017c79ebac7a7cd35b2a985066f6a` |

The full executable inventory, ELF notes and dynamic dependencies are frozen
under `results/v7-agave-v42-txv1-runtime-readiness-20260830/runtime/evidence/`.

## Disposable runtime result

The validator bound only to `127.0.0.1`, warped to slot 150, and returned:

| Observation | Exact result |
| --- | --- |
| health | `ok` |
| RPC core | `4.2.0` |
| feature set | `565236538` |
| genesis hash | `3TBu9RgYSgZKS5VEHJkWbysNtLunwc9kqvy5nuDEVnh9` |
| finalized slot | 150 |
| TxV1 feature | `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` |
| feature owner | `Feature111111111111111111111111111111111111` |
| feature data | `010000000000000000` |
| CLI status | active since epoch 0, activation slot 0, SIMD-0385 |
| transaction version | 1 |
| serialized ceiling | 4,096 bytes |

This is the exact local capability described by Solana's larger-transaction
upgrade page: Agave/CLI 4.2+ local validators enable Transaction V1, whose
feature raises the serialized transaction ceiling to 4,096 bytes.

## Resource evidence

Both jobs ran under separate user systemd services with
`MemoryHigh=9G`, `MemoryMax=12G`, and `MemorySwapMax=0`.

| Unit | Wall | GNU max RSS | Direct/systemd cgroup peak | Swap peak | Exit |
| --- | ---: | ---: | ---: | ---: | ---: |
| acquisition `r1` | 17.43 s | 18,128 KiB | 376,770,560 B | 0 | 0 |
| readiness `r1` | 1.02 s | 438,756 KiB | 434,610,176 B captured while validator live | 0 | 0 |

The readiness unit's final systemd journal summary reports only the shell after
the background validator had been stopped. The authoritative peak is therefore
the `memory.peak` value captured from the exact service cgroup while the
validator was still alive, corroborated by GNU time's 438,756 KiB maximum RSS.

## What remains

The old eleven-case materialization cannot be executed as release evidence:
its source and Pool SBF binding predates the stack-frame correction. The exact
next input is a regenerated materialized bundle at the centrally consolidated
source containing Pool fix `5f993765647266252989682d077a9415481fcef6`, with
Pool artifact 526,056 bytes / `0bbe441f...956586d` and the selected verifier
artifact 1,812,264 bytes / `c4396030...c5e47`.

After all bundle source/tree, program and case hashes are updated together, run
the existing eleven-case disposable-Agave suite once. That run must still show:

- transfer same-page and rollover success;
- withdrawal same-page and rollover success;
- stale lane, replay/nullifier, wrong checkpoint, wrong release/registry,
  malformed and mutated proof rejection;
- withdrawal CPI failure rollback;
- exact account rollback for every negative case;
- serialized TxV1 bytes below 4,096 and combined CU below the selected ceiling.

No CU or lifecycle result is inferred from this readiness gate.
