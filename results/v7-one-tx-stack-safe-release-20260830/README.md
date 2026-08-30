# V7 one-transaction stack-safe local release evidence

This directory freezes the successful current-source release gate for production
source commit `6bc7d3caf181be23a8a6ac7769497c965cd7273d`.

The local gate is green. Two isolated Linux source copies produced byte-identical
Pool and verifier SBF programs, and the exact materialized programs then passed
all eleven signed, identically simulated/submitted, finalized TxV1 cases on a
disposable official Agave v4.2.0 validator. No public cluster was used and no
program was deployed.

This is release evidence for the Rust/SBF/local-runtime layer. It does not by
itself claim that the separate end-to-end Lean/Aeneas/cryptographic closure or a
public-devnet/mainnet deployment gate is complete.

## Frozen program identities

| Program | Bytes | SHA-256 | A/B result |
|---|---:|---|---|
| Pool | 526,056 | `0bbe441f0e13c2f61e2369674628b06c9d538192514b4e9a92d229479956586d` | byte-identical |
| Verifier | 1,812,264 | `c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47` | byte-identical |

The Pool analyzer emitted no overflow diagnostic. The maximum observed stack
offsets are 2,912 bytes for the checkpoint planner and 3,024 bytes for the lane
decoder helper, both below the 4,096-byte SBF limit.

The authoritative reproducible-build record is
`dual-sbf-r2/reproducible-sbf.json`, SHA-256
`3411d0b9de283fa3015a0e357d888c5b9d4f7d1256d101991876785edf0378e5`.
All four focused builds exited zero, used 566,076–570,100 KiB peak RSS, and used
zero swap. The enclosing r2 unit later failed before its first transaction
because the initial runner supplied RPC-shaped account JSON directly to the
Agave genesis loader; this does not invalidate the already completed A/B build
record. The corrected loader adapter is part of the committed runner.

## Finalized one-transaction measurements

Simulation and landed execution consumed exactly the same CU in every case.

| Case | Outcome | Tx bytes | Landed CU | State result |
|---|---|---:|---:|---|
| Transfer, same page | success | 833 | 1,157,102 | expected transition |
| Transfer, rollover | success | 866 | 1,206,015 | expected transition |
| Withdrawal, same page | success | 998 | 1,148,696 | expected transition |
| Withdrawal, rollover | success | 1,031 | 1,217,607 | expected transition |
| Stale selected lane | failure | 833 | 67,809 | exact rollback |
| Replay/nullifier | failure | 833 | 23,666 | exact rollback |
| Wrong checkpoint | failure | 833 | 15,587 | exact rollback |
| Wrong registry/release | failure | 833 | 39,727 | exact rollback |
| Malformed proof | failure | 833 | 30,837 | exact rollback |
| Mutated proof | failure | 833 | 974,231 | exact rollback |
| Failed withdrawal CPI | failure | 998 | 1,147,481 | exact rollback |

The worst honest case leaves 82,393 CU below 1.3M and 3,065 bytes below the
4,096-byte TxV1 ceiling. Each successful transaction returned the exact 792-byte
ASR8 result. Every negative transaction finalized with an error and left every
protected RPC account value unchanged.

The authoritative suite is `agave-r5/suite.json`, SHA-256
`5a3502e74c259071d49bbefdb3ead8853d139259912f131282551250d82ce8db`.
The lifecycle ran in 2:44.38 wall time. The systemd cgroup reported 822.5 MiB
peak memory and zero swap under `MemoryHigh=9G`, `MemoryMax=12G`, and
`MemorySwapMax=0`.

## Runtime metadata boundary

Agave records `rentEpoch = u64::MAX` on touched rent-exempt accounts, whereas
the pre-existing LiteSVM expected-state fixtures record zero. The release gate
therefore compares all program-controlled account state exactly—data, owner,
lamports, executable flag, and space—while separately requiring `rentEpoch` to
be either zero or `u64::MAX`. The four honest state-comparison files preserve
both exact views. Negative rollback comparisons do not normalize anything.

## Runtime provenance

The suite used official Agave `v4.2.0`, tag commit
`ac82b5d438b0c2303dc7169f52c748977713a111`:

- release asset SHA-256: `1f5eb13bcf3694dbd3cf634602aee5edcf8eab519acac75778391c979c3002b0`;
- `solana` SHA-256: `b6134ccddcb3456e49c0c15bc028c2902184a8fef6f6e6e665d9f8ae5bea8d10`;
- `solana-test-validator` SHA-256: `78ee817e9a4fade8a6606ee663060d39728017c79ebac7a7cd35b2a985066f6a`;
- TxV1 feature: `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL`.

## Replay

First validate every checked-in input and evidence binding:

```bash
release/v7-one-tx-candidate-preflight-v1/verify-inputs.sh
```

For a fresh dual build plus local lifecycle, use an absolute, previously absent
output directory and the frozen official Agave binary directory:

```bash
scripts/v7_one_tx_release_replay.sh \
  build-and-lifecycle \
  /absolute/task-owned/replay-output \
  /absolute/official-agave-v4.2.0/solana-release/bin
```

Run the command in a dedicated zero-swap cgroup no larger than the limits in
the release manifest. Do not reuse the local disposable-signing authorization
for a public cluster.

`release-evidence.json` is the compact machine-readable summary. The `dual-sbf-r2`
and `agave-r5` subdirectories retain the detailed logs, timings, individual case
records, state comparisons, signatures, transaction responses, and systemd
accounting used to derive it.
