# V7 official Agave v4.2.0 TxV1 runtime readiness

This directory freezes the signer-free runtime prerequisite for the V7
one-transaction lifecycle. It proves that an official, provenance-checked
Agave v4.2.0 Linux release starts a disposable loopback validator with the
Transaction V1 feature active. It does **not** claim that the eleven Aspis
lifecycle cases ran.

## Result

| Gate | Result |
| --- | --- |
| GitHub stable release | `v4.2.0`, signed/verified commit `ac82b5d4...` |
| Linux archive | 86,392,960 B, SHA-256 `1f5eb13b...` |
| `solana` | 32,607,160 B, SHA-256 `b6134ccd...` |
| `solana-test-validator` | 75,151,616 B, SHA-256 `78ee817e...` |
| RPC | healthy, `solana-core` 4.2.0, loopback only |
| TxV1 feature | active since epoch 0, activation slot 0 |
| TxV1 ceiling | 4,096 serialized bytes |
| readiness GNU-time peak RSS | 438,756 KiB |
| direct cgroup peak while validator was alive | 434,610,176 B |
| swap | 0 B current and peak |
| deployments / signed tx / submitted tx | 0 / 0 / 0 |

The four initial `curl` connection failures in `systemd/readiness-r1.log` are
the bounded health poll before the RPC socket opened. The same run subsequently
passed `getHealth`, `getVersion`, feature-account ownership/data and CLI feature
status checks and exited zero.

## Evidence map

- `run.json` is the compact run ledger.
- `runtime/provenance/` contains the official GitHub release, tag and signed
  commit API responses.
- `runtime/evidence/` records versions, ELF identities, dependencies, complete
  executable inventory and the extracted runtime materialization.
- `readiness/` contains the exact RPC responses, feature account/status and
  direct cgroup capture.
- `systemd/` contains both unit journals, stdout/stderr and GNU-time ledgers.

The 86 MB official archive and 250 MB extracted runtime are deliberately not
checked into Git. They remain in the task-owned NUC directory identified by
`runtime/evidence/bin-dir.txt` and can be recreated byte-for-byte with
`scripts/v7_agave_v42_runtime_prepare.sh`.

## Exact replay

On Linux x86_64, first materialize into a new task-owned path:

```sh
systemd-run --user --collect \
  --unit=aspis-v7-agave-v420-acquire-r1.service \
  -p MemoryHigh=9G -p MemoryMax=12G -p MemorySwapMax=0 \
  /bin/bash -lc \
  'scripts/v7_agave_v42_runtime_prepare.sh <new-runtime-root>'
```

Then run the validator-only gate, again into a new evidence path:

```sh
systemd-run --user --collect \
  --unit=aspis-v7-agave-v420-readiness-r1.service \
  -p MemoryHigh=9G -p MemoryMax=12G -p MemorySwapMax=0 \
  /bin/bash -lc \
  'scripts/v7_agave_txv1_runtime_readiness.sh \
    <runtime-root>/extracted/solana-release/bin <new-evidence-dir>'
```

## Exact remaining lifecycle input

The runtime is ready, but the current materialized eleven-case bundle is bound
to the superseded Pool artifact at `da77d5f5...`. The next lifecycle run must
receive a newly materialized bundle from the centrally consolidated source,
including the stack-safe Pool work from:

- Pool fix commit: `5f993765647266252989682d077a9415481fcef6`
- Pool SBF: 526,056 B
- Pool SBF SHA-256:
  `0bbe441f0e13c2f61e2369674628b06c9d538192514b4e9a92d229479956586d`
- verifier SBF: 1,812,264 B
- verifier SBF SHA-256:
  `c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47`

The bundle manifest, source/tree/subtree bindings, program-byte hashes and all
case/inventory hashes must be regenerated together. Only then should the
existing eleven-case Agave runner load the two programs at genesis and execute
the four successes plus seven fail-closed rollback cases.
