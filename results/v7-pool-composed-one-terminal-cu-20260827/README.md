# V7 Pool composed one-terminal CU diagnostic

## Result

A single local LiteSVM transaction executed the preserved honest 30,192-byte
native Tag-73 proof, returned a canonical 688-byte ASJA only after verifier
acceptance, and applied the same-page Pool/history/nullifier byte-write path.

- transaction CU: **1,340,241 / 1,400,000**
- remaining headroom: **59,759 CU**
- simulation equals execution: **yes**
- transaction size: **873 bytes**
- direct-verifier baseline: **1,254,737 CU**
- incremental composition cost over that baseline: **85,504 CU**
- frozen transport-only baseline: **81,922 CU**
- delta from the naive baseline sum: **+3,582 CU**

The measurement therefore establishes that the verifier and Pool byte writes
can physically fit in one transaction. It does **not** establish a sound Pool
protocol.

## Mandatory soundness boundary

The honest proof predates the pair-afterstate interface and does not bind the
appended ASJA bytes. In addition, it binds the legacy single-leaf Pool PDA, so
the diagnostic adapter substitutes that one public field while the outer Pool
instruction uses the distinct pair-tree PDA. The ASJA is checked for canonical
encoding and is returned only after the real proof accepts, but it is not
authenticated by that proof.

This code is available only through the existing mutually exclusive
`v7-pool-cu-profile` verifier entrypoint and the Pool's measurement-only
`pair-afterstate-evidence` entrypoint. No production dispatch was enabled, no
network was used, and nothing was deployed or submitted.

## Exact phase ledger

| Phase | CU |
|---|---:|
| transaction dispatch before first Pool marker | 1,830 |
| Pool validation/planning before verifier CPI | 73,242 |
| CPI entry to verifier entry | 1,910 |
| diagnostic request/proof/statement adapter | 22,152 |
| native verifier, wire parse through proof acceptance | 1,234,844 |
| set ASJA return data | 315 |
| CPI unwind to Pool | 2,195 |
| authenticate/apply/write/return Pool suffix | 3,510 |
| final runtime tail | 243 |
| **total** | **1,340,241** |

The complete 51-checkpoint trace is frozen in `evidence.json`; derived phase
arithmetic is in `phase-ledger.json`. Checkpoint syscalls are metered and are
therefore included in the total.

## Acceptance ordering and rollback

The adapter calls the unchanged native verification body with `?`, emits
`proof-accepted`, and only then calls `set_return_data`. The Pool authenticates
the immediate CPI return before any Pool/history/marker write. A verifier error
therefore reaches no write in this path, and transaction atomicity supplies the
second rollback barrier.

The already-frozen real-verifier red gate independently exercised failure at
the CU boundary and records byte-exact Pool/history/marker/vault rollback,
unchanged sequence `1 -> 1`, no marker, and empty return data in
`../pool-v1-one-terminal-runtime-20260827/evidence-native-combined-red.json`.
The composed diagnostic was deliberately limited to one changed transaction,
so that negative transaction was not redundantly rerun.

## Frozen inputs and artifacts

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| honest native proof | 30,192 | `656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c` |
| optimized Pool SBF | 451,264 | `e022074c5e8e13f3285419511e1793c8b26f3634b48c524fd9d13f0b4229ce4e` |
| diagnostic verifier SBF | 925,208 | `04a6b3b4263bf83a68bf8b37437286709772e0ca892947138578a4194953e379` |

The diagnostic verifier was built once with `CARGO_BUILD_JOBS=2`; peak RSS was
658,554,880 bytes and swap count was zero. The harness was then executed once.
The starting revision was
`155b92ce45232cbff0c80e91727929da6f8d0b40`.

