# V7 Pool composed one-terminal withdrawal CU diagnostic

## Exact result

One changed local LiteSVM transaction executed the preserved honest 30,192-byte
native Tag-73 proof, returned a canonical single-output 688-byte ASJA only
after acceptance, performed a real legacy SPL Token `TransferChecked` CPI, and
then wrote Pool state, history and the nullifier marker.

- transaction CU: **1,352,116 / 1,400,000**
- raw instrumented headroom: **47,884 CU**
- simulation equals execution: **yes**
- transaction size: **1,038 bytes**
- vault: **1,000,000 -> 975,000**
- destination: **7,000 -> 32,000**
- exact withdrawal amount: **25,000**

This is the requested one-transaction capacity measurement. It remains a
deliberately unsound diagnostic until an honest pair-withdrawal proof exists.

## Reconciliation with the two preceding measurements

| Measurement | CU |
|---|---:|
| composed private transfer | 1,340,241 |
| composed withdrawal | 1,352,116 |
| **exact combined-path withdrawal increment** | **11,875** |
| transport-double private suffix | 81,922 |
| transport-double withdrawal suffix | 93,818 |
| transport-only withdrawal increment | 11,896 |

The combined-path increment is 21 CU smaller than the isolated suffix delta.
Equivalently, the direct-verifier-plus-withdrawal-suffix naive sum is
1,348,555 CU and the measured composition overhead is 3,561 CU. This replaces
the prior arithmetic estimate with a real combined execution.

## Exact phase ledger

| Phase | CU |
|---|---:|
| transaction dispatch before first Pool marker | 2,484 |
| Pool validation, custody planning and verifier planning before CPI | 80,442 |
| CPI entry to verifier entry | 1,910 |
| diagnostic request/proof/native-statement adapter | 22,130 |
| native verifier, wire parse through proof acceptance | 1,234,844 |
| set ASJA return data | 315 |
| CPI unwind to Pool | 2,196 |
| authenticate/apply/custody/write/return Pool suffix | 7,332 |
| final runtime tail | 463 |
| **total** | **1,352,116** |

The complete 59-checkpoint trace is frozen in `evidence.json` and the derived
arithmetic is in `phase-ledger.json`.

## Fifty-thousand-CU headroom gate

The instrumented result is 2,116 CU short of 50,000 headroom. Every recorded
checkpoint executes one `sol_log` and one `sol_log_compute_units` syscall.
Under the exact Agave 4.2.1/LiteSVM cost model used here, both have a 100-CU
base cost; every marker label is shorter than 100 bytes. Thus each checkpoint
costs at least 200 CU before ordinary BPF call overhead.

Removing any 11 diagnostic checkpoints saves at least 2,200 CU and yields at
most 1,349,916 CU, or at least 50,084 CU headroom. The production feature set
removes all 59 checkpoints, giving the conservative source-exact bound:

```
1,352,116 - (59 * 200) <= 1,340,316 CU
1,400,000 - 1,340,316 >= 59,684 CU headroom
```

This is a lower bound on instrumentation savings because it deliberately does
not credit BPF call/branch overhead or any later production simplification.
Pool checkpoints are compiled only by `pair-afterstate-profile`; the verifier
checkpoints exist only in `v7-pool-cu-profile`.

## Mandatory soundness boundary

The preserved proof is a private-transfer proof, not a withdrawal proof. It
does not bind the appended ASJA, withdrawal amount, destination token account,
or pair Pool PDA. The measurement adapter restores the exact legacy native
private-transfer statement—including its fixed recipient commitment—while the
outer Pool instruction independently supplies the withdrawal data. This is
useful only for CU transport/capacity.

Production still requires an honest pair-withdrawal proof whose transcript
authenticates the current relation, afterstate, amount and destination. No
network, deployment or transaction submission occurred.

## Artifacts

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| honest native proof | 30,192 | `656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c` |
| withdrawal-profile Pool SBF | 462,848 | `7bb438c9038e5c5507b590a8ddd4544bbb841806d5d3596e08f0a853eac43b42` |
| diagnostic verifier SBF | 925,944 | `8a15a567dde126f2bbe30d4b6e442f965f7082952195a2e0eeff548d6151ed6c` |

The verifier SBF was built once with `CARGO_BUILD_JOBS=2`; peak RSS was
662,863,872 bytes with zero swaps. The harness transaction was then run once.
Starting revision: `904e4b36f6f488b1e5e72571a393b94e3e5c48d3`.
