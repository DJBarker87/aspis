# One-terminal pair withdrawal suffix audit

Date: 2026-08-27

This focused continuation extends the optimized proof-carried `ASJA` Pool
suffix to a same-page withdrawal. It retains the validated root-page-header
capability across verifier CPI, performs no Pool-side Poseidon computation,
and uses the canonical legacy SPL Token program for a real PDA-authorized
`TransferChecked` CPI.

## Exact result

The one permitted changed LiteSVM withdrawal execution consumed **93,818 CU**
in a **1,038-byte transaction**. The Pool instruction was 432 bytes and used
12 account metas, excluding the payer and compute-budget program. Simulation
and execution consumed exactly the same CU.

The transfer amount was 25,000 base units. The complete terminal transaction
checked these exact custody changes after CPI:

- vault: 1,000,000 -> 975,000;
- destination: 7,000 -> 32,000;
- vault debit = destination credit = statement amount;
- mint, destination, token-program and Pool PDA authority bindings all passed;
- the Pool signed the CPI with the canonical vault-authority PDA.

Only after that exact delta validation did the handler append chronological
root 101, write the complete next Pool image, populate the one-shot nullifier
marker, and return the transition receipt. All Pool-owned mutable borrows are
acquired before the custody CPI, so the post-delta writes are bounded copies
rather than fallible account lookups or borrows.

## Exact metered phases

Each interval is the difference between adjacent
`sol_log_compute_units` readings and includes the checkpoint overhead at its
boundary.

| Phase ending at checkpoint | CU |
| --- | ---: |
| transaction dispatch -> `handler_entry` | 2,484 |
| state and statement validation | 7,698 |
| account layout and uniqueness validation | 11,663 |
| historical/current root-page validation | 38,998 |
| nullifier marker preflight | 6,641 |
| legacy SPL custody planning and binding checks | 5,808 |
| handoff to verifier plan | 255 |
| registry, selected verifier and sealed-proof planning | 7,285 |
| verifier request/CPI preparation | 594 |
| CPI entry to transport double | 1,781 |
| double frame validation | 306 |
| double return-data set | 316 |
| CPI unwind, return decode and selected-program authentication | 2,194 |
| return authenticated afterstate to Pool handler | 238 |
| apply authenticated afterstate | 1,201 |
| construct receipt and complete next-state image | 1,028 |
| acquire all Pool-owned write borrows | 239 |
| handoff to custody CPI | 216 |
| real SPL Token `TransferChecked` CPI | 2,033 |
| exact post-CPI custody delta validation | 1,351 |
| chronological root-history write | 261 |
| complete Pool-state write | 226 |
| nullifier-marker write | 227 |
| transition receipt return | 312 |
| last checkpoint -> transaction end | 463 |
| **Total** | **93,818** |

The immediately preceding optimized private-transfer transport-double path
used 81,922 CU. The 11,896-CU full-path difference is not solely token CPI:
withdrawal also carries five extra account metas and performs custody parsing,
PDA/instruction planning, and exact post-CPI checks. The directly isolated
custody-related intervals are 5,808 CU for planning, 216 CU for the CPI-start
handoff, 2,033 CU for the real token CPI, 1,351 CU for delta validation, and
239 CU for pre-acquiring the Pool-owned write borrows.

## Rollback checks

The focused host test
`pair_withdrawal_verifier_or_custody_failure_preserves_every_byte` covers both
failure sides of the custody boundary:

- verifier failure performs no custody call and preserves Pool, history,
  marker, vault and destination bytes exactly;
- successful verifier authentication followed by a failed signed custody CPI
  preserves those same account images exactly.

The successful LiteSVM transaction separately proves that a real token CPI is
followed by the exact debit/credit check and complete state transition.

## Evidence and strict boundary

- Exact record: `evidence-withdrawal-same-page-profiled.json`
- Pool SBF: 462,848 bytes, SHA-256
  `7bb438c9038e5c5507b590a8ddd4544bbb841806d5d3596e08f0a853eac43b42`
- Selected-verifier transport double: 21,664 bytes, SHA-256
  `dd7703d9d94a66bfbd7bde17591e2f74176e799c230467fc59af3ae8150231b4`
- Toolchain: `solana-cargo-build-sbf 2.3.0`, platform-tools `v1.48`,
  SBF Rust `1.84.1`, LiteSVM `0.16.0`.

This is **transport-double evidence**, not a real-proof combined measurement.
The selected verifier authenticates the request and returns a framed 688-byte
`ASJA` body but performs no cryptographic proof verification. Therefore
93,818 CU is the executable withdrawal Pool prefix/suffix plus transport-double
CPI; it must not be arithmetically added to a frozen verifier measurement and
described as an observed combined transaction.

The `ASJW` route is compiled only under the existing measurement feature. The
default production entrypoint remains unchanged and disabled for this route.
No real proof, network, deploy or transaction submission was used.
