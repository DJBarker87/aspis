# One-terminal pair Pool phase audit

Date: 2026-08-27

This is a focused CU decomposition of the measurement-only, one-terminal
private-transfer path.  It uses the authenticated selected-verifier transport
double, not the real Tag-73 verifier.  The Pool performs no Poseidon call: the
double returns the exact 688-byte `ASJA` proof-carried afterstate.

## Result

The one permitted changed LiteSVM execution was the same-page transition
100 -> 101.  It consumed **115,695 CU** in an **873-byte transaction**.
Simulation and execution metadata were identical.

The prior clean transport-double baseline was 150,223 CU.  The changed path
parses the collocated historical/live 8,256-byte root page once instead of
twice.  The observed total is 34,528 CU lower even though the new artifact
also meters 19 logging checkpoints.  This is not an exact production saving:
the source optimization and profiling overhead changed together.  It does
give a conservative executable bound for this profiled transport-double path.

The 115,695-CU number is 26,292 CU below the current 141,987-CU verifier
headroom.  It must not be added to, or subtracted from, the frozen verifier
reference as if a real combined transaction had run.  The real verifier has
not yet emitted `ASJA` in the same execution.

## Exact metered phases

Each interval is the difference between adjacent `sol_log_compute_units`
readings.  It therefore includes the checkpoint overhead at its boundary.

| Phase ending at checkpoint | CU |
| --- | ---: |
| transaction dispatch -> `handler_entry` | 1,830 |
| Pool/state and statement validation | 7,754 |
| account layout and uniqueness validation | 10,216 |
| historical/current root-page validation | 38,961 |
| nullifier marker preflight | 6,643 |
| handoff to verifier-plan function | 254 |
| registry, selected-program and sealed-proof framing; statement digest/request | 7,285 |
| verifier instruction/account construction and return-data clear | 594 |
| CPI entry to transport double | 1,781 |
| double proof-account framing | 306 |
| double 688-byte return-data set | 316 |
| CPI unwind, 688-byte fetch/decode, selected-program authentication | 2,194 |
| return authenticated afterstate to Pool handler | 238 |
| check/apply authenticated afterstate | 1,202 |
| construct receipt and next Pool image | 1,015 |
| revalidate and append the root-history page | 34,084 |
| write Pool state | 234 |
| write nullifier marker | 233 |
| set 200-byte receipt return data | 312 |
| last checkpoint -> transaction end | 243 |
| **Total** | **115,695** |

Useful grouped readings are:

- Pool dispatch/state/account/history/nullifier preflight: **65,404 CU**.
- Registry/proof/request planning through the CPI-start marker: **8,133 CU**.
- CPI plus double framing, 688-byte return transport, decode and immediate
  selected-program authentication: **4,835 CU**.
- Authenticated afterstate application, receipt/image creation, history/Pool/
  marker writes and transaction tail: **37,323 CU**.

The 34,084-CU `history_written` bracket is the largest remaining byte-only
hotspot.  The page was already validated before the verifier CPI, and the CPI
does not receive the history account.  A future source change can retain a
private validated-header capability across the CPI and append with the
existing checked header, as the mature transition path already does.  That
change was deliberately not implemented or remeasured here: the task allowed
only one changed measurement.

## What remains versus a directly integrated real verifier

Work that remains semantically necessary:

- decode and bind the Pool statement and immutable membership anchor;
- lock and validate the current live Pool/root-history state for concurrency;
- authenticate the active verifier release under registry policy;
- reject a consumed/nullifier marker before expensive verification;
- verify the transparent proof and construct the typed afterstate;
- check `next_pair_index = current + 1`, the exact next root/frontier and
  zero-bit frontier invariant;
- append the chronological root, write Pool state and create the marker;
- for withdrawal only, validate and execute custody movement atomically.

Work that disappears when proof verification runs directly inside the Pool
handler rather than through a selected-program CPI:

- creation/copy of the 456-byte verifier request instruction;
- CPI entry/exit and the transport double's framing work;
- `set_return_data`/`get_return_data` transport of 688 bytes;
- re-decoding those bytes and checking the immediate return program id.

The ASJA *serialization* can disappear in a direct call, but its typed semantic
checks cannot.  Registry/release authentication also remains unless governance
is intentionally redesigned; that is outside this optimization.

There is no custody CPI in this private-transfer measurement, so its exact
custody cost is **0 CU / not applicable** here.  Withdrawal SPL-token CPI,
balance-delta checks and destination validation remain a separate required
combined measurement and cannot be inferred from this run.

## Evidence and boundaries

- Exact record: `evidence-same-page-profiled.json`
- Profiled Pool SBF: 450,504 bytes,
  SHA-256 `321ea8659b5f004420bf3d13dd1e0a4fc308ccbab7741e1d392f0d328858e056`
- Profiled transport double SBF: 21,664 bytes,
  SHA-256 `dd7703d9d94a66bfbd7bde17591e2f74176e799c230467fc59af3ae8150231b4`
- Toolchain: `cargo-build-sbf` 2.3.0, platform-tools 1.48, SBF Rust 1.84.1,
  LiteSVM 0.16.0.

The measurement feature remains disabled by default.  No real proof was run,
no production entrypoint was enabled, and nothing was deployed or submitted.
