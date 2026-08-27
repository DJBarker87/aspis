# Pool V1 one-terminal native Tag-73 baseline (2026-08-27)

## Scope and result

This is the current **30,192-byte native single-leaf Pool relation baseline**.
It is not the final proof-carried staged pair profile and must not be reported
as that profile's expected proof size or CU result.

One top-level Pool private-transfer instruction was executed in LiteSVM with:

- the real native Pool Tag-73 verifier CPI;
- one finalized, verifier-owned proof account containing the honest proof;
- the current Pool/history/nullifier atomic transition path;
- a strict 1,400,000-CU transaction limit.

The exact result is RED. The transaction consumed the full 1,400,000 CU and
failed with `InstructionError(1, ProgramFailedToComplete)`.

The Compute Budget instruction consumed 150 CU, leaving 1,399,850 CU at Pool
entry. The verifier CPI was entered with 814,592 CU remaining. Therefore the
exact Pool prefix before verifier entry cost 585,258 CU. The verifier consumed
all 814,592 available CU and failed before it returned. The Pool append,
nullifier creation, history update and remaining suffix were never reached.

A distinct direct-ASVQ component measurement with the same verifier and proof
also consumed the full 1,400,000 CU and returned
`InstructionError(1, ProgramFailedToComplete)`. Its verifier invocation
consumed all 1,399,850 CU available after the Compute Budget instruction and
returned no data. Simulation and execution metadata were identical. This
establishes the conservative bound that the combined design needs **more than
585,258 additional CU just to finish the verifier**, before any unexecuted Pool
suffix. It is not presented as a summed or exact total-CU estimate. Exact logs
are frozen in `evidence-native-direct-verifier-red.json`.

## Exact artifacts

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| `native-proof.bin` | 30,192 | `656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c` |
| `artifacts/pool/aspis_pool.so` | 415,776 | `c883c62d57d979c0ea3d4159cc591496579c50e6cf42417d84f216b03c19123c` |
| `artifacts/verifier/aspis_verifier.so` | 1,493,504 | `adef3256d220f45a2bd78013d36db078d4aaca56c94f3b6645db09d51ab76bc5` |

The proof has 197 frontier nodes per tree, 16 queries, and checked 35/31/34-bit
work with nonces `629060504`, `329587272`, and `41222128809`.

## Transaction and rollback evidence

The private-transfer transaction had one Compute Budget instruction and one
Pool instruction. The Pool instruction had 432 data bytes and nine account
metas: four writable, one signer. Its serialized size was 907 bytes as a legacy
transaction and 695 bytes as v0 with an address lookup table.

Simulation metadata equaled execution metadata byte-for-byte. Failure rolled
back the Pool account, history page, vault and nullifier marker exactly. The
root sequence remained `1 -> 1`, no nullifier marker existed afterward, and
return data was empty. The complete logs and assertions are frozen in
`evidence-native-combined-red.json`.

## Build and generation provenance

Source revision: `200c2eb974b4a66304aee425c2feb599556fd0ab`, plus only the
task-owned harness in this directory.

The NUC had no active Euler/r41 or other task scope before launch. The honest
proof run used `MemoryHigh=26G`, `MemoryMax=30G`, `MemorySwapMax=0` and
`CARGO_BUILD_JOBS=1`. It completed in 7:07.68 wall time including the clean
focused release build, with 632,328 KiB process peak RSS, 1.6 GiB cgroup peak,
and zero swap.

The current Pool and native-dispatch verifier were built sequentially in one
second NUC cgroup with `MemoryHigh=8G`, `MemoryMax=10G`,
`MemorySwapMax=0`, and `CARGO_BUILD_JOBS=1`. Pool build time was 1:38.35
with 560,332 KiB peak RSS; verifier build time was 17.70 seconds with 401,500
KiB peak RSS. The cgroup peak was 1.0 GiB with zero swap.

No transaction was deployed, signed for a network, or submitted.
