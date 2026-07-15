# Compute-unit reconciliation across local, devnet, and mainnet execution

The certified release worst case is `1,340,803` CU
(`max_literal_production_tag65_cu` in
[`profile23_one_transaction_release.json`](../results/stage2/profile23_one_transaction_release.json)).
The finalized mainnet-beta transaction consumed `1,343,749` CU — `2,946` CU
above that certificate value. This note reconciles the two numbers from the
public evidence.

## Measured values

| Execution | Transaction CU | Program CU | Overhead CU | Label |
|---|---:|---:|---:|---|
| Local validator (agave `2.3.0`, feat `3640012085`) | 1,340,803 | — | — | measured, local simulation; maximum over the two certified production marker paths |
| Devnet, 2026-07-14, slot `476282685` | 1,340,749 | 1,340,393 | 356 | measured, on-chain |
| Mainnet-beta, 2026-07-14, slot `432933949` | 1,343,749 | 1,343,393 | 356 | measured, on-chain |

"Program CU" is the `consumed … of 1399700 compute units` figure from the
transaction log; "overhead" is the remainder: two ComputeBudget instructions
at 150 CU each plus a 56-CU charge for the requested 262,144-byte heap frame.
The overhead is identical on both clusters, so the entire devnet-to-mainnet
difference — exactly 3,000 CU — sits inside program execution.

## The difference is deterministic cluster pricing, not variance

Both cluster executions were preceded by a same-cluster preflight simulation,
and in both cases the simulation and the finalized execution consumed the
same CU to the unit
(`final_transaction_simulation_cu` equals
`final_transaction.compute_units_consumed`, and
`final_transaction_submitted_identically_to_simulation` is `true`, in
[`mainnet-execution.raw.public.json`](../release/profile23-q18-g37-mainnet-v1/evidence/mainnet-execution.raw.public.json)
and
[`devnet-finalized.raw.public.json`](../release/profile23-q18-g37-mainnet-v1/evidence/devnet-finalized.raw.public.json)).
The verification instruction was wire-identical across clusters: the same
released proof bytes, the same tag-65 instruction data, the same account
shape, the same two ComputeBudget instructions.

The same program execution is therefore priced 3,000 CU higher by the
mainnet-beta runtime of 2026-07-14 than by the devnet runtime of the same
date. Solana compute-unit pricing changes ship behind feature gates that
activate on devnet before mainnet-beta, so a fixed binary and instruction do
not cost the same on two clusters running different feature schedules.

Attribution, checked against the public record:

- Every feature gate known to the agave `2.3.0` CLI has the same activation
  status on devnet and mainnet-beta (checked 2026-07-15; the newest such gate
  activated on mainnet at slot `384480000`, months before the demonstration).
  The 3,000-CU difference therefore comes from newer gates outside that
  CLI's list.
- The Anza feature-gate tracker's pending-on-mainnet set for mid-July 2026
  contains one entry that changes execution-cost accounting: SIMD-0449
  (direct account pointers in program input), active on devnet since epoch
  1099 and not yet active on mainnet-beta. This note does not establish
  per-gate attribution beyond that observation.
- The 54-CU difference between the local worst case and the devnet execution
  is within the certificate's path spread (the certificate value is the
  maximum over two measured marker paths) and is consistent with CPI
  repricing gates newer than the pinned local validator.

## What the certificate number is

`max_literal_production_tag65_cu` is defined as a local measurement: the
maximum CU over the two certified production marker paths, simulated on the
pinned local validator (`solana-test-validator 2.3.0`, recorded in
[`atomic_state_only_profile23_mutation_production_mined.json`](../results/stage2/atomic_state_only_profile23_mutation_production_mined.json)).
The release gate `production_tag65_under_1_4m_cu` binds that local value
under the 1.4M-CU cap. It is not, and was never evaluated as, an upper bound
on what other cluster runtimes charge for the same execution.

The binding pre-submission control on each cluster is the same-cluster
preflight simulation: the executor simulates the exact transaction on the
target cluster, requires success, and submits the identical wire bytes. The
mainnet preflight returned 1,343,749 CU before submission.

## Headroom and repricing exposure

All values derived from the measured mainnet execution:

| Quantity | Value |
|---|---:|
| Cap | 1,400,000 CU |
| Consumed (mainnet, finalized) | 1,343,749 CU |
| Headroom | 56,251 CU |
| Headroom as a fraction of the cap | 4.02% |
| Tolerated uniform repricing of consumed CU | +4.19% |
| Observed devnet-to-mainnet divergence | +3,000 CU (+0.22%) |

A future runtime repricing that pushed this workload above the cap would be a
liveness failure for these parameters — the preflight simulation fails and no
transaction is submitted — not a soundness failure: compute-unit pricing
cannot make the program accept an invalid proof or commit a partial state
transition. Verification-cost parameters (query count, grinding split) would
have to be re-selected and a new release certified to restore operation under
the cap.

## Reproduce

On-chain values (archival RPC):

```bash
curl -s -X POST https://api.mainnet-beta.solana.com -H 'content-type: application/json' -d '{
  "jsonrpc":"2.0","id":1,"method":"getTransaction",
  "params":["4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo",
  {"encoding":"json","maxSupportedTransactionVersion":0}]}' |
  jq '{cu: .result.meta.computeUnitsConsumed, logs: .result.meta.logMessages}'

curl -s -X POST https://api.devnet.solana.com -H 'content-type: application/json' -d '{
  "jsonrpc":"2.0","id":1,"method":"getTransaction",
  "params":["4HRnTBPqSh9HW4Nw52rJgnd36fzR6CiKgiaL29WkeH4Gk4xLJVhGEt9CAStyUTpuajo9sw4iDLXQHWwFFQALWmto",
  {"encoding":"json","maxSupportedTransactionVersion":0}]}' |
  jq '{cu: .result.meta.computeUnitsConsumed, logs: .result.meta.logMessages}'
```

Pinned evidence and certificate values (offline):

```bash
jq '{final_cu: .final_transaction.compute_units_consumed,
     sim_cu: .final_transaction_simulation_cu,
     identical: .final_transaction_submitted_identically_to_simulation}' \
  release/profile23-q18-g37-mainnet-v1/evidence/mainnet-execution.raw.public.json

jq '{final_cu: .final_transaction.compute_units_consumed,
     sim_cu: .final_transaction_simulation_cu}' \
  release/profile23-q18-g37-mainnet-v1/evidence/devnet-finalized.raw.public.json

jq '{max_literal_production_tag65_cu, exact_headroom_under_1_4m_cu}' \
  results/stage2/profile23_one_transaction_release.json
```

Feature-status comparison (point-in-time; requires the agave CLI):

```bash
solana feature status -u https://api.devnet.solana.com --display-all > /tmp/fd.txt
solana feature status -u https://api.mainnet-beta.solana.com --display-all > /tmp/fm.txt
diff /tmp/fd.txt /tmp/fm.txt
```

Devnet transaction history ages out of default RPC retention; the pinned
evidence files above carry the same numbers permanently.
