# V7 one-transaction Agave fixture freeze — atomic marker source

Date: 2026-08-30

Status: **offline fixture closure passes; fresh Pool SBF and Agave execution
remain open**. No transaction was signed, submitted or deployed.

## Outcome

The complete deterministic eleven-case fixture set now exists for the
one-terminal eight-lane Pool after atomic nullifier-marker creation. It is
bound to these exact production source objects:

| Object | Exact identity |
|---|---|
| commit | `da77d5f5a22681200cceec8e90fc69ac2cc81ad8` |
| whole tree | `aee02a157b9866a4eaada912fe7ca8976ae51fce` |
| Pool tree | `872814145eb07077fae2f15cf507643d28f3fa4b` |
| verifier tree | `e7370c020cac1e51ca9e41092dcf6ecbf095bd99` |
| verifier SBF | 1,700,384 B, `4ee9b4789533e049e2d9e1f43c84fa97f745a98151f9477ebd828de742b75e5c` |

The Pool SBF field is deliberately null. Atomic marker creation changes Pool
runtime bytes, so the earlier `61f80a...` Pool artifact is not reused or
misrepresented as current evidence. The executable runner requires a non-null
fresh binding and therefore fails closed on the checked-in template.

The build preflight now pins the dedicated builder's exact Linux x86_64
platform-tools v1.48 bytes in
`release/v7-one-tx-candidate-preflight-v1/linux-x86_64-sbf-toolchain-v1.48.json`
(SHA-256 `2bcdd08e9c26f5cd1743a07cfb8aae341dc278e9d4e33eed512b746bc365d61c`).
An earlier preflight revision incorrectly reused the platform-specific Darwin
arm64 V5 inventory while labelling the required host Linux; the byte gate
caught that mismatch before any release build. The historical V5 inventory is
unchanged and is no longer selected by this replay.

## Exact fixture coverage

The generated bundle contains exactly:

1. transfer, same page;
2. transfer, rollover;
3. withdrawal, same page;
4. withdrawal, rollover;
5. stale selected lane;
6. replay/already-consumed nullifier;
7. wrong retained checkpoint;
8. wrong registry release;
9. malformed proof-account header;
10. mutated proof body;
11. withdrawal CPI failure after verifier success.

All seven negative cases set `rollbackRequired: true`. The runner compares
every requested simulated post-account to its exact prestate and then proves
the disposable validator ledger remains unchanged after simulation.

The marker starts in three exact forms:

| Form | Cases | Purpose |
|---|---:|---|
| absent/zero-lamport System account | 7 | real CreateAccount path and rollback |
| one-lamport dusted System account | 3 | top-up + Allocate + Assign and rollback |
| consumed Pool account | 1 | replay rejection before another reservation |

The failed-withdrawal-CPI case uses an explicitly scoped disposable test
double: the exact verifier SBF is also loaded at the legacy Token program
address for that validator instance only. The first verifier CPI accepts; the
10-byte Token instruction then fails in the test double. This is a runtime
atomic-rollback probe, not a replacement for production SPL Token and not a
claim about production Token behavior.

The runner warps every new ledger to slot 150. This is required because the
frozen registry entry activates at slot 90; without the warp, a correct proof
would be rejected for an unrelated inactive-release reason.

## TxV1 preflight result

The real wallet preflight accepted all eleven generated inputs:

| Operation | History | Accounts | TxV1 bytes | Headroom to 4,096 |
|---|---|---:|---:|---:|
| transfer | same page | 11 | 833 | 3,263 |
| transfer | rollover | 12 | 866 | 3,230 |
| withdrawal | same page | 16 | 998 | 3,098 |
| withdrawal | rollover | 17 | 1,031 | 3,065 |

Every request has one required signature, a canonical 320-byte ASQ8 payload,
a 1.3M compute limit and no signing/submission code path.

## Determinism and offline verification

Two independent optimized runs produced byte-identical outputs:

| Artifact | SHA-256 |
|---|---|
| `bundle.json` | `5768416d9f720a93749408763ab72131cba7cf52ae77d1b739d1f2cfb68f289d` |
| `TEMPLATE-SHA256SUMS` | `5086e0c3da9e4eda6c6111ee8a2a0ee25a745c66f8d011d21ef1fe1df1621341` |

The template contains 44 files and 647,048 bytes. The offline verifier checks
the exact file inventory; all hashes and account-data lengths; unique case,
genesis and post-state account sets; canonical ASQ8 encoding; payer/System
metas; exact 11/12/16/17 account shapes; marker start forms; all failure
rollback flags; expected success poststates; and the pinned failed-CPI test
double.

Focused commands executed:

```sh
NO_DNA=1 cargo check \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml \
  --bin generate_txv1_agave_bundle

NO_DNA=1 cargo run --release --quiet \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml \
  --bin generate_txv1_agave_bundle -- \
  results/v7-one-tx-agave-bundle-template-20260830

scripts/v7_txv1_bundle_verify.sh \
  results/v7-one-tx-agave-bundle-template-20260830

# Repeated into a distinct /tmp output, then:
cmp <first>/bundle.json <second>/bundle.json
cmp <first>/TEMPLATE-SHA256SUMS <second>/TEMPLATE-SHA256SUMS

# Each of the eleven input.json files:
NO_DNA=1 cargo run --release --quiet \
  --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --features eight-lane-plumbing-v2 \
  --example tx_v1_simulation_request -- <input.json>
```

## Exact remaining runtime prerequisite

The next permitted build-host run must:

1. export `da77d5f5` twice into isolated Linux source copies;
2. use the frozen v1.48 SBF toolchain under a capped cgroup with no swap;
3. require byte-identical Pool and verifier artifacts across both builds;
4. require the verifier to retain its frozen `4ee9...` identity;
5. materialize the byte-identical fixture template with the fresh Pool length
   and hash derived from actual bytes (an independent regeneration with
   `--pool-sbf <fresh-pool.so>` is equivalent and remains available);
6. materialize those exact SBFs and pass the offline validator in
   `--materialized` mode;
7. run the eleven-case suite under Agave 4.2+, reporting actual CU and exact
   success/rollback states.

Agave 4.2+ remains unavailable in the inspected local and dedicated-builder
assets. Consequently no Agave runtime result is claimed here until a prebuilt
Linux Agave 4.2+ binary directory is supplied. LiteSVM and sums of earlier
component measurements are not substituted.
