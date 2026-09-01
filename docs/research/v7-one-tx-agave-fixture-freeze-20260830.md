# V7 one-transaction Agave fixture freeze — atomic marker source

Date: 2026-08-30

Status: **offline fixture closure and the provenance-complete dual Linux SBF
replay pass; the Pool checkpoint stack repair and Agave execution remain
open**. No transaction was signed, submitted or deployed.

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
| Linux Pool SBF | 525,888 B, `82606a25f00fd683b06186cdaae519b52c793d9a2f16f9d3f7c40c2b241685c2` |
| Linux verifier SBF | 1,812,264 B, `c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47` |
| historical Darwin verifier | 1,700,384 B, `4ee9b4789533e049e2d9e1f43c84fa97f745a98151f9477ebd828de742b75e5c` |

The checked-in fixture template deliberately retains a null Pool binding and
the historical verifier binding, so it cannot execute by itself. The release
replay materializes a distinct copy with the two Linux identities above and
rewrites the pinned failed-CPI verifier test-double hash before validation.
Atomic marker creation changes Pool runtime bytes, so the earlier `61f80a...`
Pool artifact is neither reused nor represented as current evidence.

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

## Build-host preflight corrections

Two bounded attempts stopped before compilation and are retained as negative
release-harness evidence. `r1` showed that a transient user service does not
inherit the interactive shell's Cargo path. `r2` then showed that the SBF
platform Cargo 1.84 resolves the older `6f17...` registry-cache namespace,
whereas the complete current offline cache is in the host Cargo 1.94
`1949...` namespace. `r3` passed the complete cache and locked-metadata checks,
then established that `cargo-build-sbf` separately invokes the rustup manager;
the deliberately narrow PATH had not yet included it. `r4` then proved the
wrapper uses Cargo's rustup-proxy `+solana` dispatch rather than a direct Cargo
payload. The corrected capture pins both proxy and payload and checks that the
`solana` rustup toolchain resolves to the already-frozen v1.48 platform Rust.
None of these attempts involved memory pressure, a compiler error, or changed
program source, and none was retried unchanged.

The `r5` run was the first attempt to complete all four SBF builds. Each build
exited zero. The two Pool outputs were byte-identical, as were the two verifier
outputs, under a 9 GiB/12 GiB/no-swap cgroup. Peak cgroup memory was
2,257,649,664 bytes and wall time was 7:26.80. The harness then failed closed
because it still compared the Linux verifier against the historical Darwin
artifact. That failure is preserved in
`results/v7-one-tx-linux-sbf-derivation-20260830/r5/`.

ELF inspection makes the platform split explicit: both verifier files have
entry point `0x29118`, and their 28,311-byte `.rodata` sections are
byte-identical with SHA-256 `dabe1a78...`; their `.text` sections differ in
size. The old artifact remains historical CU/runtime evidence. It is not
accepted by the Linux release replay.

The run also exposed the second Cargo namespace used internally by
`cargo +solana`. The corrected replay now authenticates both complete input
sets before and after compilation:

- host Cargo metadata: 428 package/source pairs and 395 index/config entries
  in `1949...`;
- platform Cargo: the complete 186 package/source pairs and 399 index/config
  entries in `6f17...`.

It keeps `--offline --locked` and does not download into or clean the shared
cache.

The corrected `r6` replay then exited zero. It reproduced the Pool and
verifier identities from both independent source copies, authenticated both
Cargo namespaces before and after the build, and materialized the exact
eleven-case bundle. The reproducible-SBF record is SHA-256 `1b66865f...`; the
materialized bundle and its offline audit are `b4ca543d...` and `206e1237...`.
The capped service took 9:49.19, peaked at 2,094,817,280 bytes, and used zero
swap.

The Pool build simultaneously exposed a genuine ecosystem release blocker:
`plan_pair_forest_checkpoint_accounts_v1`, used by the production
permissionless-checkpoint instruction, has SBF stack offset 4,368 bytes—272
bytes over the 4,096-byte limit—with an estimated 4,544-byte frame. The
one-terminal spend function is not the flagged function, but the Pool is not
mainnet-ready until this checkpoint frame is reduced and the Pool SBF/runtime
evidence is refreshed.

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

After the checkpoint source repair, the next release replay must:

1. freeze the new Pool source commit and export it twice into isolated Linux
   source copies;
2. use the frozen v1.48 SBF toolchain under a capped cgroup with no swap;
3. verify both Cargo registry namespaces before and after compilation;
4. require a clean Pool stack report, byte-identical new Pool outputs, and the
   unchanged Linux verifier `c4396030...` from both copies;
5. materialize those exact SBFs and pass the offline validator in
   `--materialized` mode;
6. run the eleven-case suite under Agave 4.2+, reporting actual CU and exact
   success/rollback states.

Agave 4.2+ remains unavailable in the inspected local and dedicated-builder
assets. Consequently no Agave runtime result is claimed here until a prebuilt
Linux Agave 4.2+ binary directory is supplied. LiteSVM and sums of earlier
component measurements are not substituted.
