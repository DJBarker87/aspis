# V7 Registry V2 release/runtime audit plan

Date: 2026-08-31

Status: focused input/provenance and stack checks are executable. The existing
combined LiteSVM measurement is internally consistent and below both release
ceilings. It is still one Linux SBF build, not an independent A/B
reproducibility result, and it is not a devnet receipt.

This work is pinned to evidence commit
`7179f7c550fe0461f4251dea5268af73876da91d`. That commit changes the runtime
harness and freezes evidence; its production `Cargo.lock`, Pool, verifier and
Registry trees are byte-identical to parent
`4722228b991ebb72850b8d79dd54b0fee4899462`.

## What the measured result actually proves

The selected ledgers execute one complete path:

```text
TxV1 -> Pool -> immutable ASR2/ASE2 selection -> production Tag-73 CPI
     -> exact 792-byte ASR8 -> marker creation -> lane/history mutation
     -> optional SPL custody CPI
```

It is a real combined LiteSVM 0.16.0 execution, not a sum of separately
measured components. The proof remains in its verifier-owned account and the
terminal instruction carries the exact 320-byte compact request.

| Shape | Combined CU | TxV1 bytes | CU margin to 1.3M | Byte margin to 4,096 |
|---|---:|---:|---:|---:|
| transfer, same page | 1,161,460 | 845 | 138,540 | 3,251 |
| transfer, rollover | 1,207,174 | 878 | 92,826 | 3,218 |
| withdrawal, same page | 1,153,110 | 1,010 | 146,890 | 3,086 |
| withdrawal, rollover | 1,218,822 | 1,043 | 81,178 | 3,053 |

The seven selected negative paths also bind real combined execution:

| Path | CU | Bytes | Required state result |
|---|---:|---:|---|
| mutated strict proof | 975,390 | 845 | exact rollback |
| wrong release | 36,629 | 845 | exact rollback |
| stale selected lane | 72,167 | 845 | exact rollback |
| replay/nullifier (second execution) | 23,727 | 845 | settled state preserved exactly |
| wrong-length result | 47,114 | 845 | exact rollback |
| result bound to wrong lane | 50,151 | 845 | exact rollback |
| failed withdrawal Token CPI | 1,151,875 | 1,010 | exact rollback |

The one-time real Registry V2 governance instructions measure 106,065 CU / 504
bytes for initialize, 929,136 / 617 for schedule, 12,794 / 373 for activate,
and 4,914 / 340 for freeze.

Run the fail-fast audit from any checkout containing the frozen Git objects:

```bash
release/v7-registry-v2-runtime-audit-v1/verify-inputs.sh \
  > /absolute/new-output/input-audit.json
```

The check verifies all 110 files in the original evidence inventory, the
three SBF identities, all eleven selected ledgers, exact packet/CU values,
Registry V2 governance receipts, code-certificate assertions, success-state
transitions and failure rollback flags. It labels the evidence honestly as
local LiteSVM and one pinned Linux build.

## Focused packet-size source gate

The TxV1 builder source itself fixes the four Registry V2 terminal sizes.
Compile only its exact focused test:

```bash
/usr/bin/time -l cargo test --locked --offline \
  --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --features eight-lane-plumbing-v2 \
  lane_forest_transaction_v1::tests::immutable_registry_v2_terminal_wires_preserve_account_count_and_exact_four_kib_sizes \
  -- --exact --nocapture
```

The expected account/address/packet triples are 11/12/845, 12/13/878,
16/17/1,010 and 17/18/1,043. The test also proves that Registry V2 replaces
the V1 Registry/entry keys one-for-one rather than adding terminal accounts.

## Existing focused stack corroboration

The original Linux build workspace still contained its same-build unstripped
Pool SBF. The exact platform-tools-v1.48 `llvm-objdump` was used to parse every
`r10 - 0xHEX` access by function. The stripped artifact matched the committed
534,608-byte Pool SBF, SHA-256
`0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6`.

The checkpoint planner's largest observed access was 2,912 bytes and the
separate lane decoder's was 3,024 bytes. The global maximum access in the Pool
artifact was exactly 4,096 bytes, and the build log contained no analyzer
overflow diagnostic. The result is frozen in
`results/v7-registry-v2-release-audit-20260831/focused-single-build-stack-audit.json`.

This is useful corroboration, but it is deliberately not called reproducible
build evidence: it uses one original build workspace. The A/B gate below must
derive the same values independently.

## Dual isolated Linux SBF and stack gate

`scripts/v7_registry_v2_dual_sbf_audit.sh` is the release gate. It:

1. verifies the frozen evidence/source manifest;
2. requires exact v1.48 build and disassembly tool bytes;
3. requires Linux x86_64, offline/locked Cargo and a 10-GiB-high,
   12-GiB-max, zero-swap cgroup;
4. exports two isolated copies of the exact source;
5. builds Pool, verifier and Registry serially in separate target directories;
6. rejects any `Stack offset of` / frame-overflow analyzer diagnostic;
7. disassembles each same-build unstripped SBF and bounds every observed
   stack access by 4,096 bytes;
8. requires planner 2,912 and lane decoder 3,024 in both copies;
9. requires A/B byte equality and equality to all three committed artifacts;
10. writes resource records and a machine-readable audit without signing,
    deployment or submission.

Exact invocation shape on the dedicated Linux builder:

```bash
systemd-run --user --wait --collect \
  --unit=aspis-v7-registry-v2-dual-sbf-audit-r1 \
  -p MemoryHigh=10G \
  -p MemoryMax=12G \
  -p MemorySwapMax=0 \
  --setenv=ASPIS_V7_CARGO_BUILD_SBF=/absolute/pinned/cargo-build-sbf \
  --setenv=ASPIS_V7_SBF_SDK=/absolute/pinned/platform-tools-sdk/sbf \
  --setenv=ASPIS_V7_LLVM_OBJDUMP=/absolute/pinned/v1.48/llvm/bin/llvm-objdump \
  --setenv=ASPIS_V7_PLATFORM_RUSTC=/absolute/pinned/v1.48/rust/bin/rustc \
  --setenv=ASPIS_V7_CLANG19=/absolute/pinned/v1.48/llvm/bin/clang-19 \
  --setenv=ASPIS_V7_CARGO_HOME=/absolute/provenance-frozen/offline-cargo-home \
  --setenv=ASPIS_V7_RUSTUP_HOME=/absolute/pinned/rustup-home \
  --setenv=ASPIS_V7_HOST_RUST_BIN=/absolute/pinned/host-rust/bin \
  /absolute/repo/scripts/v7_registry_v2_dual_sbf_audit.sh \
  /absolute/new-output/v7-registry-v2-dual-sbf-r1
```

Do not reuse an output directory and do not relax `--offline --locked`. A
different tool hash, artifact hash, stack offset, swap event or nonzero build
exit fails closed.

## Exact Agave/4-KiB feature gates

The TxV1 feature account is:

```text
txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL
```

The frozen local runtime is official Agave v4.2.0 at commit
`ac82b5d438b0c2303dc7169f52c748977713a111`. Before any lifecycle work, run the
read-only gate against the disposable validator:

```bash
AGAVE_BIN=/absolute/official-agave-v4.2.0/solana-release/bin
LEDGER=/absolute/new-disposable-ledger

"$AGAVE_BIN/solana-test-validator" \
  --reset --quiet \
  --ledger "$LEDGER" \
  --bind-address 127.0.0.1 \
  --rpc-port 18942 \
  --warp-slot 150

scripts/v7_txv1_4k_feature_gate.sh \
  "$AGAVE_BIN/solana" \
  http://127.0.0.1:18942 \
  /absolute/new-output/local-feature-gate
```

The same non-mutating gate for public devnet is:

```bash
scripts/v7_txv1_4k_feature_gate.sh \
  "$AGAVE_BIN/solana" \
  https://api.devnet.solana.com \
  /absolute/new-output/devnet-feature-gate
```

The read-only check was executed on 2026-08-31 at finalized slot 491,127,793.
Devnet reported `solana-core 4.3.0-beta.2`, but the feature account was null
and `solana feature status` reported `inactive`, activation slot `NA`, with
feature activation not allowed at that time. The gate therefore failed closed
before any simulation or submission. The exact status is frozen in
`results/v7-registry-v2-release-audit-20260831/devnet-txv1-feature-gate.json`.
Public-devnet Registry V2 lifecycle execution cannot honestly start until this
same finalized-commitment gate becomes active.

Its underlying direct checks are:

```bash
"$AGAVE_BIN/solana" feature status \
  txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL \
  --url https://api.devnet.solana.com

curl --fail-with-body --silent --show-error \
  -H 'content-type: application/json' \
  --data-binary '{"jsonrpc":"2.0","id":1,"method":"getAccountInfo","params":["txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL",{"encoding":"base64","commitment":"finalized"}]}' \
  https://api.devnet.solana.com
```

The script requires a non-null Feature-program-owned active account at
finalized commitment and records RPC core version, feature set and finalized
slot. It never invokes `sendTransaction`, never reads a keypair and never
deploys a program.

## Remaining release boundary

This milestone does not activate Registry V2. The remaining runtime gates are:

1. execute the prepared dual SBF/stack gate and commit its exact A/B record;
2. materialize an Agave Registry V2 lifecycle bundle from those exact three
   binaries rather than reusing V1 Registry fixtures;
3. run the four success and seven rollback cases on official disposable Agave
   4.2+;
4. after source/formal closure is integrated, execute the same lifecycle on
   finalized feature-enabled devnet and freeze receipts;
5. perform the final deployment-identity and mainnet-readiness audit.

No CU value in this document is represented as Agave/devnet CU until those
runtime executions exist.
