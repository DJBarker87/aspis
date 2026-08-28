# V7 one-terminal TxV1 devnet preflight

Date: 2026-08-28

Status: simulation plumbing ready; public-devnet execution feature inactive at
the recorded observation. This document authorizes no signing, submission,
deployment, faucet use, or external state mutation.

## Frozen baseline

This branch starts from `06a59a052f446966d4205a79c7d99ff2a097ca2f` and
integrates the existing TxV1 wallet builder from
`3f898921f1bc1a621d18bfbc6415e00f5fe2b280`.

The actual combined runtime harness is
`results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs`.
It executes, in one top-level transaction:

```text
TxV1 -> Pool ASQ8 -> registry/entry checks -> selected Tag-73 verifier CPI
     -> exact 792-byte ASR8 -> lane/history/nullifier/custody settlement
```

The exact packet builders are:

- release-harness builder: `transaction_v1` in the combined harness;
- wallet ASQ8 account builder:
  `build_pair_forest_terminal_instruction_v1_4k_v2`;
- wallet TxV1 compiler: `build_exact_pair_forest_v1_transaction_v2`;
- strict simulation compiler:
  `build_pair_forest_tx_v1_simulation_preflight_v2`.

The wallet's maximum-shape sizing builder explicitly carries priority-fee and
heap fields and therefore reports 844-byte rollover transfer and 1,009-byte
rollover withdrawal packets. The frozen combined harness leaves those optional
fields absent and uses the protocol defaults, producing 832 and 997 bytes.
This preflight intentionally follows the frozen combined representation and
changes only the declared compute limit from 1.4M to the strict 1.3M release
gate. Field values remain the same width, so all four exact sizes remain:

| Operation | History | TxV1 bytes | Headroom to 4,096 | Strict CU limit |
| --- | --- | ---: | ---: | ---: |
| transfer | same page | 799 | 3,297 | 1,300,000 |
| transfer | rollover | 832 | 3,264 | 1,300,000 |
| withdrawal | same page | 964 | 3,132 | 1,300,000 |
| withdrawal | rollover | 997 | 3,099 | 1,300,000 |

The proof remains account-backed and is never placed in the transaction.

## Public-devnet feature observation

Read-only finalized RPC observation on 2026-08-28:

- endpoint: `https://api.devnet.solana.com`;
- genesis: `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`;
- `solana-core`: `4.3.0-beta.2`;
- feature set: `2409014235`;
- finalized probe slot: `489297672`;
- TxV1 feature:
  `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL`;
- finalized feature-account result: `null`.

The RPC accepts a `maxSupportedTransactionVersion: 1` block request, but that
only proves RPC decoding support. It does not activate TxV1 execution. The
public-devnet rail therefore fails closed before simulation today.

Recheck with the signer-free, read-only probe:

```bash
NO_DNA=1 cargo run --quiet \
  --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --features eight-lane-plumbing-v2 \
  --example tx_v1_devnet_probe
```

`executionActivated` must be `true` at finalized commitment before constructing
a live-cluster simulation request.

## Reviewed simulation input

`tx_v1_simulation_request` accepts one JSON manifest with schema
`aspis.v7.txv1-simulation-input.v1`. It contains only public addresses,
account flags, the 320-byte ASQ8 instruction, a finalized blockhash and a
minimum context slot. It accepts no keypair or signature and performs no RPC.

The compiler rejects:

- any non-TxV1 shape;
- a non-ASQ8 or non-320-byte request;
- any instruction signer besides the fee payer encoded by the message;
- the wrong same-page/rollover account count;
- a compute limit other than the fixed 1,300,000;
- any wire at or above 4,096 bytes; and
- any packet whose exact size differs from 799/832/964/997 for its declared
  release case.

It emits the exact placeholder-signature wire, hashes, packet summary, and a
`simulateTransaction` JSON request with:

```text
sigVerify: false
replaceRecentBlockhash: false
commitment: finalized
minContextSlot: <the slot that supplied the blockhash>
```

Example:

```bash
NO_DNA=1 cargo run --quiet \
  --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --features eight-lane-plumbing-v2 \
  --example tx_v1_simulation_request -- \
  reviewed-case.json > preflight.json
```

## Disposable Agave 4.2+ workflow

`scripts/v7_txv1_disposable_agave_simulate.sh` is a zero-signature suite. It
starts a fresh ledger for each case, genesis-loads the two pinned SBFs and all
reviewed account images, verifies TxV1 is active, injects the validator's own
finalized blockhash, compiles the exact packet, and calls only
`simulateTransaction`.

It requires this complete case set:

1. transfer, same-page success;
2. transfer, rollover success;
3. withdrawal, same-page success;
4. withdrawal, rollover success;
5. stale selected-lane rejection;
6. replay/nullifier rejection;
7. wrong checkpoint rejection;
8. wrong registry/release rejection;
9. malformed proof rejection;
10. mutated proof rejection; and
11. failed withdrawal CPI rollback.

For every failed case, the simulation-returned protected accounts must equal
their pre-simulation images byte-for-byte. For every case, a second RPC read
must show the disposable ledger itself is unchanged because no transaction was
submitted. Successful cases must return exactly 792 bytes and consume no more
than 1.3M CU. They must also match the reviewed SHA-256 of the canonical
simulation-returned account array. Every case supplies mandatory log substrings
so a positive case cannot silently skip the selected verifier CPI and a
negative case cannot fail at an unrelated stage.

The bundle format is deliberately separate from production code:

```json
{
  "schema": "aspis.v7.disposable-agave-txv1-bundle.v1",
  "poolProgram": "<pool program id>",
  "verifierProgram": "<verifier program id>",
  "poolSbf": "artifacts/aspis_pool.so",
  "verifierSbf": "artifacts/aspis_verifier.so",
  "cases": [
    {
      "name": "transfer-same-page",
      "input": "cases/transfer-same-page.json",
      "expectedOutcome": "success",
      "expectedSimulationAccountsSha256": "<sha256 of canonical returned accounts>",
      "expectedLogContains": ["Program <verifier id> invoke"],
      "genesisAccounts": [
        { "address": "<account>", "file": "accounts/master.json" }
      ]
    }
  ]
}
```

Run only after a frozen case bundle exists:

```bash
NO_DNA=1 scripts/v7_txv1_disposable_agave_simulate.sh \
  /path/to/agave-4.2/bin \
  /path/to/reviewed-case-bundle \
  results/v7-txv1-disposable-agave-20260828
```

This uses genesis loading rather than deployment transactions. It neither
loads user keys nor signs or submits anything.

## Public-devnet simulation-only workflow

After the feature account has a finalized activation slot and exact programs
and state exist on devnet, the safe order is:

1. read and authenticate genesis, version, feature account and finalized slot;
2. read the complete account snapshot and verify owners, lengths, versions,
   registry/release and selected lane;
3. obtain a finalized blockhash with `minContextSlot` at least the snapshot
   slot;
4. construct the exact zero-signature packet and review its human-readable
   summary;
5. run `simulateTransaction` only;
6. show CU, logs, return data, program/account list, and expected state deltas
   to the user;
7. stop and request separate signing approval;
8. after approval, sign the exact already-simulated message through a wallet
   boundary, verify byte equality, simulate the signed wire with
   `sigVerify: true`, and show that result;
9. stop and request separate submission approval; and
10. submit only that exact signed wire, then reconcile finalized state.

This branch implements the read-only feature probe and the zero-signature
packet/simulation rail used by steps 1, 4 and 5. It deliberately does not yet
implement the production devnet snapshot collector/authenticator required by
steps 2 and 3, and it has no key, signing or submission path. The public script
requires the literal
acknowledgement
`I_ACKNOWLEDGE_TXV1_DEVNET_SIMULATION_IS_RPC_ONLY_AND_WILL_NOT_SUBMIT`, verifies
the feature gate again, and contains no signing or `sendTransaction` code:

```bash
NO_DNA=1 scripts/v7_txv1_public_devnet_simulate.sh \
  preflight.json \
  results/v7-public-devnet-txv1-simulation.json \
  I_ACKNOWLEDGE_TXV1_DEVNET_SIMULATION_IS_RPC_ONLY_AND_WILL_NOT_SUBMIT
```

Do not run it while `executionActivated` is false.

## Remaining gates

- Export the frozen combined harness's exact four positive and seven negative
  account/instruction snapshots into the disposable bundle contract.
- Rebuild the selected Pool and verifier SBFs reproducibly and pin both hashes.
- Run the complete disposable Agave suite and independently inspect its ledgers.
- Finish formal/source composition and the production caller theorem; this
  transport work does not replace those gates.
- Wait for finalized public-devnet TxV1 feature activation.
- Deploy/initialize the exact devnet candidate only under a separate explicit
  authorization.
- Simulate the exact devnet transaction and present its summary before any
  signing request.
- Require separate explicit approvals for signing and for submission.

## Primary sources

- SIMD-0385 transaction v1:
  <https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0385-transaction-v1.md>
- SIMD-0296 larger transactions:
  <https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0296-larger-transactions.md>
- official TxV1 examples and feature id:
  <https://github.com/solana-foundation/transaction-v1-examples>
- Agave feature-gate process:
  <https://github.com/anza-xyz/agave/wiki/Feature-Gate-Setup-Process>
