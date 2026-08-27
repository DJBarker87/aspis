# V7 Pool wallet: Solana TxV1 4 KiB transport gate

Status: default-off wallet/runtime plumbing. No transaction was signed,
simulated, submitted, deployed, or enabled in production.

## Exact format decision

Solana's 4,096-byte transaction envelope is transaction version 1 (TxV1,
SIMD-0385), whose wire starts with `0x81`. Legacy transactions and transaction
version 0 remain capped at 1,232 bytes; v0 is not a 4 KiB fallback. TxV1 has:

- at most 12 signatures;
- at most 64 inline addresses;
- at most 64 instructions;
- no address lookup tables;
- resource requests in the message's `TransactionConfig`, not ComputeBudget
  instructions; and
- a total priority fee in lamports, not the v0 micro-lamports-per-CU unit.

The wallet builder therefore rejects every ALT and every ComputeBudget-program
instruction. It explicitly supplies nonzero compute-unit, loaded-account-data,
and heap limits. The full approximately 30 KiB proof remains in its proof
account. The compact ASQ8 request is exactly 320 bytes and contains only public
input/bindings.

## Frozen maximum wallet shapes

All byte counts include the TxV1 message, native `TransactionConfig`, and the
full placeholder signature array. They use distinct fee payer, page payer, and
source authority where the instruction permits them.

| Path | Instruction accounts | Signatures | Inline addresses | TxV1 bytes | Headroom to 4096 |
|---|---:|---:|---:|---:|---:|
| AS8I initialize | 14 | 2 | 16 | 904 | 3,192 |
| AS8C checkpoint | 12 | 2 | 14 | 662 | 3,434 |
| AS8D rollover deposit, 512-byte encrypted note | 11 | 3 | 13 | 1,277 | 2,819 |
| ASQ8 rollover private transfer | 10 | 1 | 12 | 844 | 3,252 |
| ASQ8 rollover withdrawal | 15 | 1 | 17 | 1,009 | 3,087 |

The same ASQ8 instructions serialize to 822 and 987 bytes under v0, but those
measurements are comparison-only and never authorize v0 as a 4 KiB format. The
maximum encrypted-note rollover deposit is 1,277 bytes and therefore proves
why silently reverting to the legacy 1,232-byte rule is incorrect.

## Public devnet activation probe

The exact TxV1 feature account is:

`txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL`

The probe is hard-coded to `https://api.devnet.solana.com`, authenticates the
devnet genesis hash
`EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`, checks the feature account at
finalized commitment, and asks `getBlock` to parse
`maxSupportedTransactionVersion: 1`. It has no signer and only calls
`getGenesisHash`, `getVersion`, `getSlot`, `getAccountInfo`, and `getBlock`.

Read-only observation on 2026-08-27:

- `solana-core`: `4.3.0-beta.2`;
- feature set: `2409014235`;
- finalized probe slot: `489069026`;
- the RPC accepted the version-1 ceiling; and
- the feature-account result was `null` at finalized commitment.

Consequently public-devnet TxV1 execution is **not activated** at this
observation. The module fails closed: RPC decoding support is not treated as
runtime activation.

Run the read-only probe only with:

```text
cargo run --features eight-lane-plumbing-v2 --example tx_v1_devnet_probe
```

## Safe executable test path

TxV1 is locally testable with Agave/test-validator 4.2 or later, or Surfpool
1.5 or later. A release test should:

1. start a disposable validator with TxV1 active at genesis;
2. verify its genesis hash, runtime version, and feature status;
3. deploy only the pinned candidate programs to that disposable ledger;
4. build each exact maximum-shape placeholder wire above;
5. replace placeholders with test-only signatures and submit to the disposable
   validator;
6. assert `0x81`, exact bytes/account indices/resource config, successful
   execution, replay rejection, and state rollback on verifier failure; and
7. destroy the ledger.

For public devnet, do not proceed until the finalized feature account contains
a nonempty activation slot. The first live-cluster action should then still be
`simulateTransaction` with an exact candidate and explicit user authorization;
submission remains a separate approval boundary.

## Sources

- Solana larger transaction sizes:
  <https://solana.com/upgrades/larger-transaction-sizes>
- SIMD-0385 transaction v1:
  <https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0385-transaction-v1.md>
- SIMD-0296 larger transactions:
  <https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0296-larger-transactions.md>
- Official examples:
  <https://github.com/solana-foundation/transaction-v1-examples>
