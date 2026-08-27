# TxV1 ASQ8 versus ASF8 byte-for-CU audit

Status: default-off wallet measurement only. This change does not add an ASF8
program dispatch, alter cryptography, estimate CU savings, sign, submit, or
deploy a transaction.

Base: `041780f4ef0be98c5b1675df87917046b62b4c2f`.

## Exact variants

- Variant 0 is the current canonical 320-byte ASQ8 request.
- Variant 1 substitutes the canonical 1,880-byte ASF8 statement.
- Both use one TxV1 instruction, the same native `TransactionConfig`, the same
  fee payer, the same program id, and byte-for-byte equal ordered account
  metas, signer flags, and writable flags.
- The approximately 30 KiB proof remains in its read-only proof account.

The measurement builder accepts a previously validated ASQ8 instruction and
fails closed unless ASF8 has the identical payment public input and exact
master/checkpoint/selected-lane account identities.

## Serialized TxV1 results

Every number includes the version byte, message, `TransactionConfig`, account
indices, instruction data, and placeholder signature array.

| Payment/page shape | Accounts | ASQ8 bytes | ASF8 bytes | ASF8 headroom to 4096 |
|---|---:|---:|---:|---:|
| transfer, same page | 9 | 811 | 2,371 | 1,725 |
| transfer, rollover | 10 | 844 | 2,404 | 1,692 |
| withdrawal, same page | 14 | 976 | 2,536 | 1,560 |
| withdrawal, rollover | 15 | 1,009 | 2,569 | 1,527 |

The exact increase is 1,560 bytes in every terminal shape, equal to
`1880 - 320`. No short-vector boundary changes under TxV1's wincode encoding.

Unaffected maximum operations retain their previously frozen sizes:

| Operation | TxV1 bytes |
|---|---:|
| AS8I initialize | 904 |
| AS8C checkpoint | 662 |
| AS8D rollover deposit with 512-byte encrypted note | 1,277 |

## Binding boundary

ASF8 itself carries and canonically validates:

- transition kind and output lane;
- master, retained-checkpoint, and selected-lane account identities;
- checkpoint sequence and historical global root;
- the 800-byte live lane snapshot: Pool/domain, sequence/index, current root,
  and all 20 frontier nodes;
- the 688-byte candidate afterstate: next index/root/frontier; and
- the complete transfer or withdrawal public input.

The outer program id and all Pool/registry/verifier/proof/token metas remain in
the transaction. ASF8 does not literally encode ASQ8's profile, release, or
Pool-program fields. Any executable Variant-1 caller must therefore derive and
validate profile/release from the retained registry entry and bind the
executing Pool program. The measurement helper uses the canonical ASQ8
reference to enforce these identities; this is not a substitute for a program
implementation.

## Instruction-carried verified-hint inventory

The actual verifier caller in
`programs/aspis-verifier/src/v7_pair_forest_dispatch.rs` currently:

1. decodes ASQ8;
2. decodes and authenticates the proof/master/checkpoint/lane accounts and
   their PDAs;
3. constructs and serializes the 800-byte live snapshot;
4. parses the proof-carried candidate afterstate; and
5. reconstructs the typed ASF8 statement.

The following ASF8-carried values are plausible reuse inputs, but no saving is
claimed until measured in SBF and proved equal to the authenticated sources:

| Candidate reuse | Existing authenticated source | Required check before reuse |
|---|---|---|
| encoded live snapshot slice | decoded lane + master | canonical decode and exact equality to account fields |
| output lane | low three canonical nullifier bits | recompute and compare |
| checkpoint sequence/root | decoded checkpoint PDA/account | exact equality and retained-root validation |
| master/checkpoint/lane ids | runtime account keys | exact ordered equality |
| candidate ASJA afterstate | finalized proof-account suffix | canonical parse and exact equality to proof-carried bytes |
| complete ASF8 bytes | reconstructed typed statement | canonical decode plus all comparisons above |

Several tempting hints are not independently trustworthy:

- a supplied statement/request digest still needs recomputation unless the
  proof transcript already binds exactly that digest;
- supplied selector values, Poseidon intermediates, Merkle routing, or fold
  values are not in the committed ASF8 codec and cannot replace computation
  without a new cryptographic constraint; and
- proof length/frontier-node count and selected profile/release remain outside
  ASF8 and must continue to come from authenticated proof/registry state.

This makes Variant 1 a useful byte budget: up to 1,527 bytes of TxV1 headroom
remain in the worst withdrawal-rollover shape. It is not evidence that any
specific reuse will save CU.

## Reproduction

From `crates/aspis-pool-wallet-v1`:

```text
CARGO_BUILD_JOBS=2 cargo test --locked --features eight-lane-plumbing-v2 lane_forest_transaction_v1::tests::asq8_and_asf8_variants_measure_same_page_and_rollover_exactly
```

No Solana CLI command is needed for this offline serialization audit. If a
future CLI check is added it must be prefixed with `NO_DNA=1`.
