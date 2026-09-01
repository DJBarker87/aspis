# V7 fresh-deposit witness adapter audit — 2026-09-01

## Result

The smallest honest live-account adapter is implemented in the host-only
release harness. It maps exactly this finalized state into the native V7
eight-lane input witness and terminal statement:

1. all eight canonical lane PDAs were freshly initialized;
2. one public deposit appended one occupied/empty pair leaf;
3. the first coherent immutable checkpoint was finalized immediately after
   that deposit; and
4. the wallet supplies the private note opening and matching nullifier key.

The adapter then constructs and checks:

- `PoolV1PairForestInputNoteWitnessV1`;
- the private three-level lane-to-global-root path;
- the exact selected live output-lane snapshot;
- the native private-transfer relation and candidate afterstate;
- canonical 320-byte ASQ8 and 1,880-byte ASF8 images;
- byte-exact ASQ8-to-ASF8 reconstruction;
- the Tag-73 statement digest; and
- the existing host semantic-terminal result/residual check.

No Pool/verifier Rust, cryptography, transaction format, Lean/Aeneas source,
SBF artifact, CU measurement, deployment identity, key or transaction was
changed.

## Why the adapter is deliberately narrow

An authenticated incremental-tree account stores the root and carry frontier,
not every historical leaf. In a populated lane, those bytes do not determine
an old note's Merkle siblings. Deriving a path from the frontier would be
unsound.

The very first deposit is the unique useful live case whose complete path is
determined without an indexer history: pair index zero has the twenty pinned
pair-empty roots as siblings. The other seven lane roots are also pinned empty
roots, so the three super-root siblings are reconstructed exactly from the
eight authenticated lane accounts.

The adapter therefore rejects even a completely canonical first checkpoint
that contains two deposits. General populated operation must consume the
finalized append stream and the existing durable per-lane witness state.

## Fail-closed account boundary

Before decoding a field, the adapter requires all ten state accounts (master,
eight lanes and checkpoint) to have:

- finalized commitment;
- one identical nonzero RPC context slot;
- exact Pool program ownership;
- `executable = false`;
- exact byte length;
- canonical codec round trip;
- canonical master/lane/checkpoint PDAs;
- unique lane addresses in lane-id order;
- exact master/deployment/lane/checkpoint bindings; and
- exact first-checkpoint chronology and lane sequences.

It independently replays the one deposit from the private opening, checks the
nullifier key derives the note owner key, checks the routed deposit lane, and
requires every finalized lane tree to equal the replayed fresh state.

## Focused replay

Run only the two adapter targets:

```sh
CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=1 cargo test --release --lib \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml \
  -- fresh_deposit_witness_adapter::tests::first_finalized_deposit_maps_to_exact_witness_asq8_and_asf8 \
  --exact --nocapture

CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=1 cargo test --release --lib \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml \
  -- fresh_deposit_witness_adapter::tests::adapter_fails_closed_on_rpc_account_and_secret_mismatch \
  --exact --nocapture
```

Measured locally on the first focused green runs:

| Target | Result | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| exact witness + ASQ8/ASF8 | 1/1 | 2.81 s | 161,726,464 B | 0 |
| fail-closed mutations/populated state | 1/1 | 1.50 s | 172,589,056 B | 0 |
| final combined focused replay | 2/2 | 1.28 s | 173,309,952 B | 0 |

The second target rejects non-finalized commitment, wrong owner, incoherent
context slot, wrong spending key, malformed account bytes and a canonical but
populated two-deposit checkpoint.

## Remaining integration boundary

This closes the deterministic account-to-witness/statement gap for the fresh
deposit disposable lifecycle. It does not yet:

- fetch or attest RPC finality itself;
- generate/mine the 30.5-KiB proof from the returned native witness;
- upload a proof account;
- sign or submit a transaction; or
- recover general populated-lane paths.

For general operation, the already implemented durable lane witness machinery
needs an authenticated production event/append source. Its current V2 module
explicitly records that the compact pair-forest event ABI is not yet emitted
by a deployed Pool instruction. That emitter/indexer integration, followed by
the ordinary proof-builder call, is the smallest remaining general-case
adapter work. Registry/profile/release authentication remains the Pool's
existing on-chain boundary and is intentionally not duplicated here.
