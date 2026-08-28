# V7 pair-forest strict-work KAT (2026-08-28)

## Result

One deterministic eight-lane private-transfer proof was built through the
production Tag-73 prover entry point and accepted through the production ASQ8
dispatcher with all three work checks enabled.

The frozen proof is
`programs/aspis-verifier/fixtures/v7-pair-forest-transfer-strict-work.bin`.
Its exact record is:

| Field | Value |
|---|---:|
| Proof body | 30,400 bytes |
| Frontier | 201 nodes per tree |
| SHA-256 | `b5f2c4cc2fd3e3851396a2eb32050a15dabfe0cec5a5f1ee10998e227632b03f` |
| Batch work | 35 bits, nonce `41,330,364,500` |
| Fold work | 31 bits, nonce `516,418,238` |
| Final work | 34 bits, nonce `29,526,748,214` |
| ASR8 | 792 bytes, exact decoded equality |

The fixed fixture uses literal program/mint/token/registry/proof keys, derives
the master, checkpoint and selected-lane PDAs canonically, reconstructs ASF8
from those accounts, and frames the finalized proof account as the 40-byte
ASPU header followed by the 688-byte ASJA and this proof body.

## Work search and minimum rule

The Apple Metal runner used 65,536 lanes with 4,096 trials per lane, hence
268,435,456 candidates per completed chunk. Searches began at nonce zero.
Every completed chunk advanced the durable checkpoint by exactly that amount;
the successful chunk was also completed in full and the runner selected the
minimum success across all lanes. Therefore every smaller nonce was tested,
including smaller successes in the successful chunk.

| Stage | Transcript state | Containing chunk end | Rate | Metal wall |
|---|---|---:|---:|---:|
| 35-bit batch | `51e2e0fbe0d95244742bbeae532db34a5a0e31b7d38254b05b275116cbece1e4` | 41,339,060,224 | 686.19 MH/s | 60.244 s |
| 31-bit fold | `c17f0dacf28ebe8d47e8f60e0d1f8232a5e0f357de04d706bd302b3024e6491f` | 536,870,912 | 686.25 MH/s | 0.782 s |
| 34-bit final | `18aabb3f34427578073bee058b3035ff1a1eddac1a5207b09d4953cbf2567b4c` | 29,527,900,160 | 686.06 MH/s | 43.040 s |

After each external process returned, the Rust honest prover independently
called the canonical `Transcript::grinding_ok(nonce, bits)` predicate before
absorbing that nonce. The built proof also recorded `pow_valid = true`.

The complete sequential checkpoint/progress transcript is frozen as
`programs/aspis-verifier/fixtures/v7-pair-forest-transfer-strict-work.metal.log`
with SHA-256
`99bcf097bf88dc89f85c4effae827760a0cfa14aba9b1a569d7bf06f661cc97c`.
The Metal runner removes a stage checkpoint after successful completion; the
log retains every completed checkpoint boundary and the successful containing
chunk.

Proof construction plus all three searches took 117.870 seconds after the
optimized test executable started. The first complete command, including a
cold optimized Rust build, took 263.43 seconds. `/usr/bin/time -l` recorded a
maximum RSS of 471,334,912 bytes and zero swaps.

## Frozen strict dispatcher test

`frozen_strict_work_transfer_dispatches_through_production_checks` does not
call the prover or a miner. It:

1. loads the frozen proof with `include_bytes!`;
2. pins its length, SHA-256, frontier count, nonces and 35/31/34-bit profile;
3. reconstructs the exact authenticated ASF8 statement from fixed canonical
   master/checkpoint/lane accounts;
4. invokes `process_v7_pair_forest_asq8_instruction`, whose production path
   hardcodes `check_work = true`;
5. captures and decodes the exact 792-byte ASR8 result; and
6. replaces only the batch nonce with zero and requires production rejection
   with empty return data.

The focused optimized test itself completed in 0.01 seconds. Its command took
12.38 seconds including an incremental rebuild, with maximum RSS 373,555,200
bytes and zero swaps.

## Replay

Build the checked Metal miner:

```sh
NO_DNA=1 ./tools/build-aspis-pow-metal.sh target/release/aspis-pow-metal
```

To regenerate the public KAT with resumable per-state checkpoints:

```sh
chmod +x programs/aspis-verifier/fixtures/v7-pair-forest-transfer-strict-work-miner.sh
NO_DNA=1 \
ASPIS_POW_MINER="$PWD/programs/aspis-verifier/fixtures/v7-pair-forest-transfer-strict-work-miner.sh" \
ASPIS_POW_METAL_BIN="$PWD/target/release/aspis-pow-metal" \
ASPIS_POW_METAL_CHECKPOINT_DIR="$PWD/target/strict-work-kat/checkpoints" \
ASPIS_POW_METAL_LOG="$PWD/target/strict-work-kat/metal.log" \
ASPIS_STRICT_FOREST_KAT_OUT="$PWD/target/strict-work-kat/v7-pair-forest-transfer-strict-work.bin" \
CARGO_BUILD_JOBS=1 \
cargo test --release -p aspis-verifier --features v7-pair-forest-asq8 --lib \
  v7_pair_forest_dispatch::tests::regenerate_strict_work_transfer_kat_with_production_miner \
  -- --ignored --exact --nocapture --test-threads=1
```

The checkpoint wrapper is fixture-only because it deliberately persists the
transcript states. It must not be used for an unpublished production wallet
attempt.

To replay the frozen strict production dispatcher test without mining:

```sh
NO_DNA=1 cargo test --release -p aspis-verifier \
  --features v7-pair-forest-asq8 --lib \
  v7_pair_forest_dispatch::tests::frozen_strict_work_transfer_dispatches_through_production_checks \
  -- --exact --nocapture --test-threads=1
```

No Pool harness, deployment, signing, transaction submission or chain state
was touched by this KAT.
