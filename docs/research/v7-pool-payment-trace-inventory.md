# Pool V1 payment trace: exact block and cell inventory

Status: host-side trace/compiler foundation, 25 August 2026.

Implementation: `crates/aspis-statement/src/pool_v1/payment_trace.rs`.

This freezes the Pool V1 payment schedule inside the existing Tag-73 physical
geometry: 1,024 rows, 16 M31 C1 columns, 49 aligned 16-row Poseidon blocks.
It does not change either Pool V1 executable payment relation and it does not
claim a prover, verifier, transcript, terminal oracle, or Solana integration.

## Admission rule

The public builders first execute the applicable relation:

- `evaluate_pool_v1_private_transfer_v1`, or
- `evaluate_pool_v1_withdrawal_v1`.

No trace allocation or hash recording happens until that call returns
`Ok(())`. The public validators execute the same relation before checking a
candidate trace. Thus a failed conservation, range, path, public-binding, or
spent-nullifier check cannot be converted into a trace.

## Fixed 49-block schedule

| Block(s) | Rows | Operation | Transfer | Withdrawal |
|---:|---:|---|---|---|
| 0 | 0..15 | owner-key sponge, one permutation | real | real |
| 1..3 | 16..63 | input-note sponge, three permutations | real | real |
| 4..23 | 64..383 | depth-20 v3 Merkle path, one permutation per level | real | real |
| 24..25 | 384..415 | nullifier sponge, two permutations | real | real |
| 26..28 | 416..463 | recipient-note slot, three permutations | real | fixed zero-input permutations |
| 29..31 | 464..511 | change-note sponge, three permutations | real | real |
| 32..48 | 512..783 | reserved tail, 17 permutations | fixed zero-input permutations | fixed zero-input permutations |

The path block at index `4 + level` uses private direction bit `level`, where
level zero is the leaf-side bit. A zero bit orders `(current, sibling)` and a
one bit orders `(sibling, current)`. The ordered pair is fed to the exact
existing `merkle_node_compress_v3`: right occupies row-zero lanes 8..15, the
v3 tweak is added to row-zero lane 15, and left occupies absorption-row lanes
0..7.

Every padding block is a fresh, independent permutation whose 16-lane
pre-absorption state and eight-lane absorption vector are both zero. Padding
blocks are not chained together. Consequently all fixed padding blocks have
the same trace, and no witness value can hide in their preimage.

## Cells inside every 16-row block

For block `b`, let `base = 16*b`.

| Local row | Global row | 16 C1 cells |
|---:|---:|---|
| 0 | `base` | exact state before the block's rate-lane absorption |
| 1..10 | `base+1 .. base+10` | state after round pairs 0..9 |
| 11 | `base+11` | final state after round pair 10 (all 22 rounds) |
| 12 | `base+12` | absorbed rate-8 vector in lanes 0..7; lanes 8..15 zero |
| 13..15 | `base+13 .. base+15` | fixed zero |

Sponge block zero has capacity lanes `(domain, input_length)` in row zero.
Each continuation block has the previous block's final state in row zero.
The final partial note chunk contains exactly two live absorption limbs; its
other six rate limbs are zero. The construction records transitions from the
existing `hash_fields_with_trace` and `permute_optimized_with_trace` paths.

Validation deliberately takes a separate route. It reads only the 16-C1
candidate, checks each exact preimage and absorption vector, and invokes
`evaluate_trace_round_pair` for all

`49 * 11 = 539`

two-round edges. Each computed successor is compared with the next recorded
state. It then compares the replayed owner key, input leaf, every v3 parent,
anchor, nullifier, recipient commitment (transfer), and change commitment
with the existing typed primitives and the payment public statement.

## Auxiliary cells

Rows 784..791 record the only scalar witnesses not already present in a hash
preimage. All unspecified cells in these rows are zero, and every cell in rows
792..1023 is zero in this foundation.

| Meaning | Cells | Bit order |
|---|---|---|
| path directions 0..15 | row 784, columns 0..15 | least-significant path bit first |
| path directions 16..19 | row 785, columns 0..3 | remaining columns zero |
| input value bits 0..29 | row 786 columns 0..15, then row 787 columns 0..13 | least-significant bit first |
| recipient/withdrawal value bits 0..29 | rows 788..789 in the same layout | transfer recipient value; withdrawal public amount |
| change value bits 0..29 | rows 790..791 in the same layout | least-significant bit first |

Each value is therefore represented by an exact 30-bit Boolean decomposition.
The executable relation has already established the corresponding `< 2^30`
range and conservation equation before these bits are emitted.

## Public-output parity

For both variants, replay must equal the statement's historical anchor,
nullifier, and change commitment. Transfer additionally binds the recipient
commitment. Withdrawal has no hidden recipient-note preimage: blocks 26..28
are fixed padding, while the withdrawal amount is public and is recorded as
the middle 30-bit value decomposition.

The trace stores a typed public-output summary, but validation recomputes it
from the C1 cells and rejects metadata disagreement. It never trusts that
summary as a source of hash values.

## Frozen proof grammar screen

This trace work preserves, but does not instantiate, the existing 30,504-byte
Tag-73 native proof grammar:

| Component | Bytes |
|---|---:|
| fixed grammar | 9,936 |
| roots | 52 |
| work | 24 |
| 16 query records at 621 bytes | 9,936 |
| two 203-node frontiers at 26 bytes per node | 10,556 |
| **total** | **30,504** |

The total is a compile-time assertion in `payment_trace.rs`. No proof bytes,
query count, frontier shape, verifier dispatch, or terminal behavior are
modified by this foundation.

## Focused evidence

Run only the new host tests:

```sh
NO_DNA=1 CARGO_BUILD_JOBS=2 \
  cargo test -p aspis-statement pool_v1::payment_trace::tests --no-fail-fast
```

The focused corpus covers both honest variants, all geometry/schedule
constants, exact withdrawal padding, independent replay of the 539
two-round edges, auxiliary placement, transition/cell mutation rejection,
and the rule that relation rejection precedes construction.
