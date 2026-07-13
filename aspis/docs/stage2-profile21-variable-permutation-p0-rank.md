# Profile-21 first-variable permutation p0 screen

Date: 2026-07-13

## Verdict

All ten choices of the first sumcheck variable are **RED**.  After exact raw
opening and masked-sumcheck conditioning, every choice leaves the same
one-QM31 early-`p0` quotient:

```text
selected p0-view mask rank       292 M31
semantic augmented rank          296 M31
legal-sumcheck augmented rank     296 M31
semantic pivots                  [284,285,286,287]
```

Because this screen retains the complete H raw view and all seven
coefficients of the round-zero relation polynomial, a failure is conclusive.
No choice warrants a full PCS replay.

## Exact transformation

For each `b=0..9`, define the stable physical coordinate order

```text
pi_b = [b, 0, ..., b-1, b+1, ..., 9].
```

Every trace row, copy-active row, relation-free mask cell and copy-inactive
mask is reindexed together.  The sampled Fiat--Shamir vector remains in
physical round order.  The three opening points are

```text
[z, pi_b(succ(pi_b^-1(z))), pi_b(xor12(pi_b^-1(z)))].
```

Using `succ(z)` or `xor12(z)` after reordering would change the statement
map, so that cheaper but invalid transformation is not tested.

The root-zero circle encoding, raw openings and literal arity-four dual `p0`
polynomial are evaluated on the physically reindexed word.  Shared layer-zero
and masked-sumcheck maps are cached across the ten variants; terminal maps and
`p0` are rebuilt for each permutation.

## Identity and dense guards

The identity choice reproduces the known four-M31 obstruction.  Independent
dense-reference guards run for identity `b=0` and nontrivial `b=7` and pass:

- the grouped inactive covector equals a materialized dense covector on all
  1024 rows;
- the cached unit-row `p0` map equals `polynomial_for_extension` on a
  deterministic dense message;
- structured and dense `WeightAccumulator` forms produce identical `p0`;
- logical and physically reindexed messages agree at all three conjugated
  terminal points.

## Results

All variants have raw C1 rank `1976`, raw G rank `268`, masked-sumcheck rank
`1080`, p0-view size `296`, selected rank `292`, and semantic/legal rank
`296`.

| first bit | physical-to-logical order | inactive low-mask groups | result |
|---:|---|---:|---|
| 0 | `0,1,2,3,4,5,6,7,8,9` | 7 | RED |
| 1 | `1,0,2,3,4,5,6,7,8,9` | 7 | RED |
| 2 | `2,0,1,3,4,5,6,7,8,9` | 7 | RED |
| 3 | `3,0,1,2,4,5,6,7,8,9` | 7 | RED |
| 4 | `4,0,1,2,3,5,6,7,8,9` | 7 | RED |
| 5 | `5,0,1,2,3,4,6,7,8,9` | 7 | RED |
| 6 | `6,0,1,2,3,4,5,7,8,9` | 11 | RED |
| 7 | `7,0,1,2,3,4,5,6,8,9` | 13 | RED |
| 8 | `8,0,1,2,3,4,5,6,7,9` | 11 | RED |
| 9 | `9,0,1,2,3,4,5,6,7,8` | 11 | RED |

Bits 0--5 preserve the current seven-group copy-inactive representation and
are therefore genuine zero-cost failures.  Bits 6--9 also fail privacy and
increase the low-mask group count, so they point in the wrong CU direction.

## Reproduction

```text
NO_DNA=1 cargo build --release -q -p aspis-prover \
  --example profile21_variable_permutation_p0_rank

NO_DNA=1 target/release/examples/profile21_variable_permutation_p0_rank \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin 0 1

NO_DNA=1 target/release/examples/profile21_variable_permutation_p0_rank \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin 1 10
```

Machine-readable results are in
`results/stage2/profile21_variable_permutation_p0_rank.json`.  This diagnostic
does not mutate the production proof or verifier.
