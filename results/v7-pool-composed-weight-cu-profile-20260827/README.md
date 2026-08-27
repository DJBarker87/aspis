# V7 Pool composed relation-weight audit (2026-08-27)

## Result

The exact composed Tag-73 weight tail is correct and reduces the complete
direct native Pool verifier from 1,255,491 CU to **1,254,737 CU** on the
identical honest 30,192-byte proof. The transaction accepted in both local
simulation and execution with byte-identical metadata, leaving **145,263 CU**
under the 1.4M limit.

The saving is real but small:

| Measurement | Sequential | Composed | Saving |
| --- | ---: | ---: | ---: |
| Three weight regions | 71,333 | 70,562 | 771 |
| Complete verifier | 1,255,491 | 1,254,737 | 754 |

The 17-CU difference between the two savings is the aggregate change in the
other measured tail regions and minor code-layout effects. No unmeasured
diagnostic-removal or frozen-schedule saving is credited.

The diagnostic SBF grows from 876,240 to 911,280 bytes (**35,040 bytes**) for
this 754-CU saving. The kernel is therefore exact and marginally faster, but
it is not an especially attractive production trade unless CU headroom is
valued more highly than program size.

## Exact transformation

For one dual arity-four fold, define

```text
d(a) = (1, a^3, a^2, a) / 4.
```

Two sequential folds over one 16-entry chunk are exactly

```text
sum_h d(b)[h] * (sum_l d(a)[l] * w[4h+l])
  = sum_h sum_l d(b)[h] * d(a)[l] * w[4h+l].
```

The composed deferred-mask kernel constructs that tensor product directly,
aggregates coefficients having the same frozen group identifier, and applies
four halvings. It therefore produces the same four terminal weights as the
two former grouped folds.

The complete accumulator kernel preserves the original semantic sequence:

1. apply round one's ordinary dual fold with `alpha[1]`;
2. perform the same checked merge of multilinear components 0 and 2;
3. apply the `alpha[2]` and `alpha[3]` folds in order to every component;
4. use the composed 16-entry map only for the deferred grouped-row component;
5. compare the same final four-weight dot product with the same running claim.

Only execution timing moves. The transcript still absorbs each polynomial and
derives every alpha challenge in its original round, and the running claim and
final256 values are still updated round by round. Relation weights are not
read between query-batch installation and the terminal dot, which is why their
equivalent fold can safely be delayed until the third round.

## Equality evidence

Two focused deterministic randomized tests passed:

- `composed_grouped_high_rows_match_two_sequential_folds`: 64 schedules,
  1--23 distinct groups, random values and both challenges; compares all four
  values represented by the sequential and composed schedules;
- `tag73_composed_weight_tail_matches_sequential_rounds`: 32 complete
  accumulator shapes containing the three multilinear claims, the deferred
  64-by-16 mask, two circle tensors and the 16-line M31 query batch; compares
  every terminal weight and the terminal dot against the original three
  sequential folds.

The existing ten focused `v7_compact` host tests also passed. There is no
proof-byte, hash, Merkle, transcript, field, sumcheck or terminal-equation
change.

## Measured phases

The old diagnostic placed a checkpoint after each sequential weight fold. The
new diagnostic keeps those phase labels, so rounds one and two now record only
the 224-CU checkpoint and round three records the complete composed kernel:

| Weight phase | Sequential CU | Composed CU |
| --- | ---: | ---: |
| Round one | 25,859 | 224 |
| Round two | 25,475 | 224 |
| Round three | 19,999 | 70,114 |
| **Total** | **71,333** | **70,562** |

This falsifies the earlier 35,640-CU target. Most work is intrinsic field
arithmetic in the multilinear, circle and 16-line components; composing the
control flow removes only intermediate grouped-row bookkeeping and loop
overhead. The result should not be represented as a large remaining CU lever.

## Provenance

- baseline source/evidence commit:
  `2586d6244553720596c9f6192c6059b01c2d9d46`;
- proof SHA-256:
  `656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c`;
- diagnostic SBF: 911,280 bytes, SHA-256
  `e53b42cf14cae4dd849e55708b2f4d9043a270df18c31fb9474b0846fad70694`;
- focused SBF build: 16.77 seconds, 655,048,704-byte peak RSS, zero swap;
- no final stack-offset or frame-clobber linker diagnostic;
- exactly one source-changed LiteSVM measurement;
- local simulation/execution only: no RPC, deployment, signing or network
  submission.

The diagnostic checkpoints remain production-inactive behind the isolated
`v7-pool-cu-profile` feature. The evidence does not claim any saving from
removing them or from freezing the inactive schedule.
