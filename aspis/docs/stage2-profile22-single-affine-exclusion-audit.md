# Profile 22: single affine-exclusion audit

Date: 2026-07-13

## Result

Excluding only the known last-round hyperplane is **not sufficient** to make
the canonical `FullSharedLinear` raw-quotiented masked-sumcheck map
surjective for every distinct `q16` tuple.

There is an explicit, non-random counterexample.  Keep the frozen fixture's
16 distinct queries and every challenge other than `z`, and set

```text
z = (1, 1, 1, 1, 1, 1, 0, 1, i, u).
```

The exact M31 elimination reaches every C1 and G raw-rank check, then reports

```text
MaskedSumcheckRank { got: 790, want: 1080 }.
```

Thus this is a counterexample to the proposed universal implication, not a
scan or a failure to find a minor.  It makes no production wire or verifier
change.

## Why the last-round condition misses it

Write the two linear families used by `FullSharedLinear` as

```text
L0  = sum_v a_v x_v,     a_v = 3 + 22v,
L16 = sum_v b_v x_v,     b_v = 275 + 150v.
```

In sumcheck round `r`, after fixing the earlier coordinates to `z` and a
source row's later coordinates to the Boolean suffix `s`, write the two
restricted lines as `C0+a_r t` and `C16+b_r t`.  Their determinant is

```text
Delta_r = a_r C16 - b_r C0
        = 5600 * (
            sum_{v<r} (r-v) z_v
          + sum_{v>r} (r-v) s_v
          ).
```

The identity is immediate from

```text
a_r b_v - b_r a_v = 5600(r-v).
```

For `r=9` there is no Boolean suffix, recovering the known identity.  On the
counterexample,

```text
Delta_9 / 5600 = 41 + i != 0.
```

So it is outside the excluded hyperplane.  Earlier rounds still have
proportional suffix fibres:

| round | relation-free row | cancellation in `Delta_r/5600` |
|---:|---:|---|
| 1 | 896 | `1 - 1 = 0` |
| 2 | 912 | `3 - 3 = 0` |
| 3 | 897 | `6 - 6 = 0` |
| 4 | 915 | `10 - (1+4+5) = 0` |

All four rows occur in the relation-free support of every one of the 16
semantic columns.  This does not, by itself, derive the numerical rank 790;
it shows algebraically why one last-round determinant cannot control the
whole map.  The exact source-aware elimination below is the rank certificate.

## The source map that was actually ranked

The rank calculation does not replace the source map by an abstract span of
factor polynomials.

* Each semantic column uses only its cells from
  `atomic_state_only_relation_free_mask_cells_v3`.  There are 5,262 such
  cells.  Inactive cells are the balanced directions `e_r-e_1023`; active
  cells are `e_r`.  The common inactive block `896..=1023` is retained.
* Semantic column `c` is an M31 source lane multiplied by the exact tower
  rotation `beta_(c mod 4)` and its scheduled power of `L0`.  It is not an
  arbitrary QM31 coefficient for that power.
* The ten mask-only columns likewise retain their M31 source lanes and
  rotations `beta_(j mod 4)`.
* G retains all four M31 tower-coordinate sources multiplying the exact
  factor `1+L16^26`.
* For each of the 26 C1 blocks the implementation first eliminates its exact
  76-M31 raw view.  It separately eliminates G's exact 268-M31 raw view.
  Only the resulting kernel images are inserted into the 1,080-M31 legal
  masked-sumcheck quotient.

Multiplication by every `beta_j` is invertible over M31, but those rotations
do not manufacture four independent source coordinates where the protocol
provides only one.  Likewise, the unequal semantic supports and their
inactive balancing relations survive raw quotienting.  This is why
factor-polynomial span is not a substitute for source-map span.

## Executable certificate

Fast algebra/support guard:

```sh
NO_DNA=1 cargo test -q -p aspis-prover --test profile21_hvzk_privacy \
  a_nonzero_last_round_determinant_does_not_control_earlier_round_fibers
```

Exact raw-plus-sumcheck elimination:

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  single_last_round_exclusion_still_leaves_masked_sumcheck_rank_790 \
  -- --ignored
```

The slow test calls the baseline atomic-v3 `FullSharedLinear` gate directly.
That gate returns a raw-rank error before sumcheck if any raw block is not
full.  Reaching the pinned `790/1080` sumcheck error therefore certifies both
raw fullness for this distinct `q16` and failure of the quotiented source
map.

## Consequence

The proposed theorem with the sole premise `Delta_9 != 0` is false.  A valid
replacement must either:

1. construct and prove a source-aware triangular 1,080-row minor after all
   raw quotients, including every round, Boolean suffix, semantic support and
   tower rotation; or
2. define `Good` by a nonzero exact minor polynomial and charge its rejection
   probability.

Even excluding every visible `Delta_r(s)=0` locus is not yet proved
sufficient.  This audit establishes a counterexample to the single condition;
it does not claim a complete characterization of the bad locus.

## Direct-sum follow-up

Continuing the deficient sumcheck elimination and comparing only downstream
PCS ranks produces a false green.  Literal raw-to-sumcheck-to-PCS block
elimination, including independently allowed legal sumcheck directions, is
recorded in
[the direct-sum containment audit](stage2-profile22-direct-sum-containment-audit.md).
The frozen actual schedule is also red by four under that documented target.
