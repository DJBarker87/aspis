# Profile-21 two-variable restriction-kernel closure

Date: 2026-07-13

Status: **red for complete-view hiding.** The full three-generator kernel of
restriction at `s=2,t=3` does not cover the semantic view. No q20 replay or
profile-22 production wire is credited for this construction.

## Exact construction

The ten-variable message is duplicated over four physical blocks. The fixed
M31 restriction covector is

```text
[(1-2)(1-3), (1-2)3, 2(1-3), 2*3] = [2,-3,-4,6].
```

The three fresh QM31 G masks are

```text
(s-2)R1,
(t-3)R2,
(s-2)(t-3)R3.
```

Together with the constant function these form a basis of all bilinear
functions on the two Boolean variables. The three masks therefore span the
entire kernel of evaluation at `(2,3)`; this is not a partial mask family.
All pair products are performed in QM31 before serialization to four M31
coordinates.

## Exact q16 result

```text
masked sumcheck quotient                1080
G raw rank                               268
raw kernel per restriction generator    4096,4096,4096
baseline PCS rank                         712
after (s-2)R1                             808
after (t-3)R2                             872
after product R3                          936
after semantic directions                 940
after legal sumcheck                       940
missing pivots                    1084..1087
```

The final boolean is false. The restriction, semantic and legal minor
fingerprints are respectively

```text
0x7c278cc4c2d61a11
0x62237980a33f44b3
0x8070bc4cf4b76e45
```

The sparse log-12 public-map builder was differentially checked against the
dense encoder on sixteen rows. In every physical `(s,t)` quadrant the rows
exercise low base-four fold-slot patterns `0000`, `1111`, `2222` and `3333`.
This caught and corrected an earlier primal/dual quarter-normalization error;
the final expanded guard passes.

## Algebraic obstruction

All three generators lie in the restriction kernel. Consequently every fresh
direction has zero initial slice claim. After conditioning on authenticated
raw and OOD observations, its first relation polynomial has zero remaining
boundary carry. The extra variables substantially enlarge the later-opening
image—by 224 M31 dimensions in total—but cannot affect that carry.

The semantic quotient is exactly one QM31 boundary-carry direction. In the
q16 coordinate layout it appears as pivots `1084..1087`, the serialized
coefficient `c4` of the first relation polynomial after the already-covered
`c0` contribution is eliminated. This is the same separating functional as
in the one-variable closure. Adding more generators from an ideal that
vanishes at the statement slice cannot repair it.

A viable successor must bind a claim-carrying one-time pad: for example, an
upstream-style masked combined claim whose mask evaluation is committed but
not separately revealed. It cannot be another vanishing restriction-kernel
column.

## Soundness geometry retained for successors

The separate rate-1/128 q20/g38 Johnson ledger remains useful for any successor
that genuinely passes complete-view containment. It is not evidence for this
red construction. Production slices must stay in M31; the primary constants
are `2,3`. The subfield/Frobenius reduction and exact numeric ledger are in
`stage2-profile21-rate128-q20-johnson.md`.

The machine-readable rank evidence is
`results/stage2/profile21_two_variable_slice_lift_rank.json`; the implementation
is
`crates/aspis-prover/src/state_only_hiding_rank/state_only_two_variable_slice_rank.rs`.
