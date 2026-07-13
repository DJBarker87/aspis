# Profile 22 complete shared-factor mask basis

Date: 2026-07-13

Status: **complete bounded family is rank-deficient; no production change.**
The host probe completes every full-domain M31 mask-only lane of the form
`beta_r * L_0^d`, for `d=0..26` and tower rotation `r=0..3`, and conditions
each lane on its own literal q16 leaf values and three terminal values.  The
complete family fails on both frozen-query control points.  Consequently no
ordering, subset, or "minimum lane count" inside this family can repair the
schedule.

This is a host-only algebra diagnostic.  It changes no proof wire, transcript,
commitment, verifier, layout fingerprint, or accepted proof.

## Complete bounded object

The grid contains 108 full-domain M31 lanes.  Production already contains the
ten pairs

```text
(degree, rotation) =
(1,0), (3,1), (5,2), (7,3), (9,0),
(11,1), (15,2), (17,3), (19,0), (21,1).
```

The probe inserts the remaining 98 pairs in degree-major, rotation-minor
order.  The 16 semantic lanes are replayed separately because they are not
full-domain mask-only lanes.  Production G is also replayed.  Every processed
extra lane has literal raw rank 76 M31 after its q16 four-slot leaf block and
three QM31 terminal values are conditioned separately.  The missing-lane
schedule fingerprint is `0xbcf75c64bbeda45a`.

## Exact rank result

The legal masked-sumcheck target is 1,080 M31 dimensions.

| schedule | production width | after all 98 lanes | first full prefix |
|---|---:|---:|---:|
| frozen profile-21 fixture | 1,080 | not processed | 0 |
| nonzero-last control, `z=[1,1,1,1,1,1,0,1,i,u]` | 790 | 808 | none |
| affine-degenerate control, `z_0=-(32+i)/9` and the same tail | 916 | 976 | none |

The exact prefix vectors are pinned in
`results/stage2/profile22_complete_shared_mask_basis.json` and by the ignored
three-schedule regression.  Both controls reuse the fixture's 16
without-replacement query indices, which the test confirms are all distinct.

Because the probe evaluates the complete 108-lane shared-factor span, the red
result is stronger than a failed greedy order.  Every subset of those lanes
has image contained in the tested image.  Reordering cannot raise the final
rank, and a minimum successful lane count does not exist in this family.

## What the local inverses do prove

Two q-uniform local algebra facts and the tower-basis fact are green.

For every monic degree-16 query kernel

```text
g_q(X) = X^16 + sum_(a=0)^15 g_a X^a,
```

the map from `h_0..h_15` to degrees 16 through 31 of `g_q h` is triangular
with unit diagonal.  Given targets `y_16..y_31`, descending substitution is

```text
h_j = y_(j+16) - sum_(k=j+1)^15 h_k g_(j+16-k).
```

On sumcheck round `r`, the shared linear form restricts to

```text
L_0 = C + s_r t,       s_r = 3 + 22r.
```

Every `s_r`, for `r=0..9`, is nonzero in M31.  Thus powers
`(C+s_r t)^d`, `d=0..26`, span every degree-at-most-26 polynomial.  If
`p(t)=sum_k p_k t^k`, one explicit inverse is

```text
a_d = sum_(k=d)^26 p_k s_r^(-k) binom(k,d) (-C)^(k-d),
p(t) = sum_(d=0)^26 a_d (C+s_r t)^d.
```

Finally, rotations `{1,i,u,iu}` are the frozen M31 basis of QM31.  Fast tests
exercise all three statements directly.

These local inverses do **not** compose into a global right inverse after each
source is separately conditioned on its authenticated raw q16 and terminal
block.  The two exact counterexamples retain distinct queries, monic `g_q`,
all ten nonzero affine slopes, and all four tower rotations, yet remain short
by 272 and 104 M31 dimensions respectively.  Therefore those premises alone
cannot support an all-distinct-q full-rank theorem.  The missing load-bearing
property is cross-round/source coupling compatible with all three terminal
conditions and the separately authenticated raw blocks.

## Wire and CU screen

One hypothetical extra M31 lane adds:

```text
C1 leaf value                         16 bytes
q16 opened values                 16*16 = 256 bytes
three terminal values              3*16 =  48 bytes
serialized opening increment                304 bytes
```

Completing all 98 missing lanes would therefore move:

```text
C1 leaf width                       416 -> 1,984 bytes
outer generator width                28 ->   126 lanes
proof bytes                      56,686 -> 86,478 bytes
```

The prior q36 layer-zero width probe measured 7,380.1875 CU per removed M31
column over its 49-to-33 interval.  Scaling only its query-linear arithmetic
to q16 gives a planning proxy of 3,280.0833 CU per lane, or approximately
321,448 CU for 98 lanes.  This is **not** a measurement of this wire.  It
already exceeds the exact 230,286-CU System-create headroom before Merkle
hashing, terminal-factor evaluation, transcript, parsing, and handling are
counted.  Since the complete family is rank-red, no integrated verifier or CU
measurement was built.

## Reproduction

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile22_complete_shared_mask_basis \
  -- --skip complete_shared_grid_is_still_rank_deficient_on_both_distinct_q_controls

NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile22_complete_shared_mask_basis \
  complete_shared_grid_is_still_rank_deficient_on_both_distinct_q_controls \
  -- --ignored --nocapture

NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile22_complete_shared_mask_basis
```

## Verdict

The requested shared-`L_0`/tower-rotation completion has been exhausted and is
retired as a universal repair.  A successful construction must add factor
families with genuinely independent source/round coupling or change the
conditioning architecture; either is outside this bounded no-X/no-switch
probe and needs a new proof obligation.
