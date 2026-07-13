# State-only late-switch rank probe

This note records an exact host-side affine-rank result. It is not an HVZK
claim and it does not authorize production integration.

## Result

At the measured rate-1/32, q29 schedule, the existing mask map covers all
1,080 M31 dimensions of the external masked-sumcheck quotient. After that
wire is conditioned, its complete PCS image has rank 1,024 inside an ambient
rank-1,144 View. The deficit is exactly 120 M31, or 30 QM31, dimensions.

The complete View used here retains both tests that must not be conflated:

1. the concrete valid-witness-difference containment test remains green, and
   the stronger active zero-sum helper augmentation leaves rank 1,024
   unchanged; and
2. the independently generated ambient target remains rank 1,144, so the
   baseline construction still fails full ambient containment by 120.

The missing quotient has 116 pivot coordinates in later query openings and
four in the transmitted relation coefficients. It has no OOD or final-
coefficient pivots in the canonical elimination order.

## One late 31-variable group

A greedy exact basis of the missing quotient uses the 30 independent source
rows

```text
1, 2, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48,
52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100,
104, 108, 112
```

and row 3 as the dependent variable. Equivalently, the 31-variable support is

```text
{1,2,3} union {4*j : 1 <= j <= 28}.
```

For coefficients `c_i = gamma^(i+1)`, the probe inserts, for every free
variable `i` and every M31 tower basis vector `b`,

```text
A_i(c_30 * b) - A_30(c_i * b).
```

Each displayed column satisfies the dense identity
`sum_i c_i v_i = 0`. The resulting 31-QM31 group therefore has a
30-QM31 conditioned kernel. Its exact complete PCS rank is 1,144/1,144.

The q29-plus-two-pad dimension is not just numerology: an independent unit
test constructs the block-triangular Construction-9.7-shaped evaluation map
in which 29 query observations see the inherited randomness and two OOD
observations see that randomness plus two fresh pads. That map has QM31 rank
31; conditioning one dense switch identity leaves rank 30.

The actual complement basis is not contained in a small coefficient prefix.
The exact incremental complement ranks are 36/120 for the first 31 rows,
68/120 for the first 64, 100/120 for the first 96, and 116/120 for the first
112. Row 112 completes it. The selected stride-4 support is structured and
may admit a 28-term lower-dimensional evaluation plus three exceptions, but
this note does not assign it a verifier operation count.

## Shared-power factor family

The terminal factor evaluator has a separate structural reduction which
survives the complete rank gate. Use one shared dense linear form `L`, cache
`L^0..L^26`, and assign:

```text
semantic: 0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25
mask-only: 1,3,5,7,9,11,15,17,19,21
```

The mask-only factors retain their `column mod 4` tower rotations. The
explicit QM31 `G` factor must retain its independent dense degree-26 linear
form. With that one exception the exact ranks are:

```text
masked sumcheck       1080 / 1080 M31
baseline PCS          1024 / 1144 M31
conditioned switch    1144 / 1144 M31
```

Sharing `G` as well fails: the original mask exponent schedule reaches only
1,052, and the unused-odd schedule reaches 1,076. Thus the independent `G`
factor supplies four necessary dimensions. CU savings remain unmeasured
until the schedule is implemented in the production-neutral evaluator and
replayed on SBF.

## Rejected seven-column interpretation

Materializing the earlier coordinate-factored QM31 diagnostic as ordinary
M31 C1 columns does not preserve its 28-rank jump. Exact prefixes zero through
eight give:

```text
columns     0     1     2     3     4     5     6     7     8
SC rank  1040  1044  1048  1052  1056  1060  1064  1068  1072
PCS rank 1024  1024  1024  1024  1024  1024  1024  1024  1024
```

The target is 1,080. The late switch repairs the PCS quotient but cannot
repair the still-public sumcheck deficit. Seven columns are therefore
rejected; this family still needs ten ordinary M31 columns.

## Why this is not yet HVZK

The rank probe adds the old tail-image map but does not yet add the new mask
commitment's own roots, leaves, OOD answers, carried masks, or receipt bytes to
the simulated View. Opening the mask directly would cancel the privacy gain.
A valid protocol must commit before a fresh switch challenge, carry or hide
the mask through the later reductions, and one-time-pad it at the base case.

The missing proof obligations are the exact circle code-switch/opening
identity, arity-four masked-sumcheck simulation, fold/code-switch commutation,
Fiat-Shamir ordering and bad-schedule termination, proximity soundness for the
mask code, and integrated CU measurement. The nearby deterministic batching
algebra is Plonky3 commit `6b6a3b4d40fca2187d368c9dc1fca417c84ae8c3`,
`whir/src/pcs/zk/code_switch.rs`; source similarity is not a transport proof.

The machine-readable result is
`results/stage2/state_only_late_switch_rank_probe.json`.
