# State-only hiding: query-schedule rank audit

Date: 2026-07-13

Status: layer-zero structural result and complete-rank theorem boundary. This
is not an FS-HVZK claim.

## Ruling

The ambient scaled-GRS identification does **not** prove the required rank
for the current relation-free semantic mask subspaces or for the complete
degree-27 sumcheck quotient.

There is a useful rate-1/32 structural fact. Every semantic column may use
rows `896..1023`, a complete 128-coordinate affine Boolean subcube. After the
invertible four-slot circle butterfly, those coordinates split into four
aligned 32-dimensional line-polynomial blocks. Consequently every tuple of
29 distinct query fibers gives rank `4*29=116` on this layer-zero mask
slice. This is the deterministic part of the rate-1/32 raw-view rank.

The analogous simple argument does not cover rate 1/16. The largest common
aligned block has dimension 32 per butterfly component, while q36 requires
36 independent evaluations per component. The larger common relation-free
tail `879..1023` has 145 coordinates and passes the structured tests below,
but its extra coefficients are not one consecutive monomial/Vandermonde
space. No all-q36 theorem is claimed for it.

For either rate, the three Boolean-MLE terminal functionals and the 271-QM31
sumcheck observation functionals are not circle-code evaluation rows. No
choice of basis for an already fixed mask subspace changes rank, and the
scaled-GRS theorem does not turn these rows into Cauchy/Vandermonde rows.
The observed 1,080-dimensional quotient therefore remains a sampled
engineering result, not a query-schedule-wide theorem.

## Exact objects

Let `E_Q` be the layer-zero circle-code evaluation map at the four symbols in
each distinct fiber in `Q`. Let

```text
T_z = (MLE_z, MLE_succ(z), MLE_xor12(z))
```

and let `S_z` be the 271-QM31-coordinate independent degree-27 sumcheck wire.
For each semantic C1 column the raw map is

```text
(E_Q, T_z): K_c -> M31^(4q+12),
```

where `K_c` is the coordinate subspace supported on that column's mechanically
derived relation-free cells. The full hiding gate further quotients the
sumcheck map by every raw map, includes the explicit `G`, and includes ten
full-domain M31 mask-only columns. Its maximum is 1,080 M31 coordinates,
because the terminal equation supplies one unavoidable QM31 relation.

The sampled ranks remain:

```text
rate 1/16, q36: 1040,1044,...,1080
rate 1/32, q29: 1040,1044,...,1080
```

for zero through ten extra M31 mask-only columns. Those values do not
universalize over query tuples.

## What the four-slot decomposition proves

In `CircleEncoder`, the last line butterfly mixes positions `(0,2)` and
`(1,3)` in a fiber, and the final circle butterfly mixes `(0,1)` and `(2,3)`.
Every twiddle is nonzero, so this local four-by-four map is invertible. Before
those two butterflies, component `r` depends only on message coordinates
congruent to `r mod 4`.

For the common tail `879..1023`, the four quotient-index sets are

```text
r=0,1,2: 220..255 (36 coordinates)
r=3:     219..255 (37 coordinates).
```

The aligned suffix `224..255` has dimension 32. In the direct line tensor
basis, its three high binary factors are common and nonzero on the canonical
coset; the remaining five tensor factors span all univariate polynomials of
degree at most 31 by a triangular change of basis. Evaluation at any 29
distinct lower-domain points is therefore a nonzero diagonal scaling of a
29-by-32 Vandermonde matrix. This proves rank 29 in each of the four
components and rank 116 for q29.

Rows `896..1023` are exactly the corresponding four aligned blocks and are
relation-free in every semantic column. They are also a complete affine
7-bit Boolean subcube (`111xxxxxxx`), which is useful for a future symbolic
terminal analysis.

At q36, dimension 32 is insufficient. Adding tensor indices `220..223` (and
`219`) produces the measured 36/37-dimensional tail, but not a consecutive
monomial space. A diagnostic checks the ratio required by a scaled monomial
Vandermonde representation between three adjacent tail columns. It holds at
`0/16384` rate-1/16 domain points. Thus citing the ambient GRS code as if this
shortened direct-tensor coefficient slice were itself GRS is invalid.

The ambient theorem is still useful for the complete circle code and its
Johnson list bound. It does not say that every coordinate-supported subcode,
or every chosen generator submatrix, is MDS.

## Machine-checkable regressions

`crates/aspis-prover/tests/state_only_query_schedule_rank.rs` independently
builds the exact circle encoder and checks the common 145-coordinate tail on
structured schedules:

```text
rate 1/16 q36: consecutive starts, strides 2,4,16,64, and odd stride 573
rate 1/32 q29: consecutive starts, strides 2,4,16,64,128,256, and odd stride 573
```

Every tested schedule has the maximum query-only rank, respectively 144 and
116. These tests include subgroup/coset-shaped schedules which random tests
are unlikely to hit. They are regression evidence, not exhaustive proof.

Exhaustive enumeration is infeasible:

```text
C(4096,36) = approximately 2^293.683 distinct rate-1/16 tuples
C(8192,29) = approximately 2^274.126 distinct rate-1/32 tuples.
```

Circle rotation removes at most one domain-size factor and does not make
either search remotely finite.

## Why the complete matrix is not Cauchy/Vandermonde

The query rows are circle-polynomial evaluations. The terminal row

```text
row -> product_i (z_i if row_i=1 else 1-z_i)
```

is a Boolean-MLE evaluation. As `z` varies, these projective functionals form
the ten-dimensional Segre family `(P^1)^10`. Univariate Reed--Solomon
evaluation functionals form a one-dimensional rational normal curve. A fixed
invertible change of message basis preserves dimension and cannot identify
the whole MLE family with the univariate evaluation family.

The successor point is a higher-degree polynomial transformation of `z`, and
the degree-27 sumcheck rows add further coefficient functionals. Therefore a
common scaled-GRS/Cauchy determinant does not exist merely by rebasing mask
coins. A basis change right-multiplies the matrix by an invertible matrix and
cannot repair a deficient schedule in any event.

This does not prove that the current complete determinant is zero for some
distinct query tuple. It proves that the proposed ambient-GRS shortcut does
not establish it.

Also, full raw rank cannot hold for every continuous challenge. If `z` is a
Boolean M31 point, all three MLE values lie in M31, so their four serialized
coordinates cannot contribute twelve independent M31 rows. Such points may
be placed in a Schwartz--Zippel bad set; they cannot be excluded by a claim
of deterministic rank.

## Exact bad-rank ledger boundary

Let `beta_Q` be the probability that the sampled distinct query tuple makes
every candidate complete minor the zero polynomial in the forty M31
coordinates of the ten QM31 sumcheck challenges. For a query tuple outside
that set, the current conservative degree bound for one proved-nonzero minor
is 24,000. Therefore the only justified symbolic form is

```text
beta_gate <= beta_Q + (1-beta_Q) * 24000/(2^31-1).
```

Numerically,

```text
24000/(2^31-1) = 1.1175870900589913e-5 = 2^-16.449253...
```

but `beta_Q` currently has no nontrivial proved bound. Consequently the
smallest unconditional ledger entry today is `beta_gate <= 1` (zero bits),
not `2^-16.45`.

This zero-bit bound is an availability/completeness statement, not a privacy
error for an emitted proof and not a verifier-soundness error. A canonical
exact rank/containment gate makes every proof it emits rank-good by
construction, even if the only currently proved bound is `beta_Q <= 1`.
If in fact every schedule were bad, the honest prover would emit nothing;
that is failure of completeness/availability, not a distinguishing transcript
or a larger verifier acceptance set. Conditional privacy on emission still
requires the complete-view, FS-conditioning, and Merkle hypotheses in the
rank-rejection audit.

If a nonzero minor is later proved for every distinct query tuple, exact
honest-prover rank rejection turns `2^-16.45` into an availability term. The
conditional expected attempts are at most `1.000011176`; seven fresh capped
attempts have conditional no-proof probability below `2^-115`. This does not
remove the separate EPRO/Fiat--Shamir conditioning, private-Merkle simulation,
complete-view containment, and retry-state obligations in
`stage2-state-only-fs-hvzk-rank-rejection-audit.md`.

## Deterministic redesign boundary

There is no established no-opening-change choice of the current
relation-free cells and public factors which makes the **complete** view
Cauchy/Vandermonde for every query tuple.

Two honest redesigns remain:

1. **Exact post-schedule rejection.** Generate the canonical complete affine
   view matrix, emit only if containment/rank passes, burn the nonce on every
   failed attempt, and use fresh random-oracle prefixes. This makes emitted
   proofs rank-good by construction but still needs a termination theorem;
   it is not an all-schedule algebraic rank proof.
2. **Triangular code-switch masking.** Use round-local affine sumcheck pads
   whose wire map is triangular and surjective, then bind their terminal with
   the upstream-style mask code-switch/proximity check. Keep raw-opening pads
   in a mask code whose puncturing matrix is proved MDS. This separates the
   circle-evaluation and Boolean-MLE functionals instead of pretending both
   are one GRS matrix. It necessarily changes the binding/opening protocol
   (though query positions may still be shared and values batchable), so its
   CU and proof-byte cost must be measured.

For rate 1/32, the aligned 128-cell semantic slice should be retained in
either redesign: it removes the discrete-query uncertainty from the
layer-zero semantic openings at no column cost. It does not by itself bind or
hide `T_z`, `S_z`, `h1`, later folds, roots, or authentication paths.
