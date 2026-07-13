# Profile-21 lean affine-multiplier mask

Date: 2026-07-13

Status: **protocol shape is soundness-compatible; exact complete-View rank is
pending.**  This note does not authorize CU credit or a hiding claim.  It
records the conditions under which one precommitted `X` lane can replace the
`X/F/U` source switch.

## Construction

Let `K = QM31`.  Fix a profile constant

```text
zeta in K \ M31,                 p(t) = t - zeta.
```

The four canonical M31 limbs of `zeta` and the degree-one multiplier are part
of the frozen layout registry.  They are not proof fields and are not derived
from `gamma`.

Before `gamma`, commit one uniform degree-below-`d` `K` polynomial `X` in one
widened C2 lane.  The source message occupies the slot-zero natural-line rows
`4*i`, `0 <= i < d`.  The retired source switch required `d=19`; the lean wire
has no source-code handoff, so `d` is an honest-mask parameter.  For affine
`p`, any `d <= 255` fits the existing root-zero message, and `d=255` is the
maximal free-entropy candidate.  After the compact auxiliary-tail value and its
separator `tau` are fixed, disclose and absorb the exact scalar

```text
tX = L_tau(pX),
```

where `L_tau` is the literal compact root-zero functional: the three point
weights are `[tau,kappa,kappa^2]`, and the atomic copy-inactive functional is
included.  Check and absorb the post-target group work witness, then sample
fresh nonzero `(delta,epsilon)` with no prover message between them.  The main
root-zero word is

```text
W0* = delta*S_gamma + AUX_gamma + epsilon*pX.
```

Every later commitment, OOD relation and fold is the ordinary continuation
from this one word.  There is no translated root and no source polynomial
`F`, disclosed affine combination `U`, source MCA event, or source-query
event.

The honest prover must not try to precommit `X` in `ker L_tau(pX)`: `tau` and
therefore `L_tau` are not known when the X root is fixed.  It samples `X`
uniformly first and discloses the actual target later.

## Frozen Fiat--Shamir order

The causal order is:

1. bind the profile/layout registry, statement and hiding precommit;
2. commit C1 and the one shared C2 root containing `(H,G,X)`;
3. finish the external masked zerocheck and derive `z`;
4. absorb the 60 compact raw claims;
5. sample `kappa`, check and absorb the main pre-gamma g38 witness, and sample
   `gamma`;
6. absorb the compact auxiliary-tail claim `A`, then sample nonzero `tau`;
7. absorb `tX = L_tau(pX)`;
8. check and absorb the outer-group g38 witness;
9. sample nonzero `(delta,epsilon)` consecutively, with no prover message
   between the coordinates;
10. start the ordinary OOD relation and commit/fold `W0*` through the existing
    later roots and final polynomial;
11. check and absorb the final g38 witness, then sample q16 without replacement;
12. authenticate the ordinary C1/C2 fibers and every later opening, derive the
    pX contribution from the authenticated X fiber, and check the standard
    fold path.

Moving the X root after `gamma`, moving `tX` after `epsilon`, inserting a prover
message between `delta` and `epsilon`, or deriving q before a later root/final
polynomial invalidates the corresponding reduction.  A fixed `zeta` adds no
Fiat--Shamir challenge.  A `zeta` derived from `gamma` is a different
gamma-dependent polynomial generator and is not covered by this note.

## Exact local identity

For root-one query index `q`, let

```text
x_q = line_domain_x_for_circle(domain_log, 1, q) in M31,
h_q = x_q - zeta in K.
```

The four root-zero symbols of a fiber have the same line quotient `x_q`.
Therefore, for every four-symbol vector, including an adversarial vector that
is not a codeword,

```text
Fold_alpha0(h_q * X_q[0..4]) = h_q * Fold_alpha0(X_q[0..4]).
```

The verifier authenticates the raw `X` fiber from the shared C2 root, reuses
its normalized fold, and checks the ordinary first-later equality with
`epsilon*h_q*Fold(X_q)` included.  It never accepts a separately supplied
`pX(q)` value.  Thus there is no hidden pX commitment or extra pX opening.

The implementation guard must independently construct `pX` from ordinary
coefficients and check, for every selected query and all four slots,

```text
Encode(pX)[4*q+s] = h_q * Encode(X)[4*q+s],   s=0,1,2,3,
```

followed by the normalized-fold equality.  The guard must exercise all four
QM31 tower basis coordinates: an M31-only coefficient path erases the tower
mixing that this candidate is intended to test.

## Code membership and degree

For honest `deg X < d`, `deg pX < d+1`.  At maximal `d=255`, the product uses
natural line coefficients through degree 255 and root-zero row
`4*255 = 1020`, still inside the 1,024-coordinate main circle FFT space.
`d=256` is not allowed for a degree-one multiplier because its product could
require row 1024.  Extension-field coefficients do not make the fold matrix-valued: the
PCS is already a scalar `K`-linear code, and `pX` is one ordinary `K`-valued
codeword.  All later folds are unchanged.

For every M31 domain point `x`, `x-zeta != 0`.  Hence coordinatewise
multiplication

```text
T_zeta : w(x) -> (x-zeta)w(x)
```

is a Hamming isometry on the complete source/main evaluation domain.  In
particular, `X` and `pX` have identical agreement sets.  No root exception,
schedule retry, or extra local collision term is needed for fixed
`zeta in K \ M31`.

## Proximity and target binding

The X root fixes the virtual word `pX` before every batching challenge.  The
proximity reduction has two levels:

1. the existing `gamma` generator batches the fixed semantic and auxiliary
   columns; and
2. the outer generator

   ```text
   G(delta,epsilon) = (delta, 1, epsilon)
   ```

   batches `(S_gamma,AUX_gamma,pX)`.

`G` is a multivariate polynomial generator with linearly independent
coordinate polynomials and individual degrees `(1,1)`.  The tensor-product
and full-rank linear-transformation lemmas for MCA reduce it to two copies of
the degree-one powers generator.  Applied to the exact-circle Johnson result,
the outer error is therefore bounded by the sum of the two degree-one MCA
errors.  The post-target g38 witness can ground that union because `delta`
and `epsilon` are sampled consecutively with no intervening prover message.

A Schwartz--Zippel root bound alone is not a code-membership proof.  The main
MCA event is what rules out a far malicious `pX` canceling the other two
groups.  Conversely, no standalone source MCA is necessary: `X` is an
auxiliary mask and is not consumed by the statement.  Even if a malicious
prover chooses an `X` outside the honest degree-below-19 source space, the
outer MCA forces its derived `pX` into the main code, except for the charged
event.

The precise theorem chain is pinned as follows.

- Carmon--Goldberg--Habock--Lerer--Lesokhin--Papini--Samocha, *S-two
  Whitepaper*, ePrint 2026/532, PDF dated 2026-03-24 and SHA-256
  `e3b0132ec598ca16835c1de3c85d0c8b07c41b5f063f1d88b5a9628c22252c3f`:
  Theorem 31 and Corollary 1 give correlated agreement under linear
  constraints for the exact circle subspace; Lemma 3 proves the cross-domain
  powers-batching reduction and Theorem 19 item 1 records its Johnson error.
  Lemma 4 and Theorem 19 item 2 are the unchanged ordinary fold reductions.
- Bordage--Chiesa--Guan--Manzur, *All Polynomial Generators Preserve Distance
  with Mutual Correlated Agreement*, revision dated 2026-05-19 and PDF
  SHA-256
  `23519c2d5d6541ee53e635b10c22d5f5964301b79a853d9394da267062e520a6`:
  Definition 3.19 covers the multivariate generator above; Lemma 4.4 preserves
  MCA under tensor products and Lemma 4.1 preserves it under a full-column-rank
  linear image.  Thus select `(delta,1,epsilon)` from
  `(1,delta) tensor (1,epsilon)` and sum the two exact-circle degree-one MCA
  errors.  Theorem 8.2 states the general polynomial-generator result, while
  Definition 9.1, Theorem 9.2 and Lemma 9.3 give the ambient RS Johnson
  specialization.

The last ambient-RS theorem is not silently used as a subcode-inheritance
claim.  The exact circle-subspace base case comes from S-two; only the
code-agnostic tensor/linear-image transformations are imported from BCGM.

For claim binding, all semantic/auxiliary discrepancies and

```text
eX = tX - L_tau(pX)
```

are fixed before `(delta,epsilon)`.  A nonzero `eX` contributes
`epsilon*eX` to the exact main relation discrepancy and has at most one
epsilon root.  With exact-uniform nonzero challenges the conditional bound is
`1/(|K|-1)`.  A conservative full compact local accounting retains the
existing two-root `tau/delta` separator bound and adds this one-root target
bound, namely `3/|K|` after negligible denominator normalization.  This
argument requires the real `L_tau(pX)`, including the
inactive term; using `L_tau(X)`, stale `[1,kappa,kappa^2]` weights, or sampling
`epsilon` before `tX` invalidates it.

## Conservative Johnson ledger sensitivity

This is a numeric sensitivity, not an integrated soundness claim.  It uses
`K=QM31`, rate `rho=1/512`, `N=131072` query fibers, q16, agreement
`1.05*sqrt(rho)`, the selected S-two list parameter
`ell_GS=237.58787847867995`, g38 before `gamma`, g38 after `tX`, and final g38
before q.  The existing width-28 unground batching anchor is
`70.36848753424952` bits.  Scaling its `(M-1)` factor gives:

| Johnson event | unground bits | positioned bits |
| --- | ---: | ---: |
| inner semantic powers, width 16 | 71.2164844408 | 109.2164844408 |
| inner auxiliary powers, width 12 | 71.6639434178 | 109.6639434178 |
| union of the two inner events | - | 108.4229353183 |
| one outer degree-one MCA coordinate | 75.1233750364 | 113.1233750364 |
| outer `G(delta,epsilon)` (two-coordinate union) | 74.1233750364 | 112.1233750364 |
| four ordinary folds, union | - | 112.0797907885 |
| main q16 miss | - | 108.9018865972 |

For the auxiliary group written with exponents `16..27`, condition on
`gamma != 0` and divide out `gamma^16`; the rejected-zero event is already
subsumed by the local gamma row.  Resetting that group to exponents `0..11`
removes this presentation issue but is a wire change and must be ranked
separately.

Keeping the selected atomic local rows, replacing the width-28 main batch by
the inner union, adding the outer union, deleting all source-MCA/source-q
rows, and conservatively charging the compact/target local term as `3/|K|`
gives

```text
round-event union                           107.3916499447 bits
after conservative BCS factor 34           102.3041871034 bits
after factor-40 sensitivity                 102.0697218498 bits.
```

The event list used in that union is: inner gamma MCA, outer arity-three MCA,
four folds, main q16, ordinary two-sample OOD/list binding, relation/OOD
mixers `24/|K|`, gamma/point claims `29/|K|`, copy-inactive `27/|K|`, atomic
tuple compression `183*17/|K|`, atomic copy/range poles
`4*(183+1024)/|K|`, theta `24/|K|`, ten degree-27 zerocheck rounds
`270/|K|`, compact-plus-target `3/|K|`, and the pinned Poseidon2/SHA
assumptions.  It deliberately grants no standalone source-query credit.

The transcript compiler must still confirm the exact BCS factor.  Factor 34
is retained because it is the conservative compact-profile value; removing
the disclosed source vector may reduce a prover-message boundary, but no bit
credit is taken here.

## Hiding dimension and remaining proof obligation

For any `d >= 16`, the authenticated raw four-symbol q16 view has rank at most
16 QM31 and the exact target contributes at most one further QM31 row.  An
honest uniform d255 `X` therefore retains at least 238 QM31 conditional
directions on every distinct-query schedule, without changing a proof field or
verifier operation.  The decisive gate is whether their complete `pX` PCS
carries span the one-QM31 compact semantic quotient.  The rank probe
must include the literal raw view, full unbalanced p0/later/OOD/relation/final
tail, exact tower mixing, and an independent dense reference.

Passing that gate would establish only the fixed-schedule affine containment
used by the current rank program.  It would not by itself prove
challenge-universal rank or simulate witness-dependent Merkle roots, paths,
retry behavior, proof-account bytes or logs.

Before any complete HVZK claim, the same frozen wire still needs:

1. a challenge-universal containment minor, or a witness-independent
   rank-retry law whose failures and retry count are simulated;
2. an EPRO/private-Merkle simulator for the `(H,G,X)` root, q paths, salts,
   failed roots and every oracle query made by the adversary;
3. simulation of proof-account bytes, logs, aborts and any mutation/receipt
   data visible outside the verifier;
4. same-statement/two-witness distinguishers on the lean proof surface; and
5. one integrated acceptance path with the corruption, padding,
   cross-residual, challenge-order and local-pX identity teeth green.

## Wire and CU delta if rank is green

Relative to the d19 `X/F/U` mini-switch, this construction removes:

- the F C2 lane and its four raw symbols per query;
- the 19-QM31 disclosed affine vector;
- its source polynomial evaluations and affine q equalities;
- the source MCA and source-q ledger rows; and
- every source-only transcript field other than `tX`.

It retains one shared C2 X lane and one 16-byte target.  It adds no root,
Merkle path, proof opening, final coefficient or challenge round relative to
the compact three-group design.  Raising the honest X dimension from 19 to
255 changes only prover-side sampling/encoding: the committed word, leaf
width, target, query surface and verifier CU are identical.

The query hot path should add the X contribution after the normalized fold,
not multiply four raw symbols separately.  With `a = epsilon` (or the exact
frozen X-group scale), precompute `a*zeta` once and use

```text
c_q = a*x_q - a*zeta,
X_contribution_q = c_q * Fold(X_q).
```

This costs one `K x M31` scalar product plus one generic K multiplication per
query and one proof-global fixed multiplication.  Compared with a plain
`a*X` lane, the incremental multiplication count is only `4*q + 9` M31
products under the current tower kernels (`73` at q16), before instruction
level measurement.  No CU saving is booked until the exact rank gate is green
and an integrated SBF path with all teeth is measured.
