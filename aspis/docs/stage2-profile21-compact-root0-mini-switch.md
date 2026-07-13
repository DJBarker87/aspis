# Profile-21 compact root-zero mini-switch

Date: 2026-07-13

Status: **exact rank RED; CU gate cancelled.**  The decisive complete-View
calculation used the raw four-symbol C2 openings and the corrected compact
`[tau,kappa,kappa^2]` unbalanced relation.  This file records the rejected
wire and prevents the same dimension-count argument from being retried.

## Purpose

The compact 61-claim candidate removes 23 unnecessary auxiliary terminal
values, but its exact log-10 rank remains short by one QM31 direction:

```text
compact mask PCS image       444 M31
semantic augmentation        448 M31
missing quotient               4 M31 = 1 QM31
```

The existing dimension-35 switch was sized for the former 17-QM31 deficit.
This candidate sizes a physical source code for the remaining one-QM31
quotient and carries it through root zero, so there is no translated-W1
codeword or seam equation.

## Source code and exact rank target

Work over `K = QM31`, with `q = 16` and source line domain `N = 131072`.
Use the ordinary degree-below-19 source code with the explicit direct-sum
basis

```text
M = span{1, x, x^18}                 dimension 3
R = (x^2 + 1) P_<16                  dimension 16
M (+) R = P_<19.                     dimension 19
```

Evaluation of `R` at every accepted tuple of 16 distinct M31 abscissae is

```text
diag(q_i^2 + 1) * Vandermonde(q_0,...,q_15),
```

and is invertible because M31 is 3 modulo 4.  Therefore the source randomness
block has no schedule-dependent retry.

Commit independent `X,F in K^19` before the source challenge.  After a fresh
nonzero `epsilon`, disclose the 19 logical coefficients

```text
V = F + epsilon X.
```

The complete honest affine View of the source is:

```text
V[19], raw-C2-fiber(X)[q16], raw-C2-fiber(F)[q16], tX.
```

Here `tX = L_tau(X)` is the one complete root-zero relation functional,
including the three terminal-point weights and the copy-inactive functional.
It is not three separately claimed evaluations.  Because X is itself in the
main root-zero word, the ordinary relation binds `tX`; no `muF` field and no
`L(V) = muF + epsilon*tX` dot are needed.

The existing diagnostic helper `raw_root0_row_pcs_tail_sparse` is not usable
unchanged: it initializes the old weights `[1,kappa,kappa^2]`.  The compact
probe and production wire must use one parameterized unbalanced-root helper
whose target and every propagated PCS tail both start from
`[tau,kappa,kappa^2]`, plus the same atomic inactive-mask functional.  Mixing
an `L_tau` target with old-weight tails (or conversely) invalidates the rank
result even when each submatrix has the expected dimensions.  A dense
reference comparison must pin this equality before the d19 result is read.

The decisive expected calculation was over the two 19-QM31 source vectors:

```text
variables                                      38 QM31
rank of V                                      19 QM31
conditional rank of both physical raw fibers  16 QM31
independent tX row                              1 QM31
conditioned kernel                              2 QM31.
```

The physical raw map has rank 16, not the conservative predicted rank 17.
The folded-q map has the same rank and its rows are contained in the raw map.
Thus `V + raw(X,F)` has rank 35 of 38, and adding the complete `tX` row gives
rank 36 of 38.  This leaves *more* hidden source freedom than required, but
neither remaining QM31 direction moves the compact PCS quotient.  Carrying
the complete X word through the real root-zero PCS map adds zero pivots:

```text
compact PCS before X                         444 M31
compact PCS after conditioned full-X carry  444 M31
semantic augmentation                       448 M31
semantic pivots                         [5,4,6,7].
```

All 19 sparse unbalanced tails equal the independent full-codeword reference.
The code-basis fingerprint is `0xf0fae5146210660a`; the empty switch-complement
minor fingerprint is `0xf70765b477a9b454`.  Therefore this is not a raw-view
overconditioning artifact and not a stale `[1,kappa,kappa^2]` target.  The
surviving source kernel lies inside the existing 444-dimensional PCS mask
image, while the missing semantic quotient remains transverse to it.

Dimension 18, with message complement `span{1,x}`, cannot improve this result:
the larger dimension-19 full-X code already leaves a two-QM31 conditioned
kernel and its entire carried image adds no pivot.  A d18 run may be retained
only as an archival control; it cannot establish the missing containment.

## Main word and compact claims

Keep the compact claim partition

```text
S = C0,...,C15
AUX = M0,...,M9,H,G.
```

Let `S_gamma` and `AUX_gamma` be their separately gamma-batched committed
words.  The ordinary root-zero word used by every OOD relation and fold is

```text
W0* = delta * S_gamma + AUX_gamma + epsilon * X.
```

Thus X is folded by the ordinary first fold and all later folds.  W1 is the
normal first-later commitment to `Fold(W0*)`; it is not a translated root and
there is no check of `W1 - Fold(W0) = Enc(V)`.

The compact auxiliary-tail claim remains

```text
A_tail = kappa   * AUX_gamma(succ(z))
       + kappa^2 * AUX_gamma(xor12(z)).
```

After `A_tail`, sample `tau`.  Then disclose the honest complete functional
`tX = L_tau(X)`.  X cannot share the semantic gamma group: `tX` necessarily
follows `tau`, and therefore also follows gamma, so a false X claim could
otherwise cancel an already known semantic gamma aggregate.  The independent
post-`tX` coefficient `epsilon` is mandatory.

For fixed prechallenge discrepancies, the main relation discrepancy has the
shape

```text
delta*tau*Z_S + delta*T_S + tau*Z_AUX + E_A + epsilon*E_X.
```

The existing compact S/AUX separator contributes its sequential degree-two
bound.  A false `tX` is fixed before epsilon and contributes at most one
epsilon root.  A conservative local ledger may charge `3/|K|`; it must not
pretend that `tX`, chosen after tau, was fixed before the complete
`(tau,delta,epsilon)` polynomial.

## Fiat--Shamir order

The frozen causal order is:

1. Commit C1 and the shared C2 leaf containing `(H,G,X,F)`; X and F are fixed
   before every challenge below.
2. Finish the external masked zerocheck, derive `z`, and absorb the 60 compact
   raw claims.
3. Sample `kappa`, check/absorb main pre-gamma g38, and sample `gamma`.
4. Absorb `A_tail`, then sample nonzero `tau`.
5. Absorb `tX = L_tau(X)`.
6. Check and absorb one group/source g38 witness.
7. Sample nonzero `(delta,epsilon)` as one domain-separated two-coordinate
   verifier challenge, with no prover message between the coordinates.
8. Disclose and absorb logical `V[19]`.
9. Run the ordinary root-zero OOD relation and all ordinary folds on `W0*`.
10. After the existing final g38, derive q16 without replacement; authenticate
    the shared raw X/F fibers and check
    `Eval(V,q) = F(q) + epsilon*X(q)` at every query.

One g38 can normalize the union of the group-CA and source-CA events only
because both challenge coordinates follow that work witness with no adaptive
prover message between them.  The ledger must union their unground
probabilities first and apply the common 38-bit normalization once.  If the
wire inserts any message between `delta` and `epsilon`, this reuse is invalid.

## Johnson rows

For the dimension-19 source code,

```text
rho_s       = 19 / 131072
alpha_s     = 1.05 * sqrt(rho_s)
A_s         = floor(alpha_s * 131072) = 1656
ell_s       = 872.1023599989795
source MCA  = 71.4952666285 unground bits
            = 109.4952666285 after the positioned g38
source q16  = 101.0077586247 unground bits
            = 139.0077586247 after final g38.
```

These are the standalone S-two/Johnson source rows.  The final ledger must
also recount the two-level compact main generator, the third X group, the
shared group/source work normalization, and the BCS round factor.  Sampling
`(delta,epsilon)` as one verifier message should not add a prover round, but a
factor-34 sensitivity is required until the transcript compiler confirms the
exact round count.

## CU shape (cancelled)

Relative to the selected dimension-35 translated switch, this candidate
removes:

- 16 disclosed QM31 coefficients (`35 -> 19`);
- the complete translated-W1 relation injection;
- the translated seam query equality;
- the two rejected beta evaluations; and
- any dedicated U tree, root, path, or salt.

It retains:

- the exact measured 1,027-CU shared-C2 leaf-widening delta;
- one 19-coefficient fused M31-point evaluation at q16;
- two authenticated source folds and one affine equality per query;
- one 16-byte `tX` field and 304 bytes of V coefficients; and
- the source/group g38, shared with the compact two-group construction only
  under the order above.

The proposed append-only tag-56 source-only CU probe was cancelled before any
program, xtask, or primitive change.  A cheaper verifier for an algebraically
RED mask does not advance the one-transaction claim.  The old 153,684-CU
transcript bucket remains inapplicable for the reasons above, but no
dimension-19 saving is booked or measured.

## Closed gates

1. Exact physical raw-fiber rank: complete, `38 -> 36`, kernel two QM31.
2. Correct compact unbalanced sparse/full PCS parity: complete for all 19
   natural source rows.
3. Conditioned full-X carry: RED, zero new pivots.
4. Semantic containment: RED, the same one-QM31 quotient remains.
5. Johnson sensitivity: recorded above but not promoted because rank is RED.
6. SBF tag-56 and integrated implementation: intentionally cancelled.
