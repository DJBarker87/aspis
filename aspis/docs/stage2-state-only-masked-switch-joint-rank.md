# State-only masked single-switch joint-rank gate

Status: **complete field-View rank green; profile-21 implementation gate.** No
production acceptance path is enabled. The selected construction uses one
ordinary pre-alpha line-codeword X, not the rejected coefficient-selective
row-one/two-channel construction. Circle code-switch soundness, ROM/HVZK and
integrated CU remain open.

## Decisive rate-1/512 result

The exact profile-20 transcript has a log-10 message, log-19 circle domain,
q16 and the FullShared terminal-mask factor schedule. Its baseline complete
View is:

```text
masked zerocheck       1080 / 1080 M31
baseline PCS            712 /  780 M31
deficit                  68 M31 = 17 QM31
valid-witness containment       green
```

The selected single-switch map uses one genuine pre-alpha slot-zero source
coordinate at combined-PCS coefficient row four and 18 other source
coordinates. They are embedded in the ordinary-polynomial complement
`span{x,1,x^18,...,x^34}`; its 16 carried encoding-randomness coordinates are
`(x^2+1)P_<16`. The generated ordinary-to-natural transform is shared by the
prover, rank gate and verifier and is pinned by fingerprint
`0xceb35dd3ee50e051`. An independent fresh 35-QM31 pad supplies F. Exact
elimination gives:

```text
variables                         70 QM31
public-observation rank           52 QM31
conditioned kernel                18 QM31
q randomness block               16 / 16
conditional q co-opening block   16
OTP U block                       35 / 35
disclosed logical U block         35 / 35
complete PCS View                780 / 780 M31
shared-C2 raw View                52 / 70 QM31
shared-C2 raw randomness              16 / 16
```

The switch adds 64 missing M31 pivots in later query openings and four in the
relation-coefficient block. It adds none in the OOD or final blocks. Thus the
one available QM31 dimension beyond the 17-dimensional deficit is real, not a
serialized-coordinate counting artifact.

The earlier q29/rate-1/32 construction also passes the same joint gate:
1024/1144 becomes 1144/1144, with 122 variables, observation rank 91,
conditioned kernel 31, q-randomness rank 29, q-co-opening rank 29 and OTP rank
61. The q16 result is the tighter and cheaper candidate.

## Exact linear View

Let `q` be 16 or 29, `m=q+3`, `r=q`, and `d=m+r=2q+3`. Over `K=QM31`, write

```text
X = (X_m, R) in K^m x K^r
F = (F_m, F_r) in K^m x K^r
U = F + delta X in K^d.
```

`X_m[0]=e` is the genuine slot-zero row-four direction in the old View. Its
logical code image is ordinary monomial `x`; the constant is second, and the
remaining message image is `x^(q+2),...,x^(2q+2)`. Randomness uses
`(x^2+1)x^j`, `j=0,...,q-1`. A generated triangular change of basis converts
these ordinary polynomials to the natural line tensor coefficients. The rank
gate then checks every generated column against the real circle encoder and
normalized first fold at the actual production root-one positions. The
rejected row-one candidate needed alpha-selective scaling of coefficient zero
and is retired.

The gate eliminates the following observations jointly, in this order:

```text
U[d], tX, muF, AX[q], AF[q],
tX  = <X_m,c>,
muF = <F_m,c>.
```

It does not pre-delete redundant rows. Gaussian elimination discovers

```text
AF = A(U) - delta AX,
<U_m,c> = muF + delta tX.
```

The `q x q` randomness block is universally invertible, not merely invertible
on the measured schedules. At distinct M31 abscissae `a_i` it is

```text
diag(a_i^2+1) * Vandermonde(a_0,...,a_(q-1)).
```

Since `2^31-1 = 3 mod 4`, `a_i^2+1` never vanishes. The query sampler is
without replacement and the production root-one line abscissae are distinct.
Consequently this block needs neither a schedule-dependent minor nor an
honest-prover rank retry.

For every `dX_m in ker(c)`, the unique

```text
dR = -A_R^-1 A_m dX_m,
dF = -delta (dX_m,dR)
```

fixes the entire serialized switch View. Hence the projection onto the old
public tail is exactly `ker(c)`, of dimension `m-1=q+2`.

An earlier diagnostic serialized two evaluations `U(beta_s)` after the W1
root. Those values were functions of already disclosed U and supplied no
authentication of `Fold(W0)(beta_s)`. Treating bare base-fold scalars as a
cross-equation would let the prover satisfy the equation by definition. The
production profile therefore has **no beta extension bytes or beta cross
equations**. This rejected diagnostic history is not credited in either the
rank or soundness ledger.

## Required Fiat--Shamir order

Any implementable version must use the following causal order:

1. Commit `(H1,G,X,F)` in the widened shared C2 root. X and F are source-code
   lanes only and are excluded from the main gamma combination. The shared
   root precedes all challenges used below.
2. Run the unchanged base-codeword round-zero OOD relation, sumcheck, fold
   work and fold challenge. `alpha0` fixes the source covector `c` at logical
   coordinates `[1,0,2,...,18]`.
3. Absorb the real targets `tX=<X_m,c>` and `muF=<F_m,c>`.
4. Check and absorb a dedicated powers-generator work witness for the
   `(X,F)` source-code batching round. This nonce is bound to the X/F root and
   both target scalars and precedes `delta`; the existing final work witness
   occurs after `delta` and cannot be credited backward.
5. Sample a fresh nonzero `delta`.
6. Reveal and absorb `U=F+delta X`.
7. Convert logical U through the pinned basis only for the relation/codeword
   splice, inject the full `phi(U)` target immediately after `alpha0`, and
   commit W1 with `W1=Fold_alpha0(W0)+Enc(phi(U))`.
8. Continue the ordinary later-layer OOD relations and folds from W1. No
   unauthenticated beta/base-fold scalar is serialized.
9. Finish all later roots and check/absorb the positioned final g38 witness,
   then derive q16 without replacement.
10. In the same main q loop, co-open X and F from the shared C2 record and
    check both `F(q)+delta X(q)=Enc(phi(U))(q)` and
    `W1(q)-Fold_alpha0(W0)(q)=Enc(phi(U))(q)`.

Sampling delta before `tX` and `muF`, deriving q before the shared X/F
commitment, moving U after W1, or placing the source-code work nonce after
delta invalidates this map.

## Implementability and soundness boundary

Row four here is **not trace row four**, not a semantic relation-free C1 cell,
not a mask-only C1 cell and not G. It is coefficient row four of a new
post-zerocheck auxiliary PCS mask oracle. Therefore it cannot change the
external zerocheck or its initial claim. Its physical lane is in the shared
C2 leaf, but it is excluded from the main gamma codeword. The same
authenticated source is bound by the disclosed target identity and by the
source and translated equations in the final q loop. Teeth independently
alter each use.

Using the same host scalar in three builders is not sufficient. The reduction
must bind `tX` through the post-alpha source covector, inject all of `phi(U)`
into the first later relation target, and use authenticated X/F values in the
translated q transition. Until that verifier and reduction exist, 780/780 is
a rank result, not production HVZK.

If that binding is supplied, the remaining soundness outline is:

- false target identities leave a nonzero degree-one polynomial in the
  post-claim delta;
- translation by the public codeword `Enc(U)` is a Hamming isometry;
- root-one disagreement is fixed before all later OOD challenges and is
  tested by the translated ordinary relation plus the direct q branch;
- the X/F branch is a length-131072, dimension-35 line code. Its own
  polynomial-generator MCA/Johnson term and the q16 without-replacement miss
  term are charged separately. For a bad set of size B the exact miss is
  `prod_{i=0}^{15}(B-i)/(131072-i)`, at most `(B/131072)^16`;
- the S-two Theorem-19 powers-batching term at `d=35`, `n=131072` has
  `ell` approximately 642.555 and supplies only approximately 72.8173 bits
  before grinding. A dedicated conservative `g=38` source-round work witness
  therefore precedes delta. The final `g=38` witness is after delta
  and supplies no backward credit. Separately, the exact q16 miss term for
  `A=2248`, together with its correctly positioned final `g=38`, is
  approximately 129.925 bits;
- substituting this switch term for the ledger's generic 110-bit hiding
  reserve previously gave only approximately 100.0955 bits at `g=34`,
  100.3246 at `g=35`, and 100.4545 at `g=36`, before the atomic registry and
  local-switch terms were re-unioned. Profile 21 fixes g38 at the main batch,
  source and final positions and requires a freshly regenerated complete
  atomic ledger; the earlier g36 aggregates are stale;
- U is chosen after delta, so root timing alone does not prove it low degree.
  Its 35 disclosed coefficients, full relation-target injection, translated
  ordinary-FRI continuation, and both direct q equations reduce the splice to
  the two precommitted source codewords. No beta equation is credited;
- no post-challenge degrees are chosen: X and F coefficients precede all PCS
  challenges, U is their forced affine combination, and W1 is the forced
  translated continuation; and
- roots, paths, failed retries and receipt copies must be covered by the ROM
  HVZK simulator, not treated as field rows or hidden by Merkle salting.

## Bytes

The frozen beta-free profile-21 prefix extension is exactly:

```text
tX                  16
muF                 16
source g38 nonce     8
logical U[35]      560
total              600 bytes
```

W1/W2/W3 roots remain in their existing base-prefix slots. Private openings
then widen the shared C2 opened value from 128 to 256 bytes and serialize one
32-byte salt per opened leaf for C1, C2, W1, W2 and W3. Their exact frontier
and wire delta is taken only from the integrated transcript-derived q16
measurement; the retired standalone-X/F-tree estimate is not additive.

## Executable guards

- `CircleEncoder::encode_c1_basis_value` is checked against full circle FFTs.
- The log-19 gate computes only selected entries but uses the production
  normalized circle/line arity-four functions recursively.
- `check_state_only_sparse_row_map_reference` compares sparse and full public
  tails on the exact q29 transcript and adversarial row classes.
- The ignored full-proof gate checks q co-opening rank, OTP rank and direct
  ambient containment. Parser/transcript teeth prove there are no production
  beta bytes and bind targets, U and W1 in causal order.

Machine-readable values are in
`results/stage2/state_only_masked_switch_joint_rank.json`.
