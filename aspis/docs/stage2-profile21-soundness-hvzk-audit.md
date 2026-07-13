# Profile-21 masked-switch / atomic soundness and HVZK audit

Date: 2026-07-13

Status: **numeric Johnson/direct-q plus pre-delta-target reduction green at
102.243960 bits; production combo check and complete system claim not yet
quotable.** The selected verifier pays for
literal `Enc(U)(q)` at all 16 queries and freezes g38 at the main, source and
final normalization points.  This closes the earlier disjoint-agreement-set
fork. The target-binding reduction and relation primitive are executable, but
the check is not yet inside the profile-21 acceptance wire. The exact profile-21 acceptance wire, all-schedule affine containment,
EPRO/private-Merkle simulator, mined work and live profile-21 mutation are not
yet all present on one production path.

## Result

The selected switch computes the disclosed degree-below-35 polynomial `U`
at every sampled query and checks

```text
Enc(U)(q) = F(q) + delta X(q)
          = W1(q) - Fold_alpha0(W0)(q).
```

`X` and `F` are authenticated from the pre-delta shared root, `U` is fixed
before the translated root and every later OOD sample, and the q positions are sampled
only after all roots, the final polynomial and final g38 work witness are
fixed.  Consequently the standalone dimension-35 source MCA event and its
q16 miss event apply to the same source word.  No common-set identification
between independently decoded source and main lists is assumed.

The q equation alone does not bind the two source targets. Tag 45 computes
`tX` and `muF` with a diagnostic power vector `(1,eta,...)`; the integrated
round-zero relation instead needs

```text
c_j = first_later_weights.weight_at([1,0,2,...,18]_j),
tX = <X_m,c>,  muF = <F_m,c>.
```

That covector depends on `z`, kappa, both round-zero OOD mixers and alpha0.
The exact repair needs no second PCS. Let `L` be this covector extended by
zero on the 16 source-randomness coordinates, and let `phi` be the frozen
logical-to-natural basis map. After U is disclosed, the verifier checks

```text
L(U_message) = muF + delta*tX.                 (target-combo)
```

To see why this is binding, put
`D=Enc(phi(U))-(F+delta X)`. If `D` is nonzero, the literal q test is exactly the
charged source MCA/q event. If `D=0`, define the pre-delta errors
`eF=muF-L(F)` and `eX=tX-L(X)`. The target-combo equation becomes
`eF+delta*eX=0`. Both errors were fixed before uniform nonzero delta, so any
nonzero pair has at most one delta root. This is the existing
`1/(|QM31|-1)` degree-one event. No free cancellation scalar remains.

Profile 21 serializes U directly in the frozen logical coordinates, so
production computes `L(U_message)` as one 19-term dot and applies `phi` only
for full relation injection and source-code evaluation. The generated inverse
basis remains a differential guard and is not on the production target path.
The diagnostic eta-power dot is not a substitute.

The previously proposed no-`Enc(U)(q)` variant is rejected.  It could only be
sound through one common-set, attached-function reduction of the following
shape:

```text
X,F fixed by root_XF
c <- H(...,root_XF); tX,muF fixed
source g36 checked; delta <- H(...)
U and translated W1 root fixed
beta_0,beta_1 <- H(...,U,root_W1)
later roots/final polynomial/final g36 fixed
q16 <- H(...)

W1(q) - Fold(W0)(q) = F(q) + delta X(q)
U(beta_s) = p_W1(beta_s) - p_Fold(W0)(beta_s), s=0,1.
```

Here `X` and `F` must be attached functions in the **same** S-two reduction
as `W0,W1,...`, and the q transition must authenticate their values from the
pre-delta `root_XF`.  S-two Theorem 31 (the RS linear-subspace CAT used by
Theorem 19/Lemma 3) then supplies set-specific correlated agreement, while
Lemma 4 carries the common agreement set through the fold.  Polynomial
uniqueness on that common set identifies

```text
p_F + delta p_X = U.
```

The two post-root beta equations select the same ordinary-FRI polynomial pair
and bind its difference to the already disclosed `U`.  They do **not**, by
themselves, identify an independently decoded source-list element with `U`.

Without that attached-function theorem, deleting the literal source check
allows a received word to agree with two distinct low-degree polynomials on
disjoint Johnson agreement sets.  Profile 21 therefore retains the literal
check; neither the no-direct variant nor the measured batch-evaluation
sumcheck is an accepted alternative.

## Correct Johnson parameterization

Let `Q=(2^31-1)^4`, `N=131072`, and let the ordinary profile-20 agreement be

```text
alpha_main = 1.05/sqrt(512) = 0.04640388251536719,
A_main = floor(alpha_main*N) = 6082.
```

For the source code, `k=35` and `rho_s=35/N`.  The repository's standalone
source row chooses its own Johnson agreement
`alpha_s=1.05*sqrt(rho_s)`, giving `A_s=2248`, `ell=642.5549003782`, and,
with the frozen source g38 and final g38 checks,

```text
source MCA: 72.8172998620 + pre-delta g38 = 110.8172998620 bits
source q16: -log2(C(2248,16)/C(N,16)) + final g38
          = 131.9250478007 bits.
```

Those rows are applicable because the selected verifier checks the disclosed
`U` against the authenticated source evaluations at q16.  They are not a
handoff theorem for the rejected no-`Enc(U)(q)` construction: that
construction needs a common agreement set with the wider ordinary code.
Under such an attached-function mapping, use `alpha_main` in Theorem 31. Then `m=3`,
`ell=214.1849667927`, and the source MCA row is

```text
80.7421085624 + pre-delta g36 = 116.7421085624 bits.
```

The one ordinary common q16 round is then the existing
`106.9018865972`-bit row.  No second, independent source-query credit is
needed.  Conversely, retaining the `108.8173/129.9250` pair requires a
separate source relation whose query checks `Enc(U)` (or an equivalent
authenticated source-code value).

## Selected all-round numeric ledger

With that reduction, the following conservative ledger retains both source rows justified by the
literal q binding, replaces the generic hiding reserve, sets the atomic copy
count to `m=183`, uses the exact pole numerator
`4*(183+1024)=4828`, and uses two new interactive rounds (`c` and `delta`),
so the former BCS factor 31 becomes 33.  Main pre-gamma, source pre-delta and
final pre-q work are all frozen at g38.

| event | bits |
| --- | ---: |
| main width-28 powers batching, pre-gamma g38 | 108.3684875342 |
| source `d=35,N=131072` MCA, pre-delta g38 | 110.8172998620 |
| four normalized fold rows, union | 112.0797907885 |
| main q16 miss, final g38 | 108.9018865972 |
| standalone source q16 miss, final g38 | 131.9250478007 |
| ordinary four-round OOD/list union | 213.1000183949 |
| relation sumchecks/OOD mixers `24/Q` | 119.4150374966 |
| gamma plus three-point batching `29/Q` | 119.1420190022 |
| copy-inactive gamma claim `27/Q` | 119.2451124951 |
| atomic tuple compression `183*17/Q` | 112.3968373178 |
| atomic copy/range poles `4*(183+1024)/Q` | 111.7627900366 |
| atomic 25-lane theta collision `24/Q` | 119.4150374966 |
| ten degree-27 zerocheck rounds `270/Q` | 115.9231844003 |
| post-claim delta identity `1/Q` | 123.9999999973 |
| Poseidon2 public digest assumption | 124.0000000000 |
| SHA-256/ROM assumption | 128.0000000000 |

The union is `107.2883541461` bits.  Subtracting `log2(33)` gives
`102.2439600267` bits.  Even replacing 33 by a conservative factor 40 leaves
`101.9664260512` bits.  These are the selected numeric soundness values. They
are not yet a complete-system claim because the production target-combo
check, integration, mined work and computational-HVZK closure remain open.

For reference only, the rejected attached-function/no-direct sensitivity
replaces the two source rows by the `116.7421085624`-bit common-set MCA row
and retains only the main q row.  Its older factor-33 result was
`100.5153253592` bits at g36.  It supplies no CU or proof benefit to the
selected construction and is not used.

The isolated-switch beta equations are not part of profile 21. They evaluated
disclosed U but had no authenticated `Fold(W0)(beta)` operand, so they supplied
no additional binding. The full `phi(U)` relation injection and the two q
equalities are the selected handoff. Removing the stale translated cross-list
pair leaves the ordinary four-round OOD/list row above.

## Causal transcript audit

The following order is necessary and non-circular:

1. Complete the external zerocheck and bind the ordinary roots.
2. Commit the shared C2/XF root before every round-zero challenge that defines
   the production covector `L`.
3. Compute, absorb and fix `tX,muF` under that exact covector.
4. Check and absorb the dedicated source g38 witness; only then sample
   nonzero `delta`.
5. Reveal logical `U`, commit translated `W1`, and inject full `phi(U)` into
   the existing first-later relation before its subsequent OOD/fold work.
6. Commit every later root, absorb the final polynomial, check/absorb final
   g38, then sample the distinct q16 positions.
7. At exactly those positions authenticate `X,F` from the shared root,
   authenticate W0/W1 from the main roots, evaluate
   the disclosed logical `U` with the fused literal evaluator, and check
   `W1-Fold(W0)=Enc(phi(U))=F+delta*X`.

Sampling delta before the two target claims, q before either root, omitting
the full relation injection, or using an unauthenticated copy of `X` in q
breaks the reduction.  A host scalar reused by multiple builders is not a
binding argument.

## HVZK and complete public view

The exact fixed-schedule atomic replay now gives `780/780` affine PCS rank,
`1080/1080` masked-zerocheck rank, and witness-difference containment. It is
still not an all-schedule computational profile-21 HVZK theorem:

- the universal MDS q block is proved, but remaining challenge-dependent
  containment minors and their witness-independent retry law are not frozen;
- conditioning on a Fiat--Shamir schedule is not justified merely by rank,
  because the roots are functions of the masks;
- ordinary Merkle roots and sibling paths are nonlinear random-oracle views.
  The repository has no private-Merkle/EPRO simulator or protocol-specific
  conditional-min-entropy proof for them;
- abort/retry count, failed roots, proof-account bytes, logs, and any remote
  proving transcript must be simulated or suppressed; and
- the proof account contains the entire proof and is therefore part of the
  adversary's view.

For a fixed public atomic statement, successful mutation writes only the
public next root/sequence and the public nullifier marker.  Those account
images and the deterministic rent effect add no witness-dependent field value.
This observation does not hide the proof that authorized them.  The current
live atomic acceptance path is read-only; the mutation tag remains fail-closed.

The one-transaction design has no receipt.  If the split fallback is retained,
its receipt exposes terminal points and claim scalars.  Those fields must be
exact copies of already simulated masked-view values (or replaced by hashes);
the existing receipt type predates profile 21 and is not covered by the current
rank artifact.

## Closure conditions

`complete_system_claim_quotable` may become true only after all of these are
green on the same frozen profile:

1. production verifier teeth showing one authenticated `X` is used in OOD,
   fold and q, and literal `Enc(U)(q)` is checked, with the causal order above;
2. the exact target-combo check above using the production covector and
   generated inverse basis, with target/basis/U/order teeth and measured CU;
3. a written reduction from those exact direct-binding equations to the
   standalone source MCA/q events and the ordinary S-two Theorem-19 events;
4. an atomic profile-21 complete-view containment artifact;
5. an EPRO/private-Merkle simulator covering roots, paths, retries, proof
   account, logs, and mutation/receipt data;
6. mined source/fold/final work witnesses on the production path; and
7. the complete proof verifier wired into the atomic mutation closure and a
   literal one-transaction SBF measurement below 1.4M CU.

Source: S-two revision in `/tmp/s-two-real.pdf`, especially Theorem 19,
Theorem 31, Lemmas 3--4, and Theorem 22; repository profile-20, masked-switch,
atomic-registry, and FS-HVZK notes dated 2026-07-13.
