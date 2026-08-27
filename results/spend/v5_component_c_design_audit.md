# v5 Component C: exact decoupling obligation

Status: design/result note only. This does not authorize a production wire or
claim that v5 is zero-knowledge. It records the smallest theorem that would do
so for Component C and the exact evidence currently available.

## Verdict

The proposed C lane is not disqualified merely because its physical sampler is
the same shape as v4's D lane. The roles differ:

- v4 D was paired with a compensating G direction, so its contribution to the
  gamma-batched FRI word was cancelled;
- proposed v5 C is added to the word that is actually folded. In the current
  19-lane stress relation its contribution is `gamma^18 * C`, with no
  compensating term.

That second role is the independent FRI mask polynomial of Haboeck--Al Kindi,
ePrint 2024/1037, Protocol 2. Their Lemma 2 proves that the independent mask is
an information-theoretic isolator even after its queried values are fixed, and
Theorems 4 and 6 give explicit perfect honest-verifier zero-knowledge
simulators. The same paper also explains why ordinary trace randomizers alone
lose entropy through FRI folds. Component C is therefore the right *kind* of
construction.

It is not proved for Aspis yet. The cited theorem is for binary univariate
Reed--Solomon FRI over a subgroup/coset. Aspis uses a circle code, arity-four
folds, a one-codimensional mask space, and four additional non-point linear
claims. The exact adaptation below is the gate.

## Fixed-schedule spaces and maps

Let `K = QM31`, and fix the complete Fiat--Shamir schedule `sigma`, including
the q18 indices, statement points, OOD points, relation challenges, four fold
challenges, and the nonzero lane-batching challenge `gamma`.

Let

```
V       = K^1024
ell     : V -> K
ell(c)  = sum of c[row] over the atomic-v3 copy-inactive rows
C       = ker ell
```

`ell` is nonzero: its selected rows have coefficient one. The first such row is
the pivot in `v5_c_mask.rs`. Hence `dim_K C = 1023`, and
`V5ComponentCLane::encode_free_coordinates` is an explicit linear bijection
`K^1023 -> C`. Uniform independent free coordinates therefore give the uniform
law on `C`.

For the fixed schedule define:

```
E_sigma : C -> K^76
```

as the values of C disclosed before/alongside the combined FRI transcript:

1. 72 authenticated layer-zero values: 18 queried fibres times four slots;
2. the three MLE claims at `z`, `successor(z)`, and `xor12(z)`;
3. the fourth structured terminal-functional claim.

Define

```
F_sigma : V -> Y_sigma
```

as the contribution of one coefficient word to every *post-combination* PCS
field coordinate: all four rounds' OOD and relation-sumcheck values, all opened
values in the three later FRI layers, and the four final coefficients. Merkle
roots, salts, nonces, and frontier hashes are not field leakage and are not in
`Y_sigma`.

For later-layer unique-leaf counts `n1,n2,n3`, the current grammar gives

```
dim Y_sigma = 4 * 9 + 4 * (n1 + n2 + n3) + 4
            = 40 + 4 * (n1 + n2 + n3).
```

The first term is four rounds times `(2 OOD + 7 relation-sumcheck)` QM31
values. The last term is the final polynomial. Derived-count bounds give
`8 <= n1+n2+n3 <= 54`, hence `72 <= dim Y_sigma <= 256`. The frozen q18 fixture
has no parent collisions, so `n1=n2=n3=18` and `dim Y_sigma=256`.

Thus the maximum joint linear inventory relevant to C is

```
76 conditioned C coordinates + 256 post-combination coordinates = 332 QM31.
```

This count excludes the 280-QM31 main sumcheck block, which Component B must
hide, and the separately opened layer-zero semantic/B/Hcopy values, which A
and B must hide. C cannot hide those layer-zero values because its own value at
the same position is disclosed.

Let the combined word before C be

```
X_gamma(w) = sum_(j=0)^15 gamma^j * S_j(w)
             + gamma^16 * Hcopy(w)
             + gamma^17 * B(w).
```

The word entering the fold protocol is

```
W_gamma(w,c) = X_gamma(w) + gamma^18 * c.
```

Let `Delta_sigma` be the K-linear span of all differences
`X_gamma(w)-X_gamma(w')` allowed by the accepted v5 relation at this schedule.
This is the legal witness-difference space; using all of `V` would be a
stronger condition than zero-knowledge requires.

## Required theorem: full-fold conditional decoupling

For every valid schedule with `gamma != 0`, every two legal witnesses `w,w'`,
and every `e` in the image of `E_sigma`, require

```
Law(F_sigma(W_gamma(w,C_uniform)) | E_sigma(C_uniform)=e)
  =
Law(F_sigma(W_gamma(w',C_uniform)) | E_sigma(C_uniform)=e).
```

For finite vector spaces this is equivalent to the exact image-containment
statement

```
F_sigma(Delta_sigma)
  <= image(F_sigma restricted to (C intersect ker E_sigma)).       (C-DEC)
```

Equivalently, with

```
J_sigma(c) = (E_sigma(c), F_sigma(gamma^18 * c)),
```

every legal witness shift must satisfy

```
(0, F_sigma(delta)) in image J_sigma  for every delta in Delta_sigma.
```

This is the exact theorem to formalise. Full row rank of a 332-by-1023 matrix
is sufficient but not necessary; `(C-DEC)` is the correct target because the
accepted transcript has public linear relations and `Y_sigma` need not be the
whole legal difference space.

Once `(C-DEC)` holds, the conditional fibre of C is a uniform affine coset and
translation by any legal witness difference permutes that fibre. The
post-combination field view is therefore perfectly witness-independent. The
remaining FRI transcript is a deterministic function of that field view and
fresh verifier challenges, so it remains independent. This is the circle,
arity-four analogue of the decoupling step in Haboeck--Al Kindi Lemma 2.

## What must be adapted from the published lemma

The cited result supplies the construction and simulator template, but not the
following Aspis-specific facts:

1. **Circle transport.** Show that the coefficient encoder and four arity-four
   folds give the same linear-oracle experiment used in `F_sigma`, or transport
   it through an explicit circle-code/GRS isomorphism.
2. **One-codimensional mask.** Show that restricting the independent mask to
   `ker ell` removes only a public relation direction. Concretely this is
   `(C-DEC)`; dimension `1023 > 332` alone does not prove it.
3. **Extra claims.** The three MLE claims and structured terminal claim are
   arbitrary linear functionals, not the domain point evaluations covered
   directly by the paper's interpolation proof. They must be included in
   `E_sigma`, as above.
4. **Complete fold view.** Include the 28 relation-sumcheck values as well as
   the eight OOD values, all three later opening layers, and the final four
   coefficients. A probe of only layer zero or OOD is insufficient.
5. **Adaptive ordering.** The C commitment must be bound before `gamma` and
   every later fold/OOD challenge. A frozen matrix rank cannot replace this
   causal condition.
6. **Bad schedules.** Either prove `(C-DEC)` for every valid transcript or give
   a nonzero-minor/Schwartz--Zippel bound in the Fiat--Shamir model. The Boolean
   and repeated-point schedules cannot simply be ignored. If a retry predicate
   is used, it must depend only on public schedule data.

## `gamma^18 C` non-cancellation tooth

The current stress verifier has 16 C1 lanes and three C2 helpers. In
`prepare_generic16`, helper `i` receives power `gamma^(16+i)`. Consequently
helper 2, the C position, receives `gamma^18`.

`generic_combine` parses the three helper values and computes either

```
sum_products3([gamma^16,gamma^17,gamma^18], [Hcopy,B,C])
```

or the algebraically identical two-product sum plus
`gamma^18 * C`. It then **adds** that sum to the combined layer-zero value.
There is no subtraction or correlated helper transformation.

The relation-claim path independently builds `qm31_power_table::<19>(gamma)`
and adds `lane_powers[lane] * claim[lane]` for lanes 0 through 18. Thus C's
three MLE claims and fourth claim also enter with coefficient `gamma^18`; again
there is no compensating term. Every later contribution is a linear fold of
the combined word, so it is `gamma^18 * Fold_sigma(C)`.

Therefore the partial derivative of every layer-zero combined symbol with
respect to the corresponding C symbol is exactly `gamma^18`. It is nonzero
whenever `gamma != 0`. This proves non-cancellation in the current stress
arithmetic. Production still needs to reject/resample `gamma=0` and derive it
after the binding commitment.

The existing literal-path regression is intended to check the fused formula
against a direct 19-term sum. At the time of this audit it does not reach that
assertion because the deterministic test account has a separate stale-length
mismatch (`6423` source bytes versus `6583` destination bytes). The source
identity above is direct; this test failure must not be reported as a passing
runtime tooth.

## Measurements and controls already obtained

- The alternative “drop C and use only B's 255 pads” map was tested on the
  exact frozen schedule over `72 raw + 3 MLE + 8 OOD + 4 final` coordinates.
  Its prefix ranks were `72, 75, 83, 86`, not the proposed target 87. With
  Boolean `z` and frozen OOD/folds they were `72,72,80,83`; on a fully
  degenerate valid circle-identity/line-zero/alpha-zero schedule they were
  `72,72,76,77`. That proposal is not a universal replacement for C. The
  missing frozen dimension might be a public relation direction, but that has
  not been proved.
- The exact old-D q18 control reproduced `raw=300/300`,
  `conditional=1076/1076`, `gd_schur=12`, `hcopy_schur=12`, and
  `complete=true`. This validates the historical D+full-G compensation
  certificate only. It neither proves nor refutes `(C-DEC)`.

## Gate and next checks

Component C is a **conditional GO** as the standard independent FRI mask. It
must not be described as complete until all of the following are green:

1. instantiate the exact 332-row worst-case joint map and test `(C-DEC)` on the
   frozen q18 schedule;
2. run adversarial Boolean/repeated-point schedules and identify whether the
   theorem is universal or only Fiat--Shamir high probability;
3. prove the circle/arity-four adaptation and the four-claim conditioning in
   Lean (or reduce them to an explicit published lemma plus kernel-checked
   transport);
4. bind the real C commitment before `gamma`, reject `gamma=0`, and authenticate
   all 76 lane claims;
5. re-enumerate the actual v5 serialisation and prove every C-target coordinate
   occurs in `F_sigma` exactly once.

Until then the honest statement is: the current C shape is a credible
instantiation of the published FRI isolator, and unlike v4 D it is not cancelled,
but full-fold conditional decoupling remains open.
