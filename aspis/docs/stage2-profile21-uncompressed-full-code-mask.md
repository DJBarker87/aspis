# Profile-21 uncompressed native full-code mask

Date: 2026-07-13

Status: **protocol reduction and Johnson sensitivity are green; complete-View
rank, EPRO/HVZK, production integration and CU are pending.**  No hiding or
one-transaction claim is authorized by this note.

## Frozen production candidate

Keep the profile-20 relation surface unchanged:

- all 84 serialized statement evaluations;
- the existing width-28 powers batch under `gamma`;
- the existing four normalized folds, OOD records and final polynomial; and
- the existing q16/rate-1/512 query geometry.

Add one independent native root-zero circle-code message

```text
X in K^1024,                         K = QM31,
```

to the shared C2 commitment.  `X` is sampled uniformly over the complete
1,024-dimensional message space and encoded with the same root-zero encoder
as the existing combined word.  It is one C2 lane, not 1,024 columns.

Let the three frozen statement points be

```text
z0 = z,                z1 = succ(z),                z2 = xor12(z),
```

let `kappa` be the existing point-scale challenge, and let `I` be the exact
atomic copy-inactive row indicator.  After `gamma` and `kappa` are known, the
prover discloses the single scalar

```text
tX = L_kappa(X)
   = X(z0) + kappa*X(z1) + kappa^2*X(z2) + <I,X>.
```

This is the literal old three-point-plus-inactive functional.  It is not the
post-alpha source covector, a power-vector diagnostic, or a compact
`[tau,kappa,kappa^2]` replacement.

After absorbing `tX`, verify and absorb a fresh g38 work witness and sample a
nonzero `epsilon`.  If

```text
F_gamma = sum_{j=0}^{27} gamma^j F_j,
```

the virtual round-zero word and its initial relation claim are

```text
W0* = F_gamma + epsilon*X,

T0* = T0_gamma + epsilon*tX,
T0_gamma = sum_j gamma^j
             (F_j(z0) + kappa*F_j(z1) + kappa^2*F_j(z2)).
```

The existing columns retain their mandatory zero copy-inactive claims.  The
possibly nonzero inactive contribution of `X` is carried exactly inside
`tX`.  The ordinary incremental relation then starts from `(W0*,T0*)` and is
unchanged thereafter.

There is no compact `A`, `tau`, `delta`, multiplier, source polynomial,
translated root, disclosed source vector, source MCA, or source query test.

## Frozen Fiat--Shamir order

The causal transcript is:

1. absorb the profile/header, circle-basis discriminator, public statement
   digest and hiding precommit;
2. absorb the C1 root, sample the existing `lambda,chi`, and absorb the shared
   C2 root containing `(H,G,X)`;
3. run the complete masked zerocheck transcript and derive `z`;
4. absorb the three derived statement points and the unchanged 84 statement
   evaluations;
5. verify and absorb the existing batch g38 witness, then sample `gamma` and
   `kappa` in the existing order;
6. absorb `tX=L_kappa(X)`;
7. verify and absorb the new outer-group g38 witness, then sample exact-uniform
   nonzero `epsilon`;
8. form the virtual `(W0*,T0*)` and execute the ordinary round-zero OOD,
   relation sumcheck, fold work and `alpha0`;
9. bind each later root before its OOD values, relation sumcheck, fold work and
   next fold challenge, exactly as in profile 20;
10. absorb the final tensor polynomial, verify and absorb the existing final
    g38 witness, and only then sample 16 distinct query fibers; and
11. authenticate the ordinary C1/C2 fibers and later openings.  At layer zero
    compute each opened `W0*` symbol from the width-28 gamma combination plus
    `epsilon` times the authenticated raw X symbol, then check the unchanged
    normalized fold path.

Steps 6 and 7 are one additional public-coin round: `tX` and its work nonce
are adjacent prover data and there is no challenge between them.  Moving the
X root after `gamma`, sampling `epsilon` before `tX`, deriving q before any
later root/final polynomial, or accepting a separately supplied X value at q
invalidates the reduction.

## Completeness and malicious-X soundness

For an honest proof, every `F_j` and `X` is in the same `K`-linear main code,
so `W0*` is a main codeword.  Linearity of `L_kappa` gives

```text
L_kappa(W0*) = T0_gamma + epsilon*tX = T0*.
```

No degree multiplication or code transport occurs.

A malicious prover is not assumed to choose a codeword X.  Soundness instead
uses the following exact chain.

1. The shared C2 Merkle root fixes the complete received word X before
   `gamma`, `tX` and `epsilon`.
2. The existing width-28 powers-generator MCA event binds the inner word
   `F_gamma` after the pre-gamma g38 position.
3. Conditioned on the entire pre-epsilon view, `(F_gamma,X)` is a fixed pair
   of received words.  The exact-circle degree-one generator

   ```text
   Gen(epsilon) = (1,epsilon)
   ```

   and the post-`tX` g38 position give the outer MCA event.  Thus a far
   arbitrary X cannot cancel `F_gamma` into a near main codeword except for
   that charged event.
4. The ordinary WHIR/S-two fold/list-commutation reduction is applied to the
   same `W0*`; no new code or matrix-valued generator is introduced.
5. q is sampled after all commitments and the final work witness.  The
   verifier recomputes the X contribution from the authenticated shared-C2
   fiber, so the queried word is exactly the word used by the reduction.

The target has a separate elementary binding check.  For any selected pair
of component codewords define the pre-epsilon errors

```text
e0 = T0_gamma - L_kappa(F_gamma),
eX = tX       - L_kappa(X).
```

Both are fixed before nonzero `epsilon`.  An accepted false initial claim
requires

```text
e0 + epsilon*eX = 0.
```

If `(e0,eX)` is nonzero, this equation has at most one root, for conditional
probability at most `1/(|K|-1)`.  This row is charged in addition to the
unchanged gamma/three-point collision row.  A Schwartz--Zippel bound alone
would not bind an arbitrary X to the code; the outer MCA event is essential.

The theorem pins are unchanged:

- S-two Whitepaper, ePrint 2026/532, PDF 2026-03-24, SHA-256
  `e3b0132ec598ca16835c1de3c85d0c8b07c41b5f063f1d88b5a9628c22252c3f`:
  Theorem 31 and Corollary 1 for the exact circle subspace, Lemma 3 and
  Theorem 19 item 1 for powers batching, and Lemma 4/Theorem 19 item 2 for
  folding;
- Bordage--Chiesa--Guan--Manzur, revision 2026-05-19, SHA-256
  `23519c2d5d6541ee53e635b10c22d5f5964301b79a853d9394da267062e520a6`:
  the polynomial-generator framework remains a cross-check, but the outer
  `(1,epsilon)` row already uses the exact-circle degree-one S-two base case.

No ambient-RS-to-circle subcode inheritance is assumed.

## Conservative q16/rate-1/512 Johnson sensitivity

Use

```text
|K| = (2^31-1)^4,              N = 131072,
rho = 1/512,                   alpha = 1.05*sqrt(rho),
A = floor(alpha*N) = 6082,     q = 16.
```

The selected numerical rows are:

| event | bits |
| --- | ---: |
| inner width-28 powers MCA after pre-gamma g38 | 108.3684875342 |
| outer `(1,epsilon)` degree-one MCA after post-`tX` g38 | 113.1233750364 |
| four normalized fold rows, union | 112.0797907885 |
| main q16 miss after final g38 | 108.9018865972 |
| ordinary four-round OOD/list union | 213.1000183949 |
| relation sumchecks/OOD mixers `24/|K|` | 119.4150374966 |
| gamma plus three-point batching `29/|K|` | 119.1420190022 |
| copy-inactive gamma claim `27/|K|` | 119.2451124951 |
| atomic tuple compression `183*17/|K|` | 112.3968373178 |
| atomic copy/range poles `4*(183+1024)/|K|` | 111.7627900366 |
| atomic theta degree `24/|K|` | 119.4150374966 |
| ten degree-27 zerocheck rounds `270/|K|` | 115.9231844003 |
| false-X-target epsilon identity `1/(|K|-1)` | 123.9999999973 |
| Poseidon2 public-digest assumption | 124.0000000000 |
| SHA-256/ROM assumption | 128.0000000000 |

Their direct union is `107.3916788247` bits.  If the transcript compiler
confirms that the one adjacent `(tX,work)->epsilon` boundary increases the
profile-20 BCS factor from 31 to 32, the result is

```text
107.3916788247 - log2(32) = 102.3916788247 bits.
```

Sensitivity to a larger factor remains green:

| BCS factor | bits after factor |
| ---: | ---: |
| 33 | 102.3472847053 |
| 34 | 102.3042159834 |
| 40 | 102.0697507298 |

These are numerical sensitivities, not a complete-system claim.  The exact
transcript compiler must pin the factor, and the PoW records must be mined on
the final bytes.

## Hiding and implementation gates

At q16, the authenticated raw X surface contains at most 64 `K` linear
observations and `tX` adds one.  A uniform 1,024-dimensional native message
therefore retains at least 959 conditional `K` directions before the rest of
the proof view is considered.  This large dimension does not itself prove
hiding.  CU credit and a shielded-spend claim require all of:

1. exact complete-View containment for the literal 1,024-row basis against
   the uncompressed width-28 baseline, with sparse/dense parity;
2. a challenge-universal minor or a witness-independent rank-retry law;
3. the EPRO/private-Merkle simulator for the widened `(H,G,X)` tree, including
   failed roots, paths, salts, retries, proof bytes and logs;
4. same-statement/two-witness and fixed-witness/resampled-mask distinguishers;
5. an integrated acceptance path with corruption, challenge-order,
   padding/cross-residual and raw-X recombination teeth; and
6. one overlap-subtracted SBF measurement including the widened C2 leaf,
   target/work parsing, relation initialization, q recombination, atomic
   mutation and every hiding-visible byte.

Relative to the prior `X/F/U` switch, this wire removes an entire source PCS,
translated seam, disclosed source vector, source work/query logic and source
soundness rows.  That is the intended six-figure structural saving.  No CU is
booked until the integrated measurement exists.
