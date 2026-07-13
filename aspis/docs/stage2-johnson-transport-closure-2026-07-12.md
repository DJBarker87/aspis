# Rate-1/16 Johnson transport closure audit

Date: `2026-07-12`

Status: **the code/list/fold/OOD transport can be reduced to published
Johnson-bound results, but the current transcript is not a 100-bit candidate.**
The remaining blocker is concrete rather than conjectural: profile 15 has no
proof-of-work filter in the `gamma` batching round.  The exact proven batching
bound is only **81.9795 bits** before round-specific work.  A later fold nonce
or the final query nonce cannot be credited to this earlier BCS round.

This note does not approve a production security claim.  It separates source
theorems from the reductions made here and identifies the minimal protocol
change needed before the numeric ledger can close.

## 1. Version-pinned primary sources

The statements used below are from these versions:

- Carmon--Goldberg--Haböck--Lerer--Lesokhin--Papini--Samocha, [*S-two
  Whitepaper*](https://eprint.iacr.org/2026/532), ePrint 2026/532: Theorem 5
  (paper p. 7), Definition 6 and Theorem 7 (pp. 9--10),
  Protocol 3, Theorem 19, Lemmas 3--4, Theorem 22, and the grinding paragraph
  following equation (90) (pp. 31--33, 42--43 and 64--67).
- Bordage--Chiesa--Guan--Manzur, [*All Polynomial Generators Preserve
  Distance with Mutual Correlated Agreement*](https://eprint.iacr.org/2025/2051),
  ePrint 2025/2051, revision dated `2026-05-19`: Definition 9.1, Theorem 9.2,
  and Lemma 9.3 (pp. 40--41).
- Haböck, [*A note on mutual correlated agreement for Reed--Solomon
  codes*](https://eprint.iacr.org/2025/2110), ePrint 2025/2110: Theorem 2
  (paper p. 4).
- Arnon--Chiesa--Fenzi--Yogev, [*WHIR*](https://eprint.iacr.org/2024/1586),
  ePrint 2024/1586: Lemma 4.13 (pp. 25--26) and Theorem 4.20/Lemma 4.21
  (pp. 28--30).

The BCGM revision matters.  Its explicit Johnson-regime theorem is not the
old capacity conjecture and does not require that conjecture.

## 2. Correct exact code object

Let

```text
F0 = M31,
F  = QM31,
Q  = |F| = (2^31-1)^4.
```

The layer-zero codeword has **16,384 circle symbols**, not 4,096.  The exact
circle domain is the canonical coset `G'_14`; 4,096 is the number of
four-symbol query fibers.  The committed message has 1,024 direct tensor
coefficients and lies in the circle FFT space `L'_10(F)`.  Thus the exact
starting code is

```text
C' = { p|G'_14 : p in L'_10(F) }.
```

S-two Theorem 5 and equations (19)--(22) give
`dim L'_10 = 2^10 = 1024` and `L'_10 subset L_10`.  Definition 6 identifies
the full `L_10` circle code, under the rational circle parametrization and a
nonzero coordinate scaling, with a generalized Reed--Solomon code generated
by univariate polynomials of degree at most 1,024.  Coordinate permutation
and nonzero coordinate scaling preserve Hamming agreement.  Passing to the
`L'_10` subcode can only shrink every decoding list.

Consequently:

- the conservative minimum distance is `1 - 1024/16384 = 15/16`;
- the FFT-space rate used by the folding protocol is exactly
  `rho = 1024/16384 = 1/16`;
- every Johnson list statement for the full scaled GRS code is a valid upper
  bound for this exact subcode.

This is a theorem-level consequence of S-two's code identification.  The
Aspis-specific premise that the committed bytes are evaluations of those
direct tensor coefficients is implementation conformance, covered by the
circle encoder/basis tests; it is not supplied by the paper.

The 49 C1 columns are words over `F0` embedded in `F`; `(h1,G)` are two words
over `F`.  After embedding, all 51 are ordinary scalar words over the same
`F`-linear code.  No packed or matrix-valued generator is involved.

## 3. Two commitment phases do not create a new MCA theorem

The transcript order is

```text
C1 root -> lambda,chi -> C2 root -> statement reduction and claimed values
        -> gamma -> second-point scale -> OOD/fold rounds.
```

Condition on the complete transcript immediately before `gamma`.  At this
point both Merkle roots, all 49 C1 words, both C2 words, and every claimed
evaluation are fixed.  Although C2 may depend on `lambda,chi`, it cannot
depend on `gamma`.  Therefore `gamma` is an exact-uniform seed applied to a
fixed 51-word ensemble, which is precisely the hypothesis needed by a powers
generator MCA/batching theorem.

This conditioning argument closes the *two-phase* issue.  It would fail if
C2 or any claimed value were absorbed after `gamma`; the existing ordering
teeth remain load-bearing.

Using two Merkle roots instead of one tuple root is also not a new coding
assumption.  In the ideal-oracle proof, regard a layer-zero oracle symbol as
the tuple of the 49 C1 and two C2 symbols.  The verifier evaluates the virtual
combined oracle from authenticated tuple coordinates.  In the BCS compiler,
the roots are two oracle messages at their actual transcript positions; after
the second root both components of the tuple are binding.  No explicit third
root for the virtual combination is needed.

## 4. Exact `gamma`-batching bound, and the current fatal gap

For the selected Johnson agreement threshold, set

```text
alpha = 1 - theta = (1 + 1/(2m))*sqrt(rho),
m = 10,
rho = 1/16,
alpha = 0.2625,
theta = 0.7375.
```

S-two equations (73)--(74) give the Guruswami--Sudan list parameter

```text
ell_GS = (m + 1/2)/sqrt(rho) = 42.
```

Specializing Theorem 19 item 1 (equivalently Lemma 3) to one domain,
`M=51`, and `|D0|=16384` yields

```text
eps_batch = (M-1) * ell_GS
            * ((2*ell_GS^4/3)*rho + 1)
            * |D0|/Q
          = 2^-81.9795080671... .
```

The theorem applies to `L'_10`, not merely the full circle code: Protocol 3 is
stated for circle FFT spaces, and its proof uses correlated agreement for
linear subspaces.  The single-domain case is an immediate specialization.

BCGM gives an independent, more general bound for the **ambient scaled GRS
code**.  For the univariate powers generator of degree `d`, Definition 9.1
and Lemma 9.3 give

```text
eps_BCGM = ((m+1/2)^7/(3*rho^(3/2))) * d*n^2/Q.
```

For `d=50,n=16384,m=10`, this is only 62.1949 bits, so it is much weaker than
the structured S-two batching theorem.  BCGM Theorem 9.2 is not, by itself, a
subcode-inheritance theorem for `L'_10`: its RS-specific conclusion applies to
the ambient scaled GRS code.  The exact FFT subspace step is supplied here by
S-two Corollary 1 and Theorem 19, whose proofs explicitly treat linear
subspaces.  (BCGM's general-linear-code theorem also applies to the subcode,
but not at this Johnson radius with the RS-specific bound.)  The local
polynomial identity bound `50/Q` is not a substitute for either result: the
nearby codeword may depend on `gamma`, which is exactly the situation
correlated agreement controls.

### Current transcript finding

`circle_hiding_prefix.rs` absorbs the 102 values and immediately samples
`gamma`.  It has no nonce predicate between those actions.  The four existing
fold nonces filter `alpha[0..3]`; the final nonce filters the query sample.
S-two's grinding rule is round-specific: a `z`-bit salt reduces the error of
the verifier randomness sampled in that round.  A later salt cannot be moved
backwards across an intervening prover message and credited to `gamma`.

Therefore the current profile has an 81.9795-bit proven round.  No choice of
q36 query arithmetic, later fold work, or hiding reserve can make the current
transcript a 100-bit argument.

### Minimal repair

Add a separately framed batching nonce after both point rows and all claimed
values, and before `gamma`.  The verifier must:

1. check `grinding_ok(batch_nonce, batch_pow_bits)` against that exact state;
2. absorb a domain-separated batch-nonce record;
3. only then sample `gamma` and the point-batching scalar(s).

At 22 bits the batching round becomes 103.9795 bits.  A 25-bit candidate gives
106.9795 bits and leaves room for the BCS `(1+R/T)` factor and same-round local
events.  The final bit choice must come from the regenerated all-round ledger,
not this isolated row.  This adds one verifier hash call; changing difficulty
does not change verifier CU.

Required teeth: omit the nonce, alter it, verify it against the state before
the second point row, absorb it after `gamma`, reuse a nonce across statements,
and mine a nonce for one transcript then swap either root.

The byte-exact repair specification is:

```text
logical placement:
    absorb(statement points)
    absorb(all statement-evaluation rows)
    check batch work
    absorb(batch nonce)
    gamma <- challenge_qm31()
    point batching scalar(s) <- challenge_qm31()

absorption domain tag:
    M31_PAYMENT_BATCH_POW_NONCE = 28 = 0x1c

wire record:
    batch_nonce_le : [u8;8]

work predicate on the pre-gamma transcript state s:
    d = SHA256(s || [DOM_GRIND=0x03] || batch_nonce_le)
    u64_be(d[0..8]) < 2^(64-batch_pow_bits)

state update after a successful predicate:
    s <- SHA256(s || [DOM_ABSORB=0x00, 0x1c] || batch_nonce_le)
```

The predicate input is deliberately domain-separated from the absorb input.
The current fixed-prefix draft stores the eight bytes at offset 4,104 and
moves `openings_start`/the fixed prefix length to 4,112.  Physical storage may
remain in the nonce trailer; *transcript processing* must occur at the logical
position above.  `batch_nonce=0` is not a diagnostic bypass on a production
entry point: it is accepted only if it actually satisfies the configured
predicate.

This nonce is one BCS-round salt.  It is not a new field challenge and does
not replace `gamma` or a point-batching scalar.  The proof format, KAT,
prover/verifier parity test, and every challenge-order tooth must all bump
together.

## 5. Arity-four folds and list commutation

Each Aspis fold is exactly a degree-three powers generator.  Expanding the
production formulas gives

```text
a0 + alpha*a1 + alpha^2*a2 + alpha^3*a3,
```

where `(a0,a1,a2,a3)` are the two successive inverse-FFT components of the
four authenticated input slots.  The coordinate-dependent divisions by
`2x`/`2y` are the invertible FFT change of basis, not challenge coefficients.

This matches S-two equation (68), including the dependence
`(1,alpha,alpha^2,alpha^3)`.  For later all-line rounds, split the incoming
word by two successive line decompositions.  This is a restriction of the
four arbitrary component words treated in the proof of S-two Lemma 4: a
restriction of the adversary's input set cannot increase its error.  Full
agreement on a four-symbol fiber is equivalent, by the invertible local FFT
matrix, to joint agreement of all four component words at the projected
coordinate.

The exact output-domain sequence is

```text
(n,k) = (4096,256), (1024,64), (256,16), (64,4),
```

where `k` is line-code dimension.  Applying the explicit S-two Lemma 4 bound
at `theta=0.7375` gives the following unground round bits:

| fold | output domain | GS multiplicity | list parameter | bits |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 4096 | 10 | 42.0823 | 88.0299 |
| 1 | 1024 | 9 | 38.3004 | 90.7263 |
| 2 | 256 | 6 | 26.8527 | 95.3581 |
| 3 | 64 | 3 | 16.1658 | 101.3400 |

The current `[39,35,31,27]` fold work raises these to at least 125.7 bits and
is therefore much larger than needed under this theorem.  For example,
`[19,17,12,6]` raises every fold row above 107 bits.  This is a prover-time
rebalancing, not a verifier-CU saving: all four verifier hash checks remain.

WHIR Lemma 4.13 then gives list-decoding commutation for each powers
generator on the ambient scaled GRS code: except with its MCA error,
list-decode-after-combine equals combine-the-joint-list.  WHIR Theorem 4.20
states the iterated version using block distance.  Its block metric is exactly
the relevant one here because a query opens all four symbols of a fiber.  The
linear constraint selecting the circle FFT subspace is carried separately:
S-two Corollary 1 proves correlated agreement under such linear constraints,
and the terminal tensor check enforces the folded image of that constraint.
Thus this note does not assert the false general rule that MCA automatically
inherits from a code to every subcode.

Thus grouped folding and list commutation do not require the refuted capacity
conjecture.  They are a Johnson-bound specialization of the published
S-two/BCGM/WHIR results.

## 6. Two OOD samples and the Boolean-MLE relation

Let `S = Q - (2^31-1)^2`.  The accepted layer-zero parameter sampler is a
bijection

```text
QM31 \ CM31  <->  C(QM31) \ C(CM31),
```

and later line samples are exact-uniform in `QM31 \ CM31`.  Therefore every
accepted OOD domain has cardinality `S`; bounded exhaustion is a completeness
event.

For a fixed decoding list before the first sample, two sequential samples and
adaptive claimed values still give the standard pair collision event: some
pair of distinct list elements must agree at both independently sampled
points.  With conservative list cap 160 and exact root caps

```text
R = [1024,255,63,15],
```

the four errors are bounded by

```text
C(160,2) * (R_i/S)^2.
```

Their union is below `2^-214.2729`.  The first cap is 1,024, not 1,023: the
circle FFT subspace can contain a rational numerator of univariate degree
1,024.  The later caps are `degree-1` for ordinary line polynomials.

The custom relation is a constrained-code linear functional, not S-two's
circle-point quotient protocol.  Its soundness reduction is nevertheless
local:

1. The claimed Boolean-MLE values and the OOD values define a linear
   functional on the direct tensor message.
2. `WeightAccumulator::fold(alpha)` is the dual of the exact arity-four FFT
   fold, so the functional and the folded codeword have identical inner
   product after every honest fold.
3. If a prover sends a different degree-at-most-six sumcheck polynomial, its
   difference from the true polynomial is nonzero and vanishes at random
   `alpha` with probability at most `6/Q`.
4. OOD list uniqueness and WHIR Lemma 4.13 identify the same predecessor
   codeword through the list cascade.
5. The terminal four-coefficient dot is the final constrained-code check.

This proves the relation for any fixed number of externally claimed MLE
points.  For the current two-point profile the post-claim check is

```text
E0(gamma) + kappa*E1(gamma).
```

For the state-only three-point candidate use two independent post-claim
scalars in the affine form

```text
E0(gamma) + kappa1*E1(gamma) + kappa2*E2(gamma).
```

After all three claim rows are bound, this is a nonzero multivariate
polynomial of total degree at most 51, so its collision term remains `51/Q`.
A nested form such as `E0+kappa1*(E1+kappa2*E2)` has total degree 52 and must
not silently retain the 51/Q line.

The statement-specific obligations remain local: the zerocheck must derive
the claimed point(s), the successor/shift maps must be the intended
polynomial representatives, and the sumcheck degree cap must include them.
None is a circle-code transport assumption.

## 7. Fiber queries and BCS

At distance `theta=0.7375`, a codeword can agree with the received word on at
most

```text
floor((1-theta)*16384/4) = 1075
```

complete four-symbol fibers.  The production sampler draws 36 distinct fibers
uniformly without replacement.  Its exact miss probability is

```text
C(1075,36)/C(4096,36) = 2^-70.1080533003... .
```

The query-round 36-bit nonce raises this round to 106.1080533003 bits.  This
is a direct block-counting statement and is at least as strong as S-two
Theorem 19's with-replacement `(1-theta)^36` row.

S-two Theorem 22 supplies the BCS/ROM conversion:

```text
eps_BCS(T) <= (T+R)*max_i eps_i + 3*(T^2+1)/2^256.
```

Aspis uses ordinary Merkle trees, not S-two's release-specific mixed-domain
tree, so Remark 23's unproved mixed-tree adaptation is unnecessary.  Multiple
ordinary roots are ordinary multi-round BCS oracle messages.  A final claim
must still state an attacker-query ceiling and use the theorem's factor; a bare
`128-bit SHA collision` line is not the complete BCS calculation.

Most importantly, BCS uses the maximum round error.  It does not permit a
query-round nonce to repair an earlier 81.9795-bit batching round.  Adding the
pre-`gamma` nonce is therefore necessary, not merely conservative.

## 8. Rate-1/32 consequence

Rate 1/32 is a genuine structural option, not a free soundness win.  Keep the
same `L'_10` message and evaluate on `G'_15`:

```text
symbols = 32768,
four-symbol fibers = 8192,
rho = 1/32.
```

With the same `m=10` Johnson choice,

```text
1-theta = (1+1/20)/sqrt(32) = 0.1856155301...,
max complete agreement fibers = floor(0.1856155301*8192) = 1520.
```

Then q29/g36 gives

```text
C(1520,29)/C(8192,29) / 2^36 = 2^-106.7903862559...,
```

where q28/g36 gives only 104.3384 bits.  Thus rate 1/32 can replace q36 by
q29 at essentially the same query-round target.  This is the plausible
six-figure CU lever: seven fewer layer-zero RLCs and seven fewer paths, offset
by one extra tree level and larger proof geometry.  It requires an exact SBF
measurement.

The algebraic round errors get worse because the domains are larger.  The
51-column batching row falls from 81.9795 to 79.4795 unground bits, so a
roughly 28-bit pre-`gamma` nonce is the conservative 107-bit candidate.  The
four unground fold rows become approximately

```text
[85.5299, 88.2263, 92.8581, 98.8403] bits.
```

No additional verifier hashes are needed relative to the repaired rate-1/16
schedule; only the nonce difficulties change.  Therefore rate 1/32 trades
prover work and proof/path geometry for materially fewer on-chain query
arithmetic operations.

For the proposed scalar state-only width 18, the same calculation substitutes
`M=18` and changes no theorem.  The unground batching rows are 83.5359 bits at
rate 1/16 and 81.0359 bits at rate 1/32.  Conservative approximately 107-bit
round targets therefore use about 24 and 26 bits of pre-`gamma` work,
respectively.  The three Boolean-MLE point rows affect the local affine
claim-batching polynomial described in Section 6; they do not increase `M`,
which counts committed scalar columns.

## 9. Closure verdict

The Johnson transport itself no longer needs an unnamed circle conjecture:

- exact `L'_10` code/scaled-GRS identification: **closed by S-two**;
- two-phase C1/C2 conditioning before `gamma`: **closed locally**;
- scalar powers batching and arity-four folds: **closed at Johnson by S-two;
  BCGM independently covers the ambient scaled GRS generator but needs
  S-two's linear-subspace bridge for the exact FFT space**;
- list/fold commutation: **closed on the ambient lists by WHIR Lemma
  4.13/Theorem 4.20, with the FFT-subspace constraint transported by S-two
  Corollary 1 and the terminal check**;
- two-sample OOD binding: **closed by the explicit root/list calculation**;
- two- or three-point Boolean-MLE aggregation: **local constrained-code
  sumcheck, not a circle opening theorem**;
- without-replacement fiber query term: **closed by exact counting**;
- ordinary-tree Fiat--Shamir composition: **covered in the ROM by S-two
  Theorem 22/BCS, subject to an explicit `T` ledger and hash assumptions**.

The minimal blocker in the current proof format is the missing pre-`gamma`
batch PoW.  Until that nonce is present, mined, verified on the production
path, and included in the transcript KAT and all-round BCS ledger,
`q36/g36/rho=1/16` is at most an **81.9795-bit proven-round candidate**, not a
100-bit-class argument.
