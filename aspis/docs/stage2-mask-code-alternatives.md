# Late mask/code-switch verification below 100K CU

Status: protocol-design and measurement note only. No production integration,
HVZK claim, circle code-switch theorem, or sub-100K measured result.

## Measured baseline and arithmetic floor

The isolated one-switch probe uses a 31-QM31 message and 29-QM31 encoding
randomness coefficients. Its specialized point check evaluates the resulting
60-coefficient polynomial and checks one affine carried/fresh equation at each
of q=29 positions. The probe loop executes 61 generic QM31 multiplications per
query (60 Horner steps, including the zero first state, plus one affine
scaling), or 1,769 in total, and measures 659,669 CU. Skipping the first zero
Horner multiplication still leaves 1,740 generic QM31 multiplications. The
separate dense 31-term target costs 18,323 CU.

A direct pointwise evaluator therefore cannot reach 100K CU by a field
microkernel alone. QM31 multiplication is nine M31 products, so even the
optimized direct shape has 15,660 M31 products before the target identity.

The only arithmetically plausible overlap found is to reveal the upstream
blinded vector

```text
U = F + delta X,
```

where X is the carried mask codeword's coefficient vector and F is a fresh
one-time pad, and translate an already-required next FRI word by Enc(U). The
verifier then:

1. evaluates P_U at the two already-required post-root OOD points;
2. checks `next - fold(previous) = fresh + delta * carried` at q=29 sampled
   positions, without evaluating P_U there; and
3. checks the dense carried/fresh target identity.

With a dense length-60 U this has the exact multiplication shape

```text
two OOD Horner evaluations  2 * 59 = 118 QM31 mul
q affine checks                         29 QM31 mul
dense target                            31 QM31 mul
total                                  178 QM31 mul
                                     1,602 M31 products
```

Scaling only the measured point-check block gives
`659,669 * 147 / 1,769 = 54,817 CU`. Adding the exact measured 18,323-CU
target and 1,857-CU shared-root transcript gives 74,997 CU before leaf-width,
decode, equality, and relation-bookkeeping deltas. This is a probe projection,
not a CU result. It has roughly 25K CU available for those deltas only if no
new tree or path is introduced.

The incremental revealed transcript is one QM31 fresh claim plus U:

```text
16 + 60 * 16 = 976 bytes.
```

If carried and fresh values add one four-slot QM31 helper apiece to an
existing layer-zero C2 leaf, the opened-value increment is 3,712 bytes at q29.
One already-present helper cuts that to 1,856 bytes. Root count and frontier
bytes remain unchanged, but the wider leaf hashing must be measured.

## Exact local simulator algebra

Let the carried code have message X_m and q=29 independent encoding-randomness
coordinates R. Let the fresh pad F have the same total dimension. After the
carried target t_X and fresh target mu_F are fixed, sample nonzero delta and
reveal U.

At q distinct nonzero points, the randomness submatrix A_R is a square
Vandermonde matrix and is invertible. The public linear observations satisfy

```text
U                 = F + delta * (X_m, R)
fresh_openings    = A U - delta * carried_openings
<U_m, c>          = mu_F + delta * t_X.
```

Consequently fresh openings add no rank after U and the carried openings are
uniform in K^29 independently of X_m. For any variation dX in ker(c), choose

```text
dR = -A_R^-1 A_m dX,
dF = -delta * (dX, dR).
```

This keeps the complete displayed local view fixed. For a 31-variable carried
message, the conditioned kernel is exactly 30 QM31 dimensions. Revealing U
does not reveal X: U is uniform because F is uniform. OOD evaluations of P_U,
the translated next-word openings, and receipt copies are deterministic from
U and already-public openings, so they add no field-linear observation.

This is only the local affine simulator. Merkle roots require the same
random-oracle simulator/programming argument as upstream Hiding-WHIR, and the
receipt must contain no unmasked X or F coefficients.

## Causal transcript required by the overlap

The carried and fresh roots must be fixed before the target covector and
delta. After the previous sumcheck challenge has fixed the carried covector:

```text
absorb carried target t_X
absorb fresh target mu_F
sample fresh nonzero delta
absorb U = F + delta X
commit/absorb translated next root
sample both next-layer OOD points and subtract P_U(beta_s)
complete later roots, work, and q29 query derivation
open carried/fresh rows and check the affine equation
```

A false t_X or mu_F gives a nonzero degree-one polynomial in the post-claim
delta. Translation by Enc(U) is a codeword translation and therefore a
Hamming isometry. The query branch still needs the proven Johnson/MCA result
for the actual line code and the correctly positioned g36 work. The
coefficient-to-translated-word binding is checked only after U and the next
root are fixed. Conservatively, a nonzero difference between the next-word
polynomial and the expected translated fold has degree at most the first-line
degree (255 in the current main code), giving at most 255/|QM31| at the first
OOD point; the second OOD check is retained for completeness and the existing
relation schedule.

Every equation must use the literal normalized circle-to-line fold. Replacing
it with an unnormalized butterfly or treating four co-opened symbols as one
independent value is unsound.

## Decisive rank result and the early-p0 obstruction

The corrected strict-root1 map invalidates the old 1,144/1,144 artifact:

```text
structured {1,2,3} U {4j,1<=j<=28}  1,136 / 1,144 M31
distinct folded coefficients 0..30           1,140 / 1,144 M31
```

The distinct map supplies all 116 missing later-opening M31 pivots. Its exact
remaining deficit is four M31 coordinates, one QM31 direction in the
round-zero relation polynomial p0. A word first committed at root1 cannot
affect p0, so no choice of root1 basis can close this deficit.

The natural boundary-zero early mask is

```text
Z_e(T) = e * (2T - 1),
Z_e(0) + Z_e(1) = 0.
```

It can mask p0 without changing the statement claim and is bound before
alpha0 by the transmitted p0 coefficients. However, the implementation link
to the one-word late code switch is not yet pinned:

* if e is uncommitted, the verifier has no codeword binding for a downstream
  cancellation involving e;
* if e is placed in a precommitted residue-one source coefficient while 31
  later variables occupy residue zero, the first fold collapses e and the
  coefficient-zero variable into one line coefficient. The p0 carry depends
  on e separately, but the single revealed line word U does not retain that
  second degree of freedom;
* retaining e as a separate line channel requires a matrix-valued/two-word
  code switch, another commitment lane, and a new theorem and CU row; and
* choosing the carried mask only after alpha0 moves its commitment too late
  to mask p0 and shifts the translated-word check to a later root, leaving
  the already-opened first later layer uncovered.

Thus an echelon experiment that simply combines one full root0 row image with
31 root1 coefficient images is not by itself an implementable protocol. The
joint gate must include the actual p0 mask polynomial, carried target,
pre-delta commitments, U encoding map, query co-openings, both OOD equations,
and receipt coordinates. Until that exact map reaches 1,144/1,144, the
sub-100K overlap is conditional and must not be integrated.

The separate log11/domain16 upper-G padding probe does not supply the p0
pivot: its upper and lower witness quotients are disjoint. It therefore does
not automatically repair strict root1's 1,140/1,144 result.

## Rejected alternatives

* The `{1,2,3} U {4j}` set is support in the source/public-map basis, not 31
  sparse monomial exponents in the blinded 60-coefficient mask code. The
  fresh OTP makes U dense. A stride-four Horner rewrite does not follow.
* Fast multipoint evaluation has no pinned sub-100K kernel at these sizes.
  The q positions are independently sampled subgroup positions, so replacing
  them with a consecutive/arithmetic-progression FFT window loses the query
  miss bound. A dynamic product/remainder tree also does not solve the p0 or
  proximity-linkage obligations.
* Ristretto/Edwards MSM, BN254 operations, and Poseidon syscalls operate in
  different fields or groups. Reduction from M31/QM31 arithmetic to those
  scalar fields is not a ring homomorphism, and group outputs do not expose
  the required field equality without a discrete logarithm. `sol_big_mod_exp`
  supplies modular exponentiation, not a vector dot-product primitive or a
  QM31 tower operation.
* Merkle authentication alone commits an arbitrary word. It does not prove
  that the word belongs to the mask RS/circle code.

## Best next probe

The only useful next measurement is gated on the exact joint rank above. If
it passes with an implementable early-p0 channel, an append-only measurement
tag should isolate:

1. U/target parsing and transcript absorption;
2. two prepared-QM31 Horner evaluations;
3. q29 normalized affine query links;
4. any widened existing-leaf hashes, with no new root/path credited;
5. the target identity; and
6. translated relation bookkeeping.

The guard suite must corrupt t_X, mu_F, delta order, every U limb, each OOD
subtraction, the translated root, carried/fresh openings, circle
normalization, and receipt copies. If the exact joint rank fails, or if a new
tree is required, retire this avenue: the measured standalone-tree and
ordinary-evaluation rows cannot fit the requested budget.
