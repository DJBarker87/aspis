# Profile-21 atomic HVZK / privacy closure

Status: **literal profile-21 fixed-schedule affine field view green; beta-free
five-tree computational wire and canonical-minimum miner implemented; all-q
availability and the complete EPRO/side-channel theorem remain open; complete
privacy claim red.**

Date: 2026-07-13.

This note covers the exact intended state-only profile at rate `1/512`, q16,
the atomic-v3 statement, and the auxiliary masked-switch oracle.  It does not
promote the unmined diagnostic verifier or the field-rank result to a
zero-knowledge claim.

## Ruling

The actual atomic-v3 rank replay closes the linear field-view deficit:

```text
masked zerocheck quotient                 1080 / 1080 M31
baseline PCS image                         712 /  780 M31
selected masked-switch conditioned image   780 /  780 M31
switch variables / observations / kernel    70 / 52 / 18 QM31
q randomness / conditional q co-openings     16 / 16 QM31
U one-time-pad image                         35 / 35 QM31
new pivots                             64 later + 4 relation M31
```

This is the exact atomic mask inventory and literal q16 Fiat--Shamir schedule,
including profile 21's sampled `delta`, from the 62,214-byte salted tag-50
proof.  It establishes perfect affine same-schedule containment for the
**pre-final-seam** modeled field coordinates.  The source-target seam is being
replaced by the full post-`alpha0` target observation, so this fingerprint is
a regression checkpoint, not final production evidence; the exact rank replay
must be regenerated after that seam freezes.  It does **not**
establish either of the following:

1. statistical HVZK for the implemented prover; or
2. computational ROM/EPRO zero knowledge for roots, paths, proof bytes and
   retries.

### Semantic witness-difference audit

The historical `baseline_valid_witness_containment` boolean is narrower than
its name suggests: it checks the active zero-sum `H`/helper subspace only. It
does not, by itself, check differences in the sixteen semantic trace columns.
The production-neutral witness audit now quotients those semantic differences
through the exact raw openings, column-specific gamma powers, masked sumcheck
wire and PCS image. It excludes only the sixteen cells in atomic block 0's
fixed pre-absorb row and otherwise permits every semantic M31 cell to vary
independently. It also appends all 1,080 legal M31 sumcheck directions whose
unmasked initial claim is zero.

On the literal q16 profile-21 schedule the exact result is:

```text
baseline mask PCS rank                         712
semantic-compatible augmented rank             716
legal sumcheck augmented rank                   716
semantic/sumcheck compatibility cokernel rank     4 M31
remaining semantic quotient                       4 M31 = 1 QM31
```

The compatibility pivots are owner-key column 0, rows 1 through 4. The four
canonical quotient representatives are `(c0,r5)`, `(c1,r1)`, `(c2,r1)` and
`(c3,r1)`, at PCS quotient rows 276 through 279. Removing the fixed row-0
cells merely shifts the representatives along the same owner-key Poseidon
trajectory; it does not remove the quotient. All 1,080 legal sumcheck
directions add no rank after these four semantic directions.

This is a conservative containment result, not yet a GREEN complete privacy
claim. It proves that one additional QM31 mask direction is sufficient for
the modeled semantic-plus-sumcheck support, provided that direction spans the
four-row quotient. A host-only projection hook accepts a concrete 16-by-1024
valid semantic trace difference and its 271-QM31 unmasked sumcheck transcript,
then returns the compatibility remainder and exact four quotient coordinates.
That hook is the required tooth for deciding whether constrained valid
Poseidon trajectories already annihilate the quotient or actually reach it.

Two tempting full-domain QM31 tail repairs are exact RED results. A fresh C2
lane at gamma exponent 28 with its own raw q-plus-three openings and zero
zerocheck coefficient leaves ranks `712 -> 716`. Giving the same lane an
independent dense-family-17 factor `1 + L^26`, so that it participates in the
degree-27 masked zerocheck, also leaves ranks `712 -> 716`; its 4,092 M31
source directions have raw kernel 3,824 and add no post-sumcheck PCS rank.
Thus merely widening G by one QM31 lane does not span the remaining semantic
quotient, even with a fresh nonzero factor.

A post-`alpha0` scalar-leaf mask is RED as well.  The exact probe models a
fresh degree-`<256` QM31 line word `M`, commits it before the nonzero `delta`,
and exposes only `tau=L(M)` plus one scalar `M(q)` at each of the sixteen
queries.  These seventeen QM31 observations have full rank 68 over M31 and
leave a 956-M31 (239-QM31) conditioned kernel.  Nevertheless the exact
`delta*M` carries through the first-later queried symbols, OOD values,
relation polynomials and final coefficients add no pivot to the baseline PCS
image: the rank remains `712`, and the conservative semantic augmentation
remains `716` with quotient rows 276 through 279.  The observation and empty
PCS-minor fingerprints are respectively `0xfd3ba7eec650b2d0` and
`0xe336f611bb58af3f`.  This negative result prices 272 value bytes for the
sixteen scalar openings plus `tau`; a separate root and Merkle frontier were
not priced because the candidate already fails the rank gate.

Multiplying the authenticated X source by the nonvanishing line polynomial
`p(t)=t^2+1` before injecting it into the first-later word is also RED.  The
literal probe retains the full `U`, raw X/F q view and exact
`tau=L(U+pX)` observation; it has observation rank 52 QM31 and kernel 18,
but its conditioned PCS image adds no pivot to 712 and the semantic quotient
remains 716 at rows 276 through 279.  Removing U is not valid: the no-U view
has rank 33 and its row-space union with U is strictly larger.  The diagnostic
now checks row-space containment explicitly rather than inferring redundancy
from equal dimensions.

Two smaller semantic-high switches are RED and, independently, physically
unbound.  For `V=span{x}+(t^2+1)P_<16` (dimension 17), the exact raw view has
rank 33 of 34 and a one-QM31 kernel, but the candidate moves `712 -> 716`
while the conservative semantic image then moves it again to 720.  Adding
logical `1` (dimension 18) leaves a two-QM31 raw kernel: the candidate moves
`712 -> 720` and semantics move it to 724.  More decisively, for any nonzero
`r in (t^2+1)P_<16`, the variation

```text
Delta X = r,  Delta F = -delta*r,  Delta U = 0
```

has zero selective old-view carry but nonzero authenticated query vector,
because evaluation on the randomness subspace is invertible.  Hence no local
identity can equate that selective carry with full `X(q)`.  The logical `x`
source is natural coefficient 1 / row 4, whereas the desired early carry is
natural coefficient 18 / row 72; reusing one host scalar does not bind them.

The literal claim-preserving repair was tested separately: put the complete
authenticated degree-`<35` X word, including all sixteen randomness
coordinates, into the W0 gamma lane and enforce the exact relation equation
`L(X)=0`, with no serialized `t_X`.  Its raw observation rank is 52 of 70
QM31 variables with kernel 18, but its conditioned PCS image remains exactly
712.  The same semantic quotient at rows 276--279 remains, so the result is
RED without even rotating the quotient.  The observation and empty-complement
fingerprints are `0xd6869ea69c9d94bf` and `0xe7dfb74bfb764493`; the zero
target removes 16 bytes and leaves a 1,072-byte shared-root diagnostic delta.
Machine-readable details are in
`results/stage2/profile21_physical_mask_rank_search.json`.

The first claim is incompatible with the proof currently used for it.  The
rank calculation treats 22,820 M31 mask directions as independent uniform
coins, while the prover deterministically expands one 256-bit seed.  The
implemented distribution has support at most `2^256`; a uniform 780-M31
affine image has size `(2^31-1)^780`, approximately `2^24180`.  Therefore the
implemented distribution is not statistically close to the uniform
distribution used by the translation argument.  This does not by itself
exhibit two colliding spend witnesses, but it invalidates the claimed
statistical simulation hybrid.

The selected closure route is now a **computational** random-oracle/PRG
construction.  Field masks remain pseudorandom expansions of fresh 256-bit
private entropy.  Every logical Merkle leaf additionally receives a private
256-bit salt; an opening reveals the salt for that leaf and no other salt.
This is not "Merkle salting is hiding": the affine masks hide opened values,
while private-leaf salts hide the roots and frontier nodes that authenticate
unopened values.  Both layers are required.

The private-leaf primitive and exact five-tree wire are now used by the
profile-21 candidate builder and verifier.  The literal unmined fixture is
`62,214` bytes with SHA-256
`a81bc7e2a89b37a799217314fd7b50d6ca05d665d4f6bcf0375436d2e79fa2c2`;
the complete host verifier accepts it, authenticates all five salted trees,
and the production verifier rejects its deliberately zero work nonces.
Default program builds remain fail-closed, and this host artifact is not a
mined SBF transaction measurement.  The exact EPRO theorem also remains
incomplete.  Thus implementation of the wire removes an engineering
ambiguity; it does not change the current RED complete-system claim.

Accordingly:

```text
atomic profile-21 affine field privacy       GREEN
statistical HVZK                             RED
computational ROM/EPRO wire                  IMPLEMENTED, THEOREM OPEN
complete shielded-spend privacy claim        RED
```

Soundness and privacy are intentionally separate gates.  The previous
pre-seam checkpoint used literal `Enc(U)(q)` checks at all 16 queries and
reported `107.28835414607816` union bits, or `102.2439600267197` bits after
factor 33 (`101.9664260511908` after factor 40).  Its separate `tX/muF`
source-target observation is now being retired, so those figures and the
rank fingerprints below must not be carried into the final claim unchanged.

The freeze candidate discloses `U` after source `g=38`, derives and absorbs

```text
tau = L(phi(U))
```

before the translated-W1 root/OOD, and preserves the round-1 OOD and boundary
checks.  Here `L` and `phi` are public frozen maps.  Literal q16 binding is the
soundness mechanism for a false `tau`.  For privacy, `tau` is a deterministic
function of disclosed `U` and the public schedule, so it adds no independent
rank row or simulator coin.  This candidate is not production evidence until
its natural-18/root-1 carry basis lands, the soundness ledger is replayed and
the exact affine rank is regenerated.  None of its soundness bits substitutes
for the EPRO/affine/privacy obligations in this note.

The theorem-level high-carry certificate is now explicit:
`profile21_high_switch_carry_certificate(q16)` proves that the 16 distinct
root-one evaluations together with natural coefficient 18 have rank 17 over
QM31 for every accepted q tuple.  The target-free source View is intended to
have rank 51 and kernel 19.  This is not yet an integrated full-rank result:
the current builder trace has no physical X-to-old-PCS carry splice, so the
780-M31 ambient claim and final fixture remain blocked until that splice is
implemented and replayed.

The concrete splice now under exact review authenticates X in the shared C2
lane and includes it in the main-gamma W0 at `gamma^28`, while F remains
source-only.  Its mandatory order is

```text
absorb base statement evaluations
sample kappa
compute xi = <eq_z + kappa*eq_z' + kappa^2*eq_xor
              + copy_inactive_indicator, X_message>
absorb xi
check main g38
sample gamma
```

The X root is already fixed before this sequence.  A post-gamma `xi` is
unsound because it would let the prover cancel the random linear combination,
so that ordering is explicitly rejected.  The inactive-indicator summand is
mandatory because the source-X support is not inactive-balanced.  U/tau
translation stays unchanged.
Unlike derived `tau`, `xi` is an independent affine public observation and
must be a row in the privacy matrix.  The intended invariant is that, after
fixing U, source q openings and `xi`, an 18-dimensional dX kernel still
physically changes W0/W1.  This paragraph is a design target, not evidence,
until both the literal rank replay and a builder differential confirm it.

## Selected private-leaf wire

For a commitment attempt identified by the public profile, statement digest,
layout fingerprint and burned mask nonce, give every logical leaf in every
tree a 32-byte private salt `r[tree,index]`.  The minimum wire-compatible rule
is

```text
leaf_digest = SHA256(0x10 || tree_tag || fixed_width_leaf_bytes || r)
```

where every `tree_tag` is unique in the profile and the leaf width is fixed by
that tag.  The Merkle position already binds `index`; including the index and
layout fingerprint in the preimage is a permissible hardening, but must be
costed because the current CU bridge has essentially no spare margin.  Node
hashing is unchanged.  An opened leaf record becomes

```text
fixed_width_leaf_bytes || r
```

and the verifier hashes the entire record before checking the existing
minimal-subtree frontier.  There is one salt per logical leaf, not one per
lane or field coordinate.  Consequently shared X/F lanes in the early C2
leaf use the C2 leaf's one salt.  The selected U binding discloses all 35
coefficients and verifies literal `Enc(U)(q)` at all 16 q positions with the
four-query fused QM31-by-M31 evaluator.  The authenticated translated-W1
difference supplies those q values, so there is no additional U tree.  If
integration nevertheless introduces one, it must be salted independently
and its opened salts counted.

The salts may be genuinely independent CSPRNG samples, but that would require
305,152 samples and about 9.31 MiB of retained salt material for the selected
five-tree layout.  Computational privacy does not require this.  A separate
domain-separated 256-bit leaf-salt seed may derive

```text
r[tree,index] = SHA256(
  DOM_LEAF_SALT || attempt_binding || tree_tag || index || leaf_salt_seed
)
```

on demand.  The leaf-salt seed and field-mask seed must be distinct PRG
domains, and the attempt binding must include the burned nonce so a crash or
retry cannot reuse either stream.  This replaces true independence with an
explicit SHA-256/RO PRG hybrid; it is not suitable for a statistical claim.

## Complete adversarial view

For fixed public atomic statement `x`, the view is not merely the opened
fields.  It is the tuple

```text
View = (
  full proof-account bytes,
  every root and authentication frontier,
  every opened raw leaf and field message,
  all Fiat--Shamir and work nonces,
  transaction accounts and instruction data,
  program logs, return data and observable failure/timing class,
  pool/nullifier/output account images before and after the instruction,
  optional receipt bytes
).
```

The one-transaction design has no receipt.  A split fallback must either copy
only values already covered by this view or add the receipt to the simulator.
`StateOnlyCompletePublicView` inventories these categories, but no production
constructor currently populates it from a tag-46/profile-21 transaction and
checks byte-for-byte coverage.

The atomic mutation itself introduces no new private field value.  Conditional
on `x`, the new pool root and sequence, public nullifier marker, output account
data, rent sizes and account keys are deterministic public data.  This only
means the state delta can be appended to a simulator output.  It says nothing
about the proof bytes authorizing the delta.

## The exact affine statement

Fix a public verifier schedule `c`, including every field challenge, OOD
point and distinct query position.  Let `R` contain the ideal independent
mask coins and the auxiliary `X,F` coins.  After quotienting only exact public
linear identities, the non-hash field view has the form

```text
Y_c(w,R) = A_c R + b_c(w).
```

For every valid same-statement witness difference `d`, privacy requires

```text
b_c(w+d) - b_c(w) in image(A_c).                 (1)
```

On the measured atomic schedule the rank gate proves the stronger ambient
statement: the selected image equals the entire declared 780-M31 PCS image,
and the masked zerocheck image equals its entire 1080-M31 quotient.  Hence
there is a mask translation `Delta_c,d` satisfying

```text
A_c Delta_c,d = b_c(w+d) - b_c(w).
```

If `R` is uniform in the ideal mask space, translation is a bijection and the
two fixed-schedule field views are identical distributions.  The gate also
checks the actual switch quotient rather than deleting identities by hand:
`U=F+delta X`, `AF=A(U)-delta AX`, the target identity, q co-openings, and the
translated-W1 equality are eliminated by exact field arithmetic.  The
selected direct-q extension has no isolated switch beta/OOD value or
equation.  A beta/Horner rank remains only as a labelled legacy diagnostic
outside the selected `View`.

The remaining universalization obligation is explicit.  One actual schedule
does not prove (1) for every schedule the random oracle can derive.  Production
needs either a symbolic invertibility/containment proof for all distinct q16
tuples and allowed challenges, or a canonical verifier-enforced rank gate plus
a proved, witness-independent termination law.

### Universal q-block audit

The masked-switch q block has a clean symbolic construction.  View
the 35-dimensional natural line code as ordinary polynomials of degree below
35.  Its natural basis element at index `j` is a product of the doubling
polynomials selected by the bits of `j`; it has degree exactly `j` and a
nonzero power-of-two leading coefficient.  Natural-to-monomial conversion is
therefore triangular and invertible over M31.

Define

```text
R = (x^2+1) * P_<16
M = span{1, x, x^18, ..., x^34}.
```

These spaces have dimensions 16 and 19 and intersect trivially.  Indeed, if
`(x^2+1)f` of degree at most 17 lies in `M`, it lies in `span{1,x}`; reading
coefficients from degrees 17 and 16 downward forces every coefficient of
`f` to zero.  Hence `P_<35 = R direct_sum M`.

For distinct query coordinates `q_i`, evaluation on the displayed basis of
`R` is

```text
diag(q_i^2+1) * Vandermonde(q_0,...,q_15).
```

M31 has prime order `2^31-1 = 3 mod 4`, so `-1` is not a square and every
`q_i^2+1` is nonzero.  The q sampler chooses positions without replacement,
and the canonical half-odds line domain has distinct M31 x-coordinates.
Thus this 16-by-16 block is invertible for every accepted q schedule.  An
exact natural-basis compilation of `R` now supplies universal q-randomness and
conditional X/F q-co-opening rank rather than measured-schedule facts.  The
compiled core object has fingerprint `0xceb35dd3ee50e051`; its generated
polynomials are checked against the real sparse circle encoder.  This switch
q block therefore needs no rank retry or discrete-q error term.

The baseline semantic masks have a second, independent all-q proof in the
actual direct tensor-coefficient representation.  It is important not to call
this a trace-Lagrange/Cauchy map: the frozen Aspis encoder feeds the
multilinear trace vector directly as coefficients in the Stwo tensor basis.
The atomic registry nevertheless exposes the same structural reserve in all
16 semantic columns:

```text
rows 896..=1023    relation-free and copy-inactive in every column
row 1023           common balancing coordinate
rows 896..=1022    127 independent directions e_r - e_1023
```

Write the circle tensor basis as
`B_j=[1,y,x,T_2(x),T_4(x),...]_j`.  Since `896=1110000000_2`, for
`0 <= j < 128`,

```text
B_(896+j) = B_896 * B_j,
B_896 = T_64(x) T_128(x) T_256(x).
```

Every displayed high factor is nonzero on the canonical half-odds
`G'_19` domain.  The 127 mask directions therefore evaluate as a nonzero
diagonal scaling of

```text
H = { f in L'_7 : sum_j coefficient_j(f) = 0 }.
```

For any 16 distinct query fibers, let their slot-zero x-coordinates be `x_i`.
The 64 opened circle points are distinct, so evaluation of the 128-dimensional
circle space `L'_7` onto them has rank 64 by the circle/GRS root bound.  Its
kernel contains

```text
g(x) = product_i (T_2(x) - T_2(x_i)).
```

This even polynomial lies in `L'_7` and vanishes at all four points of every
selected fiber.  But its tensor-coefficient sum is

```text
g(1) = product_i (1 - T_2(x_i)) != 0,
```

because a half-odds circle point never has `x_i=+/-1`.  Thus the evaluation
kernel is not contained in the coefficient-sum hyperplane, and restricting
evaluation to `H` still has rank 64.  Multiplication by `B_896` preserves that
rank.  This proves the semantic-mask q map is surjective for every accepted
without-replacement q16 tuple.  The mask-only C1 and each tower coordinate of
G contain the same block-supported zero-sum subspace, so the proof covers
their q maps as well.

The executable guard independently evaluates the tensor basis on the frozen
schedule.  It finds the exact common pivot set `896..959` for the 64 layer-zero
symbols and then `960..971` for the 12 M31 coordinates of the three terminal
MLE values.  Both now have a query-uniform explanation.

Put `t=T_2(x)` and decompose the lower 128-dimensional circle space into the
four sectors `{1,x,y,xy}` times the 32-dimensional natural t basis.  For every
q16 tuple the q64 kernel is exactly

```text
K_q = { g_q(t) h : h has 16 natural t coefficients in each sector },
g_q(t) = product_i (t-t_i).
```

The hyperplane condition is `h(1)=0`, since `g_q(1)!=0`.  Because `g_q` is
monic of degree 16, multiplication from natural h-degrees 12--15 in all four
sectors to output blocks 28--31 is triangular.  Its 16 diagonal entries are

```text
lead(B_l) / lead(B_(16+l)),       12 <= l <= 15,
```

four times each; they are nonzero and independent of every coefficient of
`g_q`.  One low h coefficient enforces `h(1)=0` without touching those output
blocks.  Thus `K_q intersect H` projects surjectively onto blocks 28--31 for
every q.

To prove the terminal Schur-complement polynomial is nonzero, evaluate it at
the legal QM31 assignment

```text
z = [1,1,1, 1,1,1,0,1, i,u],      i^2=-1, u^2=2+i.
```

The first terminal point is supported exactly on natural block 29, and its
four M31 coordinate rows span that block because `{1,i,u,iu}` is an F basis.
The xor point flips coordinates 6 and 7 and is supported exactly on block 30,
giving four more rows.  For binary successor, carry from the two low
coordinates is `a=iu` and stops at the zero in coordinate 6.  Its support is
only blocks 28--31.  Modulo blocks 29/30, restrict the kernel to output blocks
28--30 equal to zero; successor then reads block 31 with nonzero scale
`a(1-a)`.  Its two sector parameters are

```text
v=i+u-2iu,    w=1-u.
```

The set `{1,v,w,vw}` is an F basis: equivalently
`det{1,v,u,vu}=-5 != 0` in the frozen tower basis.  Successor therefore adds
the final four rows.  The terminal map has rank 12 on the q kernel for every
q16 tuple, so q64 plus terminal12 has rank 76.  This does not make the rank
full for every z; it proves that, for each discrete q, the mixed-M31 terminal
minor is a nonzero polynomial in z and may use the existing degree/SZ ledger
without a discrete-q retry term.

The machine-readable certificate is
[`results/stage2/profile21_terminal_all_q_certificate.json`](../results/stage2/profile21_terminal_all_q_certificate.json).

This does **not** yet set `eps_aff=0`.  Three independent minor families remain:

1. the new X/xi physical carry must be acceptance-integrated and its intended
   target-free rank-51/kernel-19 view replayed exactly;
2. its fixed-U/source-q/xi kernel must add the required old-PCS tail pivots
   modulo the baseline image; and
3. after quotienting the now-universal q64/terminal12 semantic block, the
   1080 masked-sumcheck, 712 post-sumcheck PCS, helper-containment and final
   ambient ranks still contain `z`, factor, gamma, OOD/mix and fold
   challenges.  `gamma=0` is an immediate example that can kill positive
   generator powers.

Nonzero eta/delta is already rejection-sampled.  The remaining minors need a
symbolic nonvanishing proof, an explicit bad-schedule/Schwartz--Zippel term,
or a verifier-enforced canonical rank gate.  The structural q blocks and the
terminal certificate remove q from this baseline semantic block; they do not
automatically remove q from every carry/PCS minor or remove the residual
field-challenge minors.

### Selected privacy-only `Good(schedule)` rejection

The selected closure for any residual minors is honest-prover rejection, not
an on-chain rank check.  Define `Good(profile,layout,schedule)` by the exact
public rank matrices used in this note, after replacing the q-randomness block
with the compiled MDS subspace above.  It must inspect only:

- the frozen profile and layout fingerprints; and
- public Fiat--Shamir coins/points/query positions in `schedule`.

It must not inspect witness cells, realized mask values, leaf salts, roots as
opaque byte strings, proof-carried `xi/U/tau` values, opened field values, or
any private prover state.  The prover burns a fresh attempt nonce, derives
fresh field-mask and leaf-salt streams, builds a full attempt, and emits it
only if `Good` holds.  A failed attempt restarts from a fresh burned nonce; no
failed root, proof byte, counter, log, or timing class is published.

For an auditable nonzero-polynomial bound, the build artifact must:

1. pin the exact row and column indices of one full-rank square minor for
   every remaining rank assertion;
2. evaluate each pinned determinant nonzero on the frozen green schedule;
3. propagate total numerator/denominator degrees through the exact matrix
   builder, representing the circle OOD point by its uniform parameter `t`
   and clearing every power of `1+t^2`; and
4. report the sum of the per-minor Schwartz--Zippel bounds, not merely the
   largest determinant degree.

The canonical elimination now records stable source columns, pivot rows and
pre-normalization pivot values for every block.  The frozen fingerprints are:

```text
raw openings 2244                 0xb8b9b449d82cc505
masked sumcheck 1080              0x9d1b1849b90c51d5
post-sumcheck PCS 712             0x2d950f0e11ab83e9
switch observation 208            0xd6be533d3afa238e
switch PCS complement 68          0xfe7946aa9db1eb0d
terminal q64 plus residual12       0xc4440d2f95d6441e
```

The 208-row switch observation minor is especially explicit: its source
columns are `0..207`, and its rows are all 140 U coordinates, the four `t_X`
coordinates, and the 64 `A(X)` query coordinates.  No beta row is present.
The 68 complement sources are `208..275`, with 64 later-opening and four
relation pivots.

Full QM31 challenges are uniform in a set of size `|QM31|`; line OOD samples
are uniform in `QM31 minus CM31`; and the circle sampler's parameter is uniform
in the same set after rejecting its poles.  Cleared denominators are nonzero
on those accepted sample spaces.  For a minor that is proved to be a
QM31-linear determinant *before* tower expansion, a degree-`D` nonzero minor
therefore fails with probability at most

```text
D / (|QM31| - |CM31|)
```

before unioning minors and random-oracle state-collision terms.  A pinned
minor at one q tuple does not bound a different discrete q tuple.  The final
artifact must either show every remaining q-dependent minor is MDS/nonzero
for all without-replacement q, or retain an explicit discrete-q term.

The current complete gate is not wholly QM31-linear: it expands semantic and
mask-only M31 source variables into an M31 matrix.  A determinant of that
expanded matrix is an M31 polynomial in the four base-field coordinates of
each QM31 challenge.  Plain Schwartz--Zippel for such a determinant has
denominator `|M31|`, not `|QM31|`; a degree below one million would provide
only about 11 bits.  Coordinate projection cannot be treated as a small-
degree QM31 polynomial.  Therefore the minor artifact must classify every
minor as either:

- structurally full rank (for example, an MDS/Cauchy evaluation map);
- genuinely QM31-linear before expansion, where the large-field bound above
  is valid; or
- mixed-M31, for which no 100-bit large-field SZ credit is allowed.

The promising baseline route is direct universal witness-difference
containment in the trace/value basis: choose explicit relation-free source
rows whose circle-to-RS generalized-Cauchy evaluation minors cover the q/OOD/
terminal observations, then quotient deterministic fold rows.  Proving that
containment makes the stronger ambient-rank minors unnecessary.

For the selected block-triangular 4,312-row minor, the executable degree
ledger now gives a conservative mixed-M31 numerator bound.  The rational
circle accounting is done in M31 coordinates: inversion of `1+t^2` clears
through its degree-eight norm in the degree-four extension.  The ten circle
tensor factors `y,x,T2(x),...,T256(x)` use total denominator exponent 512,
so one circle sample contributes degree 4,096 and the two-sample common
denominator contributes degree 8,192.  The resulting ledger is:

```text
target entry                                      8,207
PCS entry, including gamma^27                     8,490
raw determinant block                             3,240
masked-sumcheck determinant block                37,800
baseline PCS determinant block                6,044,880
switch observation determinant block             32,968
switch PCS-complement determinant block          577,320
combined determinant                          D=6,696,208
```

**Conditional on** this determinant being a nonzero field polynomial for
every accepted discrete q tuple, plain M31 Schwartz--Zippel gives

```text
beta <= D/(2^31-1) = 0.0031181648... = 2^-8.325087...
```

and hard retry caps 13 and 16 would make the public no-proof/completeness
terms at most about `2^-108.226` and `2^-133.201`, respectively.  These are
availability terms, not privacy errors for an emitted proof.

That conditional is still open.  The fingerprints prove the combined minor
nonzero at the frozen q tuple.  The two universal q-block theorems prove the
raw q ranks, but do not yet prove that the residual PCS/switch-complement
determinant is a nonzero field polynomial for **every** accepted q tuple.
Therefore neither `beta` nor either retry cap is production-bookable yet; a
discrete identically-bad q family cannot be repaired by the displayed SZ
degree calculation.

This retry argument cannot repair an unbounded discrete q family from one
green example.  The generated masked-switch MDS block and the common
896..1023 semantic-mask block above supply the mandatory q-universality.
Once that residual all-q theorem is supplied, `Good` rejection is only over
the remaining field challenges and is witness-independent in the ideal
hybrid, affects completeness/latency only, and leaves soundness untouched.

Conditioned on `Good`, the affine translation is exact and `eps_aff=0` for an
emitted proof.  The bad-schedule bound controls expected proving attempts and,
under a finite retry cap `R`, contributes only a completeness failure
`Pr[not Good]^R`.  It is not a soundness condition: the verifier need not and
should not spend CU recomputing the privacy rank.  Suppressing retry count and
timing is essential so conditioning remains a witness-independent prover
policy in the ideal mask/private-Merkle hybrid.

## Ideal EPRO simulator and required hybrids

The relevant compiler is Ben-Sasson--Chiesa--Spooner, *Interactive Oracle
Proofs*, Sections 3.2 and 7.4
([ePrint 2016/116](https://eprint.iacr.org/2016/116)).  Its simulator first
simulates the honest-verifier IOP view, simulates private Merkle paths, and
programs the Fiat--Shamir queries.  Applying that template here requires the
following hybrids in this order.

### H0: real profile-21 execution

The prover uses fresh private entropy and a burned public mask nonce, builds
all masked oracles, commits them, derives the transcript, mines every
positioned work nonce, serializes one proof, and mutates state only after
verification.

### H1: replace the mask expander

Replace the domain-separated SHA-256 seed expander by independent exact M31
coins.  This is **not** a statistical step for the current implementation.  A
computational ROM proof must assume uniform 256-bit private entropy and bound
the adversary's probability of querying either the hidden seed-derivation
input or an expansion input.  It must include all 2,857 expansion blocks in
the accounting, bounded M31 rejection sampling, seed/nonce collisions, and
adaptive post-proof queries.

The fixture's fixed `[0xd3;32]` entropy remains measurement data, not a
production randomness source.  The production host primitives are now
implemented in `crates/aspis-prover/src/state_only_entropy.rs` and pinned by
`results/stage2/profile21_entropy_nonce_closure.json`: `getrandom` samples
three independent nonzero 256-bit values (public nonce, private field entropy,
private salt seed), secret buffers use `Zeroizing`, and an append-only wallet
ledger burns the nonce with `create_new`, file `fsync` and directory `fsync`
before derivation.  I/O failure is fail-closed and partial reservations are
never removed.  Reopen, cross-statement and concurrent-reservation tests pass
3/3.  The profile-21 candidate builder now accepts reserved attempt secrets,
but no integrated mined artifact has exercised the durable production path.
The engineering artifact is not the H1/EPRO theorem.

### H2: translate the affine field view

Choose the honest-verifier schedule and use the rank/containment translation
above to sample a witness-independent field view.  This step is perfect only
with ideal uniform coins and only for schedules covered by the universal
containment theorem.  It includes the full sumcheck transcript, all three
terminal points, OOD values, final polynomial, opened leaves, translated W1
values, disclosed `U[35]`, and all 16 literal `Enc(U)(q)` evaluations.  The
pending physical carry splice also adds the one pre-gamma `xi` observation
defined above; it must be sampled by this affine simulator and included in the
final rank matrix, not treated as a derived public value.  The
selected verifier uses the exact four-query fused QM31-by-M31 evaluator
(`246,560` CU for the complete standalone switch artifact versus `432,820`
with generic QM31 evaluation).  It adds no `zeta` challenge and no eight-round
batch-evaluation sumcheck.  That batch alternative was measured at a
`339,783`-CU bucket, `39.7K` worse, and is rejected.  Retiring the literal q
checks without another reviewed binding is a soundness failure, not a privacy
optimization.

### H3: simulate commitments and paths

Given only opened leaves and indices, simulate each root and minimal-subtree
frontier.  Under the selected construction, sample the opened salts, compute
the opened leaf digests, sample independent random labels for maximal unopened
frontier subtrees, and run the ordinary node hash upward to the root.  The
only way a bounded distinguisher can expose this replacement is to query a
hidden salted-leaf preimage (or discover the salt-expander seed).  Internal
nodes need no salts.

The byte-exact private-leaf hash and five-tree aggregate wire are implemented
in the profile-21 candidate builder/verifier.  Every tree has a unique tag and
fixed value width.  The exact section wire is

```text
u16 count
(fixed_width_value || salt32)^count
u32 frontier_count
frontier32^frontier_count
```

Query indices are transcript-derived and omitted.  Leaves hash as
`SHA256(0x10 || unique_tree_tag || value || salt32)`; node hashing is
unchanged.  The retired 56,044-byte profile-20 fixture is unsalted and remains
only a historical comparison.  It is not used by any current privacy or rank
guard.

The selected shared-X/F, direct-U commitment inventory is:

| oracle | leaves |
|---|---:|
| layer-zero C1 | 131,072 |
| layer-zero C2 including X/F lanes | 131,072 |
| translated W1 | 32,768 |
| W2 | 8,192 |
| W3 | 2,048 |
| **total** | **305,152** |

There is no separate production U tree.  `U[35]` is disclosed, U(q) is the
authenticated translated-W1 difference, and the verifier evaluates the
disclosed coefficients literally at every q.  The tag-45 U tree is the
translated-W1 geometry stand-in/replacement and must be overlap-replaced,
never added.  The exact raw-C2/root0 rank probe says
sharing X/F into that pre-alpha root is field-rank neutral (`52/70` QM31,
kernel `18`) and preserves the universal 16-rank q block.  The exact private-
salt SHA A/B probe is in
`results/stage2/state_only_private_merkle_salt_probe.json`: on the five-tree,
80-opened-leaf schedule the literal salted path measured 1,200 CU lower than
the unsalted comparison, so the conservative ledger books **zero** salt CU
rather than a negative credit.  Shared X/F physically widens C2 by 2,048 wire
bytes and 1,027 CU; deleting the dedicated X/F tree saves 31,930 CU, for a
conservative net shared-root saving of 30,903 CU.  The candidate builder and
feature-gated tag-50 verifier now use this shared source binding.  The exact
five-tree host artifact is present and accepted; default builds intentionally
remain fail-closed, and a mined SBF/CU artifact is still absent.

On the actual atomic q16 schedule, all `q`, `q>>2`, `q>>4` and `q>>6` sets
have 16 distinct leaves.  The selected five trees therefore reveal exactly
80 salts, adding exactly

```text
80 * 32 = 2,560 bytes
```

to the unsalted five-tree wire.  The literal profile-21 artifact is 62,214
bytes: its beta-free prefix is 7,336 bytes, C2 is widened to 256 value bytes
per opened fiber, and the five private sections are 16,710, 14,150, 9,542,
8,006 and 6,470 bytes.  A separate X/F tree or U tree would add exactly 512
salt bytes on this schedule for each surviving tree.  Frontier hashes and
roots do not grow.

### What the BCS private-Merkle theorem actually requires

The generic statistical construction in Ben-Sasson--Chiesa--Spooner is
strictly stronger than `SHA256(tag || salt || leaf)` with a 32-byte salt.  For
a random oracle with `lambda`-bit output it:

1. samples an **independent uniform `2*lambda`-bit** `r_i` for every leaf;
2. stores `rho(v_i || r_i)` as the leaf and uses the same salt vector for root
   generation and every path;
3. reveals `(v_i,r_i)` only for opened leaves; and
4. simulates the truncated tree by replacing unopened leaves and then fully
   hidden internal subtrees with uniform `lambda`-bit labels.

It does not salt internal nodes.  Its full IOP-to-NIROP compiler also uses
separate random-oracle subdomains for verifier messages and Merkle/transcript
chaining, commits every oracle round separately, and programs verifier
messages at the exact chained states.  Our domain-separated single-SHA
transcript is not automatically that compiler and needs a protocol-specific
EPRO argument.

For SHA-256, the cited lemma therefore requires 64-byte leaf salts, not the
selected 32-byte salts, and gives error `n*2^(-256/4+2)`.  With 305,152 leaves
this is only about 43.78 bits.  Lemma 7.5 uses the more conservative
`p*2^(-lambda/4+2)` compiler term.  Using the approximately 625,999,872-bit
committed payload gives about 32.78 bits.  The selected 32-byte salt does
**not** instantiate that statistical lemma; its justification is the
bounded-query computational theorem below.

### H4: program Fiat--Shamir and work queries

Program every domain-separated transcript squeeze so that the verifier
reconstructs the schedule selected in H2.  The proof must cover cross-domain
input collisions among mask expansion, leaves, nodes, transcript absorption,
challenge squeezes and grinding.  The current single-SHA implementation has
distinct tags.  The conditional EPRO hybrid and its complete conservative
input ledger are given below; it becomes a complete system theorem only after
the affine `Good` predicate, final seam replay, PRG terms and release policy
are closed.

The byte-exact literal profile-21 fixture makes 51 squeeze-input calls and
seven work-predicate hash calls.  The selected beta-free schedule has seven
work records:

```text
batch g38; fold0 g39; source g38; fold1 g35; fold2 g31; fold3 g27; final g38
```

For challenge programming, the accepted-schedule cap is not a round count.
At most 65 base QM31 calls consume four squeeze blocks each, q16 consumes at
most eight blocks, and nonzero delta consumes at most three QM31 calls.  Thus

```text
P_FS = 65*4 + 8 + 3*4 = 280
```

programmed squeeze inputs suffice.  This count does **not** include transcript
absorb/advance inputs, Merkle hashes, or the seven work subdomains; those are
separate inputs in the complete EPRO collision ledger.

### Exact conditioned Fiat--Shamir blocks

Programming a field challenge means programming the complete byte stream that
the literal bounded sampler would have consumed, not simply writing the
16-byte field encoding into a SHA output.  For one M31 limb, a 32-bit word is
accepted when its low 31 bits are not `P=2^31-1`.  Conditional on an accepted
limb `a`, the word is exactly uniform over the two encodings whose low 31 bits
equal `a`; its high bit remains fair.  Each preceding rejection is uniform
over the two words whose low 31 bits equal `P`.  The simulator samples the
truncated geometric rejection count, places these words in the literal
eight-word block stream, and leaves every unused word uniform.  Repeating for
four limbs gives exactly the conditional distribution of
`challenge_qm31`; at most four squeeze blocks are used.

For `challenge_ood_qm31`, rejected outer candidates are sampled uniformly
from CM31 and the accepted candidate uniformly from `QM31 minus CM31`, with
the literal cap of three.  The secure-circle parameter sampler analogously
samples each rejected candidate from the exact union of its CM31/pole reject
sets and the final parameter from the accepted complement.  These are merely
success-conditioned product distributions; the explicit bounded-sampler
exhaustion probabilities remain completeness terms.

For q16 without replacement, first choose the desired ordered uniform tuple.
Before its `i`th new position, sample a geometrically distributed number of
repeats from the `i` positions already seen, then place the desired next
position; fill unused high bits and unused block words uniformly.  Condition
on completing within the literal 64-word cap.  This produces exactly the
candidate-word stream conditioned on that ordered tuple and success.  The
ordinary query-sampler failure probability is a completeness term and is not
silently replaced by an unbounded loop.

Every programmed squeeze block is cached at the precise
`state || DOM_SQUEEZE` input, and the independent `state || DOM_ADVANCE`
output becomes the next hidden transcript state.  Once the proof is released,
adaptive queries return those cached values exactly.  Before release, hitting
one of these inputs requires guessing its hidden 256-bit state; those events,
including all rejection blocks up to the 280-block cap, are charged in `C`
below.  Thus the conditional transcript distribution is byte-exact; the open
question is the affine choice of an acceptable public schedule, not the
Fiat--Shamir byte sampler.

The production CPU and Metal miners now return the canonical minimum valid
`u64` nonce.  CPU workers retire only after their next residue-class candidate
is no smaller than the shared minimum.  Metal completes each contiguous chunk
and takes the minimum across GPU streams before advancing the checkpoint.  A
fixed transcript has global minimum 100,214 on sequential CPU, parallel CPU
and Metal.  This is an honest-prover rule; the consensus verifier predicate
and CU are unchanged.

### Exact efficient minimum-nonce sampler

Fix one hidden work state `s`, difficulty `g`, `p=2^-g`, `q=1-p`, and
`n=2^64`.  In a random oracle the predicates for distinct nonces are
independent Bernoulli-`p` variables, so the minimum successful nonce,
conditioned on existence, has law

```text
Pr[K=k] = q^k p / (1-q^n),        0 <= k < n.             (3)
```

Here is an exact sampler that does not enumerate an expected `2^g` hashes.
Draw a lazy fair-bit real `U` uniformly in `(0,1)`, and set

```text
K0 = floor(log(U) / log(q)).                              (4)
```

If `K0>=n`, discard `U` and restart; otherwise output `K0`.  Correctness is
immediate from

```text
Pr[K0=k] = Pr[q^(k+1) < U <= q^k] = q^k(1-q) = q^k p.
```

Conditioning on `K0<n` gives (3) exactly.  Endpoint equality has probability
zero.  Equation (4) is evaluated without floating-point rounding assumptions:
after `m` random bits, retain the dyadic interval containing `U`; evaluate
`log(U)/log(q)` with directed-rounding arbitrary-precision interval arithmetic;
and emit only when both certified endpoints have the same floor.  Otherwise
draw another bit and raise the arithmetic precision.  The interval engine
must certify containment; a plain `f64` floor is not an implementation of this
sampler.

This procedure terminates almost surely because the dyadic and arithmetic
interval widths tend to zero and a uniform `U` avoids the countable boundary
set `{q^k}`.  It is also efficient.  Since `p<=1/2`,
`p <= -log(q) <= p/(1-p)`, so division by `log(q)` costs `g+O(1)` precision
bits.  The tail of `ceil(-log2 U)` is geometric.  Moreover the density of
`X=log(U)/log(q)` is `(-log q)q^x`; summing it over epsilon-neighbourhoods of
the integers gives `Pr[dist(X,Z)<=epsilon] <= 6 epsilon`.  Thus the expected
extra precision needed to separate the floor is constant, and the expected
random/working precision is `g+O(1)` bits.  Certified logarithms at that
precision take polynomial (or standard quasi-linear) bit complexity.  The
rejection probability is `q^n`, so the expected number of attempts is
`1/(1-q^n)`.

After sampling `K`, the simulator stores one lazy rule keyed by `s`.  A query
at nonce `j<K` receives an independently uniform failure output; `j=K`
receives an independently uniform success output; and `j>K` receives an
ordinary uniform 256-bit output.  Uniform success is sampled by fixing the
required leading `g` bits and sampling the rest.  Uniform failure is sampled
by rejecting a uniform output only when it succeeds, with expected cost
`1/q<2`.  Responses are cached.  Conditional on `K`, this is exactly the
product distribution of a random oracle conditioned on minimum `K`, so even
an adaptive distinguisher that checks arbitrary earlier nonces after seeing
the proof gets the real distribution without the simulator evaluating all
`K` positions.

Nonce exhaustion is at most `q^n <= exp(-np)`.  At the worst `g=39` stage it
is below `2^-48,408,812`; unioning seven stages is immaterial.

### Sequential hidden-state lemma

Let `s_0,...,s_6` be the transcript states immediately before batch, fold 0,
source, folds 1--3 and final work.  Condition on the preceding private-root
and transcript-programming hybrid not being pre-queried.  Inductively, the
input that produces the next state has a distinct transcript DOM byte and
contains the prior hidden uniform 256-bit state.  If it was not queried
earlier, its random-oracle output is a fresh uniform 256-bit state.  A
cross-family input equality would itself require matching that hidden state
and is charged by the same pre-query/collision ledger.  The sampled minimum
nonce is then absorbed before deriving the next state; because the work-output
digest itself is not absorbed, this preserves the induction.  Hence every `s_i`, conditioned
on the entire earlier simulated prefix, has 256 bits of min-entropy before the
one-shot proof is released.

An adaptive pre-proof query can therefore enter one of the seven grinding
subdomains only by writing the correct 256-bit `s_i`, giving

```text
Pr[pre-query work hit | preceding hybrid] <= 7 Q_H / 2^256. (5)
```

Possible collisions among the seven hidden work states add at most
`binom(7,2)/2^256`.  Once the proof is released, all states are public, but the
lazy conditional rules above answer every post-proof query exactly.  The
factor `sum 2^g` never appears: the simulator conditions a whole nonce
subdomain by one lazy rule rather than programming every failed nonce.

The canonical-miner engineering fact, exact minimum-nonce law, lazy response
rule and sequential work-state lemma are therefore closed, conditional on the
ordinary preceding EPRO no-pre-query event.  The numeric ledger below charges
that event rather than assuming it.  The unmined fixture still supplies no
production work witness.

### Attempt, retry and failure view

The only admissible privacy-only `Good(schedule)` policy is the following
bounded state machine, with `R<=16`:

1. sample fresh OS attempt entropy and durably burn its fresh public nonce;
2. build and canonically mine the complete attempt locally;
3. evaluate `Good` using only the frozen profile/layout and public schedule;
4. on failure, zeroize and discard every byte and local checkpoint, then
   restart with new entropy and a new burned nonce; and
5. emit exactly the first good proof, or emit no transaction after `R`
   failures.

No failed root, nonce, proof length, retry count, progress line or error code
may enter the proof account, program log, return data or network message.  A
remote miner would learn the hidden work states and invalidate (5); the
canonical miner must therefore be local/trusted, or its entire channel must be
added to the simulated view.  If wall-clock submission time is in the privacy
view, the wallet must release in a public fixed window independent of retry
count, or the simulator must reproduce the exact hardware/scheduler timing
law.  The repository implements OS entropy, durable nonce burn, zeroization
and canonical local CPU/Metal search.  It does **not** yet implement this
`Good` state machine or a fixed-release wallet policy, because the residual
all-q theorem needed to define the production predicate remains open.

### H5: append public execution data

The exact proof-account image is

```text
"ASPU" || proof_len_u32_le || upload_authority32 || proof_bytes.
```

Given the public upload authority, the simulator writes this header and the
already simulated proof bytes byte-for-byte.  Chunk-upload history, if part of
the view, is merely a public framing of those same bytes and must be appended
as such; it is not omitted from the claim.

Production tag 51 calls the profile-21 verifier with no diagnostic trace
callback, and the production atomic transition uses a no-op trace closure.
It sets no return data.  The `atomic50`/`atomic52` CU messages belong only to
feature-gated diagnostic instructions and are not a production privacy path.
The remaining runtime invoke/success records have fixed public shape.

After verification, the account branch (pre-created program-owned marker or
System-owned PDA creation) is part of the public environment.  Given that
branch and the public statement, the mutation is deterministic: increment the
pool sequence, install the public output anchor, and write a marker containing
the public pool key and nullifier.  Rent/payer deltas in the System branch are
also public functions of the supplied accounts.  There is no one-transaction
receipt.  Thus proof-account bytes, production logs and successful mutation
add no witness-dependent field beyond the simulated proof and public
statement.  A literal mined tag-51 transaction is still required as an
engineering/KAT artifact; the current 62,214-byte fixture is deliberately
unmined.

## Conditional computational theorem and exact error ledger

Let `N=305,152`, let `Q_H` be the total number of adaptive SHA-256
random-oracle queries made by the distinguisher (including post-proof
queries), and let `R<=16` be the bounded attempt count.  Assume:

1. the affine HVI simulator is exact on every accepted `Good` schedule, with
   any residual all-schedule translation error denoted `eps_aff`;
2. field-mask and leaf-salt expansion have distinguishing advantages
   `eps_field_prg` and `eps_salt_prg`;
3. every attempt uses fresh independent uniform 256-bit field-mask entropy
   and leaf-salt seed, plus a unique durably burned public nonce;
4. fixed leaf/node/expander encodings use distinct rigid domain prefixes,
   same-state transcript operations use distinct DOM bytes, and any remaining
   cross-family equality involving a hidden transcript state is charged in the
   no-prequery/collision terms rather than assumed impossible;
5. `Good` is a witness-independent predicate of the public schedule, and
   failed attempts are unpublished under the bounded state machine above; and
6. retries, timing, logs and account mutation contribute leakage
   `eps_side` (zero only under the stated fixed public view).

For one attempt, a deliberately conservative ideal-RO input inventory is

```text
salted-leaf preimages                              N
hidden leaf-salt derivation inputs                 N
hidden Merkle-node inputs (forest upper bound)     N
field/source expander inputs, bounded retries  46,260
seed/binding derivations (upper bound)              8
transcript: 46 absorb + 280 squeeze
            + 280 advance + 7 grind               613
                                                    -----
C                                                962,337
```

The literal no-rejection transcript is independently counted as
`46/51/51/7`; `613` uses the bounded `P_FS=280` cap for both squeeze and
advance.  The expander count uses all 16 allowed M31 candidate words, not the
2,857-block nominal path: 45,700 main-mask plus 560 source-mask blocks.
These are the last literal pre-`xi` counts.  If the physical carry splice
lands with one serialized/absorbed `xi` and no new challenge, absorb and `C`
increase by one (`46->47`, `962,337->962,338`) and must be repinned from the
final fixture.

The selected hybrid therefore has distinguishing advantage at most

```text
eps_priv <= eps_aff
          + eps_field_prg + eps_salt_prg
          + R*C*Q_H / 2^256
          + binom(R*C,2) / 2^256
          + 7*R*exp(-2^25)
          + eps_side.                                    (2)
```

The quadratic term conservatively charges programming/internal-label
collisions.  Fixed Merkle/expander families are rigidly separated; any
transcript-to-family equality requires a match to a hidden 256-bit state and
is included in the linear pre-query or quadratic collision term.  The PoW
term is the worst-stage nonce-space exhaustion union.  In the ideal-RO
expander model the seed-query events are already in `C`; in a standard-model
PRG claim the two explicit PRG advantages remain mandatory.

For the selected computational **ROM** statement, SHA-256 expansion is part
of the same domain-separated random oracle.  In that model
`eps_field_prg=eps_salt_prg=0`; guessing either hidden seed/input is already
charged by `R*C*Q_H/2^256`.  This is a model declaration, not a standard-model
claim about SHA-256 as a PRG.  A standard-model formulation must restore and
instantiate both explicit advantages.

At `Q_H<=2^128` and the worst `R=16`, the numeric random-oracle terms are

```text
R*C*Q_H / 2^256             = 2^-104.1238173269006
binom(R*C,2) / 2^256        < 2^-209.2476347474985
7*R*exp(-2^25)              < 2^-48,408,805
```

For one attempt the leading term is `2^-108.1238173269006`; the 16-attempt
factor costs exactly four bits.  This closes the **conditional EPRO and
canonical-PoW half** above 100 bits without inventing a birthday term or a
`sum 2^g` factor.  It does not close `eps_aff`, the standard-model PRG terms or
fixed-release side channels.  The 32-byte salts remain inadequate for the BCS
statistical lemma.

At `Q_H=2^128,R=16`, the 100-bit threshold is exactly
`C<2^24=16,777,216`.  The pre-`xi` inventory is about 17.43 times smaller;
the expected one-input `xi` delta is immaterial.  The margin is nevertheless
only 4.12 security bits, so every newly hidden hash family must enter this
ledger.  Public deterministic hashes can be evaluated directly by the
simulator, but any public query made before a programmed hidden state must be
included in `Q_H`.

Equation (2) is a conditional theorem, not a completed project claim.  In
particular, `eps_aff` is currently proved only for the measured schedule and
the profile-21 seam is still being optimized.  The residual all-q
nonzero-polynomial theorem and final post-seam rank replay remain the two
algebraic blockers.  The attempt manager/fixed-release policy cannot be
production-frozen until that predicate is frozen.  None of these open terms
is folded into the `2^-104.12` EPRO/PoW number.

### Exact simulator shape

The simulator proceeds attempt by attempt and round by round rather than
inventing all roots first:

1. for each of at most `R` attempts, sample fresh private entropy and reserve
   and durably burn a fresh public nonce before deriving any stream;
2. obtain the next witness-independent field answers from the affine HVI
   simulator for the chosen public verifier coins;
3. for each newly committed tree, sample salts for opened leaves, hash those
   records, sample uniform maximal-frontier labels for unopened subtrees, and
   hash upward to its root;
4. absorb the root and explicitly program the next transcript challenge at
   the same domain-separated state as the real verifier;
5. repeat through C1, shared C2/X/F, W1, W2 and W3, then serialize the exact
   opened values, 80 salts and frontier nodes;
6. reproduce the production work-nonce selection law.  The selected canonical
   minimum miner has the truncated geometric distribution above; the
   simulator lazily conditions all earlier failures and the winning output,
   rather than placing zero in the unmined diagnostic slot;
7. evaluate the public-schedule-only `Good` predicate.  Discard and zeroize a
   bad attempt without publishing its bytes, count, logs or timing class; emit
   the first good attempt, or the fixed public no-transaction outcome after
   `R` failures; and
8. serialize exactly `"ASPU" || proof_len_u32_le || authority32 || proof`,
   append the fixed production log/return-data view, and apply the
   deterministic public atomic mutation.

The same argument covers a receipt only if its bytes are a deterministic
projection of already-simulated public/proof fields.  The selected one-
transaction path has no receipt.

## Two honest closure routes

### Computational ROM/EPRO route

This is the selected engineering route.  It requires all of:

1. retain the implemented OS-generated 256-bit attempt secrets and durable
   burned-nonce ledger in the integrated production builder;
2. instantiate the two standard-model PRG advantages, or state the selected
   ideal-RO expander model, with the explicit `Q_H` budget below;
3. the exact 32-byte salted-leaf wire above on every selected tree, with
   salts revealed only for opened leaves;
4. close universal affine containment or the public-schedule `Good` gate and
   replay the exact rank after the final seam is frozen;
5. retain the exact EPRO input inventory and lazy canonical-minimum PoW law
   proved above for the final literal transcript;
6. implement the bounded retry manager and fixed-release/timing policy, then
   emit a mined tag-51 proof-account/mutation artifact; and
7. same-public-statement privacy tests at the affine-witness-difference layer,
   because constructing two concrete binding-collision spend witnesses is not
   a legitimate test strategy.

This route supports the conditional bound (2) and may support a 100-bit
**computational** privacy claim once its open terms are closed.  It is not
statistical HVZK.

### Statistical EPRO route

Sample the full independent field-mask space rather than expanding 256 bits,
use a private-Merkle output length at least 525 bits for the quoted BCS bound,
and carry the corresponding `2*lambda`-bit independent leaf randomness.  This
would substantially change proof bytes, hash primitives and CU and has not
been costed.  SHA-512 is still short under the conservative payload bound.

## Executable guards

`crates/aspis-prover/tests/profile21_hvzk_privacy.rs` provides:

- a byte-exact 62,214-byte fixture guard whose full host verifier authenticates
  five salted sections with 16 records each and value widths
  `416/256/64/64/64` bytes;
- a cheap support-size guard pinning the 256-bit seed versus the 22,820-M31
  ideal mask model;
- an exact q16 opened-leaf count guard pinning the shared-root salt delta to
  80 salts / 2,560 proof bytes;
- a registry guard pinning the common inactive relation-free block
  `896..1023` in every semantic column;
- an exhaustive rate-1/512 domain guard proving all 131,072 fiber
  `T_2(x)` coordinates are distinct, never one, and the common
  `T_64*T_128*T_256` factor never vanishes;
- an independent tensor-basis elimination guard pinning rows `896..959` as
  all 64 q pivots and `960..971` as the 12 terminal pivots on the frozen
  schedule;
- an all-q terminal certificate guard proving that natural h-degrees
  `12..15` project triangularly onto blocks `28..31` independently of q,
  and that the legal assignment
  `z=[1,1,1,1,1,1,0,1,i,u]` makes the terminal Schur complement rank 12;
- a byte-input counter pinning the literal profile-21 transcript at
  `46 absorb / 51 squeeze / 51 advance / 7 grind`, plus the beta-free bounded
  FS programming cap `P_FS=280`;
- a conditional EPRO/PoW ledger guard pinning `C=962,337`, the
  `2^-104.1238173269006` leading term at `Q_H=2^128,R=16`, the internal-label
  collision bound and the worst-stage nonce-exhaustion bound without marking
  complete system privacy;
- a mixed-M31 degree guard pinning the 4,312-row conditional determinant
  bound `D<=6,696,208`, its 13/16 retry-cap arithmetic, and an explicit false
  flag for the still-missing residual all-q nonzero-polynomial theorem;
- an ignored exact rank replay over the actual atomic proof, currently pinned
  as a pre-final-seam checkpoint with block fingerprints
  `b8b9/9d1b/2d95/d6be/fe79/c444`;
- an ignored full-proof smoke test showing fresh masks change C1, C2, every
  later root, the initial mask claim and the serialized proof.  Minimal-
  subtree proof length is itself schedule-dependent and is included in the
  simulator obligation rather than compared position-by-position.

The smoke test is deliberately labelled non-probative.  The public atomic
statement cryptographically binds the nullifier, input/output commitments and
Merkle roots, so obtaining two known valid concrete spend witnesses for the
same fixture would require finding binding collisions.  Universal privacy is
therefore tested at the affine witness-difference/ambient-containment layer
instead.

## Final verdict

The pre-final-seam fixed-schedule atomic rank deficit is closed and the
candidate privacy wire is concrete: computational field masks plus 256-bit
private salts on all five logical Merkle trees, widened shared X/F C2,
beta-free logical U, and literal q16 binding.  The exact salt delta is 2,560
bytes on the measured schedule.  Its salt-only SHA A/B costs no positive CU
(the ledger books zero), and shared X/F has a measured 30,903-CU net saving
over a dedicated tree.

The canonical-minimum CPU/Metal miner, exact truncated-geometric law, lazy
conditioned-RO responses and sequential seven-state lemma are now closed.
With the conservative `C=962,337` inventory, `Q_H<=2^128` and `R<=16`, their
leading ideal-RO programming term is `2^-104.1238173269006`; this is a
conditional EPRO/PoW component, not complete-system privacy.

The remaining red items are named: the residual determinant needs all-q
nonzeroness before its 13/16 retry caps are usable; the physical X/xi carry
splice must land and pass a fresh exact rank/build differential; the selected
claim must remain explicitly in the stated ROM unless standard-model PRG
advantages are supplied; the bounded retry/fixed-release policy is not
implemented; and no canonically mined tag-51 proof account has exercised the
production mutation.  Until those items instantiate
every term in (2), the one-transaction result must not be described as HVZK or
shielded.
