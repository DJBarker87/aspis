# Profile-21 scalar-leaf late-mask audit

Date: `2026-07-13`

Status: **soundness-viable at Johnson without a new circle-transport
theorem; standalone complete HVZK red.**  A separate scalar `M` tree avoids
the widened-leaf disclosure that revealed all four masks beside a packed W1
leaf.  It does not repair the one-QM31 early-`p0` privacy quotient: the exact
rank replay adds zero pivots and leaves the conservative semantic rank at
`716/780` M31.

This is an interface proof and diagnostic ruling.  The six-tree parser,
transcript, relation injection, production acceptance path, EPRO simulator and
CU measurement do not exist yet.  No production file is edited by this note.

## Exact candidate and non-negotiable geometry

Let

```text
F = QM31,
Q = |F| = (2^31-1)^4,
D1 = the first line domain,
N = |D1| = 131072,
C1 = ev_D1(F[X]_<256) (or the exact pinned F-linear first-line subcode).
```

After the ordinary round-zero relation, fold work and challenge `alpha0`, set

```text
f = Fold_alpha0(W0) in F^D1.
```

The prover samples a 256-coefficient mask polynomial `m`, evaluates
`M=ev_D1(m)`, and commits a new salted scalar-leaf Merkle root.  It discloses

```text
tau = L(m),
```

where `L` is the exact post-alpha first-line functional exposed by
`first_later_weights`.  After a dedicated g38 work check, the verifier samples
uniform nonzero `delta` and the prover commits the ordinary masked word

```text
W1 = f + delta*M.                               (1)
```

The running relation target must be changed literally to

```text
r1 = r0 + delta*tau.                            (2)
```

All W1 OOD messages, later folds and the terminal check then use this actual
W1 word without another virtual mask lane.

There are two different leaf geometries:

```text
ordinary W1 root: 32768 leaves, 4 QM31 values/leaf,
                   logical value q is leaf q>>2, slot q&3;
scalar M root:    131072 leaves, 1 QM31 value/leaf,
                   logical value q is leaf q.
```

The second line is load-bearing.  A 32,768-leaf root with one scalar broadcast
over the four W1 slots is not the same line code and is not covered by the
proof below.  It would need a new interleaved/broadcast-code theorem.

For each of the 16 distinct logical queries, the verifier must authenticate
the scalar record `M(q)` and check

```text
W1_leaf[q >> 2][q & 3] - Fold_alpha0(W0_fiber(q))
    = delta*M(q).                               (3)
```

If two logical queries share a packed W1 leaf, equation (3) is still executed
once per logical query.  The M indices remain the 16 distinct raw query
indices, not the deduplicated `q>>2` indices.

## Completeness

The normalized first fold sends an honest W0 codeword into `C1`.  The mask is
sampled in that same code.  Linearity makes (1) another `C1` word, and
linearity of `L` gives (2).  Thus the later ordinary relation and FRI schedule
are unchanged after substituting the masked W1 word.

Promotion must pin that `C1` is exactly the code used by both operands.  If
the first-fold image is a strict linear subcode, sample M in that subcode and
invoke the linear-subspace form of the theorem; do not silently sample from a
larger RS supercode.

## Two-function Johnson/MCA proof

Condition on the transcript immediately after `root_M`, canonical `tau`, and
the accepted g38 nonce, but before `delta`.  At this point:

* W0 and `alpha0`, hence the entire virtual line function `f`, are fixed;
* the salted M root, hence the received function `M`, is fixed;
* `tau` is fixed; and
* W1 and every later oracle are still absent.

The random curve is the degree-one powers generator

```text
c_delta = f + delta*M,      Gen(delta)=(1,delta).
```

Apply S-two Theorem 31 (correlated agreement under linear constraints) to the
first-line RS code, or equivalently specialize Theorem 19's batching lemma to
two attached functions on one line domain.  This is also the degree-one case
of polynomial-generator MCA.  For the frozen profile-21 Johnson threshold,

```text
alpha = 1-theta = 1.05/sqrt(512)
                  = 0.04640388251536718,
rho_1 = 255/131072,
m = 10,
ell = (m+1/2)/sqrt(rho_1)
    = 238.05328123317761.
```

The number of field challenges for which `c_delta` is theta-close to `C1`
without common agreement of `(f,M)` is at most

```text
a = ceil(ell * ((2*ell^4/3)*rho_1 + 1) * N)
  = 129963047224011.
```

Because the sampler is exact-uniform on `F*`, rather than all of F,

```text
Pr[bad pair MCA]
    <= a/(Q-1)
    = 2^-77.1149051931.                         (4)
```

The positioned g38 work raises this round to `115.1149051931` work-normalized
bits.  The denominator is `Q-1`; using `Q` or the naked `1/(Q-1)` root bound
in place of (4) would undercount the correlated-agreement numerator.

The fact that W1 is committed after seeing `delta` does not defeat (4).  W1
may adaptively select a nearby codeword, but the random object in the theorem
is the already fixed pair's combination `c_delta`.  The later FRI list and the
common query branch either demonstrate sufficient agreement between W1 and
`c_delta`, which is precisely the event controlled by (4), or pay the query
miss event below.

Outside (4), the theorem supplies codewords `(p_f,p_M)` with joint agreement;
linearity supplies `p_1=p_f+delta*p_M`.  The already-proved first
circle-to-line fold/list commutation identifies

```text
p_f = Fold_alpha0(p_0),
```

and the ordinary WHIR Lemma 4.13 / S-two Lemma 4 cascade carries `p_1`
through every later fold.  M is introduced after the circle fold, so it never
needs a circle parametrization, circle isometry, or circle-code switch.

### Transport verdict

**No new circle transport theorem is required.**  What is required is a new
Aspis stitching lemma that instantiates the published same-line theorem at
`(N,k)=(131072,256)`, connects it to the existing first-fold list choice, and
uses the literal common-q seam.  That is protocol-local proof work, not an
unproved capacity conjecture or a new circle-code result.

This verdict fails if M uses a different ordering, a 32,768-symbol broadcast
code, a different coefficient basis, or a larger unpinned RS supercode.

## Query miss and decoded seam

The Johnson agreement cap on the first line domain is

```text
A = floor(alpha*N) = 6082.
```

The same ordinary q16 branch that checks the FRI path also checks (3).  If the
joint agreement set has at most A coordinates, its exact without-replacement
miss probability is

```text
C(6082,16)/C(131072,16)
    = 2^-70.9018865972,
```

or `108.9018865972` bits after the correctly positioned final g38.  This is
the existing main q16 row, not a second independent query credit.

After the MCA/list events have selected decoded polynomials, define

```text
d(t) = p_1(t) - Fold_alpha0(p_0)(t) - delta*p_M(t).
```

All three terms have degree below 256.  If `d` is nonzero it has at most 255
roots on the 131,072-point line domain, so all 16 distinct seam checks pass
with probability at most

```text
C(255,16)/C(131072,16)
    = 2^-144.7821287321,
```

or `182.7821287321` bits after final g38.  This stronger conditional seam row
may be unioned conservatively, but it cannot replace the main Johnson query
row and cannot be multiplied with it.  A previous 32,768-point calculation
used the number of packed W1 leaves as the polynomial domain; the actual
polynomial domain has 131,072 logical values.

The degree-255 argument is invalid on arbitrary received words.  It is used
only after pair MCA, ordinary list extraction and fold/list commutation have
identified the polynomials above.

## Wrong-tau binding

No on-chain 256-coefficient dot product is necessary, provided the relation
really consumes (1) and (2).  Condition on the good list events.  If `d=0`,
the W1 relation boundary gives

```text
L(p_1) = L(p_f) + delta*L(p_M)
        = r0 + delta*tau.
```

The already-bound base relation gives `L(p_f)=r0`; exact nonzero delta then
forces

```text
tau = L(p_M).
```

If `d!=0`, the decoded seam row above applies.  If the base and mask target
errors are both retained instead of conditioning on the base relation, their
equation is a nonzero affine polynomial in the precommitted `delta` and has at
most one root in `F*`; any joint-list multiplicity remains charged to the MCA
row, not erased by a bare `1/(Q-1)` entry.

The following variants are unsound or non-binding:

* adding `tau` instead of `delta*tau` to the relation target;
* serializing tau after delta or after W1;
* allowing zero delta, which removes the mask and all tau binding;
* checking (3) against unauthenticated M bytes;
* authenticating M at `q>>2` rather than at logical q; or
* updating a host-side target without the W1 relation polynomial consuming it.

## Mandatory Fiat--Shamir and work order

The exact causal schedule is:

1. Bind W0 and complete the round-zero OOD/relation message.
2. Verify and absorb round-zero fold work, then sample `alpha0`.
3. Commit and absorb a uniquely tagged salted depth-17 scalar M root.
4. Serialize and absorb canonical `tau=L(M)`.
5. Verify g38 against the state containing both root and tau, then absorb the
   labeled nonce.
6. Consume up to three fresh exact-uniform QM31 words and select the first
   nonzero `delta`; abort if all three are zero.
7. Commit and absorb the ordinary packed W1 root for (1), inject
   `delta*tau` into the running relation target, and only then sample any W1
   OOD challenge.
8. Bind every later root and final polynomial, verify and absorb final g38,
   then derive q16 without replacement.
9. Authenticate W0, the packed W1 leaves, and one scalar M record for each
   logical q; execute (3) once per q and continue the ordinary FRI checks.

Conditional on success, first-nonzero sampling is exactly uniform on `F*`.
The honest three-zero abort probability is `Q^-3`, or
`2^-371.9999999919`.  Each attempt must consume a fresh transcript word; a
zero word must not be rehashed or replaced by a biased fallback.

The current profile-21 source-work position cannot be reused by name alone.
The retained nonce predicate and transcript KAT must show that this candidate's
M root and tau are in the hashed state before work and delta.  A final nonce is
too late to normalize (4).  The literal BCS interactive-round factor must be
recounted after adding this oracle/challenge round.

## Scalar private-Merkle view

The generic private-opening wire already has the correct primitive shape:

```text
count_u16
(value16 || salt32)^count
frontier_count_u32
frontier_hash32^frontier_count
```

Only the selected scalar values and their salts are serialized.  The frontier
contains 32-byte hashes, not sibling values or sibling salts.  Thus a new
depth-17/value-width-16 section indexed by raw q has the intended property:
M siblings beside the selected coordinate are not opened.

The current aggregate profile-21 parser authenticates exactly five sections
with widths `[416,256,64,64,64]`; it does not authenticate this sixth tree.
Promotion needs a frozen sixth section with:

* depth 17, value width 16 and a unique tree tag;
* expected indices equal to the sorted 16 raw logical queries;
* strict count, canonical QM31, salt, frontier and trailing-byte checks; and
* a tooth showing that substituting `q>>2` or any W1 sibling index fails.

Every scalar leaf still needs an independent hidden 32-byte salt derived under
a distinct tag and entropy domain.  “Siblings are hashes” is a computational
ROM statement, not an information-theoretic deletion from the view.  The
private-Merkle/EPRO simulator must add this root, its 131,072 hidden leaves,
the 16 opened salts, frontier labels and no-prequery/collision inventory.

### What separate scalar leaves fix

Opening a widened `(W1,M)` packed leaf reveals all four W1 values and all four
M values, so the verifier reconstructs all four unmasked base values even
though only one logical coordinate was queried.  With the separate scalar
root, it learns M only at q.  At q,

```text
Fold(W0)(q) = W1(q)-delta*M(q),
```

but that value is already derivable from the opened W0 fiber.  The other
three W1 slots in the packed leaf remain masked by unopened M values.  This
removes the widened-leaf leakage mechanism.

## Complete HVZK ruling

It does not make the whole transcript hiding.  The round-zero relation
polynomial `p0` is transmitted before alpha0 and before M exists.  Every
post-alpha M direction therefore has zero image in the residual p0 quotient.

The exact production-geometry diagnostic uses all 256 natural first-line
QM31 mask coefficients, public `tau` plus the 16 authenticated M(q) values,
and the complete delta-scaled W1/later PCS carry.  It reports:

```text
M variables                              256 QM31
public tau + q observations               17 QM31
observation rank                           68 M31
conditioned kernel                        956 M31
baseline PCS rank                         712 M31
PCS rank after scalar M                   712 M31
new PCS pivots                              0
conservative semantic rank                716 M31
remaining semantic pivots          [276,277,278,279]
```

Those four pivots are one QM31 direction in the already transmitted p0 view.
The scalar-M search therefore gives an exact negative result, not merely an
entropy-count warning.  The 272-byte figure in the rank artifact counts only
the 17 public field values; it excludes the root, salts, path/frontier,
transcript bytes and verifier CU.

For unconditional algebraic witness indistinguishability, standalone scalar
M is **refuted**.  It can hide the later continuation and packed W1 sibling
slots, but a complete construction still needs a pre-alpha mask whose image
covers the p0 quotient, or a proved exact-language theorem that every valid
same-statement witness difference has zero projection there.  The latter is
currently an unresolved Poseidon hash-fiber statement and cannot be replaced
by computational witness uniqueness.

Even after adding a successful early mask, fixed-schedule affine containment
would not by itself prove Fiat--Shamir HVZK.  The simulator view must include
`root_M,tau,g38,delta,W1`, every later message, all six Merkle sections,
rejection/abort metadata, proof-account bytes, logs and atomic mutation.  It
must program the root-dependent challenge schedule in the private-Merkle/EPRO
hybrid and keep field-mask entropy independent from leaf-salt entropy.

## Final verdict and implementation gates

| property | verdict |
| --- | --- |
| exact honest algebra | viable, if (1) and (2) use the pinned line code and functional |
| two-function proximity | proven Johnson primitive; exact local stitching still required |
| new circle transport theorem | **not required** |
| capacity conjecture | not required |
| wrong tau | bound by relation plus nonzero delta after decoded seam |
| M sibling disclosure | avoided by the separate scalar root |
| standalone complete ambient HVZK | **refuted by exact rank / early p0** |
| current production acceptance | absent |

Before implementation can be selected, require:

1. a written attached-line lemma with the exact `(N,k)=(131072,256)` object,
   bound (4), and first-fold/list handoff;
2. a depth-17 scalar-root basis/order differential against production W1;
3. literal `r1=r0+delta*tau` relation consumption and wrong-tau teeth;
4. root/tau/g38/delta/W1 transcript KAT plus zero-delta and work-position
   weakening teeth;
5. a six-tree parser and prover with raw-q scalar indices and sibling-hash
   privacy teeth;
6. the updated private-Merkle/EPRO simulator and BCS round/input ledger;
7. a pre-alpha p0-covering mask or a genuine same-statement semantic closure;
8. complete-view all-q rank after that early repair; and
9. labelled proof-byte and integrated SBF CU measurements.

## Sources and executable anchors

* S-two, revision pinned in
  `docs/stage2-johnson-transport-closure-2026-07-12.md`, especially Theorem
  19, Theorem 31, Lemma 4 and Theorem 22.
* WHIR, Lemma 4.13 and Theorem 4.20.
* `crates/aspis-core/src/state_only_private_openings.rs` for the exact
  value/salt/frontier wire.
* `crates/aspis-core/src/state_only_profile21_openings.rs` for the current
  five-tree depth/width freeze.
* `crates/aspis-prover/src/state_only_hiding_rank/state_only_extra_mask_rank.rs`
  and `results/stage2/profile21_extra_mask_rank_search.json` for the exact
  scalar-M negative rank result.
* `docs/stage2-profile21-semantic-quotient-audit.md` for the remaining
  one-QM31 p0 quotient and same-statement reachability boundary.
