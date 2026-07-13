# State-only two-round payment trace candidate

Date: 2026-07-12

Status: **research profile; host layout/oracle foundations and exact SBF width
measurement complete, integrated proof construction in progress.** This
candidate is not a production proof format and must not be included in the
1.4M-CU claim until the prover, verifier, hiding view, transcript KAT, and
soundness ledger below are complete.

## Objective

The current overlap-subtracted profile-15 baseline after the exact copy
rewrite **and the mandatory pre-gamma batching nonce** is 1,564,821 CU. The only exact lever currently demonstrated at
six-figure scale is reducing the number of committed M31 trace columns
consumed by every layer-zero query.

## Integration freeze: what carries the wiring

The two-round composition deletes only the **within-pair intermediate**. It
does not delete a state boundary between composed pairs:

- committed row `r` in `0..10` is the input of composed pair `r`;
- the degree-25 transition polynomial computes the two consecutive Poseidon2
  rounds from that committed row;
- the three-point PCS binds the result to the same 16 committed polynomials
  at `succ(r) = r + 1`;
- consequently rows `1..10` are both the output boundary of pair `r-1` and
  the committed input boundary of pair `r`;
- committed row 11 is the final output boundary. Every sponge continuation,
  Merkle boundary, public digest, and semantic edge that leaves a permutation
  block is routed from this row, never from a virtual nonlinear value;
- committed row 12 is the absorption payload boundary.

Thus no uncommitted value crosses a composed-pair boundary. The only removed
cells are the first-round output and the other internal value of each
two-round pair. They are recomputed inside the constraint polynomial and are
not admitted to LogUp. This is enforced mechanically by
`intrinsic_state_cell`: only the 16 input lanes, row-11 final lanes, and
row-12 absorption lanes have intrinsic state-only cells.

The current generated surviving copy registry contains exactly 102 links:

| link family | count | committed interface |
| --- | ---: | --- |
| sponge continuation | 25 | row-11 final state to the next committed input |
| Merkle level | 19 | committed final/current/sibling rows |
| semantic ingress | 6 | committed auxiliary cells |
| absorption | 49 | committed row-12 payload cells |
| value reconstruction | 3 | committed direct-range triples |

The original links `0..489` are precisely the 490 intra-permutation edges
replaced by the successor identity. Original links `490..591` are remapped
in order to dense IDs `0..101`. The independent source/new endpoint walk,
row-local arity bound, Boolean replay of all 539 composed transitions, and
fresh off-domain optimized/reference equality tests are mandatory guards.

This answers the current wiring question for the existing statement. It does
**not** grandfather the planned atomic state-v3 migration. Replacing the old
two-permutation Merkle compression with the one-permutation ordered-node
compression keeps the total old-plus-new private-path permutation budget at
40, but changes block semantics and boundary edges. That migration must
regenerate the block schedule, copy registry, routing constants, active h1
registry, hiding registry, and every layout/factor fingerprint. A build that
retains the present 102-link or fingerprint constants after that migration
must fail.

### Production hiding instantiation

The complete-view rank probe requires ten mask-only M31 columns. Therefore
the live hiding candidate is not the provisional width-18 profile below. Its
opening order and algebraic dimensions are:

| object | live hiding candidate |
| --- | ---: |
| semantic C1 columns | 16 |
| mask-only C1 columns | 10 |
| C2 columns `(h1,G)` | 2 |
| scalar generator width `k'` | 28 |
| point claims | `3 * 28 = 84` QM31 |
| gamma collision degree | 27 |
| point batching | degree 2, `(1,kappa,kappa^2)` |
| zerocheck individual degree | 27 |
| transmitted zerocheck values | 270 QM31 |

For this exact width, the generated Johnson/BCS ledger reports 100.387473665
bits at rate 1/16, q36/g36/b24, and 100.504300041 bits at rate 1/32,
q29/g36/b26. These are ledger rows, not a complete privacy or transaction-fit
claim. The old width-18 rows remain useful only as the no-mask-column
diagnostic.

The suffix-only h1 padding repair is rejected by the full PCS view. The live
repair masks every copy-inactive h1 row and must satisfy all of the following
before it replaces that negative baseline:

1. the active-copy selector is generated from the exact 102-link registry;
2. the verifier enforces a public zero claim for the h1 mass on the complete
   inactive-row selector, rather than trusting honest balancing;
3. the ordinary all-row helper zero claim remains in force, so inactive h1
   values cannot cancel a nonzero active-copy discrepancy;
4. the mask image contains the complete active, zero-sum h1 subspace, not
   merely the difference of two fixtures;
5. an adversarial active residual deliberately cancelled by inactive h1 is
   rejected;
6. the inactive registry and its dense weight vector are absorbed into the
   layout/factor fingerprint.

The exact verifier form is a dense public `WeightAccumulator` term over the
1,024-row combined message. It adds no proof field, but its arity-four fold
work and memory are a separately measured relation-phase cost. A regional
interval claim is not an acceptable substitute because the inactive rows are
not one interval.

### Bridge ruling and integration gate

The later session ledger reconciles

`1,560,775 - 250,822 + 88,084 = 1,398,037 CU`.

The arithmetic is exact, but the 1,963-CU remainder is not credited as
headroom. The checked-in profile-15 artifact still records the earlier
1,564,821-CU baseline, so the 1,560,775 replacement must be emitted as a
named measurement artifact before it supersedes that file. In either case a
bridge is only authorization to integrate.

The integrated measurement must name, and must not model, these moving
planks:

| plank | required artifact |
| --- | --- |
| composed relation | terminal plus theta-lane phase markers |
| narrower Merkle leaves | exact authentication phase at q36 and q29 |
| reduced copy registry | generated-layout evaluator/reference parity and isolated CU |
| changed terminal | segmented Poseidon, copy, mask-factor, selector, and residual CU |
| hiding | full-view rank/containment, distinguishers, and incremental CU |
| atomic mutation | proof-bound output root, nullifier consume, account writes, rollback teeth, and incremental CU |

Only a production instruction that includes the proof, hiding, mined work,
canonical public-statement derivation, nullifier consumption, output-root
mutation, and all account writes may replace the bridge. The final reported
number is the literal transaction measurement or the ledger-defined
overlap-subtracted integrated total, never a naive sum of phase totals.

## Proposed physical layout

Keep the 1,024-row, rate-1/16 code and the 49 two-round Poseidon permutation
blocks. Replace the 49-column C1 table by:

- 16 committed Poseidon state/input columns.

The selected direct-range path does not consume the old multiplicity column;
that column belongs only to the retired lookup branch and currently supplies
mask entropy. It is omitted semantically. A seventeenth mask-only C1 column
remains an allowed fallback if the complete-view privacy rank fails at width
16.

Within each 16-row permutation block:

- rows 0..10 hold the inputs to each two-round transition;
- row 11 holds the final two-round output;
- row 12 holds the absorbed payload;
- rows 13..15 are payment-relation-free masking padding. The unmasked host
  projection initializes them to zero, but the production payment relation
  must not constrain them after masking.

At a Boolean row `r` in 0..10, the constraint computes both Poseidon rounds
from the 16 state values at `r` and compares the result with the same 16
polynomials at the binary-successor row `r+1`. The absorbed payload for row 0
is read from the row-12 shift. Auxiliary and direct-range values are spread
over additional unused rows rather than widening C1.

The PCS width becomes 18: 16 M31 C1 columns and the existing two QM31 C2
columns `(h1, G)`.

## Statement points

The statement opens the same 18-column gamma combination at three points:

1. `z` for the current state and helpers;
2. `succ(z)` for the binary-successor state;
3. `xor12(z)` for the absorption payload.

`succ` is the fixed polynomial arithmetization of binary increment. It maps
every Boolean row to its next Boolean row. The sumcheck oracle uses
`f(succ(z))` directly and the PCS binds that claimed evaluation. This is a
different polynomial representative from the multilinear extension of a
permuted table, but it agrees on the Boolean cube; its individual degree must
be included in the statement bound.

The three point equations require independent post-claim batching scalars (or
an explicitly equivalent multivariate collision bound). Fixed public scales
are forbidden because cross-point errors could cancel deterministically.

## Constraint degree

Two composed `x^5` rounds have individual degree 25. Multiplication by the
active-row selector gives degree 26, and the outer zerocheck equality factor
gives the conservative production bound 27. The successor-coordinate
representative must be checked not to exceed that bound.

The existing same-build SBF probe measures:

| statement polynomial | full coefficients | incremental verifier CU |
| --- | ---: | ---: |
| current degree 10 | 11 | 102,393 |
| candidate degree 27 | 28 | 190,477 |

The literal verifier premium is therefore 88,084 CU before any specialized
degree-27 evaluation kernel. The production verifier must stream one round at
a time; materializing all 4,320 sumcheck bytes on the SBF stack is forbidden.

## Copy routing

The 490 intra-permutation state links disappear: the successor opening checks
them directly. The remaining cross-block, Merkle-boundary, semantic-ingress,
absorption, value, and balance links refer only to committed state/auxiliary
cells and remain in a much smaller LogUp.

The wiring is therefore:

- rows 0..10 are committed transition inputs;
- `S(succ(row)) = R_{2r+1}(R_{2r}(S(row)))` replaces the ten ordinary
  intra-block links plus the final link into row 11 for every permutation;
- row 11 is a committed final-state source for sponge continuation, Merkle
  boundaries, and public digests;
- row 12 is a committed absorption-payload endpoint;
- auxiliary endpoints are deterministically repacked into rows 784..863;
- each Merkle selection uses an existing three-point triple: at `z`,
  `bit || current`; at `succ(z)`, `left || right`; at `xor12(z)`, `sibling`;
- the six direct-range limbs use two triples `(864,865,876)` and
  `(866,867,878)` so the three-limb reconstructions need no fourth point;
- rows 13..15 in every permutation block and the unused late slab remain
  unavailable to copy routing and reserved for masking.

The old registry has 592 links. Removing exactly 490 intra-permutation links
leaves an exact `m = 102`; the direct-range bitness/reconstruction equations
are ordinary constraints, not extra LogUp links. Every surviving tuple
contains at most the existing tag plus 16 state limbs, so `w = 17`.

Derived nonlinear round outputs must never be inserted into `h1` as though
they were multilinear witness columns. In general

`MLE(D(row))(z) != D(MLE(row)(z))`.

Doing so would make the helper relation false off the Boolean cube and break
the terminal identity. Final outputs are committed in row 11 specifically so
the surviving copy endpoints remain linear openings.

The exceptional routing constants and tensor factorization must be generated
from the new layout, bound to its hash, and compared with an independent walk
at at least 50 fresh random QM31 points plus the full adversarial corpus.

The host-only logical layout is now mechanically complete. It maps 2,434
retained logical old cells to 749 physical auxiliary cells. The 60 frozen
source equalities are structural aliases: both logical names resolve to the
same committed cell. The Merkle triples and remaining copy components reach
79 of the available 80 rows in `784..863`. The six range limbs occupy the two
triples above, with bits in columns `0..9` and the reconstructed limb in
column `10`; unused cells from rows 864 onward remain relation-free. Exactly
490 intra-permutation links are removed, leaving 102
dense surviving copy links. Independent old/new endpoint and value walks,
capacity/collision checks, row-local endpoint arity checks, and the pinned
layout fingerprint `0x121db4ec14af2130` pass on the host. The separate
relation-free mask registry has 5,374 column-major cells and pinned fingerprint
`0x1420cb9210f52636`. This remains a
production-neutral mapping foundation; it does not yet implement the new PCS,
prover, verifier, or copy helper.

No derived even-round output is admitted to the copy helper. In general,

`MLE(D(table))(z) != D(MLE(table)(z))`.

Putting a virtual nonlinear value into `h1` would therefore invalidate the
off-domain terminal identity even if every Boolean trace row passed. The
committed row-11 final state is what keeps the surviving LogUp linear and at
its existing degree.

The production-neutral semantic oracle is now complete. Its exact source
inventory is 95 lanes: 16 initial-state, 16 absorption-zero, 17 Merkle
selection, 33 direct-range, two value/balance, eight public-digest, two
public-asset, and one copy-LogUp lane. The 94 M31-valued lanes pack injectively
four-at-a-time into 24 QM31 lanes; copy remains the 25th. Together with the
four packed two-round Poseidon lanes, the provisional state-only randomized
constraint registry has 29 lanes and theta collision degree 28, before the
final hiding-mask composition is frozen. The copy helper has exactly 102
producer and 102 consumer values, so its pole union is recounted from 204
active denominators rather than the old 1,024-row cap.

The semantic oracle has degree at most 21 per sumcheck variable: direct-range
bitness at `succ(z)` contributes 20 and its activation selector contributes
one. Its outer zerocheck bound is therefore 22; the composed Poseidon branch
still dominates the complete statement at 27. All 1,024 Boolean rows,
relation-family corruptions, arbitrary rows-13..15 padding, lambda zero and
one, and 50 fresh random-QM31 optimized-versus-independent walks pass.

## Algebraic and transcript re-instantiation

The candidate is a new profile, not an implementation flag.

| object | profile 15 | state-only candidate |
| --- | ---: | ---: |
| C1 M31 columns | 49 | 16 |
| C2 QM31 columns | 2 | 2 |
| gamma generator width `k'` | 51 | 18 |
| MLE statement points | 2 | 3 |
| statement values | 102 QM31 | 54 QM31 |
| gamma collision degree | 50 | 17 |
| point-batching degree | 1 | 2 with scales `(1,kappa,kappa^2)` |
| payment sumcheck degree | 10 | 27 |
| transmitted sumcheck values | 100 QM31 | 270 QM31 |
| copy links `m` | 592 | 102 exact |
| copy tuple width `w` | 17 | 17 |

The roots retain their causal order: C1 commits first; lambda/chi are sampled;
C2 `(h1,G)` commits afterward; all 54 claimed values are absorbed, then a
separately framed batching nonce is checked and absorbed, and only then are
gamma and the post-values point-batching challenges sampled. No extra root or
commitment phase is introduced. The width-18 rate-1/16 Johnson row uses a
24-bit batching nonce provisionally; its final difficulty comes from the
frozen all-round ledger.

The baseline schedule change is already pinned independently of the future
state-only profile. Append-only wire tag 20 recomputes the full payment-v4 KAT
on SBF, including the batch nonce before gamma, both OOD samples, four fold
work records, final work, and the 36-distinct-query tail. Host and SBF match
`760bff524d283adf2aa1a9db38f2137d38dbd419dfddd436e1322552ed7615fc`;
the older tag-5 and tag-19 pins remain unchanged. State-only will receive its
own new profile/KAT rather than reusing this digest.

Local ledger lines to freeze with the implementation are:

- powers-generator batching: S-two Theorem 19 at the Johnson radius, plus the
  dedicated pre-gamma work filter (83.5359 unground bits for width 18 at
  rate 1/16; provisionally 24 work bits);
- three-point batching: at most `2/|QM31|`;
- degree-27, ten-round zerocheck: at most `270/|QM31|` before any tighter
  correlated analysis;
- copy tuple compression: at most `(102*17)/|QM31|`;
- copy poles: recount from the generated four-slot row registry, rather than
  retaining the old `1024` cap;
- theta/constraint batching: recount from the final state-only constraint
  registry; no profile-15 lane count is inherited.

The field size is unchanged, so the local algebraic terms remain above the
100-bit target. The separate circle/fold transport is closed at the Johnson
radius by the source-pinned reduction in
`stage2-johnson-transport-closure-2026-07-12.md`; the remaining task is to
regenerate its BCS union after the state-only registry and hiding view freeze.

## Expected CU direction

The corrected equally specialized width-16/17 SBF diagnostic is authoritative.
The arithmetic model at width 16 is:

- C1 layer-zero products per query: 784 -> 256 M31 multiplications;
- C1 block reductions per query: 224 -> 80;
- C1 leaf bytes per opened fiber: 784 -> 256;
- relation width/points: `2 * 51` -> `3 * 18`, while the gamma power table
  falls from 51 to 18 entries;
- 490 copy links and their routing evaluator disappear;
- degree-27 statement verification adds the measured 88,084 CU.

This shape is expected to save well over 200K CU if the exact width probe and
reduced-copy evaluator agree with the arithmetic model. No fit claim is made
from that projection.

### Rate-1/32 structural A/B

Rate 1/32 is an implemented alternative, not a soundness projection. The
Johnson ledger selects width 18 at `q29/g36` with a 26-bit pre-gamma batching
nonce and reports 100.821 BCS-normalized bits, versus 100.586 bits for the
rate-1/16 `q36/g36/b24` row. The prover and verifier now support the odd
Merkle depths by applying radix four until the final two-node level and then
one domain-separated ordinary binary cap. The exact geometries are:

| rate | layer-zero depth | later depths | queries |
| --- | ---: | --- | ---: |
| 1/16 | 12 | 10, 8, 6 | 36 |
| 1/32 | 13 | 11, 9, 7 | 29 |

Both complete width-18 opening paths pass host round trips through C1/C2
commitments, all four folds, the natural final tensor, and every query
equation; authenticated C1 corruption rejects. The rate-1/32 query count is
19.4% lower and the naive authenticated tree-level inventory is 11.1% lower.
This is the next six-figure SBF A/B, but no CU saving is credited until the
same integrated state-only proof is measured under both geometries.

## Soundness obligations

1. Boolean equivalence of every two-round transition and successor edge.
2. A finite-difference upper-bound test and a nonzero top-degree witness for
   the degree-27 oracle.
3. Three-point post-claim batching collision term and challenge-order teeth.
4. Ordinary scalar polynomial generator of length 18; no packed or
   matrix-valued generator is introduced.
5. Recomputed T1--T9 union ledger at rate 1/16, q36/g36.
6. Re-run the Johnson/BCS ledger from the proven transport reduction after the
   width-18 registry, 24-bit pre-gamma nonce, and hiding terms freeze.
7. Corrupt every sumcheck coefficient, every successor point coordinate,
   every state/aux column, and every retained copy endpoint.

## Hiding obligations

The profile-15 hiding proof does not transfer. Degree 27 exposes 270 wire
coefficients rather than 100, while C1 supplies fewer padding cells. The new
profile needs:

- per C1 column, q36 exposes 144 raw M31 layer-zero symbols and the three
  QM31 terminal evaluations expose 12 more M31 coordinates: 156 coordinates
  before combined later-layer observations;
- block rows 13..15 supply 147 independent candidate cells per column, which
  is insufficient by itself; the layout must reserve additional late-slab
  relation-free cells and prove the complete joint rank rather than count
  cells;
- the masked initial claim plus 270 transmitted QM31 wire values expose 271
  QM31, or 1,084 M31, coordinates which must lie in the image of the combined
  C1-padding and full-domain `G` mask map;

- a full transcript-and-proof `View`, including all three point rows, raw
  query symbols, proof-account bytes, logs, and atomic output accounts;
- a fresh adaptive rank/surjectivity proof for the exact mask variables;
- claim-preserving mask factors of sufficient degree;
- two-witness distinguishers, per-position comparisons, fixed-non-mask
  randomness tests, and receipt/account leakage tests;
- a layout fingerprint covering every maskable physical cell.

Merkle salting alone is not hiding and is not credited.

### Production-neutral state-only hiding rank candidate

The semantic layout now derives a column-major inventory of every C1 cell
which is excluded from the state, copy, direct-range, and public-binding
registries.  It contains 5,374 independently maskable M31 cells with per-
column counts

```text
[316,316,316,316,316,316,316,316,333,352,355,359,360,361,363,363]
```

and layout fingerprint `0x1420cb9210f52636`.  Rows 0..12 of every state
block, every remapped semantic/copy cell, and all direct-range bits,
reconstructions, and totals are excluded by construction.

The current public factor candidate uses the first fourteen C1 columns with
distinct dense linear forms and exponents `0,2,...,26`, then two independent
odd perturbations with exponents `13,25`.  Column `j` also carries tower basis
coordinate `j mod 4`.  One full-domain QM31 mask `G` uses factor
`1 + L_16^26`. Ten selected full-domain M31 mask-only columns use distinct
variable-local degree-at-most-26 factors. Every factor has individual degree
at most 26, so multiplying by a multilinear C1/G oracle gives a degree-at-most-27 mask polynomial. A
finite-difference guard checks vanishing 28th differences and a nonzero 27th
difference. The generated copy-active registry has 170 rows and fingerprint
`0xdfba37ae14a1a2cc`; the combined semantic-layout/factor/inactive-claim
fingerprint is `0x12672251efe5eafb`. The selected opening order is semantic C1 columns 0..15,
mask-only C1 columns 16..25, C2 `h1` at 26, and C2 `G` at 27.

`crates/aspis-prover/tests/state_only_hiding.rs` builds the exact rate-1/16
circle-code observation map for three deterministic-random, distinct-q36
schedules. The first version incorrectly sampled the terminal `z` and the
sumcheck challenge vector independently. That 1,084/1,084 result is withdrawn.
The corrected gate identifies `z` with the ten degree-27 sumcheck challenges
and uses `z,succ(z),xor12(z)`. For every corrected schedule:

- each C1 column has raw-view rank 156/156 over M31 (144 opened fiber symbols
  plus three QM31 evaluations);
- the explicit G has raw-view rank 147/147 over QM31;
- after quotienting both raw views, the one-G construction has rank
  1,040/1,084 over M31. The deficit is eleven QM31 coordinates.

One QM31 relation is unavoidable because the raw terminal openings determine
the final masked sumcheck claim, so the maximum quotient dimension is 1,080.
Ten additional independent full-domain M31 mask-only columns raise the ranks
linearly through
`[1040,1044,1048,1052,1056,1060,1064,1068,1072,1076,1080]`.
The same vector occurs on three rate-1/32 q29 schedules, where the raw blocks
are 128 M31 observations per C1 column and 119 QM31 observations for G. Thus
rate-1/32 does not reduce the minimum: nine columns stop at 1,076 and ten reach
the 1,080 terminal quotient.

The first width-28 construction was still not hiding: it left the separately
opened copy helper `h1` unmasked. Relation-free semantic mask cells are
structurally disjoint from every copy endpoint, and the ten mask-only columns
and G are not inputs to the h1 builder. Two independently valid spend
fixtures produced the exact negative tooth
`rank(M_mask)=0 < 1=rank([M_mask|M_diff])`. That construction is withdrawn.

The ordinary copy row equations also leave no affine helper freedom: with
nonzero denominators the residual is `h_i * product(denominators) - rhs_i`, so
each active or inactive helper value is unique. A successor-pair padding mask
was measured and rejected (rank 75 at q36 and 61 at q29 versus 147 and 119
public h1 coordinates). The suffix-only rows 868..1023 also fail the complete
PCS view by exactly one rank and remain a permanent negative tooth.

The live repair masks every row outside the generated 170-row copy-active
registry. There are 854 inactive rows and one global zero-sum dependency,
leaving 853 free QM31 helper masks. Every one of the 28 generator columns is
balanced on that same complete inactive set. The verifier adds one exact
dense inactive-indicator component to the ordinary PCS relation; no proof
field is added.

The fixed-coefficient two-claim version was rejected before freeze. Adding a
suffix-zero vector and an inactive-zero vector with coefficient one to the
same relation checks only their sum and permits deterministic cancellation.
Production therefore has exactly one inactive zero claim. Roots and all
column sums precede gamma, so invalid cross-column cancellation contributes
at most `27/|QM31|`.

The complete helper PCS view, including layer-zero symbols, three terminal
points, all later folds, OOD values, relation sumcheck coefficients, and final
coefficients, now has:

```text
rate 1/16 q36: outputs 539, mask rank 292,
                  witness-augmented rank 292,
                  full active-zero-sum augmented rank 292
rate 1/32 q29: outputs 487, mask rank 256,
                  witness-augmented rank 256,
                  full active-zero-sum augmented rank 256
```

Thus containment is universal for the complete active zero-sum helper
subspace, not only for two fixtures. A malicious active residual balanced by
inactive helper mass rejects under the dense claim.

Packing the 40-M31 deficit into three C2 masks does not rescue width. A scalar
QM31 factor adds only four M31 ranks per oracle (`1040,1044,1048,1052`). Giving
the four base coordinates independent factors reaches
`1040,1068,1084,1084`, but exceeding the 1,080 terminal quotient is the
negative tooth: four independent coordinate MLEs contain sixteen M31
dimensions and cannot be reconstructed from one QM31 off-domain opening.
Making that variant terminal-bindable requires four openings per oracle and
loses the proposed packing gain.

For a fixed query schedule and fixed direct M31 minor, a conservative
determinant-degree bound after substituting `z=sumcheck_challenges` is 24,000.
Because the actual map is M31-linear, ordinary Schwartz--Zippel gives only
`24000/(2^31-1)`, approximately `2^-16.45`; dividing by `|QM31|` is invalid.
The separate query-schedule audit proves a deterministic rank-116 layer-zero
slice for every distinct rate-1/32 q29 tuple. It does not prove the complete
MLE-plus-sumcheck quotient or an all-q36 minor. The honest prover must
therefore compute the canonical exact rank/containment gate after the actual
schedule is known and emit only a rank-good proof. This gives privacy
conditional on emission; the missing all-schedule minor theorem is an
availability/completeness boundary, not a verifier-soundness error.

The G-only negative gate is 163/271 on the production diagonal. A mask-reuse
tooth demonstrates that reusing one affine pad across two transcripts reveals
their unmasked difference exactly. The one-mask shortcut and reuse are
rejected.

The precommit helper now absorbs a public proof nonce and both layout
fingerprints before masked roots, then derives private masks from caller-
supplied secret entropy plus that transcript state. The public `View` type
includes proof bytes, parsed roots/openings, statement values, logs, and full
before/after state/nullifier/output account snapshots. These are implementation
foundations, not by themselves an FS zero-knowledge claim. The actual-schedule
rank gate, durable nonce storage, full transcript-conditioning/Merkle
simulation, and two-witness distinguishers remain mandatory before the
shielded claim is complete.

## Go/no-go gates

1. Exact q36 width-49/33/17 SBF A/B/C with canonical-byte and corruption
   checks.
2. Host state-only trace replay and complete Boolean constraint corpus.
3. Streaming degree-27 prover/verifier with transcript KAT and coefficient
   corruption suite. The production-neutral degree-27 wire and all 280
   coefficient teeth are complete; the new profile transcript integration is
   still pending.
4. Reduced-copy independent-walk identity guard and measured phase artifact.
5. Complete-view hiding proof and distinguishing suite.
6. Johnson soundness transport and exact union ledger.
7. Atomic nullifier/account mutation in the same transaction, followed by the
   final overlap-subtracted and literal transaction CU measurement.

## Earlier checked-in speculative bridge — not a fit result

The checked-in profile-15 artifact currently supplies these older inputs;
the later 1,398,037-CU session reconciliation is recorded in the integration
freeze above and must gain its own artifact before replacing them:

- integrated profile-15 after the exact copy rewrite and pre-gamma work
  check: 1,564,821 CU;
- isolated, equally specialized q36 N49 -> N16 layer-zero arithmetic:
  506,647 -> 255,825 CU, saving 250,822;
- isolated degree-10 -> degree-27 sumcheck-verifier premium:
  102,393 -> 190,477 incremental CU, adding 88,084.

Their arithmetic bridge is

`1,564,821 - 250,822 + 88,084 = 1,402,083 CU`.

The 2,083-CU deficit is still only a speculative arithmetic bridge. It omits
the changed relation, narrower Merkle leaves, reduced copy registry, changed
terminal composition, regenerated hiding construction, and atomic account
mutation. Only a complete integrated profile with all teeth green can replace
this bridge.
