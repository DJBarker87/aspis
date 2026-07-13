# Aspis hiding note

Status: design gate, not a hiding claim. No implementation may be described as
"hiding", "zero knowledge", or "shielded" until every mandatory gate in this
note is closed by a proof argument and by the corresponding tests.

This note is deliberately separate from the soundness note. Soundness asks
whether a false statement can be accepted. Hiding asks whether an accepting
transcript reveals which witness produced it. A construction can pass every
existing corruption and rejection test while completely failing hiding.

## 1. Security objective and leakage surface

For a fixed public payment statement `x`, choose any two valid witnesses
`w_0,w_1` for `x`. The target is that the public distributions

```text
View(x, w_0; fresh prover randomness)
View(x, w_1; fresh prover randomness)
```

are indistinguishable under the final Fiat--Shamir and hash model. `View`
includes all of the following, not only the Merkle roots:

1. instruction data and proof-account bytes;
2. the payment zerocheck messages and its derived point `z`;
3. every terminal evaluation or replacement claim;
4. every C1, C2, fold-layer, mask-oracle, and final-polynomial opening;
5. Merkle roots, authentication paths, nonces, and derived query positions;
6. any receipt or intermediate account retained by a multi-instruction or
   multi-transaction fallback;
7. return data, program logs, account-size choices, timing classes, and public
   state transitions.

Proof size, the selected fixed profile, the public nullifier, output
commitments, fee information, and the fact that a valid spend occurred are
intended public leakage. Witness trace values, private note data, authentication
paths inside the private tree, and values derived only from them are not.

Merkle salting alone is not hiding. It may make a leaf preimage harder to guess,
but the current verifier directly receives 102 witness-derived MLE evaluations
and opens raw codeword symbols. Salting does not hide either channel.

## 2. Current concrete leak

Profile 13 serializes 102 QM31 values in point-major, column-major order:
49 C1 columns and two C2 helpers at each of `z` and `xor11(z)`. The payment
sumcheck derives `z`, after which the values are absorbed and gamma is sampled.
The PCS relation then gamma-compresses the 51 values at each point. The values
are proof messages, not public statement fields, so treating them as allowed
public evaluations would simply redefine the leak as an input.

The payment sumcheck itself is also part of the leak surface. Its ten degree-10
round polynomials are deterministic functions of the witness and transcript in
the current implementation. Hiding only the subsequent 102 values is therefore
insufficient.

The present 515,952-CU artifact is the payment-statement diagnostic alone. It
does not authenticate the 102 values with the PCS and contains no hiding. The
existing rate-1/16 PCS measurements are different measurement objects. They
must not be added to 515,952; the final number must be measured in one
instruction and overlap-subtracted by labelled phases.

## 3. Upstream invariant and why it is not a verbatim transplant

The inspected upstream reference is the public WHIR repository at commit
`10aa7d0bae3663fd149b6b88b6eff2209b867970`, especially
`src/protocols/whir_zk`, `src/protocols/sumcheck.rs`, and
`src/protocols/code_switch.rs`. It tracks the construction in
[Chiesa--Fenzi--Weissenberg, ePrint 2026/391](https://eprint.iacr.org/2026/391).

The useful invariant has two layers:

1. Sumcheck round messages are randomized, and the final claim is an affine
   combination of the real terminal claim and a mask claim.
2. Witness codewords are replaced by masked codewords. A separate committed
   mask family proves the mask contributions to queried and claimed linear
   forms, so the verifier can check the affine terminal identity without
   learning the unmasked codeword symbols.

The upstream `whir_zk::verify` API still receives its evaluation claims as
public verifier inputs. That is appropriate for a hiding PCS whose evaluations
are intentionally public. It is not sufficient for Aspis, because Aspis's 102
values are witness-derived internal terminal data. A direct wrapper transplant
would hide Merkle openings but preserve the 102-value leak.

Aspis therefore needs the sumcheck and proximity layers together. Neither one
alone meets Section 1.

Four transport obligations are currently open:

### 3.1 Circle code at rate 1/16

The upstream implementation is gated on ordered Reed--Solomon support. Aspis
uses the genuine circle encoder, a circle-to-line fold schedule, M31 source
columns, QM31 challenges, and rate 1/16. The hiding simulator and the
mask-code-switch rank argument must survive the same circle isometry used by
the soundness transport. These are coupled obligations: they cannot be closed
by proving the non-ZK circle transport and the RS hiding argument separately
unless a composition/isometry lemma explicitly joins them.

### 3.2 Derived-`z` payment zerocheck

The mask commitment must precede every challenge on which its values depend.
The ten payment-sumcheck challenges derive `z`; the mask must hide the round
messages and terminal data without allowing the prover to choose a mask after
seeing `z`.

The required terminal equation has the shape

```text
masked_terminal = mask_terminal + eta * real_terminal,
```

where `eta` is sampled after the relevant mask commitment. The verifier must
bind `mask_terminal` to the same mask oracle used to hide the codeword. It may
not accept a caller-supplied free scalar. The original zerocheck continues to
start from the public zero claim; masks must not be able to cancel a nonzero
constraint residual.

### 3.3 Gamma-RLC placement

Two placements must be prototyped and measured before selection:

* In-batch: masked witness lanes replace the current witness lanes and any
  required binding lanes join the existing commitment/RLC schedule.
* Separate: masked witness lanes stay in the current commitment while a
  dedicated mask-oracle commitment and opening proof are transcript-bound
  separately.

A naive in-batch layout that opens a masked symbol and the matching mask symbol
in the same wide Merkle leaf is immediately invalid, because subtraction
recovers the witness symbol. Any in-batch proposal must state which shares are
opened together and prove that the observed projection of mask randomness has
full rank. If it cannot do so, that probe is rejected before CU measurement.

Adding mask lanes changes the gamma polynomial degree and therefore the T5'
collision term. A separate commitment adds its own binding, proximity, Merkle,
and transcript error terms. Neither cost or soundness term may be hidden inside
the old 51-column ledger.

### 3.4 Receipt and public-state boundary

The one-transaction target has no inter-transaction receipt. Nevertheless,
proof-account bytes, logs, and mutated accounts remain public and are in
`View`. If a receipt-bound split is retained as a fallback, every receipt field
must be simulator-covered. A receipt containing unmasked terminal values or raw
opening symbols reintroduces the leak even if both verifier instructions are
locally hiding.

## 4. Preliminary leakage sizing for the current profile

This section is a sizing probe, not a theorem for the circle construction.

The upstream policy bounds per-polynomial leakage by

```text
q_ub = k1*q_delta_1 + k2*q_delta_2 + (d+1)*mu + T1 + T2,
```

and chooses the smallest `ell` for which `2^ell > q_ub`. The upstream
implementation sets `d=3` for its own cubic PCS sumcheck. Aspis's degree-10
payment sumcheck is an additional public view; it cannot simply replace that
`d` as though the two protocol shapes were identical. For the q36/fold-2 PCS
shape, the literal upstream defaults give

```text
k1 = k2 = 4
q_delta_1 = q_delta_2 = T1 = T2 = 36
mu = 10
q_ub = 4*36 + 4*36 + (3+1)*10 + 36 + 36 = 400.
```

This still selects `ell=9`. A conservative Aspis-wide leakage sizing that
charges the payment degree as well is

```text
mu = 10
d = 10
k1 = k2 = 4
q_delta_1 = q_delta_2 = T1 = T2 = 36
```

and gives `q_ub = 470`, hence the same `ell=9`. In either reading, the literal
upstream implementation creates a second blinding-side WHIR and sends
`weights * polynomials * (mu+1)` folded blinding evaluations. Its code-switch
verifier explicitly requires a mask-proximity verification against the same
mask tree; omitting that check breaks its soundness reduction. It is therefore
not a free one-column rewrite of the current circle PCS.

The count is per independently masked polynomial. It must not be multiplied by
51 if masks are independent, and it must not be reused unchanged if masks are
shared or packed. A shared/packed construction needs a rank bound for the
entire observed 102-evaluation and query projection. In particular:

* two QM31 terminal evaluations of one M31 polynomial require eight independent
  M31 output coordinates at the observed pair of points;
* source-field masks evaluated at QM31 points require a proved full-rank
  M31-to-QM31 evaluation map, including a bound on bad `z` values;
* the four raw arity-4 symbols opened per base query count separately in the
  leakage matrix even when they share one Merkle authentication path.

If the exact mapping forces `ell >= mu`, the current profile has no mask-size
slack and the construction must change; the implementation must not silently
truncate the mask.

### 4.1 Zero-width C1 padding probe

The frozen trace has a cheaper source of entropy than a literal extra mask
oracle. Rows after the semantic/copy slab contain cells which are not read by
the Boolean payment relation. A conservative rectangular subset is rows
857..1023 in columns 0..47: 167 random M31 cells per column, or 8,016 cells.
Column 48 is the range multiplicity witness and is deliberately excluded.

An independently derived dependency walk also reclaims unused cells in the
auxiliary slab. It finds 10,702 relation-free cells across columns 0..47. The
layout fingerprint is

```text
0xd1a049c458a39d93
```

and its exact per-column counts are 208..240. Randomizing all 10,702 cells at
once passes structural replay, both LogUp checks, and all 252 Boolean payment
constraints on all 1,024 rows. The helper values remain unchanged; inactive
range denominators record some random padding values but have zero weights.

For the conservative 167-cell subset, eight fresh fixed q36 schedules were
tested. For each schedule the exact M31-linear map from one column's padding to

```text
36 queries * 4 raw C1 symbols + 2 QM31 terminal evaluations
= 144 + 8 M31 coordinates
= 152 observations
```

had rank 152. The expanded layout also had rank 152 in every one of columns
0..47 for three fresh schedules. Thus this slice is an affine one-time pad for
the layer-zero C1 symbols and both terminal values under those fixed schedules.

This is a partial result, not a hiding result. The rank matrix does not yet
include column 48, either C2 helper, payment-sumcheck messages, OOD values,
later folded leaves, the final polynomial, or Fiat--Shamir adaptivity. The next
rank artifact must include the complete public view and prove a bad-schedule
bound rather than relying on sampled schedules.

This probe changes no column count, copy link, leaf width, or gamma degree, so
the existing copy-routing fingerprint correctly remains unchanged. The new
padding layout has its own fingerprint. If the helper-masking design adds
dummy copy/range links, the copy-routing compile-time fingerprint must then
fail and be deliberately regenerated.

### 4.2 Rejected free-terminal degree-10 mask probe

The payment sumcheck now has an isolated affine masking kernel. It samples 11
fresh QM31 mask coefficients for each of ten rounds (110 total), sends one
initial mask claim, samples a nonzero `eta`, and transmits the same ten wire
coefficients per round as the unmasked degree-10 protocol. For an honest round
polynomial `p_r` the verifier sees a polynomial `q_r` satisfying

```text
q_r(0) + q_r(1) = mask_claim_r + eta * original_claim_r.
```

After the round challenge, the same split holds at the next claim. At the
terminal:

```text
masked_terminal = terminal_mask + eta * real_payment_terminal.
```

For fixed challenges, the exact linear map from the 110 mask coefficients to
the 101 public fields (one initial claim plus ten transmitted coefficients in
each of ten rounds) has rank 101 over QM31. The wire is therefore uniform over
its full affine image and independent of the honest round polynomials. A real
depth-20 payment trace, including the expanded C1 padding, completes the same
terminal equation in the host prover/verifier test.

This kernel is not an accepting candidate. The `terminal_mask` is
prover-internal and unbound. Revealing it would recover the real terminal;
accepting it as a free scalar would destroy soundness. It remains as a
negative/reference test for the wire distribution only.

### 4.3 In-batch direct-range/helper-padding candidate

The range LogUp is the obstruction to zero-width masking. Its pre-`chi`
multiplicity column is constrained on all 1,024 table rows, and its QM31 helper
is then determined row by row. Adding arbitrary masks to either value breaks
the lookup identity; choosing a cancelling mask after `chi` would break the
challenge order and lookup soundness.

The in-batch probe will therefore remove that obstruction rather than hide it:

1. Store the six private 10-bit limb decompositions in two unused rows, using
   30 existing C1 columns for bits and three reconstruction cells per row.
2. Enforce beta-batched Boolean and reconstruction identities on those rows.
3. Add two fixed three-limb copy links from the reconstructed tuples to the
   existing input/output limb cells.
4. Remove the range multiplicity semantics from C1 column 48 and remove the
   range C2 helper entirely.

This retains the exact range `0..1023` relation with low-degree Boolean and
linear constraints. It changes the frozen registry, copy layout, C2 width,
statement value count, gamma degree, prefix shape, and every affected
fingerprint; it therefore requires a new profile rather than a repin of profile
13.

The host probe is now concrete: two rows hold the bit decompositions, 30
bit columns are beta-batched, three reconstruction columns are checked, and
two three-limb tuple copy links bind the six reconstructions back to their source
cells. Bit, reconstruction, and source-copy corruptions reject. Removing the
multiplicity semantics yields 11,611 independent C1 mask cells with layout
fingerprint `0x3a8106eb75a82cde`; the dependent last row makes every column's
helper-padding sum zero. For three fresh fixed schedules, every one of the 49
C1 columns had full rank 152 for its 144 raw q36 symbols and two QM31 terminal
evaluations.

The remaining copy helper has no real endpoints after the two bit rows. The
candidate reserves rows 866..1023 (158 QM31 cells) as helper padding, samples a
zero-sum vector there, and disables the row-local copy-helper identity only on
those padding rows. The active copy relation remains unchanged.

To stop a malicious helper mask from cancelling an invalid active copy sum,
the PCS relation adds the public linear claim

```text
sum_{row=866}^{1023} combined_message[row] = 0.
```

Every C1 column and the helper are sampled with zero sum on that region. Since
the combined message uses root-bound gamma powers, a cross-column cancellation
is a nonzero polynomial in gamma and receives its own exact collision term.
The interval indicator is the union of aligned Boolean subcubes and can be
folded as a small product-weight component; it does not require materializing a
1,024-entry verifier vector.

The helper has 157 independent QM31 mask values after the zero-sum condition.
The first required rank target is 146: 144 raw q36 symbols plus two terminal
evaluations. That exact 146-by-153 QM31 map has full rank for eight fresh fixed
schedules. The complete-view rank test must now include later leaves, OOD
values, relation sumchecks, the final polynomial, and the 101 masked payment
sumcheck fields jointly with all C1 padding. Until that rank passes and the
gamma collision term is in the ledger, this is only an in-batch probe.

### 4.4 PCS-bound degree-10 mask-oracle candidate

A single committed multilinear mask oracle is insufficient even when it is
multiplied by a public degree-nine factor. The product has degree ten and its
terminal is cheaply bound as `G(z) S(z)`, but after enough sumcheck folds one
multilinear oracle supplies only two fresh final-round values. Exact rank tests
rejected two plausible one-oracle factors at ranks 56 and 76 out of the 101
public sumcheck fields.

The candidate therefore commits independent QM31 mask oracles `G_k`, samples
a dedicated nonzero powers-generator challenge `kappa` after their roots, and
uses

```text
H(x) = sum_k kappa^k G_k(x) S_k(x),
S_k(x) = L(x)^(2k) (1 + L(x))       for k = 0..4,
S_5(x) = 1 + L(x)^2,
L(x) = sum_j (3 + 22j) x_j.
```

Every `G_k` is multilinear, so `H` has individual degree at most ten. The
initial mask claim is the Boolean-cube sum of `H`; it is absorbed only after
the mask commitment and before the nonzero affine-combination challenge
`eta`. The terminal mask is not a prover scalar:

```text
H(z) = sum_k kappa^k G_k(z) S_k(z).
```

For fixed fresh QM31 challenges, an exact 101-by-192 minor of the map from six
committed mask oracles to the initial claim plus the one hundred transmitted
sumcheck coefficients has rank 101. Five oracles reach only rank 100: the
previous running claim consumes one of the ten naive final-slice dimensions.
Six is therefore the first passing count for this construction. A real
depth-20 direct-range payment trace completes the masked sumcheck and the
verifier-computed terminal equation with no free correction scalar. The
`kappa` scaling is invertible per lane and therefore leaves the rank result
unchanged while putting the six-column binding collision into a powers-
generator form.

The public proof must not expose all six `G_k(z)` values: doing so introduces
avoidable correlations with the masked round messages. A first construction
bound only `H(z)` with a second rate-1/16 fold/relation path. Its full SBF row
was 824,600 CU and reconciled to within two CU of the overlap-subtracted phase
sum:

| rejected second-path phase | net CU above 25,267 setup |
|---|---:|
| relation | 93,993 |
| layer-zero six-column aggregation/fold | 401,621 |
| later folds/final | 219,394 |
| later Merkle | 84,327 |

This architecture is rejected. The fold path, not a local kernel, is the
dominant cost.

The selected candidate instead nests the six mask columns into the existing
single codeword. After the mask roots it samples `delta`; after the two-point
aggregate claims it samples nonzero `tau` and the outer `gamma`. The mask lane
weights are

```text
w_k = delta^k + tau * kappa^k * S_k(z),
```

and the entire mask lane enters the existing PCS as coefficient `gamma^50`.
The proof exposes, at `z` and `xor11(z)`, only the delta aggregate and the
factor-weighted aggregate. The main PCS point claim is therefore

```text
sum_{j=0}^{48} gamma^j C1_j(point)
+ gamma^49 h1(point)
+ gamma^50 (A_delta(point) + tau H_z(point)).
```

No second roots, later folds, queries, or final polynomial are added. The exact
host identity passes at both points. Extending the fixed-schedule rank matrix
with `H_z(z)`, `H_z(xor11(z))`, `A_delta(z)`, and
`A_delta(xor11(z))` gives rank 104: the first is the dependent sumcheck
terminal and the other three are independent mask-only forms, so the 101
sumcheck fields retain full conditional rank.

For the in-batch placement, C2 changes from the old two helpers to seven QM31
columns: the surviving copy helper plus six mask oracles. This is five more
QM31 columns than profile 13. For the separate placement, the six masks live
under their own root and small evaluation-binding proof. These are now the two
concrete objects the CU probe must compare; neither may quote the host
roundtrip as a hiding or soundness result until the aggregate evaluation is
bound and the complete public-view rank test passes.

The first placement-only SBF A/B is now recorded in
`results/stage2/payment_hiding_placement_v4.json` (Agave 2.3.0, five identical
runs per row):

| placement object | measured CU |
|---|---:|
| one in-batch 448-byte C2 leaf/tree | 652,356 |
| separate 64-byte h1 and 384-byte mask leaves/trees | 736,537 |

The separate tree costs 84,181 CU in the identical q36 envelope. This object
includes the masked ten-round sumcheck transcript, nonzero `kappa`/`eta`, the
fused six-factor table, the four aggregate claims, nested seven-column RLC
arithmetic, leaf hashing, and
six radix-4 authentication levels. It excludes the main payment terminal, the
main PCS folds/relation, proof parsing/account transport,
and the atomic transition. The numbers must not be added to an existing PCS
total; they select in-batch placement only. The common aggregate relation is
the next same-instruction integration. The superseded 567,463/651,638 rows
predated the nested delta/tau claims and must not be used.

### 4.5 Rejected current-layout virtual C1 mask oracles

Profile 14's first complete integration showed that carrying six independent
QM31 mask columns in C2 is structurally expensive. After the first exact query
and terminal rewrites, the overlap-subtracted verifier still costs 1,963,913
CU before the atomic state transition. The six masks add query arithmetic, 384
bytes to every C2 fiber leaf, and six full encoded columns even though the
direct-range trace already contains independently sampled relation-free M31
padding.

The tested candidate does not pack a circle fiber or change the circle code. It
defines six *virtual* QM31 multilinear mask polynomials from 24 existing C1
columns in fixed groups of four:

```text
G_k(x) = C_{4k}(x) + i C_{4k+1}(x)
                    + u C_{4k+2}(x) + iu C_{4k+3}(x),  k = 0..5.
```

The identity holds both for natural messages and their circle codewords,
because encoding and multilinear evaluation are M31-linear and the tower
basis is fixed. At a query fiber the verifier still reads the same M31 C1
symbols. It changes only their prepared weights:

```text
weight(4k+b) = gamma^(4k+b)
             + gamma^50 * basis_b
               * (delta^k + tau*kappa^k*S_k(z)).
```

Thus the nested mask lane is the exact same combined codeword as an explicit
six-QM31-column construction, but it requires no mask symbols in C2 and no
additional per-query products. The terminal values `G_k(z)` are the same
fixed-basis combinations of the already authenticated C1 evaluations. The
surviving copy helper remains the only C2 column.

This would be viable only if the C1 padding, rather than the witness-bearing
baseline of those columns, supplies the required entropy. The proof obligation
is affine: for every two valid witness baselines, their public-view difference
must lie in the image of the padding observation map. A full-rank abstract
QM31-oracle matrix transfers to the four M31 columns only when all four
selected padding cells are independent. The gate verifies that all 768 cells
in a candidate 32-row-per-oracle minor belong to the independently sampled
direct-range padding set, then expands the existing 101-by-192 QM31 rank minor
to its 404-coordinate M31 interpretation. A complete-view rank/coset test
would remain mandatory even if this local minor passed.

That gate fails on the current layout. A naive 32-row minor from the contiguous
late padding interval has rank 82/101. Selecting 32 available rows per oracle
from the complete relation-free layout—pinned by fingerprint
`0x3561be6114b11a77`—also has rank 82/101, and the matrix including the three
independent aggregate forms has rank 84 rather than 104. The padding cells are
numerous but remain confined to the late auxiliary slab, so they cannot
randomize all ten sumcheck rounds. Moving the two high row bits to the last
sumcheck rounds by a fixed coordinate permutation leaves the ranks at 82 and
84, so variable order does not rescue it. This candidate is rejected unless a
new trace layout distributes independent padding across the full Boolean cube.

Any redesigned construction may leave the copy-routing layout unchanged, but
it must add a separate virtual-mask mapping fingerprint over the 24 column
identifiers, selected rows, tower-basis order, and the C1 padding-layout
fingerprint. A change to any one of those inputs must fail the build until the
rank artifact is regenerated and reviewed.

### 4.6 Selected one-mask plus C1-padding profile

The next profile keeps the existing 49 M31 C1 columns, the padded QM31 copy
helper, and exactly one full-domain QM31 mask oracle `G`. Its C2 leaf is

```text
(h1, G)
```

or 128 bytes per four-slot fiber, rather than profile 14's 448-byte
`(h1,G0,...,G5)` leaf. The degree-10 payment mask is

```text
H(x) = sum_{j=0}^{48} basis(j mod 4) * C_j(x) * S_j(x)
     + G(x) * (1 + L_3(x)^9),

L_f(x) = sum_{v=0}^{9} (3 + 22v + f(17 + 8v)) x_v.
```

For group `g=floor(j/4)`, the `(family, exponent)` schedule for `S_j=L_f^e`
is

```text
g=0..4:   f=0, e=(0,2,4,6,9)
g=5..9:   f=1, e=(0,2,4,6,9)
g=10..12: f=2, e=(9,0,5).
```

Every `C_j` and `G` is multilinear, so `H` has individual degree at most ten.
The profile exposes the ordinary 49 C1 evaluations, `h1`, and `G` at each of
the two statement points: 51 values per point and 102 total. It uses the
standard powers generator

```text
sum_{j=0}^{48} gamma^j C_j + gamma^49 h1 + gamma^50 G.
```

There is no nested mask lane and therefore no mask `kappa`, `delta`, or `tau`.
This keeps the gamma collision degree at 50 and keeps the combined codeword in
the existing scalar polynomial-generator form. The masked payment terminal is
checked as

```text
masked_terminal = H(z) + eta * F(z),
```

where every term of `H(z)` is computed from PCS-bound statement evaluations.
The initial mask claim is the Boolean-cube sum of the same `H`; an inconsistent
initial claim is caught by the ordinary sumcheck boundary/terminal argument.

The exact M31 rank gates are now:

* C1 padding alone with the cheap factor family: 401/404. This fails and is
  not accepted as hiding.
* Adding late-slab copy-helper padding: still 401/404. It has the wrong support
  and is not counted as the missing entropy.
* Adding one full-domain QM31 `G`: 404/404 for the initial claim plus 100
  transmitted payment-sumcheck fields.
* After conditioning on all q36 four-slot openings and both terminal
  evaluations, every C1 raw-view block has rank 152/152, the `G` raw-view block
  has rank 584/584, and the remaining mask image has rank 404/404.

The joint conditioned test is
`one_explicit_mask_and_c1_padding_remain_surjective_after_all_openings` in
`crates/aspis-prover/tests/hiding_v4.rs`. It currently covers three
deterministic-random q36 schedules and challenge vectors. Before the profile is
called complete, the gate must cover the complete proof/account/log byte
inventory and a stated determinant-degree bound for the bad-schedule/bad-point
probability. The factor schedule, tower basis, C1-padding fingerprint, and
explicit-mask column identifier must receive one build-time layout fingerprint.

This construction is an exact affine masking rewrite. It does not use Merkle
salting as the hiding claim, does not expose an unbound terminal correction,
and does not require a second WHIR or a mask-proximity subprotocol.

### 4.7 Ordered queries without replacement

The q36 hiding-rank model conditions on 36 distinct rate-1/16 query fibers.
The profile transcript therefore samples an ordered tuple without replacement
from `N=4096`, rather than sampling with replacement and silently allowing a
duplicate to remove one row from the observation map. Candidate u32 words are
masked exactly into `[0,4096)`; duplicate candidates are rejected and the order
of first occurrence is retained. Conditional on success, every ordered
36-tuple of distinct fibers has the same probability.

This also gives the exact query-detection bound in hypergeometric form. If a
bad word differs from the target on `B` of the `N` fibers, the probability that
all q36 queries miss the disagreement is

```text
binom(N-B, 36) / binom(N, 36)
= product_{i=0}^{35} (N-B-i)/(N-i)
<= (1-B/N)^36.
```

Thus without-replacement sampling is no weaker than the old independent-draw
bound. Any rate-1/16 Johnson/MCA ledger must use the hypergeometric expression
or this upper bound consistently; it must not mix a distinct-query rank matrix
with a with-replacement soundness calculation.

The rejection loop is capped at 64 candidate words. Failure to collect 36
distinct positions then implies at least `64-35=29` collisions. Before
completion each candidate collides with conditional probability at most
`35/4096`, so a union bound gives

```text
Pr[query-sampler abort]
<= binom(64,29) * (35/4096)^29
< 2^-138.
```

This is an explicit completeness/statistical-distance term, not an accepting
soundness error: exhaustion rejects the proof. If the first 36 candidates are
distinct, the query bytes and post-query transcript state are byte-identical
to the prior sampler. The zero-nonce profile fixture pins that compatibility.
The sampler switch is a transcript protocol change and must be covered by the
consolidated profile-ID/KAT bump before the profile freezes; the identifier is
intentionally not bumped in this isolated patch.

## 5. Mandatory hiding tests

These tests are required alongside the first prototype. They are regression
evidence, not a substitute for the simulator/rank proof.

### 5.1 Leakage inventory test

The proof parser emits a typed map of every public byte range. The test must
show that no range contains an unmasked C1/C2 evaluation, an unmasked payment
sumcheck coefficient, or an unmasked queried codeword symbol. It also scans for
known witness canaries in every canonical field alignment. This catches the
simple "masked root, raw opening" class of bug.

### 5.2 Two-witness distinguishing test

Construct at least two materially different valid witnesses for the same public
payment statement. Generate many proofs for each with independent fresh mask
randomness. Compare per-position field distributions and byte distributions
between the two classes and run a held-out classifier. Canonical M31/QM31 byte
encodings are not uniformly distributed as bytes, so the comparison is
`w_0` versus `w_1`, not either class versus uniform bytes.

The test fails on any stable witness-dependent offset or classifier advantage
beyond its predeclared statistical threshold. Passing is only empirical
evidence; it does not establish zero knowledge.

### 5.3 Fixed-schedule affine-uniformity test

Use a host-only kernel in which the statement, query indices, `z`, and all
non-mask coins are fixed. Resample only the private masks. For each set of
opened linear forms:

1. build the exact linear map from mask coefficients to observations;
2. compute its rank over M31 (and the induced QM31 coordinate map);
3. assert that the rank equals the number of secret-dependent observed
   coordinates that must be one-time-padded;
4. compare sampled outputs against the predicted affine image.

This is the sharp test for reuse, deficient rank, conjugacy/subfield loss, and
correlation between `z` and `xor11(z)`.

### 5.4 Full transcript A/B test

Run the real Fiat--Shamir prover with fresh mask seeds. Because commitments
change downstream challenges, this test does not artificially pin the final
Fiat--Shamir challenges. It compares the complete public views, including
query positions, roots, nonces, proof-account layout, logs, and return data.

### 5.5 Reuse and failure tests

The suite must detect deliberately reused mask seeds, zero masks, one mask
shared across columns, missing mask lanes, co-opened cancelling shares, masks
sampled after `z`, tampered mask claims, and a receipt containing an unmasked
value. The production prover uses an OS CSPRNG with transcript/domain-separated
mask derivation; deterministic fixture RNGs are test-only.

## 6. Soundness and Fiat--Shamir gates

The new profile gets a new profile ID and transcript KAT. At minimum the frozen
schedule must bind, in causal order:

1. profile and public statement;
2. every masked-witness and mask-oracle root;
3. a domain-separated nonzero mask-combination challenge;
4. the randomized payment-sumcheck initial mask claim and every round message;
5. the derived point `z` and only the masked/replacement terminal claims;
6. gamma and any mask-lane batching challenge;
7. OOD data, fold roots, sumchecks, final polynomial, work witnesses, and
   query derivation.

Challenge-order teeth must move or delete each root/claim and demonstrate that
all downstream challenges change. A mask value chosen after the challenge it
is meant to hide or bind is a protocol failure, not a serialization detail.

The soundness ledger must add explicit terms for:

* degree-10 masked-sumcheck binding;
* terminal affine-combination binding;
* mask-oracle evaluation/code-switch binding;
* any extra gamma-RLC degree;
* mask proximity/list-decoding at rate 1/16;
* Merkle/hash binding for every additional root;
* bounded challenge-resampling completeness events.

The privacy ledger separately states the statistical or computational distance
of the simulated view, the allowed leakage budget, the mask-map bad-point
probability, the random-oracle/Fiat--Shamir model, and the exact circle-code
transport theorem. A numeric "110-bit hiding reserve" without these arguments
is not a hiding result.

The existing copy-routing layout fingerprint remains tied to the 49-column
payment layout. If hiding changes that layout, compilation must fail until the
factorization is regenerated and the new fingerprint deliberately pinned. If
hiding uses a separate oracle and leaves the payment layout untouched, the note
and test must establish that fact explicitly.

## 7. Measurement contract

Both viable placements are measured in the same SBF instruction envelope with
the same public statement, query profile, proof-account mechanism, and build
revision. The artifact labels at least:

```text
parse/framing
masked commitment transcript
masked payment sumcheck
masked terminal binding
existing PCS relation
existing PCS Merkle authentication
existing PCS query arithmetic
mask-oracle Merkle authentication (if separate)
mask-oracle query/arithmetic (if separate)
grinding/transcript
atomic state transition
dispatch/return/unlabelled remainder
```

The rows reconcile exactly to the measured instruction total. Integrated totals
are overlap-subtracted; no naive sum of standalone diagnostics is permitted.
Each artifact records proof bytes, account bytes, exact profile, git revision,
SBF toolchain, run count, variance, and every exclusion.

The placement is selected only after both probes have an algebraic privacy
argument strong enough to survive Section 5.3. A cheaper layout that co-opens
cancelling shares or leaves the 102 terminal values public is not a candidate.

## 8. Gates to a shielded-spend claim

All boxes are currently open:

- [ ] randomized degree-10 payment sumcheck with bound terminal mask;
- [ ] no public unmasked 102-value terminal block;
- [ ] masked C1/C2 and fold-layer openings;
- [ ] full-rank mask observation map at `z`, `xor11(z)`, and all queries;
- [ ] selected and measured mask placement;
- [ ] circle/rate-1/16 code-switch and hiding transport proof;
- [ ] Fiat--Shamir/public-transcript ZK argument, not only interactive HVZK;
- [ ] leakage inventory and all distinguishing/reuse tests;
- [ ] receipt/proof-account/log leakage audit;
- [ ] updated soundness and privacy ledgers;
- [ ] one-instruction payment + hiding + atomic transition below 1.4M CU.
