# Rate-1/32 circle mapping of the Plonky3 Hiding-WHIR pipeline

Status: upstream extraction and executable geometry only; not integrated and
not a circle-HVZK or one-transaction claim.

Date: 2026-07-13.

## Ruling

The upstream construction is a credible replacement for the rejected ad-hoc
ten-mask scheme, but it is not a drop-in proof of hiding for the current
circle protocol.

The exact source geometry is now pinned.  At the rate-1/32, q29, four-stage
profile, prefix-interleaved source randomness gives per-limb dimensions

```text
(message, randomness, domain, degree)
(256, 29, 8192, 284)
( 64, 29, 2048,  92)
( 16, 29,  512,  44)
(  4, 29,  128,  32).
```

This exposes a new load-bearing fact: `1/32` is only the unmasked message
rate.  The actual padded source-code rates are

```text
285/8192, 93/2048, 45/512, 33/128.
```

In particular, the final virtual source is a degree-32 polynomial in a
128-point code, not the current degree-three terminal at rate 1/32.  The old
q29 Johnson ledger cannot be copied onto it.  At rate `33/128`, q29 alone
contributes only about 26.315 Johnson query bits.  Any viable design must
re-derive the source spot-check and base-case soundness terms at these padded
rates or change the geometry.

There is a second non-transfer: Plonky3's implemented masked sumcheck is the
quadratic Boolean sumcheck of Construction 6.3.  Aspis has two separate
objects:

1. four internal degree-six arity-four PCS relation polynomials with boundary
   `4(c0+c4)` and fold weights `(1, alpha, alpha^2, alpha^3)`; and
2. the external ten-round degree-27 state-only zerocheck.

The internal object needs a new arity-four masked-sumcheck lemma and at least
`ell_zk=7`.  The external object needs a separate width-ten mask group, a
degree-27 generalization with `ell_zk=28`, and an explicit composition
handoff.  Neither claim follows from the current Plonky3 implementation.

## Primary-source pin

This extraction uses:

- Chiesa, Fenzi, and Weissenberg,
  [*Zero-Knowledge IOPPs for Constrained Interleaved Codes*](https://eprint.iacr.org/2026/391),
  ePrint 2026/391;
- the official [Plonky3 Hiding-WHIR source](https://github.com/Plonky3/Plonky3/tree/6b6a3b4d40fca2187d368c9dc1fca417c84ae8c3/whir/src/pcs/zk),
  pinned at commit `6b6a3b4d40fca2187d368c9dc1fca417c84ae8c3`;
- specifically `committer.rs`, `code_switch.rs`, `config.rs`, `prover`,
  `verifier`, and `base_case` under that tree, plus the cited Plonky3
  sumcheck implementation.

The executable local geometry is
`crates/aspis-prover/tests/rate32_hvzk_geometry.rs`; its frozen output is
`results/stage2/rate32_hvzk_geometry.json`.

## 1. Exact upstream pipeline

### 1.1 Prefix-interleaved source commitments

For a fold batch of `k` variables, upstream commits `2^k` columns.  Column
`b` is the DFT of

```text
message high-bit chunk b || private randomness chunk b || zero padding.
```

If the previous oracle will be opened at `t` positions, every limb gets `t`
independent random coefficients.  The initial prover therefore samples
`t*2^k` base-field values.  Folding an authenticated row by the same linear
leaf functional folds both the message chunks and the randomness chunks.
The result is a width-one padded code with `t` random coefficients.  This is
the implementation of Definition 3.22 and Lemma 3.26 cited in
`committer.rs`.

For Aspis's four-symbol fibers, `k=2` and q29 gives 29 random values per limb,
116 per committed source word.  This budget is per committed column.  It may
not be shared across witness columns merely because gamma later batches
them.  After a nonzero linear batch, the four limb randomness vectors fold
to one 29-coordinate vector.

### 1.2 Masked reduction and code switch

The upstream opening pipeline carries the linear relation

```text
<source message, source covector>
  + sum_i <mask message i, mask covector i> = target.
```

It first runs a masked sumcheck batch.  Each batch commits its mask codewords
before sending the mask claim and before sampling its combining challenge.
The source oracle's private coefficient chunks fold alongside the source
message.

Each of the three code switches then does the following in order:

1. commit the smaller residual source with fresh per-limb randomness;
2. commit a switch mask whose message is
   `old folded randomness || fresh OOD pad`;
3. sample private OOD points and reveal their padded evaluations;
4. open q positions of the previous source oracle;
5. batch the carried claim, OOD answers, and in-domain answers; and
6. run the next masked sumcheck.

The OOD pad has exactly one coordinate per OOD answer.  With the current
two-sample schedule every switch mask has message length

```text
29 + 2 = 31.
```

The pad is not optional slack.  Upstream's negative test and code comments
state that fewer pad coordinates expose a linear functional of the source.
The OOD points must be nonzero and pairwise distinct so their pad-coefficient
matrix is invertible.

### 1.3 Base-case one-time pad

After the fourth fold, the upstream base case does not reveal the terminal
source and carried masks directly.  It:

1. commits a fresh source-code mask `g` and one fresh blind for every carried
   mask group;
2. sends the fresh-side joint claim `mu_g`;
3. samples one challenge `gamma`;
4. reveals `fresh + gamma*secret` for the source message, source encoding
   randomness, every mask message, and every mask encoding-randomness vector;
5. checks one joint linear target identity; and
6. spot-checks the source and every carried/fresh mask pair.

Uniform fresh vectors used once make the clear reveals one-time padded.  This
is the algebraic content of the cited Lemma 7.3.  It is independent of circle
geometry, but its commitment consistency checks are not.

## 2. Rate-1/32 source geometry

The current trace has ten variables.  Four arity-four folds consume two
variables each, leaving a four-coefficient terminal.  Keeping the current
source domains and assigning q29 private coefficients per limb gives:

| stage | source message before fold | four limb messages | leaf rows | padded limb dimension | degree | effective padded rate |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 1024 | 4 x 256 | 8192 | 285 | 284 | 285/8192 |
| 1 | 256 | 4 x 64 | 2048 | 93 | 92 | 93/2048 |
| 2 | 64 | 4 x 16 | 512 | 45 | 44 | 45/512 |
| 3 | 16 | 4 x 4 | 128 | 33 | 32 | 33/128 |

The final virtual source exposed to the base case is therefore

```text
message length       4
randomness length   29
domain size        128
degree              32.
```

Using the same Johnson convention as the upstream configuration,
`1-delta = 1.05*sqrt(rho)`, the q29 query contributions before any separately
justified work are approximately:

| stage | q29 Johnson bits at padded rate |
| ---: | ---: |
| 0 | 68.214 |
| 1 | 62.641 |
| 2 | 48.827 |
| 3 | 26.315 |

These are not a replacement soundness ledger.  They show why the existing
rate-1/32 q29 result, which uses the unpadded circle-code rate, does not prove
the hiding extension.  The base-case consistency term and every source
oracle opened after padding must be re-budgeted.  The alternatives are to
increase domains/queries, stop folding earlier, use a different high-distance
ZK code, or prove a stronger construction whose error does not use these
padded RS rates.  None is selected here.

### 2.1 Query/randomness fixed point and g36

Holding the random padding at 29 while increasing the number of source
queries is invalid: upstream sets each oracle's randomness length equal to
the number of positions opened against that oracle.  Therefore the correct
conservative Johnson calculation solves the fixed point

```text
q * [-log2(1.05*sqrt((message+q)/domain))] + 36 >= target,
```

where 36 is one query-grinding work factor sampled after the commitments it
is meant to protect.  It is not 36 fresh bits per stage or per query.

At branch target 103, the first passing q values are

```text
stage 0: 29
stage 1: 32
stage 2: 47
stage 3: no solution on domain 128.
```

At branch target 104 they are

```text
stage 0: 29
stage 1: 32
stage 2: 48
stage 3: no solution on domain 128.
```

The last failure is absolute for this RS-plus-q-private-padding geometry,
not merely “q75 instead of q29.”  Increasing q also increases the final code
dimension.  Over every legal q, the best final-stage value is only about
64.05 bits including g36.  A 256-point final domain still cannot reach 104
bits; 512 points is the first tested power of two that can, at q41 for a
104-bit branch target (q40 for 103).

If 104 bits is required *after* unioning four source-stage branches, a simple
two-bit union allocation asks for 106 bits per stage.  On domains

```text
[8192, 2048, 512, 512]
```

the self-consistent stage counts become

```text
[30, 33, 50, 42].
```

These numbers use the upstream Johnson query formula.  They do not include a
new MCA/code-switch theorem or claim that the existing global BCS ledger may
reuse g36 here.  Crediting g36 requires one nonce fixed after every protected
root and before every query set, with its work charged once to the union.

### 2.2 Can one shared query set cover all source stages?

Not under the exact upstream theorem as implemented.  Plonky3 samples each
STIR query set inside its code-switch round, after the next source and switch
mask commitments for that round.  Replacing these sets with one late shared
set changes the IOR and its extractor schedule.

A separate late-query circle theorem could use one master set only if all of
the following are proved:

1. every protected source and mask commitment is fixed before the master
   query seed/grind;
2. projection from the initial fiber domain to each later domain is regular,
   so the preimage of a bad later set has exactly the corresponding density;
3. stage subsets are fixed, witness-independent prefixes or
   domain-separated samples, not prover-selected subsets; and
4. the union over the four correlated miss events is included explicitly.

Under those premises, correlation does not invalidate a union bound, and a
regular projection lets an initial-domain sample test a later bad set through
its preimage.  If every stage uses the same q, the maximum self-consistent
stage count governs and every source limb needs that much private randomness.
With a 512-point final domain and a 104-bit branch target, stage two forces
q48; using q48 everywhere raises all earlier padded dimensions and opening
costs.  A master set with fixed stage prefixes can instead use the
stage-specific counts, whose maximum still determines the master-set length
but not every Merkle opening count.

This shared-set construction is unproved.  On the current 128-point terminal
there is no maximum q to choose because the final fixed point has no
100-bit-class solution at all.

### 2.3 Padded-rate-preserving code-switch schedule

There is a cleaner candidate than increasing q inside the old domains.  Keep
q29 per limb, but choose each folded source domain as the next supported
power of two satisfying

```text
N_i >= 32 * (limb_message_i + 29).
```

This gives

```text
padded dimensions  [285,   93,   45,   33]
leaf domains       [16384, 4096, 2048, 2048]
interleaved symbols[65536,16384, 8192, 8192].
```

The exact effective rates and conservative q29 Johnson terms are:

| stage | padded rate | q29 bits | q29 + one 36-bit work factor |
| ---: | ---: | ---: | ---: |
| 0 | 285/16384 | 82.714 | 118.714 |
| 1 | 93/4096 | 77.141 | 113.141 |
| 2 | 45/2048 | 77.827 | 113.827 |
| 3 | 33/2048 | 84.315 | 120.315 |

Even the coarse bound `rate <= 1/32` gives

```text
29 * [-log2(1.05/sqrt(32))] + 36 = 106.4587 bits.
```

Unioning four source branches leaves 104.4587 bits under that coarse bound.
The exact rounded-domain minimum is stronger.

This resolves the padded-rate fixed-point failure at the geometry level.  It
does not by itself make one shared g36 valid.  There are two work schedules:

1. **Exact upstream-style sequential queries.**  Use the per-round PoW hooks
   already present in Plonky3.  For a 106-bit target per branch (104 after a
   four-way union), q29 needs only work exponents

   ```text
   [24, 29, 29, 22].
   ```

   The resulting branch bits are at least
   `[106.714,106.141,106.827,106.315]`; their four-way union is above 104.14
   bits.  These are four independent, correctly positioned grinds, not four
   credits for one nonce.  They add four verifier nonce checks but require no
   unproved shared-query scheduling rule.
2. **One late shared g36.**  This is compatible with the numerical bound only
   after proving the late master-query variant listed in Section 2.2.  The
   exact upstream IOR cannot simply reuse one final nonce for queries already
   sampled in earlier code-switch rounds.

The first schedule is the sounder next design target.  Its total prover work
is dominated by two 29-bit grinds, rather than one 36-bit grind, while the
verifier cost of checking four witnesses is small and must be measured.

#### Domain support and implementation compatibility

The initial object has 65,536 circle symbols, i.e. circle domain log 16.
Aspis's circle group has log order 31, and the current host encoder's domain
constructor accepts this size (`new_for_domain_log(16)`).  The later objects
are four line-code columns on domains of size 4,096, 2,048, and 2,048.  These
sizes fit the existing circle/line coordinate parameter ranges.

That is only domain support.  The current fold builder hard-codes one initial
domain and lengths divided by four at each round.  It would produce

```text
65536 -> 16384 -> 4096 -> 1024 -> 256
```

scalar evaluations, whereas the padded-rate schedule recommits interleaved
source oracles with total symbol counts

```text
65536 -> 16384 -> 8192 -> 8192.
```

Stages two and three therefore require genuine re-encoding/code switching,
not zero padding or a reinterpretation of the direct fold.  Even where total
sizes coincide at the first switch, the old folded code and the next
four-column padded code have different coefficient layouts and fresh
randomness.  Construction 9.7 is precisely the upstream mechanism intended
to bind this change, but its circle/arity-four adaptation remains one of the
new theorems in Section 6.

#### Base case

The last committed oracle has 2,048 rows of width four.  Folding a queried
row yields a virtual width-one source code with

```text
message 4, randomness 29, domain 2048, degree 32.
```

The fresh main OTP mask must be encoded in that exact 2,048-point source
code.  The base verifier opens q29 rows of both the last carried oracle and
the fresh main mask and checks the linear encoding equation.  The base source
rate is now `33/2048`, so the terminal padded-rate scissors is removed.

The base-case algebra is unchanged, but the current Aspis final-four tensor
check is not a substitute for this new source-code check.  The final domain,
proof serializer, Merkle root, query sampler, and verifier evaluator all
change.

#### Merkle and proof delta

Relative to the fixed-domain padded geometry, source leaf-tree binary depths
move from

```text
[13,11,9,7] to [14,12,11,11],
```

or deltas `[1,1,2,4]`.  For the production radix-four tree, the maximum
single-path sibling counts move

```text
[19,16,13,10] to [21,18,16,16].
```

The base case opens both the carried final source and a fresh-main tree at
the last depth.  Ignoring all multiproof sharing, q29 therefore adds at most

```text
29 * (2 + 2 + 3 + 6 + 6) = 551
```

32-byte sibling hashes, or 17,632 proof bytes, across the five source-side
multiproofs.  This is a pathwise upper comparison, not the expected minimal
subtree size; the exact serializer should be measured because q29 paths share
many nodes.  Mask-code trees are unchanged by this source-domain choice.

The larger domains also increase prover tree work and source index widths,
but not leaf width, number of source roots, number of mask groups, or q29
opened rows.  On-chain hash count and account bytes remain unmeasured.

#### Additional theorem obligations for this schedule

In addition to Section 6, the rate-preserving schedule needs:

1. a round-indexed encoder/isometry `I_i` for the four distinct domains;
2. a Construction-9.7 code-switch theorem from domain `N_i` to `N_{i+1}`
   under the actual circle/line OOD maps;
3. proof that fresh target randomness is independent even when total symbol
   counts stay equal or grow relative to a direct fold;
4. a per-round query/PoW transcript order matching the chosen
   `[24,29,29,22]` schedule;
5. re-derived Johnson/MCA/list terms for the padded source codes and their
   constrained circle subcodes; and
6. the 2,048-point base-case source spot-check theorem and implementation.

Therefore the schedule is **arithmetically viable and geometry-tested, but
theorem-unproved**.  It repairs the rate problem; it does not repair the
circle code-switch or arity-four masked-sumcheck gaps by analogy.

## 3. Required circle coefficient layout

The candidate layout must be defined through the actual local circle-to-line
transform, not by writing 116 values after the current 1024 coefficients.
The latter is not upstream's interleaving and has no proved folding identity.

At stage `i`, write the direct tensor message as four high-prefix chunks
`M_i,b`, each of the limb length in the table, and sample independent
`R_i,b in F^29`.  The intended line-side columns are

```text
A_i,b = M_i,b || R_i,b || zeros,  b=0,1,2,3.
```

Let `T_i,z` be the invertible, coordinate-dependent local transform used by
the current normalized circle-to-line fold at fiber `z`.  A circle HVZK
encoder must construct the authenticated four-symbol fiber so that applying
`T_i,z` exposes the four evaluations of the `A_i,b` columns.  Consequently,
the current powers fold must satisfy

```text
Fold_alpha(circle_ZK_encode(M,R))[z]
 = Enc_i(sum_b alpha^b M_i,b,
         sum_b alpha^b R_i,b)[z].
```

This equation is the required implementation identity.  It is not the exact
Plonky3 prefix-equality fold: upstream's Boolean batch uses independent
sumcheck challenges and an equality-table functional, whereas Aspis uses the
degree-three powers functional.  Linearity suggests the source-randomness
fold itself can be generalized, but a new arity-four protocol and simulator
proof are required.

The implementation probe to write after the theorem is fixed must compare
both sides at every domain position for random messages, random per-limb
randomness, and random non-subfield `alpha`, at all four stages.  A shape-only
test cannot close this identity.

## 4. Mask-code groups and 100-bit spot checks

Mask codes live over QM31 on ordinary two-adic subgroups.  QM31 has enough
two-adicity for these domains, so these small codes do not need a circle
transport.  Their rate is an independent parameter from the source circle
rate.

With three code switches, the upstream chronological internal group widths
are

```text
[SC0 width2, SW0 width1,
 SC1 width2, SW1 width1,
 SC2 width2, SW2 width1,
 SC3 width2].
```

That is seven commitments/groups and eleven flat mask codewords.  Upstream's
spot-check union target is

```text
100 + ceil(log2(2*3+2)) = 103 bits.
```

At a Johnson mask-code rate of 1/32 this gives

```text
t_zk = ceil(103 / -log2(1.05/sqrt(32))) = 43
```

spot checks per group.  For the mapped internal degree-six candidate,
`ell_zk=7`, hence:

```text
sumcheck mask code: message 7, randomness 43, domain 2048;
switch mask code:  message 31, randomness 43, domain 4096.
```

These are geometry, not a degree-six theorem.  The official Plonky3 code only
instantiates a quadratic Boolean plain piece and requires `ell_zk>=3`.

The external degree-27 zerocheck is separate.  Applying an appropriately
generalized mask construction to all ten rounds adds one width-ten group with
message length 28 and domain 4096.  The complete candidate then has eight
groups and 21 flat mask codewords.  Raising the branch-union target to 104
bits still gives 43 checks at rate 1/32.  This extra group must be committed
before the external zerocheck challenges and explicitly carried or settled;
it cannot be silently counted among the seven PCS groups.

The mask-rate trade-off is executable in the probe.  At degree 27:

| log inverse mask rate | Johnson checks at 103 bits | degree-27 mask domain | switch-mask domain |
| ---: | ---: | ---: | ---: |
| 1 | 240 | 1024 | 1024 |
| 2 | 111 | 1024 | 1024 |
| 3 | 73 | 1024 | 1024 |
| 4 | 54 | 2048 | 2048 |
| 5 | 43 | 4096 | 4096 |
| 6 | 36 | 4096 | 8192 |

The source rate being 1/32 does not force the mask rate to be 1/32.  The
on-chain optimum must be measured because fewer queries trade against deeper
trees and larger prover codewords.

## 5. Verifier CU-bearing objects

The upstream overhead is not ten extra scalar columns in the existing leaf.
It is a separate family of commitments, reveals, re-encodings, and Merkle
checks.

For the internal PCS candidate only:

- four source commitments total: the initial oracle and three smaller source
  oracles;
- seven carried mask-group commitments;
- at the base case, one fresh main-mask commitment and seven fresh
  mask-group commitments;
- three q29 source multiproofs during code switches;
- at the base case, one q29 source multiproof, one q29 fresh-main multiproof,
  and fourteen 43-position mask multiproofs;
- 19 authenticated multiproofs total;
- 655 clear QM31 OTP-reveal elements before the one masked-claim scalar:
  `33` source elements plus
  `8*(7+43)+3*(31+43)=622` mask elements;
- a terminal target dot over 153 mask/source message coordinates;
- approximately
  `8*43*(7+43)+3*43*(31+43)=26,746`
  QM31 coefficient steps just to re-encode the blinded internal masks at the
  sampled positions, before source re-encoding, Merkle hashing, transcript,
  and equality checks.

Adding the separate external width-ten, `ell_zk=28` group raises this to:

- eight carried and eight fresh groups;
- 21 multiproofs;
- 1,365 clear OTP-reveal elements;
- a target dot over 433 message coordinates; and
- another `10*43*(28+43)=30,530` mask re-encoding coefficient steps.

Thus the complete candidate performs roughly 57,276 QM31 mask-code
coefficient steps at the base case alone.  This is not a CU estimate because
multi-point evaluation, batching, and specialized SolMath primitives could
change the implementation count.  It is the exact naive verifier object that
must be attacked before integration.  In particular, the upstream statement
that overhead is negligible is asymptotic in the witness length; it does not
imply negligible Solana verifier cost at this small terminal.

Potential structural optimizations such as a shared multi-point evaluator,
merging same-shape fresh base-case commitments, or a forest multiproof are
protocol deviations.  They should be probed after the reference geometry,
with exact acceptance-equivalence and privacy arguments.

## 6. What survives, and what does not

### 6.1 Facts that survive exactly

The following are exact once their stated premises are met:

1. A coordinate permutation followed by nonzero coordinate scaling is a
   Hamming isometry.  Therefore the existing circle-to-GRS identification
   preserves distance, agreement, and list sizes of a fixed scalar code.
2. Uniform one-time-pad identities such as `g + gamma*f` are field-linear
   and survive over QM31 without reference to the evaluation domain.
3. The small mask codes can remain the exact ordinary QM31 Reed--Solomon ZK
   encodings used upstream.  Their mask-code distance and spot-check theorem
   need no circle analogy.
4. Once a circle source encoding is proved to be the exact conjugate of the
   padded RS source encoding, the Hamming-isometry part of each source
   spot-check bound transfers.

These facts do not compose themselves into Theorem 10.2 for Aspis.

### 6.2 New proofs required

Before any hiding or soundness claim, the design needs:

1. **Circle padded-code conjugacy.**  For every stage, construct an explicit
   monomial isometry between the proposed interleaved circle ZK code and the
   intended padded RS code, including the current fiber serialization.
2. **Fold commutation.**  Prove the displayed powers-fold equation for the
   coordinate-dependent first circle layer and every later line layer.
3. **OOD/code-switch privacy.**  Prove that the two fresh pads make the actual
   circle/line OOD answer map full rank, or conjugate that map exactly to the
   upstream nonzero-distinct Vandermonde map.  Hamming isometry alone says
   nothing about this evaluation-functional rank.
4. **Degree-six arity-four masked sumcheck.**  Generalize Construction 6.3
   from the implemented Boolean quadratic boundary to Aspis's
   root-of-unity boundary and powers challenge, prove its simulator and
   soundness handoff, and instantiate `ell_zk>=7`.
5. **External degree-27 masked zerocheck.**  Prove the degree generalization,
   its width-ten group, and its exact handoff into or settlement before the
   PCS.  It may not cancel constraint residuals.
6. **Padded-rate ledger.**  Recompute every query, grinding, source
   spot-check, base-case, MCA, and union term with dimensions
   `285,93,45,33`, not the old message dimensions.
7. **Base-case source code.**  Construct the fresh main mask in the same
   circle folded source code and prove the per-position linear check under
   the isometry.
8. **Fiat--Shamir and commitment privacy.**  The cited construction is
   honest-verifier zero knowledge.  A noninteractive malicious-verifier or
   random-oracle claim still needs the appropriate compiler/programming and
   private-commitment argument for every root, path, retry, receipt field,
   and proof-account byte.

Until all eight are closed, the only theorem-level transported statement is
the narrow Hamming-isometry fact, not “ZO0K works on circle codes.”

### 6.3 Exact status of the arity-four masking obligation

Status: **unproved**.

The missing statement is not merely “Construction 6.3 with a larger
`ell_zk`.”  For an Aspis relation polynomial

```text
h(X) = c0 + c1 X + ... + c6 X^6,
```

the boundary functional is

```text
B4(h) = h(1)+h(i)+h(-1)+h(-i) = 4(c0+c4),
```

and the next claim is `h(alpha)` while the source and weight tensors fold by
`(1,alpha,alpha^2,alpha^3)`.  The Plonky3 implementation instead proves a
Boolean identity `h(0)+h(1)=target`, drops the determined linear coefficient,
and folds two multilinear variables at independent equality-table
challenges.  Those affine transcript spaces and residual handoffs are not
the same.

A sufficient new lemma must construct committed random degree-six masks and
prove all of the following together:

1. conditioned on the public boundary claim, the transmitted masked
   coefficient vector is witness-independent (with the exact coefficient
   removed or reconstructed under `B4` stated explicitly);
2. evaluation at `alpha` hands off the correct source residual plus a linear
   claim on the committed mask message;
3. the mask covector has the claimed length and can be carried through all
   four folds to the base case;
4. the simulator produces the same distribution for commitments, boundary
   values, coefficients, challenges, and residual claims;
5. a false relation receives an explicit field-error bound after masking;
   and
6. the resulting challenge is exactly the same `alpha` used by the current
   circle/line powers fold.

Choosing `ell_zk=7` is necessary to span a degree-six mask polynomial; it is
not sufficient to prove these six points.  No existing test or cited theorem
in this repository closes them.

## 7. Retirement of the ad-hoc ten-mask scheme

The complete-view affine-rank probe rejected the old construction at

```text
mask rank 1024 < required public-view dimension 1144.
```

That failure is structural, not a bad challenge sample.  The ten global masks
do not cover the complete public view and must not be counted as hiding.

The upstream architecture addresses the missing surfaces separately:

- q-private randomness inside every opened source oracle;
- fresh pads for every private OOD answer;
- new masks for every sumcheck batch;
- and a terminal one-time pad for the final source and all carried masks.

Therefore the right comparison is replacement, not addition.  If the ZO0K
mapping is selected, the old ten-mask scheme and its rank-rejection gate are
retired from the claim and CU ledger.  The new construction does not become
valid merely because it has more entropy: it becomes valid only after the
protocol-specific proof obligations above are met.

## 8. Next executable gates

The geometry probe passes directly with:

```text
rustc --edition=2021 --test \
  crates/aspis-prover/tests/rate32_hvzk_geometry.rs \
  -o /tmp/rate32_hvzk_geometry
/tmp/rate32_hvzk_geometry --nocapture
```

Result: four tests passed.  The workspace `cargo test` invocation was blocked
at the time of measurement by unrelated concurrent type-inference errors in
`aspis-statement/src/state_only_terminal.rs`; the standalone probe has no
project dependencies.

The next work is theorem and micro-probe work, not integration:

1. write the arity-four masked-sumcheck identity and simulator for degree six;
2. implement a host-only circle padded-encoder commutation probe at every
   position and stage;
3. build the exact two-OOD privacy-rank matrix under the real circle/line
   evaluation maps;
4. re-run the padded-rate soundness ledger;
5. benchmark the base-case mask re-encoding and 14/16 mask multiproofs,
   including a shared multi-point evaluation primitive; and only then
6. choose whether the external degree-27 group is carried into the same base
   case or settled by a separate proved reduction.

The geometry makes this direction concrete, but it also shows that the
reference implementation's terminal overhead and padded-code rate are much
larger obstacles than the old “add ten masks” model exposed.
