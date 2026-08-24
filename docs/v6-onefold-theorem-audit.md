# V6 one-fold theorem audit

This note records the first check of the proposed B10 V6 profile. The proposal
is promising enough to prototype, but its `101.51`-bit result is not yet a
proved security claim.

The 30,685-byte working profile is the released-compatible PCS width:

| Parameter | Value |
| --- | ---: |
| Initial coefficients | 1,024 |
| Initial evaluation domain | 1,048,576 points |
| Blowup | 1,024 |
| FRI folds | one arity-four circle-to-line fold |
| Disclosed final coefficients | 256 QM31 values |
| Query fibres | 16 |
| Binary frontier limit | 209 nodes per tree |
| Selectable query streams | 3 |
| Work bits | batch 34, fold 31, final 34 |
| PCS columns | 16 M31 C1 + 3 QM31 C2 |
| Screened proof body | 30,685 bytes |

This width distinction matters. The selected hiding algebra currently has ten
additional mask-only C1 columns, for 26 C1 + 3 C2. It has not been integrated
into the production PCS. At the same query count and frontier limit, that
profile is 33,785 bytes, not 30,685 bytes, and does not fit below 30 KiB. It
would require a frontier limit of at most 161; the research screen estimates
that event to be far too rare. V6 therefore needs either a different hiding
integration or another compression method before both claims can be made at
once.

## Results so far

### Checked in Lean

[`V6OneFoldParameterAudit.lean`](../AspisFormal/AspisFormal/V6OneFoldParameterAudit.lean)
proves the following exact facts:

- The dimensions are `1024 -> 256` coefficients and
  `1,048,576 -> 262,144` evaluation positions.
- The required agreement fraction is `7/192`.
- The multiplicity formula selects `m = 3` for the initial code and the
  degree-255 output code.
- More than the agreement threshold means at least 38,230 matching initial
  symbols and at least 9,558 matching output symbols.
- If distinct initial codewords overlap in at most 1,024 places, the initial
  list has at most 100 members.
- If distinct output codewords overlap in at most 255 places, the output list
  has at most 99 members.
- The existing generic encoder proof specializes exactly to one circle fold
  ending in the disclosed 256-coefficient vector.
- For the released-compatible 16+3 width, the proposed grammar formula is
  `9853 + 466q + 64f`; at `q=16` and `f=209` it gives 30,685 bytes, 35 bytes
  below 30 KiB, and 32 uploads at 960 bytes.
- For the selected-hiding 26+3 width, Lean derives 670 fixed QM31 values and a
  33,785-byte body at the same query/frontier settings. It also checks that
  frontier 161 is the largest integer limit that keeps this width below
  30 KiB.
- A deliberately over-split inventory has 23 possible post-commitment prover
  response boundaries. If each genuine BCS round maps to a distinct boundary,
  the round count is at most 23 and therefore at most 30.

[`V6OneFoldCandidateExtraction.lean`](../AspisFormal/AspisFormal/V6OneFoldCandidateExtraction.lean)
now defines the ideal 16-query verifier and proves the deterministic
accepted-proof step. Outside three explicit failures—a query miss, failure of
the published one-fold reduction, and an oversized initial list—acceptance
produces one member of a single at-most-100 initial list whose natural fold is
exactly the disclosed 256 coefficients. The list-overflow event is impossible
once the intended initial encoder's 1,024-position overlap bound is supplied.

[`V6EncoderDistance.lean`](../AspisFormal/AspisFormal/V6EncoderDistance.lean)
proves the new B10 domain geometry rather than carrying that overlap bound as
an unexplained assumption. The `2^20` half-odd circle points are pairwise
distinct and avoid the west pole. From the ordinary circle-polynomial
evaluation identity and injective coefficient split, Lean derives the
at-most-1,024 initial overlap. From an ordinary natural-line evaluation
identity, it derives the at-most-255 final overlap. What remains for the V6
encoder is the concrete evaluation identity, not a separate distance claim.

[`V6PublishedTheoremInterfaces.lean`](../AspisFormal/AspisFormal/V6PublishedTheoremInterfaces.lean)
pins the literature boundary to two exact predicates rather than a general
claim that “FRI applies.” For the 19-column initial batch, the list expression
is exactly 112 and the degree-18 challenge cap is 216,558,659,960,832. With
34 work bits this conditional term is below `2^-110`. For the only fold, the
output list expression is below 113; the conservative degree-three challenge
cap is 9,396,508,281,246, which is below `2^-111` after 31 work bits. Lean then
connects each named literature predicate to the exact bad-challenge set used
by the local extraction model.

The companion Python screen used coefficient 28 for the initial batching
term. The cited width-19 curve has degree 18, so that screen is conservative;
the theorem-specific calculation above is slightly stronger.

[`V6SecurityLedger.lean`](../AspisFormal/AspisFormal/V6SecurityLedger.lean)
checks a conservative rounded budget. It removes the three FRI fold terms that
no longer exist, uses `2^-110` for the initial batch, `2^-111` for the sole
fold, and `2^-109` for the compact-conditioned q16 miss, and provisionally
retains the V5 bounds for the remaining relation and semantic checks. Under
the named BCS conditions, the three-stream work-normalized core is at most
`0.4 * 2^-100`. The other `0.6 * 2^-100` is not silently spent: it remains
available for implementation, primitive, hiding, and any ledger corrections.

The axiom printout for these theorems contains only Lean/mathlib's standard
logical foundations. There is no `sorry` in this module.

### Supported by the cited papers

The theorem audit used the 24 March 2026 S-two paper and the two cited
polynomial-generator papers.

- [S-two, ePrint 2026/532](https://eprint.iacr.org/2026/532), Protocols 2 and
  3, allow `r = 0`. In that case the protocol performs one circle-to-line fold,
  publishes the resulting `g0`, and then runs the query checks. The proposed
  one-fold endpoint is therefore part of the published protocol shape rather
  than a new FRI conjecture.
- S-two equations (73) and (74) give the list expression and multiplicity
  rule used by the repository. The exact B10 arithmetic chooses `m = 3`.
- [Bordage et al., ePrint 2025/2051](https://eprint.iacr.org/2025/2051),
  Theorem 9.2, states its polynomial-generator result for every integer
  `m >= 3`. The selected initial multiplicity is in its stated range.
- [Haböck et al., ePrint 2025/2110](https://eprint.iacr.org/2025/2110),
  Theorem 2, also states the threshold for `m >= 3`.
- S-two's Reed--Solomon and circle-code results provide the kind of distance,
  list-decoding, and round-reduction statements needed here.

This source check answers an important feasibility question: the profile does
not presently require inventing a new decoding theorem merely because it uses
one fold or multiplicity three.

## What is not proved yet

The remaining work is substantial and must not be hidden behind the parameter
screen.

1. **Exact published-theorem application.** The paper's circle-code and
   correlated-agreement hypotheses must be matched to the V6 encoder,
   19-column batch, domains, agreement predicates, and the one-fold failure
   event. The list theorems no longer need opaque distance assumptions, but
   the eventual concrete encoder must be proved to have the circle and line
   evaluation identities used by the new distance module.

2. **Probability of the named extraction failures.** The deterministic
   accepted-proof inclusion is now proved. What remains is to show that the
   published one-fold theorem bounds its exact reduction-failure event, and
   that the compact query experiment bounds its exact query-failure event.

3. **BCS round meaning.** The 23-entry inventory is a safe count of serialized
   response boundaries. We still have to show which entries are genuine
   public-coin IOP rounds and that every such round is covered. Counting bytes
   alone is not enough.

4. **Compact-query sampling.** Selecting the first query set with a frontier
   at most 209 conditions the query distribution. The elementary conditional
   probability inequality is sound, but the exact sampler, counter domains,
   retry limit, without-replacement decoding, and random-oracle query budget
   must be modeled. The proposed three streams with eight draws each add up to
   24 candidate draws; those draws are not silently included in the BCS round
   count.

5. **PCS/hiding profile integration.** The screened 30,685-byte body uses the
   released-compatible 16+3 PCS width, whereas the selected hiding proof uses
   26+3. V6 must either integrate hiding without carrying all ten extra C1
   columns in the opened PCS records, or accept a larger proof, before it can
   claim both the selected hiding result and the 30 KiB body.

6. **Security ledger.** The V5 event list cannot simply be copied. Events for
   three removed FRI layers should disappear, the initial batch and sole fold
   change parameters, the query event becomes conditioned, and new events are
   needed for packed decoding, the explicit final vector, compact sampling,
   typed shared-salt leaves, and the three relation-only reductions.

   The numerical core and changed dominant terms are now checked. The open
   task is event-by-event inclusion: show that each V6 failure is charged to
   one listed term, show that retained V5 relation bounds still apply to the
   new transcript, and use the explicit external-event allowance for the
   remaining computational assumptions.

7. **Hiding.** Reusing one 32-byte secret salt for two separately typed leaf
   hashes needs a joint two-tree hiding proof. The numerical hiding result in
   the research report is still conditional on that proof and on revised
   masking-rank certificates.

8. **Transcript and implementation.** The exact order, labels, byte grammar,
   rejection rules, retry counters, Rust verifier, and compiled Solana program
   do not exist yet. They will need the same Rust-to-Lean and reproducible-build
   treatment used for V5.

9. **Compute and prover measurements.** The 30 KiB result is a byte count, not
   a Solana compute result. The final-vector evaluations, relation reductions,
   binary Merkle checks, packed decoding, prover memory, and grind time need a
   host prototype before any deployment decision.

## Decision

The Phase-0 kill condition has not fired. The one-fold endpoint and `m = 3`
are supported by the cited theorem statements, and the exact finite
arithmetic is now checked in Lean. The correct next step is a small host
prototype plus an exact one-fold accepted-proof model—not a production
verifier or a mainnet transaction.

If the exact published-theorem application fails, B11/q15 is the practical
fallback to test. B12/q14 should not be the default merely to get below 30,000
decimal bytes; it costs much more prover memory and has a weaker topology
margin.
