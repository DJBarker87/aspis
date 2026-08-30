# V7 adaptive q16/final-work probability milestone — 2026-08-30

## Classification

Kernel-checked semantic probability closure; production trace/source cover
still open.

This milestone fixes the adversary-prequery problem honestly. A raw SHA input
does not identify whether a cached answer will later serve as lambda, gamma,
q16, or another squeeze role. The proof therefore does not assume one global
role classifier or one verifier-only q16 router.

Instead it proves a finite-trial statement. Each genuine selectable trial has
one pre-answer causal router containing exactly 513 named fresh-answer slots:

- one literal final-work digest; and
- all `64 * 8 = 512` q16 candidate/block digests.

The current answer never determines its own slot. Later routing may depend on
earlier answers.

## Principal results

`V7Tag73FinalWorkDigestProbability.lean` proves the literal production
predicate:

- `bigEndianHead64` is identified with the exact eight-byte base-256 value;
- final work accepts exactly the heads below `2^30`;
- accepted 32-byte digests have cardinality `2^222`; and
- uniform acceptance probability is exactly `2^-34`.

`V7Tag73CausalQ16FinalWorkProbability.lean` proves:

- `finalWorkQ16DigestSlot_card`: the joint slot type has cardinality 513;
- `exactCompilerCausalFinalWorkQ16Coordinates`: the adaptive router is a
  lossless coordinate equivalence;
- `uniform_final_work_q16_bad_probability_le_semantic`: one trial costs the
  product of exact final-work probability and the existing semantic q16
  bound; and
- `exact_compiler_causal_final_work_q16_event_probability_le_semantic`: the
  same product bound after hidden-tape averaging.

`V7Tag73AdaptiveQ16TrialAccounting.lean` proves:

- `ExactCompilerCausalFinalWorkQ16Trials.event_probability_le_product`; and
- `ExactCompilerCausalFinalWorkQ16Trials.failure_union_probability_le_one_forest`;
- `work_qualified_q16_trial_union_probability_le_card_mul`, the honest raw
  bound for an arbitrary finite number of trials; and
- the exposure-indexed specializations
  `failure_union_probability_le_exposure_mul` and
  `failure_union_probability_le_one_forest`.

The latter theorem says that at most `2^34` genuinely selectable, jointly
work-qualified causal trials have union probability at most the original raw
one-forest q16 error. This is not a reporting-time work normalization and it
does not divide an already-stated soundness claim by work.

The production-facing conservative inventory is now fixed to

```text
Trial = Fin (unifiedFull256ExposureCap parameters).
```

Without a tighter source theorem, its exact raw bound is

```text
F * q16SemanticOneForestRawError / 2^34.
```

Recovering the frozen one-forest term therefore requires either the explicit
one-work-unit release condition `F <= 2^34`, or a proved source-specific
trial inventory of cardinality at most `2^34`.  A verifier-only work-query
count is not silently substituted for `F`, because an adversary can be the
first party to expose a coordinate later consumed by final work or q16.

`V7Tag73IndexedExposureCausalRouter.lean` supplies the operational counted
router used by the remaining source cover:

- its state carries the literal full-256 exposure ordinal, exact production
  `UnifiedExposureCursor`, and finite protocol memory;
- the slot is chosen from that complete state before the current answer is
  visible;
- the ordinal, production cursor, and protocol memory advance exactly once
  after the answer; and
- `exactCompilerIndexedFinalWorkQ16Router` compiles this controller into the
  exact lossless 513-slot coordinate router consumed by the product theorem.

This is a constructor, not a conclusion-shaped trace premise: the remaining
Tag-73 layer must instantiate its memory and prove the accepted execution is
covered.

`V7Tag73FinalWorkQ16CandidateController.lean` now supplies that literal raw
controller for every conservative exposure trial:

- it byte-parses the exact 41-byte grinding input and 42-byte final-nonce
  absorb input into their shared pre-final digest/nonce key;
- whichever member of that pair is exposed first can anchor the trial, so
  final work and nonce absorption need not be artificially ordered;
- after the nonce-absorb answer fixes the q16 base, it follows all literal
  candidate-absorb and squeeze/advance chains using only previously exposed
  answers, independently of whether the actor is adversary or verifier; and
- every `Fin F` exposure index now constructs the exact lossless 513-slot
  compiler coordinates used by the joint product theorem.

This removes the earlier verifier-first assumption. Cached verifier calls are
handled by their original fresh exposure; they are not relabelled later.

`V7Tag73ExactCompilerFinalWorkTraceOccurrence.lean` now closes the accepted
source occurrence half of the next step:

- strict `checkedRefine` success is split at the literal last three pre-q16
  events rather than inferred from the work-erased replay;
- the selected final-work query is proved to return a digest satisfying the
  exact deployed 34-bit predicate;
- the following final-nonce absorb is proved to return exactly the q16 base;
- both distinct raw inputs are proved to have literal first-creation records
  in the actual result-carrying compiler trace, with either adversary or
  verifier as the creator; and
- the exhaustive native target scan is proved to pause at both coordinates.

Thus the final-work/absorb pair is no longer merely an evaluator-table fact.
It is located in the literal production scheduler trace.  What remains is the
chronological minimum/index selection and the continuation proof that the
same indexed controller routes every accepted q16 coordinate outside the
already-counted forward-reference/collision event.

`V7Tag73FinalWorkEarliestExposure.lean` closes that chronological selection:

- it defines a proof-relevant first occurrence of either member of the exact
  final-work/final-nonce pair;
- it proves every earlier production trace record is pair-clean, so the trial
  cannot be selected retrospectively after seeing an answer;
- it retains an exact prefix/selected/suffix decomposition at the hit;
- it proves the complete compiler exposure trace has exactly `F` records; and
- from strict source acceptance it constructs an actual `Fin F` trial at the
  earliest pair exposure, together with the exact accepted 34-bit work result
  and q16-base digest.

The production cover therefore no longer assumes that an accepted pair has a
usable exposure index.  The remaining work starts at this constructed trial
and is the state-alignment/continuation argument for its executable causal
controller.

`V7Tag73IndexedControllerTraceAlignment.lean` now closes the deterministic
state-alignment half as well:

- replaying an actual flat-trace prefix through the indexed controller reaches
  the exact production pre-answer cursor at the selected record;
- the exposure counter after that prefix is exactly its list length;
- candidate memory remains inactive before the fixed anchor, rather than
  acquiring a role from an earlier answer;
- the selected machine record exposes its literal SHA input at that cursor;
  and
- the earliest final-work/nonce record performs the exact first controller
  transition: a work record labels the final-work slot and stores the key, or
  an absorb record stores the q16 base.

This result is independent of the current answer while choosing the slot.

`V7Tag73ExactFinalWorkEarliestExposure.lean` and
`V7Tag73ExactCompilerFinalWorkControllerAnchor.lean` close the answer binding
without assuming a global raw-input uniqueness theorem:

- the finite inventory selects the earlier of the two already-proved exact
  accepted root records, not merely an input-shaped record;
- the chosen work record therefore carries the exact accepted 34-bit digest,
  while the chosen absorb record carries the exact returned q16 base;
- selecting a trial after the run is legitimate because the union ranges over
  every `Fin F` index, while that trial's slot choice remains strictly
  pre-answer; and
- strict accepted production execution now constructs the complete exact
  controller anchor from the literal result-carrying scheduler trace.

No answer equality, record uniqueness, or conclusion-shaped trace premise is
left at the anchor.  The remaining source-specific obligation is the q16
continuation/forest realization from this exact state.

The continuation audit exposed and repaired one controller-ordering defect.
Once a q16 block digest is known, an adversary may expose the literal advance
sibling before the literal output sibling; this is an ordinary query order,
not a negligible bad event.  The original controller represented only the
output-then-advance order.  `V7Tag73FinalWorkQ16CandidateController.lean` now
uses one pending-pair state that independently records whether the output was
seen and, when necessary, retains an advance answer exposed first.  Kernel
checked transition lemmas cover both sibling orders, every nonterminal block,
and both orders at block seven.  Only outputs receive named q16 slots, so the
change preserves the exact 64-by-8, 512-coordinate forest and every existing
probability parameter.

`V7Tag73FinalWorkQ16ResidualCapacity.lean` closes the joint-router dimension
check.  After reserving one coordinate for the selected final-work digest and
all 512 possible q16 output blocks, the exact compiler tape leaves the reserve

```text
Q + 998 + R * (Q + 1511) + 2R.
```

The deployed verifier's non-routed full-width work is at most 998 calls, so
all adversary, root, replay, fork, non-q16, q16-advance, and unused execution
coordinates fit in that reserve.  Padding therefore cannot consume a still
live named slot merely because the router was undersized.  This is an exact
capacity theorem, not the remaining chronological source-classification
theorem.

`V7Tag73CausalFinalWorkQ16UsedForest.lean` removes an over-strong handoff
obligation from that remaining proof.  For the joint 513-slot router it proves
that exact recursive lookups for only the blocks consumed through the selected
counter construct `OperationalQ16ForestRealization` directly.  The routed
forest's unused suffix may remain arbitrary and independent; it no longer has
to equal the canonical source forest's deliberately zero-padded suffix.

`V7Tag73ProjectedFreshPriorQueryHistory.lean` closes the machine-local source
chronology kernel.  At an exact positional fresh-query prefix it proves that
every earlier fresh query is a literal record in the selected coordinate's
cumulative pre-answer history, and identifies that same history-indexed state
with the native scheduler request.  This is positional rather than a search by
query value, so duplicate pairs cannot select a different occurrence.  The
query also remains in the returned segment's final cumulative history.

`V7Tag73ExactRootPriorQueryHistory.lean` and
`V7Tag73ExactRootQueryCausalOrder.lean` perform the full-root composition.  They
lift the positional request state through the adversary root and across the
adversary-to-verifier callback boundary, then identify it with the
target-clean certificate state at the same global native scheduler prefix.
Consequently, every fresh adversary answer is proved not to be the literal
state prefix of any earlier adversary query, and every fresh verifier answer
is proved not to be the literal state prefix of either any adversary query or
any earlier verifier query.  This is the exact source-level causal-order fact
needed to rule out a q16 child query preceding the fresh answer that determines
its state; it introduces no raw-coordinate role classifier.

`V7Tag73ExactRootLookupCausalOrder.lean` turns that positional fact into the
source-facing lookup theorem.  Every exact final-table lookup receives its
literal adversary-or-verifier position, its answer is excluded from its own
input prefix as well as every earlier query prefix, and any second lookup whose
input begins with that answer is proved to occur strictly later in the combined
adversary-then-verifier root chronology.

`V7Tag73ExactQ16CausalCoordinateOrder.lean` instantiates the theorem across the
entire accepted q16 scan.  It proves that every candidate starts from the one
recorded q16 base, the literal counter absorb returns the canonical branch
initial digest, and recursively every used output and advance query occurs
strictly after the query that produced its current state digest.  It does not
impose an order between the output and advance siblings; the repaired
controller supports both.  Thus adversary-first creation is now a normal
causally ordered source case rather than a missing classifier or an extra bad
event.

`V7Tag73ExactRootFreshInputUniqueness.lean` closes the complementary input
invariant.  Fresh SHA inputs are pairwise distinct within each executable
projected root segment, and the verifier segment is disjoint from the
adversary segment whose final oracle table it inherits.  Hence the complete
adversary-then-verifier root list has no repeated fresh input, and any exact
selected coordinate is absent from its strict prefix.  This is derived from
the literal `lookupEntry = none` facts in the projected traces; it is not a
raw role-classification assumption.

`V7Tag73ExactCausalRouterTapeAlignment.lean` proves that both proof-indexed
casts used by the 513-slot causal router preserve the master tape byte-for-byte
and in order.  On the accepted source run the router's chronological tape is
exactly the combined root fresh-query answers followed by the verifier's
untouched suffix.  An exact root-list position therefore identifies the same
answer position in the actual router tape.

`V7Tag73CausalMachinePrefixRouting.lean` supplies the generic operational
induction for the last source fold.  It follows an actual answer prefix through
the compiled pre-answer router, proves that every still-live named coordinate
is unchanged by that prefix, and proves that a subsequently preferred slot's
recursive lookup equals the literal next answer.  The remaining protocol work
is now to instantiate this induction with the exact Tag-73 controller while
showing that its residual budget never falls back to padding before a live
q16 slot.

`V7Tag73ExactRootControllerCoordinateAlignment.lean` now performs the first
half of that instantiation for every accepted final-table lookup.  It factors
the literal full scheduler trace at the lookup's adversary-or-verifier fresh
record, replays the strict prefix through the concrete exposure-indexed
final-work/q16 controller, and proves that the reached cursor exposes exactly
the selected SHA input before its answer is consumed.  This eliminates the
previous gap between root-table membership and an executable controller
coordinate; pair completion and live-slot preservation remain below.

## Exact remaining boundary

The production/source layer must now instantiate the counted finite inventory
and prove its cover:

1. fold the exact ordered q16 coordinate certificates through the indexed
   controller and the generic prefix-routing induction, proving that every
   used output remains live and receives its literal answer (source ordering,
   fresh-input uniqueness, tape alignment, and both sibling orders are now
   proved);
2. prove that the routed forest agrees with
   `exactOperationalQ16DuplexForest` on every block used through the selected
   counter (the deterministic source forest intentionally zero-pads its
   irrelevant suffix, so whole-array equality is neither true nor needed),
   then conclude that the accepted production schedule is covered by the
   trial;
   and
3. either prove the selectable subinventory has cardinality at most `2^34`,
   or retain the exact general `F * p / 2^34` raw term.

No probability-product or per-trial independence premise remains once that
trace object is constructed.

The generated compact-frontier certificate is still required only to rewrite
the semantic denominator to the frozen release integer. It is not part of the
causal product argument.

## Verification

Focused commands:

```text
cd AspisFormal
lake env lean AspisFormal/K1/V7Tag73FinalWorkDigestProbability.lean
lake env lean AspisFormal/K1/V7Tag73CausalQ16FinalWorkProbability.lean
lake env lean AspisFormal/K1/V7Tag73AdaptiveQ16TrialAccounting.lean
lake env lean AspisFormal/K1/V7Tag73IndexedExposureCausalRouter.lean
lake env lean AspisFormal/K1/V7Tag73FinalWorkQ16CandidateController.lean
lake env lean AspisFormal/K1/V7Tag73FinalWorkQ16ResidualCapacity.lean
lake env lean AspisFormal/K1/V7Tag73CausalFinalWorkQ16UsedForest.lean
lake env lean AspisFormal/K1/V7Tag73ProjectedFreshPriorQueryHistory.lean
lake env lean AspisFormal/K1/V7Tag73ExactRootPriorQueryHistory.lean
lake env lean AspisFormal/K1/V7Tag73ExactRootQueryCausalOrder.lean
lake env lean AspisFormal/K1/V7Tag73ExactRootLookupCausalOrder.lean
lake env lean AspisFormal/K1/V7Tag73ExactQ16CausalCoordinateOrder.lean
lake env lean AspisFormal/K1/V7Tag73ExactRootFreshInputUniqueness.lean
lake env lean AspisFormal/K1/V7Tag73ExactCausalRouterTapeAlignment.lean
lake env lean AspisFormal/K1/V7Tag73CausalMachinePrefixRouting.lean
lake env lean AspisFormal/K1/V7Tag73ExactCompilerFinalWorkTraceOccurrence.lean
lake env lean AspisFormal/K1/V7Tag73FinalWorkEarliestExposure.lean
lake env lean AspisFormal/K1/V7Tag73ExactFinalWorkEarliestExposure.lean
lake env lean AspisFormal/K1/V7Tag73IndexedControllerTraceAlignment.lean
lake env lean AspisFormal/K1/V7Tag73ExactCompilerFinalWorkControllerAnchor.lean
lake env lean AspisFormal/K1/V7Tag73ExactRootControllerCoordinateAlignment.lean
```

Observed focused checks:

| Target | Exit | Wall | Peak RSS |
|---|---:|---:|---:|
| final-work digest probability | 0 | 4.22 s | 5,521,981,440 B |
| causal joint work/q16 probability | 0 | 4.41 s | 5,567,283,200 B |
| adaptive finite-trial accounting | 0 | 19.94 s | 5,573,836,800 B |
| indexed production-cursor router | 0 | 4.0 s | not separately sampled |
| order-robust final-work/q16 candidate controller | 0 | 4.05 s | 5,597,544,448 B |
| exact joint-router residual capacity | 0 | 3.86 s | 5,544,230,912 B |
| joint-router used-prefix forest handoff | 0 | 5.33 s | 5,607,358,464 B |
| projected-prefix prior-history chronology | 0 | 3.97 s | 5,575,933,952 B |
| exact full-root prior-query chronology | 0 | 3.96 s | 5,657,559,040 B |
| exact root causal ordering | 0 | 3.84 s | 5,650,186,240 B |
| exact final-table dependency ordering | 0 | 3.94 s | 5,656,248,320 B |
| exact used-q16 coordinate ordering | 0 | 3.96 s | 5,659,951,104 B |
| exact root fresh-input uniqueness | 0 | 3.9 s | 5,649,612,800 B |
| exact causal-router tape alignment | 0 | 4.23 s | 5,656,018,944 B |
| generic causal-router prefix induction | 0 | 3.96 s | 5,539,348,480 B |
| exact accepted final-work trace occurrence | 0 | 4.37 s | 5,654,528,000 B |
| exact earliest pair exposure trial | 0 | 4.21 s | 5,648,875,520 B |
| indexed controller/production-prefix alignment | 0 | 4.51 s | 5,660,295,168 B |
| exact accepted-record selector | 0 | 4.12 s | 5,647,335,424 B |
| accepted source to exact controller anchor | 0 | 3.92 s | 5,634,048,000 B |
| exact root lookup/controller coordinate alignment | 0 | 3.92 s | 5,661,720,576 B |

All reported theorem axiom sets are subsets of:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, native decision shortcut, or
project-specific axiom in these modules.

## Memory-factorisation note

An initial cardinality proof asked normalization to expand `UInt8^32` and
large powers, causing two owned local checks to cross 12 GiB. They were
stopped immediately and not allowed to continue. The proof was refactored
through explicit finite equivalences:

```text
Digest256 ≃ Fin (2^256)
accepted digests ≃ Fin (2^222)
```

The final proof checks at roughly 5.5 GiB. This is the retained design.
