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

## Exact remaining boundary

The production/source layer must now instantiate the counted finite inventory
and prove its cover:

1. define the final-work/nonce/q16 grammar and controller memory at each
   conservative exposure index;
2. route the first exposure of its final-work digest and 512 q16 blocks,
   including adversary-prequery/cache-hit executions;
3. prove the router uses distinct chronological fresh-answer occurrences;
4. prove the accepted production schedule is covered by one trial; and
5. either prove the selectable subinventory has cardinality at most `2^34`,
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
```

Observed focused checks:

| Target | Exit | Wall | Peak RSS |
|---|---:|---:|---:|
| final-work digest probability | 0 | 4.22 s | 5,521,981,440 B |
| causal joint work/q16 probability | 0 | 4.41 s | 5,567,283,200 B |
| adaptive finite-trial accounting | 0 | 19.94 s | 5,573,836,800 B |
| indexed production-cursor router | 0 | 4.0 s | not separately sampled |

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
