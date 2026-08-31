# V7 fixed-q16 K1.3 source boundary — 2026-08-31

## Classification

**OPEN — do not use the fixed q16 residual-fibre premise as a completed
actual-law K1.3 bound.**

The fixed-root factorization is useful accounting infrastructure, but its
remaining predicate has not been derived from the Tag-73 source model:

```lean
ExactFixedK13ResidualInvariant
  transitionFuel configuration projection fixedInstance decoder
```

It asks two genuine trial witnesses with equal non-q16 residual coordinates
to have the same `exactFixedK13IntrinsicBad`.  In the present implementation
that entails equality of the parsed proof and canonical K1.2 words.

## What is proved

The following source facts are kernel checked on
`research/v7-one-tx-activate-20260828`:

- `exact_prefix_k12_words_eq_of_same_prover_runtime`:
  equal returned value and prover-final oracle give equal fixed-prefix K1.2
  words;
- `exact_dag_residual_coordinate_preserves_pre_k13_values_at_verifier_anchor`:
  a **verifier-owned** selected trial anchor, equal residual coordinate, and
  the same hidden tape preserve the parsed proof and K1.2 words;
- `exact_fixed_k13_actual_joint_trial_anchor_actor_cases`:
  every literal selected anchor is first owned by either the verifier or the
  adversary, with no raw-input role classifier and no discarded internal
  actor case;
- `exact_fixed_k13_joint_trial_pre_q16_values_of_left_verifier_anchor`:
  the verifier-owned half is available directly in the proof-relevant fixed
  K1.3 event.

The corresponding commits are `80a6e5c3`, `444e376c`, and `96b1f599`.
Their focused Lean targets report only `propext`, `Classical.choice`, and
`Quot.sound`; they contain no project axiom, `sorry`, `admit`, or
`native_decide`.

## Why this does not close the adversary-first half

An arbitrary prover can first query a transcript coordinate that the verifier
will later read from the shared table.  The later verifier call is then a
cache hit and consumes no new random-oracle answer.  Treating that event as a
fresh verifier query, or as a negligible guess, is unsound.

More importantly, the existing same-tape replay model intentionally permits
a changed challenge to return a different parsed proof/DAG.  This is stated
and modeled in `V7Tag73ReplayReturnedVerifier.lean`: a replayed proof may
contain a different challenge-dependent C2 commitment.  The existing
counterfactual K1.3 provider therefore maps a challenge to an
`Option Tag73K12ParsedProof`; it does **not** require a replayed proof to be
equal to the first-run proof.

Consequently, same-tape replay alone cannot justify equality of the whole
`exactK13ParsedProof` over a q16 residual fibre.  A q16-specific causality
theorem could still prove an appropriate precommitment invariant, but that is
not presently established and must not be assumed.

## Correct next route

The existing restoration-wide classifier already has the appropriate
separation:

- `exact_restored_operational_k13_provider` obtains q16 from the retained
  verifier ledger rather than a parser-selected schedule;
- `CounterfactualParsedK13Oracle` and `counterfactualK13Provider` represent
  challenge-indexed returned proofs, with unavailable branches explicitly
  mapped to `none`;
- the K1.4 counterfactual family then reasons about available response
  branches rather than equality of all returned proofs.

K1.3 needs the analogous q16 construction:

1. define a typed state-restoring q16 response family from the pre-q16
   committed state and same hidden prover tape;
2. prove every returned branch is checked against its own literal challenge
   and shared-oracle table, with cache hits left immutable;
3. express q16/query failure through that response family and the existing
   64-by-8 semantic forest theorem, rather than through a fixed parsed-proof
   bad set on every residual fibre; and
4. connect the literal Rust/Aeneas q16 scheduler/decoder to that family.

This is a reformulation of the actual-law K1.3 proof obligation, not a change
to the protocol, proof bytes, query count, digest width, work accounting, or
cryptographic claim.

## Implemented derived-q16 seam

`V7Tag73DerivedK13Q16Handoff.lean` now makes the narrower target explicit.
`DerivedK13Q16BadProfile` contains exactly the authenticated K1.2 words,
canonically decoded fixed fields, verifier-derived gamma, and verifier-derived
round-zero alpha.  It deliberately contains no q16-selected positions and no
opaque parsed-proof value.

The kernel-checked handoff proves that a query-phase failure in
`derivedK13View` exposes the literal selected first-cap-203 schedule inside
that profile's consistency set, with the unchanged `9557` cardinality cap.
Thus the next causality theorem need only show that this *four-component
profile* is committed before the q16 forest.  It no longer needs to claim
equality of the whole replayed parsed proof.  That precommitment/source bridge
is still open; this module does not manufacture it.

## Source-binding normalization now proved

Two additional focused modules close a bookkeeping gap at that boundary:

- `V7Tag73CanonicalOneFoldScheduleUniqueness.lean` proves that alpha plus the
  exact two inverse-table equations uniquely determine the complete total
  one-fold schedule; and
- `V7Tag73DerivedK13SourceBridge.lean` uses the explicit
  `ExactParsedProofSourceBinding` to identify the legacy parsed view with the
  verifier-derived view, including the canonical schedule.  The accompanying
  `V7Tag73DerivedK13LegacyQueryBridge.lean` transfers the existing fixed
  query failure to the derived q16 bad profile.

This does not turn `ExactParsedProofSourceBinding` into a proved Rust bridge:
it remains the intentionally explicit Aeneas/source obligation.  It does
mean that, once that bridge is instantiated, no separate arbitrary
inverse-table or schedule-equality premise is left over.

## Exact remaining premise, reduced to four fields

`V7Tag73ExactFixedQ16SemanticNoninterference.lean` proves that existing q16
probability accounting needs equality only of:

1. authenticated K1.2 words;
2. gamma;
3. decoded final-256; and
4. the one-fold schedule.

It no longer asks for equality of openings or of the entire parsed proof.
`V7Tag73ExactFixedQ16DerivedProfileInvariant.lean` tightens that endpoint
again: its profile contains only K1.2 words, verifier gamma, the disclosed
final-256, and verifier alpha-zero.  It deliberately does **not** require
equality of all 641 decoded fields.  Its separate
`ExactFixedK13SourceScheduleFunctional` premise states precisely the remaining
alpha-to-total-schedule obligation.  The committed canonical inverse-table
bridge is the intended discharge of that premise; it is no longer imported by
the lightweight q16 module because Lean's module emitter expands that aggregate
past the project memory limit.  The obligation is therefore visible, not
silently trusted.

So the precise remaining K1.3 actual-law theorem is now:

> Within one genuine chronological trial and fixed hidden tape, equal
> non-q16 residual coordinates preserve the derived four-field profile.

That is the appropriate target for the q16 state-restoration/source-causality
bridge.  It is still open, and must include the adversary-first cached path;
it may not be replaced by a raw SHA-input classifier or a fresh-query claim.

## Verifier-owned partition now reaches the minimal profile

`V7Tag73ExactFixedQ16VerifierDerivedProfile.lean` proves that the existing
verifier-owned anchor theorem, together with the explicit parsed-source
provider, fixes all four values of the minimal profile on an equal-residual
fibre.  This is the exact verifier-owned half of the remaining causality
condition.  It does not claim anything about the adversary-first/cache-hit
half, and it does not import or assume a raw-input role classifier.

Focused NUC checks on 2026-08-31 compiled the lightweight profile bridge and
the verifier-owned bridge in 3.63s and 3.37s respectively, at 6.59GiB and
6.56GiB peak RSS with zero swap.  Both reported only `propext`,
`Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`, or
`native_decide` was introduced.  Lean 4.32 emitted its known
`LibrarySuggestions` recursion panic while writing module metadata, but both
commands exited zero and produced their `.olean` files; this toolchain issue
is recorded separately from theorem status.

## Current honest status

The fixed and restored q16 factorization theorems remain conditional
accounting results.  K1.3's actual-law measure bound remains open, as do the
corresponding K1.4 and K1.5 actual-law links.  K1.6 remains green only
conditional on those genuine upstream bounds.
