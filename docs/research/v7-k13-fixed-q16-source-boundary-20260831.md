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

## Current honest status

The fixed and restored q16 factorization theorems remain conditional
accounting results.  K1.3's actual-law measure bound remains open, as do the
corresponding K1.4 and K1.5 actual-law links.  K1.6 remains green only
conditional on those genuine upstream bounds.
