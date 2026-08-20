# Selected-query transcript wrapper proof

This directory checks the Rust function
`derive_v5_selected_good_queries_from_transcript`. That function is the
outer wrapper which reads the selector stored in the proof, derives the
corresponding 18 query positions, checks that selected candidate, and returns
the same polynomial and query array to the rest of the verifier.

Charon extracted the unchanged Rust wrapper together with its selector-range
check and generic success/failure helper. Aeneas translated those definitions
to Lean. The generated definitions are retained under `generated/`; the two
proof files under `proof/` establish that every successful translated run:

- used a selector below 3;
- successfully ran the separately checked transcript-tail function with that
  exact selector;
- passed the same returned 18-query array to the candidate check;
- returned that polynomial and query array unchanged; and
- reaches the maintained transcript tail consisting of the final-polynomial
  absorb, final work check and absorb, selector absorb, and query sampling.

The final theorem is
`generated_selected_wrapper_success_matches_source_tail` in
`V5TranscriptSelectedWrapperFinalJoin.lean`. Lean reports only its standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.

## Exact boundary

This proof closes the wrapper's control flow and data flow. It does not pretend
that a made-up Boolean is the production GoodA/GoodB calculation. The external
definition `candidateObservation` records only whether the exact query array
passed to the check was accepted. The production GoodA/GoodB arithmetic and
its connection to the mathematical goodness condition are checked in the
separate maintained GoodA/GoodB proof layer.

The lower transcript-tail extraction still uses its documented expansion of a
fixed four-iteration decoder loop. SHA-256 security, the Fiat-Shamir model, the
compiler, the translator, and the Solana runtime remain explicit external
assumptions; this source proof does not assign them invented probability
bounds.
