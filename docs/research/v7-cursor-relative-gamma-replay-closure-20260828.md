# V7 cursor-relative gamma replay closure — 2026-08-28

## Result

The exact production scheduler now supplies the ordered cache-or-future-fresh
property needed by counterfactual gamma replay.  The proof does not classify a
SHA input by logical role and does not charge adversarial prequeries as a bad
event.

The theorem chain is:

1. `projected_fresh_trace_scan_pauses_with_exact_split`;
2. `projected_fresh_trace_seek_aligned_scan_pauses_with_exact_split`;
3. `projected_fresh_trace_then_seek_aligned_trace_pauses_exact`;
4. `exact_compiler_aligned_future_pause_split`;
5. `exact_compiler_actual_gamma_coordinate_step`;
6. `exact_compiler_actual_gamma_replay_closure`.

At an evolving aligned cursor, a final-table coordinate is either already in
the immutable current table with its exact production answer, or its literal
fresh `(input, answer)` record lies in the remaining chronological adversary /
verifier suffix.  The crossing proof executes the residual adversary trace,
passes through its real callback, and pauses in the verifier trace.  A prior
adversary fresh query followed by a verifier cache hit therefore consumes one
fresh answer and is handled by the cached branch.

The final closure constructs the successful variable-prefix tape and proves
that `exactCompilerRoutedGammaReplay` at the actual routed gamma returns the
literal `runExactPlainRom` production run.  Unread padded duplex coordinates
are observationally irrelevant.

## Honest resource boundary

The concrete closure takes `2 ≤ transitionFuel`.  Existing concrete capstones
already carry `3 ≤ transitionFuel`.  `ExactK12OperationalInput` does not retain
this reserve as a field, and no non-circular theorem deriving it from that type
alone currently exists.  The reserve is scheduler resource data, not a replay
or probability premise.

## Remaining boundaries

This milestone closes executable gamma source alignment, but does not by itself
prove the global actual-law event inclusions:

- K1.3 still needs q16, one-fold, joint-query-batch, and later-alpha compiler
  routing/coverage plus current source binding.
- K1.4 still needs the width-29 variable-prefix actual-law coupling.
- K1.5 still needs the eight fixed-category compiler inclusions and the
  residual variable-prefix `covered` inclusion.
- Current-source decode still needs a current V7-root Aeneas trace proving the
  complete 641-field read and packed-wire-to-raw-message projection.
- `ExactOperationalParsedWireProjection` is not derivable for an arbitrary
  `AcceptedTapeProjection`; a source-backed derived proof view/openings
  projection is required.

Thus K1.5 remains exactly
`336869027002169 / (P^4 - 1)`, and no K1.6 numerical premise changed.

## Rejected shortcuts and verification

No raw/history coordinate classifier, first-verifier-origin premise,
independence assumption, grinding normalization, prequery probability charge,
extra union bound, protocol/wire/CU change, or conclusion-shaped replay premise
was introduced.

Focused builds of the pause split, joined crossing, coordinate step, padded
prefix replay, actual routed replay, and selected-proof closure are kernel
green.  The terminal axiom union is exactly `propext`, `Classical.choice`, and
`Quot.sound`.  Peak focused RSS was approximately 5.73 GB with zero swap.
