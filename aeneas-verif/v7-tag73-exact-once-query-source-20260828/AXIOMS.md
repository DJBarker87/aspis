# Kernel and axiom report

All checked proofs use ordinary Lean kernel reduction.  The bundle contains no
`sorry`, `admit`, `native_decide`, declaration of an `axiom`, or project axiom.

Reported theorem dependencies:

- `selected_revision_is_pinned`,
  `accepted_deferred_path_preserves_transcript_order`, and
  `deferred_validation_never_changes_transcript`: none;
- project finite/layout/canonicality capstone: only `propext`,
  `Classical.choice`, and `Quot.sound`;
- generated parser source theorems: only `propext`, `Classical.choice`, and
  `Quot.sound`;
- generated consumer width, malformed, and both-decoder-success theorems:
  only `propext`, `Classical.choice`, and `Quot.sound`.

The executable external definitions used to elaborate the validation model
are definitions, not axioms.  Cryptographic correctness is explicitly outside
the claim rather than assumed as an axiom.
