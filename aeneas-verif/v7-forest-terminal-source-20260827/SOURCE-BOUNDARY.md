# Exact source and semantic boundary

## Transparent in this bundle

- ASF8/ASR8 top-level framing, offsets, transition dispatch, and result
  construction;
- the complete translated host control flow around account validation,
  statement/compilation comparisons, trace-variant selection, residual
  evaluation, exact residual-count comparison, all-zero check, final result
  validation, and return;
- `Result::map_err`, filled with its exact two-constructor semantics;
- the source-level statement/result validators and account-binding control
  flow reached by the verifier, except for the named callbacks below.

## Explicit callback interfaces

- canonical digest encode/decode;
- late-statement, payment-statement, and verified-afterstate codecs;
- forest master/checkpoint/lane account encoders;
- deterministic output-lane selection;
- transfer and withdrawal forest residual evaluators;
- empty-root construction used by account validation;
- M31 zero/equality and Rust iterator operations used by the translated
  structural residual/all-zero path.

Poseidon is therefore explicit at the residual-evaluator and empty-root
interfaces.  The theorem does not identify either callback with the formal
Poseidon permutation or the mathematical forest relation; that composition is
the separate Lean semantic bridge owned by the protocol proof.

SHA-256 is not called by any of these three ASF8/ASR8 entry points.  It is not
assumed here.  Transcript/PCS SHA binding belongs to the outer Tag-73 verifier
source bridge, and must be composed separately before dispatch activation.

PDA derivation, Solana account ownership/locking, Pool state invariants, CPI
authorization, and persistence are also outside this focused crate-level
translation.  The account identities consumed here are exact 32-byte values;
this bundle proves only how the inactive terminal checks and returns them.

Charon, Aeneas, Lean's kernel, the Rust compiler provenance used by Charon,
and the pinned source/build environment remain ordinary toolchain trust.
