# Complete V5 relation-source translation

This bundle translates the unchanged production
`verify_v5_relation_stress_with_additive` function, including its four nested
Rust loops, into Lean.

It exists to remove the previous assumption that a successful execution of
the nested production loops agrees with a hand-written four-round model.  The
proof is being built from the inside out over the exact generated function.

Pinned identities:

- repository commit at extraction: `079ad0ba188e116a3ecd70bd95c28ec8c62fdf08`;
- `v5_relation_stress.rs` Git blob:
  `cbe62500353df776318fcb8933bc1c2200097ade`;
- `field.rs` Git blob: `a28ff94de05265102ca819849805a7f73c675800`;
- `sumcheck.rs` Git blob: `200110100abc81e9cc8b30701744dc985cabba48`;
- Charon commit: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`;
- Aeneas commit: `395aa6cdf0684b08c845d73a4847bd3dbfde8bec`;
- Lean: `v4.32.0`.

The Aeneas commit adds support for returning nested mutable-iterator
writebacks.  It does not change the extracted Rust.  The generated generic
mutable `Iterator` instance is not accepted by Lean because its trait shape
cannot express the returned borrow.  `V5MutableEnumerateSupport.lean` gives
that operation its exact Aeneas writeback type and delegates each step to
Aeneas's existing mutable-slice iterator model.

## Current checked result

`V5RelationGeneratedSupportProof.lean` proves the mutable-enumerate adapter
and the fixed-array iterator models.

`V5RelationFullSourceProof.lean` currently proves:

- the complete four-value final-coefficient decoder loop reads words zero
  through three, writes them to the same slots, consumes no extra word, and
  returns exactly that array; and
- the complete seven-coefficient innermost round loop reads words zero
  through six in order, reconstructs exactly that polynomial, checks its
  boundary against the running claim, evaluates it, and returns both folded
  weight states.

The printed axioms for the decoder theorem are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`.  The polynomial-loop theorem has those
same foundations plus the named external `WeightAccumulator.fold` function
because that production helper was deliberately opaque in this extraction.
There is no `sorry` in the checked snapshot or proof.

## Remaining work

The generated source still has to be proved through the three enclosing fixed
loops:

1. two off-domain samples in each round;
2. four relation rounds; and
3. two decoded circle points.

The terminal `WeightAccumulator.dot`, additive dot, final comparison, and
projection into the maintained field-level verifier then form the final join.
The production `double_x`, `WeightAccumulator.fold`, and
`WeightAccumulator.dot` helpers remain explicit source boundaries here unless
their independent generated proofs are imported.

This directory is therefore a checked intermediate proof bundle, not yet the
finished end-to-end relation theorem.

## Extraction command

From `aeneas-verif/v5-relation-acceptance-20260815/harness`:

```bash
/path/to/charon cargo \
  --preset aeneas \
  --start-from v5_relation_acceptance_harness::relation_stress::verify_v5_relation_stress_with_additive \
  --include aspis_core::field \
  --include aspis_core::sumcheck \
  --opaque 'aspis_core::sumcheck::_::fold' \
  --opaque 'aspis_core::sumcheck::_::dot' \
  --dest-file relation.llbc -- --release --locked

/path/to/aeneas -backend lean -namespace V5RelationFullGenerated \
  -no-progress-bar -split-files -dest generated relation.llbc
```

The reviewed LLBC SHA-256 is
`821aecad6f488f9a399dc07dd429694226fecee2a8e84ce140c3673000109301`.
