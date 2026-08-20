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
  weight states;
- the round-zero circle-tensor branch and the later-round line-tensor branch
  consume each of the two off-domain samples in order;
- four successive alpha rounds preserve the generated early-return behavior
  and reach the terminal comparison only after all four succeed; and
- the top-level generated function reads exactly two circle points, checks
  each circle equation, reconstructs the exact point array, executes all four
  rounds, decodes the four terminal coefficients, and returns the same
  generated success value.

`V5RelationFullSuccessInversion.lean` proves the converse control-flow fact
needed by the production theorem: if the generated outer loop returns an
accepted result, that result must originate in a real terminating branch of
the translated loop.  Error exits cannot be mistaken for acceptance, and the
accepted run exposes the four active round bodies in the released order
`0, 1, 2, 3`, together with the successful tail beginning after round four.
The tail theorem then exposes the exact final-coefficient decoder, the main
and additive production dot calls, and the equality of their sum with the
running claim.

`V5RelationTopLevelSuccessInversion.lean` carries that result through the
outermost generated function.  An accepted top-level call must finish the
real two-point circle-reading loop and then enter the real four-round relation
loop.  A decoding error, a failed circle equation, or any other early return
cannot produce an accepted result.  This closes the remaining control-flow
step between the extracted top-level Rust function and the round proof.

This removes an assumption about how a successful translated loop was reached;
it does not replace the remaining semantic proof about the weight accumulator.

The printed axioms for the complete generated theorem are Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`, plus the three deliberately
external production helpers `circle.double_x`, `WeightAccumulator.fold`, and
`WeightAccumulator.dot`.  There is no `sorry` in the checked snapshot or
proof.

## Production-linked fold and dot extraction

`generated-linked/RelationLinked/` is a stronger second extraction of the
same unchanged verifier.  It follows the production call graph through the
real field arithmetic, `circle.double_x`, every weight-fold helper, the
indexed component dispatcher, and the terminal component-specific dot loop.
The reviewed LLBC SHA-256 is
`6637ed571615edc445fded19b70d12101642c2146a5dd6eccfb936a185e5a678`.

The only helper deliberately opaque during that extraction was the generic
`WeightAccumulator::weight_at` fallback.  The checked Lean bundle gives that
unmodeled fallback a failing interpretation rather than an assumed result.
`V5RelationLinkedWeightPath.lean` proves from the generated code that four
successful production folds have the exact log-length trace
`10 -> 8 -> 6 -> 4 -> 2`, and that a four-element terminal array at log length
two enters the direct component loop.  Consequently the accepted release
path cannot call the fallback.  These theorems print only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.

The checked generated files contain a small elaboration-only normalization:
the existing mutable-enumerate adapter, scalar shift-count annotations, an
explicit proof for the fixed panic-string length, and executable models for
standard-library iterators and vector operations.  None changes the Rust
control flow.  There is no `axiom`, `sorry`, or `native_decide` in the linked
generated snapshot or its weight-path proof.

## Remaining work

The fixed generated control flow and the production fold/dot call graph are
complete.  The remaining proof is semantic: connect the successful generated
component updates and direct final dot to the maintained weight schedule,
then use the existing relation-soundness theorem.  The generic `weight_at`
fallback is outside that accepted release path and is not an assumption of
the checked path theorem.

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

The production-linked extraction uses:

```bash
/path/to/charon cargo \
  --preset aeneas \
  --start-from v5_relation_acceptance_harness::relation_stress::verify_v5_relation_stress_with_additive \
  --include aspis_core::field \
  --include aspis_core::circle \
  --include aspis_core::sumcheck \
  --opaque 'aspis_core::sumcheck::_::weight_at' \
  --dest-file relation-linked.llbc -- --release --locked

/path/to/aeneas -backend lean -namespace V5RelationLinkedGenerated \
  -no-progress-bar -split-files -dest generated-linked relation-linked.llbc
```
