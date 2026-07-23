# Component-B relation-claim consumer correspondence

> **Integration note.** This report records the consumer theorem before the
> two row equalities were joined. They are now closed by
> [`../component-b-layout-bindings/REPORT.md`](../component-b-layout-bindings/REPORT.md)
> and included in the production-default V5 proof map.

## Result

The exact source-authentic Rust consumer of the committed Component-B message
is kernel-checked through all four released claims.

The extracted helper:

1. reads exactly `c2_messages[1]`;
2. reads the three public points in order `0, 1, 2`;
3. calls the already authenticated production extension-field MLE wrapper at
   each point; and
4. computes the terminal claim by the source's increasing-row dot-product
   loop.

The strongest end-to-end theorem is
`extracted_component_b_relation_claims_exact` in
`proof/ComponentBRelationClaimsProof.lean`. It contains no abstract evaluator,
caller-supplied lane selector, opaque `Faithful` predicate, or executable
correspondence premise. A concrete all-zero invocation proves that the
execution hypotheses are non-vacuous.

`extracted_component_b_terminal_eq_tenRoundTerminal_of_layout` in
`proof/ComponentBRelationClaimsTerminalBridge.lean` connects the extracted
terminal output to the maintained
`AspisV5SumcheckCommitment.tenRoundTerminal`. Its remaining constructor/layout
interface is exactly the following two coordinatewise statements:

```lean
covectorRows : ∀ row,
  exactTerminalCovectorRows terminalCovector row =
    terminalWeights point 1 row

weightedMessageRows : ∀ row,
  exactTerminalCovectorRows terminalCovector row *
      exactCommittedBMessageRows c2Messages row =
    exactTerminalCovectorRows terminalCovector row *
      rowMessage initial tails row
```

The second condition is intentionally a weighted equality rather than full
message equality. The committed Component-B lane contains pad coordinates and
the row-993 pivot outside terminal support, so literal equality with the sparse
maintained `rowMessage` would be false. The stated interface is the exact fact
the terminal consumer needs and no stronger.

This stage closes the real MLE callsite and terminal accumulation. The later
layout theorem establishes the two row equalities above.

## Rust source binding

Owning source:
`crates/aspis-prover/src/v5_split_layer_zero.rs`

Source SHA-256:
`4731d67935d225ede9bbc063fbfbafa198d3945f598fcf3ee8e742ca12f8e438`

Extracted helper spans:

- constant: line `54:0-54:46`;
- terminal loop: lines `190:4-193:5`;
- full helper: lines `177:0-196:1`.

The small private helper is called only from the existing Component-B branch
of `build_v5_relation_claims`. It preserves the existing lane, point, terminal,
and output-slot order while making the concrete MLE consumer independently
extractable. The source was extracted under the V5 feature profile and now
ships in the default production feature set.

The Rust tooth
`component_b_relation_claims_select_exact_c2_lane_one` assigns different
values to C2 lanes zero, one, and two, verifies that all three point claims
read lane one, then swaps lanes zero and one and observes the changed output.

## Extraction integrity

- Workspace HEAD at final verification:
  `27e8265d28de88e7967626a2d2432ef161fb4f49`.
- Charon commit:
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`.
- Charon binary SHA-256:
  `8e422e8a0624bb12314210b655d5788f9e32a597cae17f4e402006e5dc0391a2`.
- Aeneas commit:
  `b59d5188c082f704a418c7cb4e52ad69328002d1`.
- Aeneas binary SHA-256:
  `99800c72be8f65a0e3357afd4905c6556d0db9c3ef41601991685b0c6e15c2c4`.
- LLBC SHA-256:
  `9c96da16e56c41b2015115738a37ea1e6dc9ef5fcc0087fd36cc3b9eccf46f76`.
- Raw generated Lean SHA-256:
  `28ba054e2872da8fd650372cf14f1f40b488ecd01549bf16cc8cb15ba398bd6d`.
- Lean-4.32 merged generated fragment SHA-256:
  `1afdb7aaecaf7688cd0b4fcbb35ff6952a90a960fff398efd6acd41ef083f3e9`.

The LLBC has `has_errors = false`, 53 ordered declarations, and embeds source
bytes equal to the owning source hash. The 62-line helper fragment in the raw
Aeneas output is byte-for-byte equal to the fragment compiled under Lean 4.32;
the latter imports the already authenticated shared field/MLE definitions
instead of redeclaring them.

## Kernel audit

All six exported theorems compile at Lean 4.32 default handwritten limits.
Every `#print axioms` result is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Accepted handwritten/merged sources contain none of `sorry`, `admit`,
`native_decide`, `axiom`, `unsafe`, raised `maxHeartbeats`, or raised
`maxRecDepth`.

The negative ordering tooth is
`lane_zero_substitution_changes_selected_row`. The separate Rust test provides
the concrete nonzero instance; the Lean theorem proves the exact source-index
dependency universally.

## Tests run

The following passed on the bound source:

```text
cargo check --release --locked -p aspis-prover --features v5-mask
cargo test --release --locked -p aspis-prover --features v5-mask \
  component_b_relation_claims_select_exact_c2_lane_one -- --nocapture
```

The targeted Rust test result was `1 passed, 0 failed`. Direct Lean-4.32
compilation of the merged generated module, consumer proof, and maintained
terminal bridge succeeded with no warnings.

## Scope

This report proves the source-authentic relation-claim consumer. The
production V5 integration and the wider cryptographic interfaces are indexed
from [`../README.md`](../README.md).
