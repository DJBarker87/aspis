# V7 Tag-73 relation-tail source composition

Date: 2026-08-27
Branch base: `c8a78f8e3d78993ffb3de9eef739684b56d58627`

## Result

`AspisFormal.K1.V7Tag73RelationTailSourceComposition` now gives the exact
maintained-model handoff for the accepted Tag-73 query insertion and relation
tail.

The principal constructor is:

```text
ExactTag73RelationSourceEnvironment.toK13SourceObligations
```

It constructs `ExactTag73K13SourceObligations` from only:

- a candidate execution and literal decoded/parser equalities;
- the shifted authenticated query covector and claim binding;
- alpha zero's parsed/transcript equality;
- the three later alpha values returned by the translated tail and their
  execution-array updates; and
- the literal terminal dot and running-claim values accepted by the final
  translated comparison.

It derives `beforeOneExact` with
`before_one_eq_joint_discrepancy_of_authenticated_source`. It derives the
terminal predicate with `relation_terminal_accepts_of_source_trace`. It does
not contain or assume `IdealAccepts`, pointwise query equality, a zero query
residual, `QueryInjectionExact`, or an aggregate terminal-acceptance field.

The K1.5 environment now consumes the same source shape:

- `ExactTag73OperationalK15Data.relationTail` stores the accepted translated
  tail values, and `.terminalSource` is derived from them;
- `ExactTag73OperationalK15SourceBinding.querySource` stores
  `ExactAuthenticatedQueryBatchSourceBinding`; and
- the classifier converts that record with `.toOperationalSourceBinding`
  only at the established K1.5 interface.

`ExactTag73OperationalK15Material.acceptedRelationSourceRun` projects the
K1.5 material back to the shared raw accepted-run type without using the K1.3
certificate.

## Source theorem mapping

The query-batch side is pinned by
`AspisV7K13QueryBatchInsertionTrace.accepted_query_batch_exposes_exact_insertion`.
Its trace exposes the exact scale array, line-covector insertion, authenticated
value dot product, and running-claim addition at lines 30--83 of
`aeneas-verif/v7-k13-onefold-batch-source-20260827/proof/V7K13QueryBatchInsertionTrace.lean`.

The relation-tail side is pinned by
`V7Tag73RoundTailTrace.accepted_tail_exposes_exact_trace`. Its trace exposes
the alpha-one, alpha-two and alpha-three challenge/update calls and terminal
dot comparison at lines 12--137 of
`aeneas-verif/v7-tag73-relation-source-20260825/proof/V7Tag73RoundTailTrace.lean`.

The retained replay summaries have SHA-256 digests:

- query-batch `REPLAY-RESULT.txt`:
  `60d8be36e24933e3760c88de5a0804faa5b9e2b8d6e8d224d294386835b2ebb6`;
- relation-tail `NUC-FOCUSED-RESULT.txt`:
  `7e4c701104f062090e8b7323ffe3c87ee64e1e261a46dbf9c0f8a7a7eef2ec74`.

No production Rust file changed in this composition branch.

## Focused maintained-model replay

All commands used Lean 4.32.0, `-j1`, and the existing focused build cache.
No broad project build was run.

| Target | Result | Wall | Maximum RSS | Process swaps |
|---|---:|---:|---:|---:|
| `V7Tag73RelationTailSourceComposition.lean` | PASS | 9.86 s | 5,740,740,608 B | 0 |
| `V7Tag73ExactOperationalK15Stage.lean` | PASS | 6.03 s | 5,659,623,424 B | 0 |
| `V7Tag73ExactCausalK15Reduction.lean` | PASS | 51.75 s | 4,221,730,816 B | 0 |

Every printed theorem uses only:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, or project-specific
axiom in the changed proof sources.

## Exact remaining source boundary

The maintained composition is closed once an accepted translated call is
projected into `ExactTag73RelationSourceEnvironment`. The remaining
source-tool boundary is the concrete namespace/value projection from the
Aeneas `field.QM31`, fixed arrays, transcript states, and weight accumulator
to the already defined exact QM31 and candidate-execution values.

That projection must use the raw fields listed above. It is not permitted to
replace them with query consistency, a residual-zero claim, terminal
acceptance, or any other conclusion-shaped premise. The older whole-tail
bundle also retains its documented frozen-original-to-staged boundary: a
byte/hash transformation certificate plus kernel-checked accepted-control
equivalence, because Aeneas did not emit a Lean body for the frozen original
`finish_onefold_relation`.
