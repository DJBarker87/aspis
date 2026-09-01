# V7 restored q16 residual-factorisation endpoint (2026-08-31)

## Result

The restored-root K1.3 q16 failure event is now reduced to the existing exact
finite joint final-work/q16 trial theorem.  The reduction does not select the
consistency bad set, the 34-bit work value, and the q16 output from independent
executions: each failure is carried by one chronological compiler exposure
trial and one concrete 513-coordinate successful outcome.

The new module is:

`AspisFormal/K1/V7Tag73ExactRestoredQ16ResidualFactorization.lean`

It proves:

- every restored-root K1.3 query failure has one joint-trial witness;
- the canonical bad set for a residual fibre has cardinality at most 9,557;
- the root query event is covered by the union of the exact compiler exposure
  trials;
- conditional on the explicit residual-fibre invariant, its probability is at
  most

  `F * q16SemanticOneForestRawError / 2^34`,

  where `F = unifiedFull256ExposureCap parameters`;
- if `F <= 2^34`, the release form is bounded by the original
  `q16SemanticOneForestRawError`.

The proof does not assume independence between the final-work search, q16
outputs, or the source-derived consistency bad set.  It also does not divide a
raw error by the amount of grinding work.

## Exact remaining endpoint

The only new premise is
`ExactRestoredRootK13ResidualInvariant`.  It states that, for a fixed compiler
trial and hidden tape, two genuine joint-trial executions with equal residual
coordinates have the same source-derived K1.3 consistency bad set.

This is deliberately a source/noninterference obligation rather than a hidden
probability or cryptographic assumption.  Closing it requires showing that the
accepted pre-q16 committed data and extracted K1.2 words are fixed before the
named final-work/q16 answers, modulo the already-accounted target/collision
events.  Once this invariant is constructed from the exact source-state and
K1.2 binding theorems, the finite q16 probability bound above instantiates
without another counting argument.

## Verification

Focused replay:

```text
lake env lean AspisFormal/K1/V7Tag73ExactRestoredQ16ResidualFactorization.lean
wall: 4.56 s
peak RSS: 5,729,615,872 bytes
swaps: 0
exit: 0
```

Every printed theorem has exactly the axiom subset:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, or project-specific
axiom in the module.

