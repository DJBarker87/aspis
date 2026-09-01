# V7 fixed K1.3 q16 residual factorization — 2026-08-31

## Scope correction

The measured K1.6 capstone does not consume the restoration-wide K1.3 event.
It consumes `exactTag73K13QueryEvent` from the fixed K1.2--K1.4 stage package.
That distinction matters: every `ExactPrefixK12Certificate` in the fixed event
has `wordsExact`, so its extracted Merkle words are the canonical
`exactPrefixK12Words input`.  The restoration-wide event instead quantified
over arbitrary extracted words and therefore exposed an unnecessarily strong
residual-invariance obligation.

## Kernel-checked result

`V7Tag73ExactFixedQ16JointEventHandoff.lean` proves that every member of the
actual fixed-root q16 event supplies:

- the canonical source-derived consistency set;
- its exact cardinality bound `≤ 9557`;
- one chronological exposure trial;
- the exact 513-coordinate final-work/q16 factor; and
- membership of that coordinate in the corresponding successful joint bad
  event.

The source interface is only `ExactParsedProofSourceBinding`: the parsed proof
queries must equal the selected operational q16 schedule.  It does not assume
the probability conclusion.

`V7Tag73ExactFixedQ16ResidualFactorization.lean` then constructs the exact
finite trial union and proves both probability endpoints:

- the exposure-multiplied raw bound; and
- the one-forest release bound when the full exposure cap is at most `2^34`.

Both endpoints are conditional on one explicit remaining proposition,
`ExactFixedK13ResidualInvariant`.  It states only that, within a genuine trial,
two runs with the same hidden adversary tape and the same non-final-work/q16
residual coordinates have the same canonical fixed-root consistency set.

## Remaining closure

The next proof must establish `ExactFixedK13ResidualInvariant` from execution
causality: all data in `exactFixedK13IntrinsicBad` is committed by the completed
prover prefix before the selected final-work digest and q16 forest are exposed.
The needed equality is therefore a scheduler/source noninterference lemma, not
a new cryptographic assumption and not a new probability estimate.

## Verification

Focused build:

```text
lake -Kjobs=1 build AspisFormal.K1.V7Tag73ExactFixedQ16ResidualFactorization
exit: 0
wall: 10.24 s after dependency cache warmup
peak RSS: 5,897,715,712 bytes
swap: 0
```

The cold dependency fill peaked at 9,556,656,128 bytes, below the 12 GiB
factorization rule.  The final endpoint theorem axiom union is exactly:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, or project-defined
axiom in either new module.
