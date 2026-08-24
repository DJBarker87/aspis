# Proofs connecting the released Rust verifier to Lean

This directory addresses a simple risk: a correct mathematical model is not
enough if the program checks something different.

Charon extracts selected production Rust. Aeneas translates that extraction
to Lean. Further Lean proofs connect one successful run of the released V5
proof checker to the mathematical objects used by the security argument.
The generated code and the bridge proofs are checked together by Lean.

For a less technical explanation, start with
[`docs/formal-verification.md`](../docs/formal-verification.md). For the short
route through the Rust source, use the
[`accepted V5 source map`](../docs/v5-accepted-source-map.md).

## Current accepted-path status

The checked chain begins with one successful translated call to
`verify_mode9_composite_with_live_statement`. From that same execution it now
derives:

- the parsed proof body and live public statement;
- the transcript state, sampled field values, and six proof-of-work checks;
- the exact 18 distinct query positions used by the verifier;
- all five authenticated opening sections and the values later read from
  them;
- the four FRI folds, coordinate calculations, and final polynomial; and
- the exact 76 decoded claims, four prepared claims, and initial relation
  value; and
- the complete decoded relation tail and four accepted relation rounds.

The phrase **same execution** matters. Earlier component theorems allowed a
caller to provide equalities between selected Rust values and model values.
The current chain obtains the values listed above by following one successful
translated call, so they cannot be mixed across different runs.

The accepted general-accumulator schedule is derived from its four initial
components and eight tensor additions, and every one of the resulting twelve
components is carried through the production folds to the exact terminal
weights and dot product. The source and maintained-field semantics cover every
release-reachable component, including the dense and deferred grouped cases.

The compact constructor, four folds, final assembly, and four-term dot are
also derived from the same accepted execution. The final theorem uses both
accumulator equalities internally. Its clean tracked replay passed on
24 August 2026, so one
successful selected translated verifier call deterministically yields the
maintained accepted-path security-event conclusion; callers supply neither
accumulator equality.

The publication theorem is
`AspisV5AcceptedOneRunDeterministicFinal.accepted_composite_security_conclusion_for_any_terminal_evaluator`
in `V5AcceptedOneRunDeterministicFinal.lean`.

The translated entry path proves the production check between the live
statement and its digest. It does not yet prove that every field of that Rust
statement is the corresponding field of the abstract public-statement object
used by the mathematical false-acceptance and theft models. This is a model
boundary after the selected-call execution proof, not an untracked equality
inside that execution.

The pinned Aeneas version emitted an ill-typed mutable-iterator
back-translation for the compact outer fold. Audit also found that the first
handwritten replacement reconstructed the array from an empty iterator and
therefore discarded its writes. Lean contains a counterexample for that old
wrapper and the proof now uses a corrected Lean wrapper around the extracted
subcalls. The Rust and deployed program were unaffected. An extended Aeneas
translation of the exact unchanged production function produces the correct
iterator handback. The final proof connects its generated caller to the
fold-semantics theorem rather than assuming their equality.

The final assembly is under
[`v5-result-aware-source-link-20260821/`](v5-result-aware-source-link-20260821/).
Its dependencies include the exact transcript samplers, the unchanged
five-section Merkle verifier, the full FRI consumer and coordinate driver, the
prepared-claim loop, and the full relation checker.

## What remains outside the completed source proofs

This is a proof about the selected accepting proof-checker path, not every
line of the repository or every part of Solana. It does not prove:

- Charon, Aeneas, Lean, `rustc`, LLVM, the SBF toolchain, or Solana;
- that SHA-256 or Poseidon2 has the required cryptographic security;
- the production SHA-256 callback semantics;
- the published decoding, PCS/FRI, and Fiat--Shamir results themselves;
- fresh prover randomness;
- extraction, the probability-space connection, and the numerical bounds
  assigned to external failure events;
- the outer account-borrowing, upload, cleanup, and refund code; or
- Solana account locking, rollback, and persistent state behavior.

The production SHA-256 callback is connected to the mathematical hash through
an explicit callback-semantics assumption. That is a boundary around an
external primitive, not a free assertion that the rest of the Rust verifier
matches Lean. Numerical primitive, random-oracle, compiler, and runtime
failure bounds also remain explicit inputs to the security calculation.

These boundaries are listed in
[`docs/assumptions-ledger.md`](../docs/assumptions-ledger.md).

## Proof map

| Area | Main retained package |
| --- | --- |
| One accepted composite call and shared values | `v5-result-aware-source-link-20260821/` |
| Transcript prefix, work successors, field samplers, and queries | `v5-transcript-prefix-extraction-20260815/`, `v5-transcript-field-samplers-20260821/`, and the accepted-entry bridges |
| Five authenticated opening sections | `v5-merkle-unchanged-full-20260820/` and `v5-fri-caller-exact-20260821/` |
| Prepared point claims and full relation call | `v5-relation-acceptance-20260815/` and `v5-relation-full-source-20260820/` |
| Corrected compact mutable-fold extraction | `v5-relation-acceptance-20260815/extraction/compact-fold-extended-20260824/` |
| Full FRI consumer | `v5-fri-consumer-exact-20260815/` |
| Production coordinate calculations | `v5-fri-coordinate-production-full-20260821/` |
| Mathematical models and security reductions | [`AspisFormal/`](../AspisFormal/) |
| Pinned Lean 4.32/Aeneas environment | `lean432/` and `scripts/prepare-aeneas-lean432.sh` |

The dated suffixes identify extraction snapshots. They are not a claim that
the corresponding Rust was written on that date.

## How to review a generated-source claim

For each important function, check four things:

1. the extraction manifest names the production Rust file and function;
2. the generated Lean contains the translated control flow;
3. the bridge theorem proves the mathematical statement from a successful
   generated result; and
4. the aggregate replay imports that exact generated module and theorem.

The source map reduces the accepting execution to fifteen review stops so an
auditor does not need to begin with the roughly 189 KB verifier file.

## Replaying the accepted-path checkpoint

The maintained mathematical project is the quick independent check:

```sh
cd AspisFormal
lake exe cache get
lake build
```

The accepted-path checkpoint replay uses Lean 4.32 and the pinned Aeneas commit
`b59d5188c082f704a418c7cb4e52ad69328002d1`. The compatibility patch and its
file hashes are recorded in [`lean432/`](lean432/). The every-commit formal CI
runs the maintained project and the tracked accepted-path replay; the exact
local command is also recorded beside the aggregate proof. That replay passed
on 24 August 2026 for all 331 tracked modules in the accepted-path closure.

Generated object files are deliberately not committed. Generated Lean source,
bridge proofs, extraction manifests, tool revisions, and replay entry points
are retained so a fresh checkout can reproduce the checked result.

## Historical component proofs

The dated Component A/B/C integration package remains useful as a record of
the staged work. It is not the primary V5 claim after the accepted-path work
began. Public documentation should use the accepted-path status above; the
older component theorem retains its original, narrower hypotheses for
historical review.
