# Component-C runtime downstream correspondence

## Verdict

**GREEN.** The source-authentic Component-C closure now covers the extracted
sampler, exact runtime schedule, encoder inputs, four production-order rounds,
relation finalisation, dynamic packer, and public output.

This closure is part of the default-Tag-67 frozen release candidate, whose
exact SBF SHA-256 is
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.

The strongest public theorem is
`generated_public_run_output_matches_deployed` in
`released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean`.
For every packaged successful generated run it proves:

- the returned vector has exactly the maintained public length; and
- every row equals the corresponding row of maintained `deployedEvaluate`.

`FormalClosureStream1.current_source_combined_capstone` imports that public
closure alongside the actual-current operational folds, the frozen-schedule
Component-A bridge, Component B, and the Tag-67 work-wire verifier.

## What is proved

The accepted Lean 4.32 graph establishes:

- the exact `40 + 4*(n1+n2+n3)` runtime row grammar and value order;
- query-derived later-fibre counts, ranges, and ordinal order;
- the extracted arity-four line and circle folds against the authenticated
  M31/CM31/QM31 model;
- all four relation-round state transitions;
- preservation of the two stored OOD values, including the generated table
  equality that completed the final seam;
- exact relation finish and packer traversal; and
- equality of the complete generated public output with maintained
  `deployedEvaluate`.

The old `RustRuntimeArithmeticCorrespondence` outer-evaluator seam is no
longer a premise of the released public-output theorem.

## Principal proof files

| File | Role |
| --- | --- |
| `proof/RuntimeFoldPrimitiveInstantiation.lean` | Instantiates extracted folds over authenticated field operations |
| `proof/RuntimeFourRoundLaterMaintained.lean` | Four-round maintained fold tower |
| `proof/RuntimeRelationSampleStorage.lean` | Stored OOD identities |
| `proof/RuntimeReleasedTraceFamilies.lean` | Released trace families and output traversal |
| `released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean` | Current generated result shape and final public-output theorem |
| `released-trace-families-current-20260722/replay-lean432.sh` | Lean 4.32 replay entry point |

## Audited boundary

This Component-C theorem has no parser, sampler-order, fold-arithmetic,
packer-layout, or output-row correspondence premise. Its dependencies audit to
Lean's standard `{propext, Classical.choice, Quot.sound}` base, with no
`sorry`, custom axiom, `native_decide`, or raised handwritten proof limit.

The repository-level cryptographic assumptions—hash security,
Fiat–Shamir/random-oracle reasoning, and cited PCS results—remain in the
maintained security ledger rather than being silently attributed to source
extraction.

## Reproduction and provenance

Run:

```sh
aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/replay-lean432.sh
```

The final normalized generated Lean and proof sources remain on `main`.
Regenerable LLBC, raw translations, intermediate logs, and earlier conditional
graphs are preserved at git tag
`research-archive-v5-production-closure-2026-07-22`.

The complete production decision, SBF identity, and accepted-input CU bound
are recorded in `release/preflight/v5-production-freeze.md`.
