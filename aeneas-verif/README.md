# Rust-to-Lean verification

This directory contains the curated source-authentic proof layer for the V5
verifier. Charon extracts the selected production Rust, Aeneas translates it to
Lean, and handwritten bridge proofs connect the generated definitions to the
maintained models in [`AspisFormal/`](../AspisFormal/).

The strongest result is
`FormalClosureStream1.current_source_combined_capstone` in
[`current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`](current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean).
It combines:

- source-authentic Component-A correspondence for the frozen concrete schedule
  and maintained Component-B correspondence;
- the actual-current Component-C fold and public-output correspondence; and
- Tag-67 wire decoding plus all six ordered work-verifier steps.

The production Rust verifier enforces the GoodA and GoodB gates for every
accepted selection. The combined theorem's Component-A conjunct is narrower:
it authenticates the frozen concrete schedule. A universal source-authentic
theorem connecting the extracted `candidate_is_good` path to
`VerifierEnforcesGoodA` remains open.

The Tag-67 side enters through
`AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure`. Its only
implementation/model premise is the exact transcript hash application:

```text
actualTranscriptGrindingDigest state nonce
  = rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

That equation names the pinned Aeneas function-pointer boundary directly.
Parser, projection, digest-predicate, and six-step correspondence are proved
inside the closure.

This proof layer is bound to the frozen V5 release candidate. Tag 67 is enabled
in the default verifier dispatch, and the exact SBF has SHA-256
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.

## Proof map

| Path | Role |
| --- | --- |
| `current-source-abc-capstone-20260722/` | Final A/B/C and Tag-67 composition |
| `component-b-mask/unified-current-20260722/` | Current generated Component-B evaluator/sampler and maintained bridge |
| `component-b-layout-bindings/` | Rust layout and relation-claim bindings |
| `component-c-runtime-downstream/` | Four rounds, finish, packer, and public deployed output |
| `tag67-work-wire-correspondence/` | Exact wire reads, predicate, ordered six-step verifier, and final closure |
| `v5-transcript-absorb-input/` | Transcript payload ordering |
| `proof/` and `lean432/` | Pinned field-operation proof base and Lean 4.32 compatibility harness |
| `FIELD-OPS.md`, `M31-INVERSE.md`, `CM31-MULTIPLICATIVE.md`, `QM31-ADDITIVE.md` | Focused arithmetic correspondence reports |

The dated directory suffixes identify the extraction snapshot that entered the
release theorem; they are provenance labels, not active work queues.

## Replaying the final closure

The maintained Lean project is the quick, fresh-clone check:

```sh
cd AspisFormal
lake exe cache get
lake build
```

The source-authentic V5 integration uses pinned Lean 4.32, Aeneas
`b59d5188c082f704a418c7cb4e52ad69328002d1`, and Charon
`cb50ff16b9f1066b8a97dc06da704de2da2fa41c`. Its two final replay entry points
are:

```sh
aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/replay-lean432.sh
aeneas-verif/current-source-abc-capstone-20260722/replay-lean432.sh
```

The integration replay accepts explicit `LEAN432_BIN`,
`COMPONENT_B_ARITHMETIC_OLEAN_DIR`, `GOOD_A_OLEAN_DIR`, and
`COMPONENT_C_OLEAN_DIR` locations so a reviewer can reuse or rebuild the pinned
dependency caches without committing generated object files.

## Curated versus archived material

`main` keeps normalized generated Lean, proof source, reports, and the final
replay entry points. Regenerable LLBC, raw/versioned translations, build logs,
and superseded retarget experiments are preserved at
[`research-archive-v5-production-closure-2026-07-22`](https://github.com/DJBarker87/aspis/tree/research-archive-v5-production-closure-2026-07-22).
This reduces the tracked directory from roughly 40 MB to about 5 MB without
discarding the extraction history.
The archive tag resolves to
[`859d8588d2761fac6714226877c9317f7d697a03`](https://github.com/DJBarker87/aspis/commit/859d8588d2761fac6714226877c9317f7d697a03).

The q18/g37 mainnet transaction predates this V5 proof layer. Its immutable
evidence remains in [`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/);
the V5 closure supports the exact frozen V5 release candidate and does not
relabel the earlier transaction.
