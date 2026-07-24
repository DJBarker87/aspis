# Proofs connecting production Rust to Lean

A correct mathematical model is only part of the implementation story. This
directory connects selected production V5 prover and verifier paths to the
Lean models in [`AspisFormal/`](../AspisFormal/).

Charon extracts the selected Rust, Aeneas translates the extracted code into
Lean, and bridge proofs show that the generated definitions agree with the
Aspis models for the stated release scope. Lean checks the generated
definitions and the bridge proofs together.

For a plain-language account of both proof layers, start with
[`docs/formal-verification.md`](../docs/formal-verification.md). The theorem
map below is the exact technical record of the Rust-to-model coverage.

## Current V5 integration theorem

The principal result is
`FormalClosureStream1.current_source_combined_capstone` in
[`current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`](current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean).
It combines:

- extracted Component-A matrix execution for the selected release schedule;
- generated Component-B evaluation and Component-C public output; and
- reading the Tag-67 work bytes plus all six ordered work checks.

The production Rust verifier enforces the GoodA and GoodB gates for every
accepted selection. The combined theorem's Component-A conjunct is narrower:
it proves the extracted path for the selected release schedule. A universal
Rust-to-model theorem connecting the extracted `candidate_is_good` path to
`VerifierEnforcesGoodA` remains open.

The Tag-67 side enters through
`AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure`. Its only
remaining Rust-to-Lean assumption is the exact transcript hash application:

```text
actualTranscriptGrindingDigest state nonce
  = rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

That equation names the function-pointer call that pinned Aeneas cannot
translate. Given successful work-byte guards and reads, the decoded values,
leading-zero test, and six ordered checks follow inside the theorem.

This proof layer is bound to the V5 release. Tag 67 is enabled in the
default verifier dispatch, and the SBF has SHA-256
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.

## Proof map

| Path | Role |
| --- | --- |
| `current-source-abc-capstone-20260722/` | A/B/C and Tag-67 integration theorem |
| `component-b-mask/unified-current-20260722/` | Current generated Component-B evaluator/sampler and maintained bridge |
| `component-b-layout-bindings/` | Rust layout and relation-claim bindings |
| `component-c-runtime-downstream/` | Four rounds, finish, packer, and public deployed output |
| `tag67-work-wire-correspondence/` | Work-byte reads, predicate, ordered six-step verifier, and final integration |
| `v5-transcript-absorb-input/` | Transcript payload ordering |
| `proof/` and `lean432/` | Pinned field-operation proof base and Lean 4.32 compatibility harness |
| `FIELD-OPS.md`, `M31-INVERSE.md`, `CM31-MULTIPLICATIVE.md`, `QM31-ADDITIVE.md` | Focused arithmetic proof reports |

The dated directory suffixes identify the extraction snapshot used by the
release theorem; they are snapshot labels, not active work queues.

## Replaying the final integration

The maintained Lean project is the quick, fresh-clone check:

```sh
cd AspisFormal
lake exe cache get
lake build
```

The retained V5 translations were produced with Aeneas
`b59d5188c082f704a418c7cb4e52ad69328002d1` and Charon
`cb50ff16b9f1066b8a97dc06da704de2da2fa41c`. Their final proofs replay under
pinned Lean 4.32 through these entry points:

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
