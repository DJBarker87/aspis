# Aspis formal security report artifact

This manifest identifies the files needed to inspect and reproduce the report.
The immutable release name is `aspis-formal-security-report-v1`.

## Identifiers

- Formal snapshot used by the report: `45d0ec466133bba6b7c52a39a288809a4943abf2`
- Deployed-program source commit: `06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`
- Repository: <https://github.com/DJBarker87/aspis>
- Paper PDF: `output/pdf/aspis-formalization.pdf`
- Paper PDF SHA-256: `1cffde2a4426f2e4dbaba09e463b6679bb7f899d9f49e702cfc21927476fbd51`
- Paper source: `paper/aspis-formalization/aspis-formalization.tex`
- Lean toolchain: `AspisFormal/lean-toolchain`
- Lean dependency lock: `AspisFormal/lake-manifest.json`
- Rust dependency lock: `Cargo.lock`

The release tag points to the report commit. The formal snapshot is an ancestor
of that commit, so both the formal source and the paper source are retrievable
from one immutable reference.

## Principal Lean entry points

- `AspisFormal/AspisFormal/V5AcceptedSpendRelation.lean`
- `AspisFormal/AspisFormal/V5TranscriptConnection.lean`
- `AspisFormal/AspisFormal/V5MerkleAuthenticationBinding.lean`
- `AspisFormal/AspisFormal/V5FriForwardCompatibleChain.lean`
- `AspisFormal/AspisFormal/V5ForwardAcceptedFalseRawAccounting.lean`
- `AspisFormal/AspisFormal/V5UnifiedSecurityExperiment.lean`
- `AspisFormal/AspisFormal/V5TheftStateTransitionReduction.lean`

The principal files contain `#print axioms` commands for the results cited in
the theorem index. At the recorded snapshot, the reported dependencies are the
standard Lean/mathlib foundations `propext`, `Classical.choice`, and
`Quot.sound`; no project-specific axiom is reported.

## Build the paper

From `paper/aspis-formalization`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../../output/pdf aspis-formalization.tex
```

The PDF build does not require rebuilding Lean, Rust, or the archived proof.
The repository records those checks separately from typesetting the report.
