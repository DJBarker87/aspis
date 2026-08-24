# Aspis formalization report

This report presents the V5 mathematical construction, its current connection
to one successful translated production verifier call, and the archived
Solana mainnet result. The source connection is complete through the decoded
relation tail; two production final-dot equalities and their outer composition
remain open. The report is separate from the earlier deployment-focused
manuscript in `paper/aspis-spend/`.

Each major claim is paired with Lean definitions or theorem names. The
soundness statement uses one explicit probability experiment, while cited
cryptographic results, primitive security, translation, compilation, and
Solana runtime behavior are listed separately as assumptions.

From the repository root, build only the paper:

```sh
mkdir -p output/pdf
cd paper/aspis-formalization
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../../output/pdf aspis-formalization.tex
```

No Lean or Rust build is required to compile the document.
