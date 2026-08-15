# Aspis formalization report

This report presents the V5 formal model and its proof boundary. It is a new
paper, separate from the earlier deployment-focused manuscript in
`paper/aspis-spend/`.

The organization follows a formal-methods report: each major claim is paired
with stable Lean definitions or theorem names, the soundness statement uses
one explicit probability experiment, and assumptions are collected in one
place.

From the repository root, build only the paper:

```sh
mkdir -p output/pdf
cd paper/aspis-formalization
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../../output/pdf aspis-formalization.tex
```

No Lean or Rust build is required to compile the document.
