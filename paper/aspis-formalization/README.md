# Aspis paper

This is the canonical arXiv and IACR manuscript:

> **Aspis: End-to-End Formal Verification of a Transparent Private Spend on Solana**

The paper reports, to our knowledge at the 24 August 2026 search cutoff, the
first publicly evidenced Solana mainnet transaction to directly verify a
transparent, computationally hiding private-spend proof and atomically record
its nullifier and new pool state within the compute limit.

Its main formal result is an end-to-end Lean theorem for every successful
execution of the deployed proof-checking path. The theorem derives every
acceptance-critical transcript, work, query, opening, low-degree, relation,
and accumulator fact from the same translated Rust call. The mathematical
development gives the complete evaluated argument, including spend-witness
extraction, concrete field and encoder results, coherent four-fold extraction,
the exact capped-query law, fold duality, theft and state reductions, and the
finite security experiment. The `2^-100` statement is a conditional
work-normalized theorem, with raw post-grinding accounting reported
separately.

Repository declaration names and release labels are intentionally absent from
the manuscript. [`ARTIFACT.md`](ARTIFACT.md) maps its mathematical theorem
names to exact Lean declarations, source files, replay commands, hashes, and
mainnet evidence.

## Build

From this directory:

```sh
mkdir -p ../../output/pdf
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../../output/pdf aspis-formalization.tex
```

The final PDF is `output/pdf/aspis-formalization.pdf`.

## Submission source

The arXiv source set consists of:

- `aspis-formalization.tex`
- `sections/`
- `references.bib`

Build products, Lean files, deployment bundles, and repository metadata are
linked through the artifact guide and should stay out of the TeX upload.
