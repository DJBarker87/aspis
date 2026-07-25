# Aspis: From Lean-Checked Private-Spend Mathematics to Solana Mainnet

`aspis-spend.tex` is the living manuscript on `main`. It presents the
end-to-end evidence chain from maintained Lean 4 mathematics, through selected
production verifier paths translated with Charon/Aeneas and joined to the
models by explicit bridge proofs, to a byte-reproducible SBF binary and the
finalized V5 Tag-67 mainnet execution.

Build it from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error aspis-spend.tex
```

The source requires a conventional pdfLaTeX installation with BibTeX and the
packages named in the preamble. `macros-generated.tex` carries the measured
q18/g37 release values. Those macros, security bounds, and the immutable paper
below remain scoped to the q18/g37 case study. The later V5 result is a
distinct source-correspondence and deployment record: its proof is 75,358
bytes and exact simulation and landed execution both consumed 1,334,452 CU.

The repository PDFs have different jobs:

- `paper/aspis-spend/aspis-spend.pdf` is rebuilt from the current manuscript.
- `release/aspis-spend-q18-g37-mainnet-v1/paper/aspis-spend.pdf` is the
  immutable paper shipped with the q18/g37 mainnet release. Its SHA-256 is
  `f157fbc36a4a6d9f049ae799148f7efce760247ba73f177b435a3157717c64d5`,
  identical to the GitHub Release attachment and the tagged bundle.
- [`paper/drafts/aspis-paper-draft-0.1.pdf`](../drafts/aspis-paper-draft-0.1.pdf)
  preserves the 29-page first publication draft. Its intentionally open V5
  release fields make it a history/review artifact, not the current result.

Later documentation and formalisation improvements update the living
manuscript without changing the executed q18/g37 release record. The living
manuscript states the selected-schedule formal scope, the remaining
transcript-hash-call equality, compiler/runtime/primitive assumptions, and the
absence of an external security audit. Citation metadata keeps the immutable
q18/g37 paper as the preferred historical citation and lists the V5 mainnet
evidence bundle as a separate later release.
