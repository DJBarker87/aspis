# Aspis Spend manuscript

`aspis-spend.tex` is the living manuscript on `main`. Build it from this
directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error aspis-spend.tex
```

The source requires a conventional pdfLaTeX installation with BibTeX and the
packages named in the preamble. `macros-generated.tex` carries the measured
q18/g37 release values.

The two visible PDFs have different jobs:

- `paper/aspis-spend/aspis-spend.pdf` is rebuilt from the current manuscript.
- `release/aspis-spend-q18-g37-mainnet-v1/paper/aspis-spend.pdf` is the
  immutable paper shipped with the q18/g37 mainnet release. Its SHA-256 is
  `f157fbc36a4a6d9f049ae799148f7efce760247ba73f177b435a3157717c64d5`,
  identical to the GitHub Release attachment and the tagged bundle.

Later documentation and formalisation improvements update the living
manuscript without changing the executed release record.
