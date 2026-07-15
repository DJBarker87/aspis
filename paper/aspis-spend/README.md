# Aspis Spend paper

`aspis-spend.tex` is the publication source. Build from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error aspis-spend.tex
```

The source requires a conventional pdfLaTeX installation with BibTeX and the
packages named in the preamble. `macros-generated.tex` carries the measured
release values; it is regenerated, and the PDF is frozen and hash-pinned,
when a release executes. Release builds set `SOURCE_DATE_EPOCH` to the
finalized verification block time so the PDF is byte-reproducible.
