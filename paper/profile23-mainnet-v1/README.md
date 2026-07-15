# Profile23 mainnet paper

`profile23.tex` is the publication source and `profile23.pdf` is the frozen
render. Build from this directory with the mainnet verification block time as
the reproducible PDF epoch:

```bash
SOURCE_DATE_EPOCH=1784065236 FORCE_SOURCE_DATE=1 TZ=UTC \
  latexmk -pdf -interaction=nonstopmode -halt-on-error profile23.tex
```

The source requires a conventional pdfLaTeX installation with BibTeX and the
packages named in the preamble. The release bundle separately authenticates
the frozen PDF by SHA-256.
