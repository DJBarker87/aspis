# Profile 23 manuscript

This directory contains the publication manuscript for:

> **Aspis Profile 23: Transparent Shielded-Spend Verification and Atomic State
> Update from a Pre-Uploaded Proof Account on Solana**

- [Read the paper](profile23.pdf)
- [LaTeX source](profile23.tex)
- [Artifact and reproduction guide](artifact/README.md)
- [Claim-to-evidence matrix](claim-evidence-matrix.md)

The manuscript describes the frozen q18/g37 release: 35/35 release gates, a
66,367-byte proof, a conservative 100.161-bit soundness floor, and a finalized
devnet execution consuming 1,314,332 CU at slot 476,231,605. The exact
publication objects are in [`release/profile23-q18-g37/`](../../release/profile23-q18-g37/).

Build from this directory with a conventional LaTeX installation:

```bash
pdflatex -interaction=nonstopmode -halt-on-error profile23.tex
bibtex profile23
pdflatex -interaction=nonstopmode -halt-on-error profile23.tex
pdflatex -interaction=nonstopmode -halt-on-error profile23.tex
```

Numeric macros in `macros-generated.tex` are derived from the frozen machine
artifacts. The generated PDF is committed so readers do not need a LaTeX
toolchain.
