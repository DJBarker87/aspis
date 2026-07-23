# Source-authentic QM31 additive correspondence

The combined artifact extracts the deployed M31, CM31, and QM31 `add`, `sub`,
and `neg` call graph directly from `crates/aspis-core/src/field.rs`. A combined
artifact is required because separately generated operation modules each
redeclare the same Rust types and cannot be imported together.

Pinned inputs:

- Aeneas `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Charon `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Rust `nightly-2026-06-01`
- Lean `v4.31.0`
- audited `field.rs` Git blob `96e8c04efee6a8231adb2723dac9acf975993e06`

Reproduce it with:

```sh
ASPIS_AENEAS_REPO=/path/to/aeneas \
ASPIS_CHARON_REPO=/path/to/charon \
./aeneas-verif/scripts/extract-field-add-sub-neg.sh
```

`proof/QM31AddSubNegProof.lean` proves the exact generated functions preserve
canonicality in every output limb and implement addition, subtraction, and
negation in the explicit nested quadratic tower. It also includes concrete
counterexample theorems for a swap within the first CM31 pair and a swap of the two
CM31 tower blocks.

The generated proof project remains replayable on pinned Lean 4.31. The same
source-authentic theorem chain is also replayed by the isolated Lean 4.32
arithmetic bundle in `component-b-weight-at/arithmetic-lean432/`; import into
maintained `AspisFormal` remains a separate integration step.
