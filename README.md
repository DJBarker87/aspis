# ZK on Solana — measurement scaffolds and the Aspis substrate

## Aspis (Stage 1)

`aspis/` is a self-contained workspace holding the Aspis staged project
(transparent shielded spend on Solana): the native WHIR-style M31 PCS
substrate, its prover, SBF verifier program, and measurement runners. See
`aspis/README.md`, `aspis/docs/aspis-staged-design.md`, and
`aspis/docs/aspis-soundness-note.md`. Stage 0 closed conditionally; Stage 1
has retired q32/g32, pinned the upstream soundness constants, and landed
exact-uniform challenges plus interleaved enforcement of external/OOD
evaluations. The frozen v3 Stage 1 PCS milestone includes the canonical C2
phase and teeth-demonstrated ordering tests. Its literal lr10/q36/g32
verifier measures 943,972 CU; after already-priced statement work the
projection is 1,175,086 CU, leaving only 14,914 CU before the still-unpriced
Stage 2 constraint composition. Stage 2 now has an executable economic-attack
evaluator and isolated SBF measurements: even after a structured/Horner
shrink, the evaluator-confirmed low one-transaction projection is 1,415,268
CU. The project has therefore recorded a three-transaction split-verification
continuation rather than silently weakening the 1.19M target.

# Phase 1 SVM Cost Model

Reproducible Solana/SVM measurement scaffold for transparent-proof verifier cost modeling.

## Commands

- Run the full Phase 1 pipeline:

  ```bash
  cargo xtask phase1
  ```

- Run the follow-on experiment set (real verifier compare, spend-profile scoring, orthogonal sweeps):

  ```bash
  cargo xtask phase1-next
  ```

- Score a hypothetical verifier profile from YAML or JSON:

  ```bash
  cargo run -p svm-cost-model --bin phase1-score -- \
    phase1_results/summary.json \
    examples/phase1/hypothetical-whir-profile.yaml
  ```

Artifacts land in `phase1_results/`, including raw measurements, sample profile scores,
Circle sweep outputs, bootstrap summaries, `summary.json`, and the follow-on
artifacts from `cargo xtask phase1-next`.
