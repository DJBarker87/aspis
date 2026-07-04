# ZK on Solana — measurement scaffolds and the Aspis substrate

## Aspis (Stage 0)

`aspis/` is a self-contained workspace holding the Aspis staged project
(transparent shielded spend on Solana): the native WHIR-style M31 PCS
substrate, its prover, SBF verifier program, and Stage 0 measurement
runners. See `aspis/README.md`, `aspis/docs/aspis-staged-design.md`,
and `aspis/docs/stage0-gate.md`. Stage 0 now has a conditional conclusion:
the old lr14 narrow-layout target and Johnson q80 are RED, while the measured
continuation target is lr10/k64/q32/g32 with a projected 887,776 CU before
Stage 1 hardening and Stage 2 composition costs.

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
