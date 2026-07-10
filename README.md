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
evaluator and isolated SBF measurements. After a historical k'=83 variance
failure, the measured-arithmetic shrink hunt re-froze the layout at
r=2/k'=51: **974,112 CU central and 1,047,561 registered combined-worst**,
23,439 below the strict 1.071M ceiling at s1. The adopted s2 line now has a
measured +49,099-CU cost, moving q36 to 1,096,660 registered (strict-red);
the held q34/g36 lever projects 1,052,181 and restores 18,819 CU of strict
margin. These are preintegration projections, not a product close; the real
v4 statement proof and final-shape draws remain.
Stage 1 has since been REOPENED: the up-to-capacity
conjecture family was disproved (ePrint 2025/2046, 2026/782; no known
attack at these parameters). The ruling keeps t=90 stated at q36/g32/s2;
the source-constant audit gives a provisional 93.73-bit sensitivity but
S-two leaves a finite-length remainder unbounded, so no computed
conjectured value is currently quotable. The ~65.5-bit proven floor is
untouched and remains the only quotable security number. The
product gate stays open until the LogUp relation and wide RLC are integrated
into one real payment proof. The measured reusable field/RLC/Merkle kernels have also been
extracted into SolMath's standalone `solmath-zk` crate at commit `682b5d4`.
Split verification remains the fallback.

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
