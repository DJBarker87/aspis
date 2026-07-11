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
23,439 below the strict 1.071M ceiling at s1. The isolated s2
OOD/transcript probe costs +49,099 CU and historically moved the arithmetic
projection to 1,096,660 registered. That is no longer a live product
projection: the corrected two-helper v4 PCS scaffold still excludes the exact
49-column C1 opening, k'=51 recombination, LogUp constraints, hiding, and final
g32 profile. That omitted seam is now measured under the standard 256 KiB heap:
unprepared q36 exhausts 1.4M CU, preparing gamma/Karatsuba factors once lands
at 1,125,266 CU, and consuming canonical wire bytes directly lands at
**1,066,396 CU**. The last step saves another 58,870 CU; total reclaim from the
unprepared cap is at least 333,604 CU. The optimization works, but this seam
alone leaves only 123,604 CU against 1.19M while excluding PCS and payment
work. It overlaps the scaffold's scalar C1/C2 path, however, so it is not an
integrated verdict and cannot be added to the scaffold. The non-additive
current-CM31 reconciliation now exhausts the 1.4M meter on all eight q36/g16
draws (only `>=1,400,001` is claimed). The column audit also closes the type
question: M31 C1 symbols are valid under a genuine circle-polynomial PCS, not
as a wire-only edit to the current PCS. A pinned host conformance test covers
the 49-column MLE message encoding, first-fold/OOD algebra, secure-circle
sampler/tensor weights, and the natural-to-bit-reversed later-line fold bridge;
the standard-heap shape probe's winning streaming RLC is **552,289 CU**,
48.21% below the comparable CM31 diagnostic. That is isolated candidate
evidence, not product headroom: production circle/C2/transcript wiring,
authenticated later line-FRI layers, soundness transport, and an in-place
eight-seed verifier remain open.
Append-only tag 24 now owns the exact `0x0b` diagnostic header and 784-byte
M31 leaf declaration, but deliberately rejects after framing; production tag
6 rejects the same flagged bytes, while a feature-gated weakened build accepts
the legacy-basis misclassification vector.
One-transaction versus split remains a project-owner ruling; q34/g36 remains
held.
Stage 1 has since been REOPENED: the up-to-capacity
conjecture family was disproved (ePrint 2025/2046, 2026/782; no known
attack at these parameters). The ruling keeps t=90 stated at q36/g32/s2;
the source-constant audit gives a provisional 93.73-bit sensitivity but
S-two leaves a finite-length remainder unbounded, so no computed
conjectured value is currently quotable. The ~65.5-bit proven floor is
untouched and remains the only quotable security number. The
product gate remains open while the one-transaction and receipt-bound options
are measured independently. The measured reusable field/RLC/Merkle kernels have also been
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
