# State Of Play

## Snapshot
- Date: April 19, 2026
- Workspace state: Phase 1 and Phase 2 experiment harnesses are working, the capacity shipping profile is now frozen from measured data, and Johnson is explicitly a research track.

## Shipping Track
- Shipping profile: `whir-m31-capacity-v0` on `whir_t128_capacity_full`.
- Exact measured config: `reference_canonical` + `karatsuba` + `late_lift_qm31` + `raw_fibers` + `minimal_subtree` + `flat_nodes`.
- Measured total: 927227 CU with 472773 CU margin against the 1.4M cap.
- This is the shortest path to a real vertical slice. The under-construction native WHIR track is not yet the frozen shipping artifact.

## Research Track
- Research branch: `research/johnson-round0`.
- Johnson is treated as a round-0 optimization problem, not as the current shipping target.
- Heap work and generic payload churn are deprioritized; the next wins must come from round-0 algebraic cost reduction.

## What We Now Know
- `minimal_subtree` is a real end-to-end win against separate paths: +87178 CU on the frozen capacity scenario.
- The current repo-local `local_interpolant` path is not a shipping win on the full path: +5209 CU versus raw.
- Canonical multiproof payloads are not ready for shipping: +31586 CU on the frozen scenario versus flat nodes.
- The next serious Johnson work should target proof-carried round-local structure and profile-specific round-0 specialization.

## Recommended Next Steps
1. Build the real native vertical slice around `whir-m31-capacity-v0`.
2. Implement proof-carried round-0 structure for Johnson.
3. Run a multiplication-taxonomy-driven round-0 specialization pass.
4. Revisit prover-emitted payload interop only after the round-0 representation settles.

## Primary Artifacts
- `results/phase2/whir-transcript/raw.jsonl`
- `results/phase2/whir-multiproof/raw.jsonl`
- `results/phase2/whir-fold-payload/raw.jsonl`
- `results/phase2/whir-multiproof-payload/raw.jsonl`
- `results/phase2/whir-m31-capacity-v0/summary.json`
- `results/phase2/manifests/whir-m31-capacity-v0.json`
- `docs/whir-m31-capacity-v0.md`
- `docs/state-of-play.md`
- `docs/phase2-experiments.md`