# Stage 2 shrink hunt — pre-registration and measured ledger

Date opened: `2026-07-10`. Purpose: find named, measured CU shrinks that
re-green the strict 1,071,000-CU ceiling after the variance and bracket
failures, before any integration nonce is ground.

## Pre-registered close condition

Registered before the sumcheck probe, k-sweep, and query-trade measurements
ran. Timing disclosure: one probe batch predates this registration (the
fixed67/fixed84/fixed65 RLC widths, the r=3 composition shape, and the
k67/k84 leaf markers ran earlier the same day); everything else in this hunt
is governed by it.

> **The hunt closes when, at the chosen final shape:**
> `central_projection + measured_statement_sumcheck <= 1,071,000 - (observed_range / 2)`
> where `central_projection` uses the multi-seed mean PCS CU (>= 8 fresh
> g16 draws at the final shape), every non-PCS term is an isolated SBF
> measurement at the final shape's exact parameters (no arithmetic
> scaling), `measured_statement_sumcheck` REPLACES the synthetic 30,000-CU
> allowance, and `observed_range` is max - min of those same >= 8 draws.
> No post-hoc criterion substitution: if this fails at every candidate
> shape, the hunt reports failure and the gate-rule decision returns to the
> table.

## Evidence standard (from the measured 55,786-CU draw spread)

- Candidates that change **proof generation** (layout re-freeze, query/
  grinding trade) are evaluated only on multi-seed means (>= 8 fresh g16
  draws); single-draw comparisons are indistinguishable from luck at the
  measured spread.
- Candidates that are **verifier-side only** (kernel swaps at fixed proof
  bytes) may use paired same-transcript comparisons.
- Isolated synthetic kernels (RLC widths, composition shapes, sumcheck
  probe) are deterministic in shape and need no seeds.

## Pre-registered losers (analysis, no measurement spent)

1. **ProofCarriedRoundLocal.** Measured loser in Stage 0 packaging runs;
   the mechanism transfers: it trades bytes for avoided fold arithmetic,
   but the CircleConjugate backend already folds with zero inversions
   (`s^-1 = conjugate(s)` at every layer), and radix-4 changed Merkle
   costs, not fold costs. Expect nothing; not remeasured.
2. **Merkle cap-truncation** (commit to a level-c frontier). The
   minimal-subtree multiproof already dedups the top of the tree — 36
   query paths converge to <= 4 shared nodes by depth 2 — so shipping a
   frontier saves single-digit hashes per tree. Loser by analysis.

## Candidate ledger

| # | candidate | class | status |
| --- | --- | --- | --- |
| 1 | statement-sumcheck probe (replace the 30K allowance) | risk retirement | **priority one: the allowance is suspected 40-60K real, which raises every target** |
| 2 | k-axis layout sweep, r in {2,3} rounds/row (k' in {51, 67}) | protocol (moves k', T5/T6, m) | note-lines below; r=3 measured, r=2 pending |
| 3 | query/grinding trade q34/g36, optionally q32/g40 (2q+g = 104 held) | protocol (moves §4 ruling + proven floor) | note-lines below; multi-seed measurement pending |
| 4 | LogUp-GKR helper elimination | research | priced only with the two-evaluation-point tax included (z_GKR != z forces a claim-merging sumcheck or a second PCS opening point); expected net 0-30K at N=2^10, sign not guaranteed — does not block 1-3 |
| 5 | PCRL / Merkle cap | pre-registered losers | closed |

## Note-lines for protocol candidates (written before code, per standing rule)

**k-sweep (candidate 2).** Row budget: 49 Poseidon2 permutations x
ceil(22/r) rows; r=2 -> 539 rows, r=3 -> 392 rows, both < 2^10; r=1 ->
1,078 rows EXCEEDS the cap, so r=2 is the sweep floor. Column budget:
16r state-output columns + 16 interface columns + statement aux; k' =
16r + 16 + 1 (multiplicity) + 2 (helpers). r=2 -> k' = 51, r=3 -> k' = 67.
Soundness deltas per §8's amended table: T5' = (k'-1)/|F| IMPROVES as k'
drops (k'=51 -> 118.3 bits); the copy multiset m grows with rows/perm
(r=2: ~490 links, r=3: ~343) but stays under the worst-case m = 2^10
reading that E1/T6 already carry at 109.9 bits, so no ledger line moves
adversely. Composition per-row terms scale with r: sbox = 16r, linear
bracket [16r, 32r] + 6 reconstruction. The PCS does not move (N fixed).
The final (r, k') choice is a layout-freeze decision recorded in §8 when
taken.

**Query/grinding trade (candidate 3).** q34/g36 and q32/g40 both hold the
conjectured query term at 2q + g = 104 work-bits; T1-T8 are untouched
(grinding covers only the query term, §6, and that is exactly the term
traded). The **proven Johnson floor improves**: 36x0.93+32 = 65.5 ->
34x0.93+36 = 67.6 (q34/g36) -> 32x0.93+40 = 69.8 (q32/g40), because each
traded query swaps 0.93 proven query-bits for 2 proven ROM work-bits.
Verifier savings scale with q across the PCS opening phase AND the
q-linear statement terms (wide RLC, leaf). Cost: honest prover grind
wall-clock for frozen artifacts — 2^36 SHA-256 is ~30-80 minutes
single-machine, 2^40 is ~half a day; the adopted setting is a product
patience decision recorded in §4 (ruling row + floor line) when taken.
q32/g32 remains retired (96 bits); q32/g40 is a different, sound point.

## Measured results

(filled as runs land; every number carries its reproduction command)

### First batch — predates the close-condition registration, disclosed above

| measurement | shape | CU | command |
| --- | --- | ---: | --- |
| wide RLC fixed-width | k84 q36 | 211,867 total | stage2-wide-rlc-probe |
| wide RLC fixed-width | k67 q36 | 171,011 total | stage2-wide-rlc-probe |
| wide RLC fixed-width | k65 q36 | 167,868 total | stage2-wide-rlc-probe |
| wide leaf | k67 | 10,295 | stage2-layout-probe |
| wide leaf | k84 | 11,519 | stage2-layout-probe |
| composition r=3 central | 67/48/54/2/0/10 | 95,601 | stage2-composition-probe |
| composition r=3 stress | 67/48/102/2/0/10 | 122,102 | stage2-composition-probe |

Build note: fixed80 re-measured at 202,056 this build vs 202,031 on the
prior build (+25 CU build-layout drift); cross-build comparisons carry
this ~tens-of-CU noise and all deltas in this hunt are same-build.
