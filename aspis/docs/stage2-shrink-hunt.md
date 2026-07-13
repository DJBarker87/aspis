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

(every number carries its reproduction command)

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

### Sumcheck allowance probe — the risk-retirement item, and it fired

`stage2-sumcheck-probe` (mu-batched claims, transcript-absorbed round
messages, boundary checks, Horner terminal evaluation, block-periodic
selectors; eq and C(v) excluded — the composition probe prices those):

| reading | shape | measured CU |
| --- | --- | ---: |
| optimistic | 10 rounds, 7 coeffs, 3 claims, 16 sel, 3 exc | 65,901 |
| **central** | 10 rounds, 8 coeffs, 3 claims, 24 sel, 5 exc | **83,849** |
| pessimistic (T3 nu=14 budget) | 14 rounds, 8 coeffs, 4 claims, 48 sel, 8 exc | 143,533 |

**The synthetic 30,000-CU allowance was understated by +53,849 CU
(central).** Every projection in `feasibility_decision.json` recorded
before this artifact carries that error; from here on the measured central
value replaces the allowance. At the pre-hunt shape (k'=84, r=4) the true
central projection is ~1,105,900 — over the strict ceiling before any
variance or bracket penalty. The hunt's real requirement was ~54K higher
than registered, exactly as the review suspected.

### k-axis sweep (isolated deterministic kernels, same build)

| width / shape | RLC total | leaf | composition central | composition stress |
| --- | ---: | ---: | ---: | ---: |
| k'=84 (r=4 current) | 211,858 | 11,519 | 120,275 | 152,299 |
| k'=67 (r=3) | 171,005 | 10,295 | 95,601 | 122,102 |
| **k'=51 (r=2)** | **131,759** | **9,143** | **70,954** | **88,617** |
| k'=49 (r=2 + GKR) | 128,621 | — | — | — |

Layout findings (research track, code-verified reasoning): the 16-column
consumer interface cannot overlap round outputs (no cross-row shifts in a
multilinear opening; producer endpoints reuse the previous row's outputs
free, consumers pay). Statement aux values live in unused rows of the same
columns, so k_main = 16r + 16 exactly. **Block alignment matters: r=4's
6-row blocks do NOT factor over the Boolean cube, so §5's stated O(2^b)
block-periodic selector form was silently false for the current
candidate**; r=3 gives 2^3-aligned 8-row blocks and makes §5 true as
written; r=2 requires padding to 2^4-aligned 16-row blocks — 49 x 16 = 784
rows of 1024, fits, with idle cells constrained off periodically. Rows:
r=2 -> 784, r=3 -> 392; r=1 exceeds the cap (pre-registered floor).

### Query/grinding trade (8-seed g16 means, radix-4, production Verify)

| profile | mean CU | range |
| --- | ---: | ---: |
| q36 | 681,619 | 27,275 |
| q34 | 644,990 | 48,668 |
| q32 | 615,946 | 45,047 |

q36 -> q34 saves **36,629** mean (mean-difference SE ~6-7K at these seed
counts); q36 -> q32 saves 65,673; marginal ~16.4K/query, matching the
independent estimate. The q-linear statement terms add ~7.9K (q34) /
~15.9K (q32) at k'=51 on top. Production pairings q34/g36 (grind ~30-80
min) and q32/g40 (~half a day) hold 2q+g = 104 and RAISE the proven floor
to 67.6 / 69.8 bits.

### Priced and rejected (research track, citations verified)

- **LogUp-GKR helper elimination: NET LOSS ~175K CU central** (adds
  ~268-427K: 78 degree-3 sumcheck rounds at ~360 CU/QM31-mult plus
  per-layer overhead; deletes only ~154K of C2 + RLC width). Engineered
  floor ~235K still exceeds the delete. GKR-LogUp pays where verifier
  mults are nearly free (recursion: SP1 Hypercube); on SBF it is
  backwards. Two further flags: the 2023/1284 paper defers its formal
  soundness proof, and a univariate-only claim language would force a
  post-chi Lagrange-kernel commitment (the Miden two-aux-column outcome).
  Pre-written abandon criterion (>143K) would have fired at 2-3x.
  [ePrint 2023/1284; stwo gkr_verifier.rs; SP1 Hypercube; Miden PR #1493]
- **STIR domain-halving: decline now priced** — ~70-90K net for a full
  restructure plus a circle-code STIR theory step that does not exist in
  the literature; strictly dominated by the adopted package.
  [ePrint 2024/390]
- **Carried-fold: measured anti-shrink** (+15,535 CU / +5,536 bytes at
  lr12, stage0 record) on top of the conjugate-backend analysis.
- **Merkle cap-truncation, digest truncation, Gruen eq-factor alone,
  SWAR/packing/u128 RLC variants**: single-digit-K or measured losers.

## Hunt close — the pre-registered condition PASSES at the r=2 shape

**Adopted package: r=2 layout re-freeze (k' = 51, 16-row-aligned blocks,
784 rows) with the measured sumcheck replacing the allowance. No fold,
rate, query, or C2 changes.**

| reading | CU | vs strict 1,071,000 |
| --- | ---: | ---: |
| central: 678,407 PCS + 9,143 leaf + 131,759 RLC + 70,954 comp + 83,849 sumcheck | **974,112** | **-96,888** |
| + composition stress (88,617) | 991,775 | -79,225 |
| + worst-of-16 draw (+55,786) | 1,029,898 | -41,102 |
| + stress + draw (combined worst) | 1,047,561 | **-23,439** |
| (nu=14 sumcheck, + stress + draw) | 1,107,245 | sensitivity-only — see labels |

Close condition: `974,112 <= 1,071,000 - 27,893 (half observed range)` →
**passes by 68,995 CU.** The condition's final-shape multi-seed re-check
happens on the integrated proof's own >= 8 draws, as registered. The
boring pair closed the hunt without GKR leaving the reading pile.

### Ledger labels (review, before hardening)

1. **Draw-row anchor annotation.** The +55,786 rows add the full
   fixed-shape range to a central anchored at the g32 draw, which the
   16-seed study places +2,236 (0.33%) above the fixed-shape mean. The
   plausible worst-draw increment from that anchor is max - anchor =
   **~17,238 CU**, not 55,786; the conservative rows stand, but the
   combined-worst margin is plausibly **~62K**, not 23K. A reader taking
   23K as the margin is reading the double-counted tail.
2. **The nu=14 pessimistic sumcheck reading is unreachable at lr10** (the
   zerocheck runs nu = 10 rounds over 2^10 rows; nu <= 14 is T3's
   conservative budget, not a shape). It is sensitivity-only and is
   excluded from every gate statistic.
3. **RLC seam basis.** The 131,759 figure is total-probe basis and
   includes the probe's per-query value-synthesis scaffold that the real
   verifier does not run (it parses leaf bytes instead) — the
   conservative direction. The seam resolves at integration, where the
   real parse-plus-RLC path is measured in place of the synthetic loop;
   the incremental-over-baseline basis for fixed51 is recorded in
   `wide_rlc_probe.json` alongside the total.

### Rulings (`2026-07-10` review)

**Post-close s2 overlay (`2026-07-10`, historical component arithmetic):**
the shrink close above was an s1 base. The contamination-free s2 A/B adds
49,099 CU, which moved the old arithmetic q36 total to 1,096,660 registered;
q34/g36 saved 44,479 CU and produced 1,052,181 in that same model. The
corrected two-helper PCS scaffold later measured +113,876.5 CU mean while
still omitting exact-wide payment components, so both additive totals are
retired as live product projections. q34 remains the named held lever, but
exact-wide integration must reprice it; the original s1 close remains valid
history, not a current q36/s2 verdict.

- **Ruling 1: r=2 / k' = 51 FROZEN**, note-first, with four conditions —
  tracked in the soundness note §8 freeze record: (i) T5' parametric
  (118.36 bits at k'=51, pin <= 52); (ii) the original m=534 recount
  covered state continuity only and is superseded by the endpoint-local
  m=589 trace layout (T6 sensitivity 110.7104); the conservative m<=1024
  line stays binding until the randomized constraint registry lands; (iii)
  padding rows constraint-dead and excluded from both copy multisets,
  round seams inside the periodic part, with a layout-freeze teeth vector
  required for the padding-leak hole; (iv) freeze confirmation on >= 8
  fresh g16 draws at the integrated v4 shape.
- **Ruling 2: q34/g36 HELD as the named recovery lever.** Insurance is not spent before
  the insured events (integration friction, final-shape spread) resolve;
  flat-commit and RLC/leaf fusion queue behind it as pocket levers.
  **Earmark: revisit q34/g36 at publication freeze regardless of CU** —
  67.6 vs 65.5 proven bits is a claims-side improvement priced only in
  grind minutes, and the three-number headline is where it earns keep.
- Calibration note for future envelopes: review estimates of SBF verifier
  costs have now run low three times (composition, C2 phase, sumcheck
  allowance — the last by 40%); measured probes precede belief.

**Historical component-model recovery menu (not a current product deficit):** q34/g36
(-44,479 measured+scaled, floor +2.1 bits, grind cost
30-80 min, needs the §4 re-rule); flat-commit of the small deep layers
(-30-33K estimate AND shrinks the draw spread itself; needs multi-seed
remeasure + named root/KAT re-pin); RLC/leaf single-pass fusion (-10-20K,
kernel-only, measure-first). Exact-wide reconciliation must reprice every row
before use. Pin-flagged and not taken: blowup 2^-3.

**Layout-freeze provenance (later superseded where noted):** §8 k' pin moved
84 -> 52 (T5' improves to ~118.3 bits). The early ~490-link state-only copy
estimate is superseded by the endpoint-local m=589 trace layout; m<=1024 stays
binding until the randomized registry lands. The 2^4-block selector form and
evaluator-corpus reconfirmation of the r=2 composition bracket (32 sbox /
[38, 70] linear) remain current.
