# Stage 2 evaluator and feasibility decision

Date: `2026-07-10`

Status: **the historical k'=83 variance failure is superseded by the
review-ratified r2/k'=51 shrink. Its central projection is 974,112 CU and
its binding registered stress-plus-full-range reading is 1,047,561 CU,
23,439 below the strict 1,071,000 ceiling at s1. The measured s2 A/B adds
49,099 CU, moving current q36 to 1,096,660 registered—25,660 over strict.
The held q34/g36 lever saves 44,479 CU and projects 1,052,181 registered,
restoring 18,819 CU of strict margin, but it is not silently adopted as a
second transcript change. This is not a product gate close: the LogUp
lookup, fixed-width wide RLC, and v4
statement proof are not yet one measured SBF proof, and the final-shape
draw set must still pass the registered rule.** The three-transaction
receipt remains the fallback.

## Executable statement oracle

`aspis-statement` implements the direct semantic evaluator before proof
plumbing. It pins Poseidon2-M31 to `p3-mersenne-31 = 0.6.1`: width 16,
rate/capacity 8/8, alpha 5, 8 full rounds and 14 partial rounds. The scalar and
lazy-linear implementations pass Plonky3's width-16 KAT and differential tests
over 16 deterministic states. Parameter source:
[Plonky3](https://github.com/Plonky3/Plonky3); construction source:
[Poseidon2](https://eprint.iacr.org/2023/323.pdf).

The 13-vector economic corpus passes in `results/stage2/evaluator_corpus.json`:
valid spend, field-wrap inflation, wrong asset/public binding, wrong anchor,
wrong path, forged ownership key, wrong nullifier, wrong output commitment,
double-spend replay, zero and `2^30-1` boundaries, `2^30` rejection, and
balance mismatch. The six-limb 10-bit lookup evaluator now replays all 13 with
the same accept/reject classification. Two additional teeth vectors inject a
non-member limb (`1024`) and corrupt reconstruction; both reject with their
specific lookup errors. Six further vectors exercise the LogUp helper, degree-3
local relation, multiplicities, active-pole handling and `sum(h)=0`. The key
teeth vector satisfies every local row for an unmatched nonmember and is
rejected only by the total-sum claim. The algebra is pinned; its columns are
not wired into the PCS yet.

## Measured `solmath-zk`-shaped wins

All SBF runs use Agave 2.3.0 and repeat five times identically.

Methodology note: `Verify` semantics changed at the kernel-integration
commit. The production `Verify` instruction now selects the optimized
cached-domain/conjugate-denominator path; the previous software path
survives as `VerifyLegacySoftware`, and `VerifyFast` is a wire-compatible
alias of `Verify`. Every before/after CU comparison must therefore name the
instruction semantics it measured. The 943,972 -> 714,111 row holds the
proof bytes fixed and changes only the verifier implementation; the
`verify_cu` fields in the radix-4 artifacts record production `Verify`.
Remeasuring the g16 comparison under the `Verify` discriminant moved both
variants by exactly -5 CU (instruction-dispatch cost; identical proof
bytes, SHA-256, and savings), which is why the g16 row reads 734,230 ->
657,643 rather than the VerifyFast-era 734,235 -> 657,648.

| kernel/system | before CU | after CU | saved |
| --- | ---: | ---: | ---: |
| frozen q36/g32 PCS verifier, same 21,364-byte proof | 943,972 | **714,111** | **229,861 (24.35%)** |
| optimized binary -> real radix-4 q36/g32 PCS | 714,111 | **678,407** | **35,704 (5.00%)** |
| M31 inverse, per call | 1,226.47 | 346.97 syscall | 879.50 |
| QM31 square, per call | 360.93 | 291.54 | 69.39 |
| Poseidon2-M31 permutation | 24,047.75 | 22,705.25 | 1,342.50 |
| correct q36/k80 gamma-power RLC | 361,963 | **202,031** | **159,932** |
| low constraint composition | 176,844 | **120,275 lookup candidate** | **56,569** |
| g16 real binary -> radix-4 PCS | 734,230 | **657,643** | **76,587 (10.43%)** |

The Poseidon2 row has **zero current verifier-gate impact**: Spend
`hash_fields` runs only in the host semantic evaluator today, while the
production PCS verifier uses SHA-256. Its depth-20 saving is future direct-
evaluator evidence, not 66,830 CU of current gate headroom.

The first PCS reduction is real and root-preserving: it verifies the frozen
binary proof with unchanged transcript bytes. Its main reductions are:

- cache public circle powers once, advancing layers with `omega' = omega^4`;
- use specialized CM31/QM31 squares and division by two;
- exploit unit-circle denominators: `s^-1 = conjugate(s)` and the fixed
  order-four element is `-i`, eliminating denominator materialization and
  batch inversion;
- cache the at-most-16 final-domain cubic evaluations instead of evaluating
  them for all 36 colliding queries;
- pack each 65-byte SHA node into one syscall slice without changing the
  concatenated preimage.

Radix-4 is also real now. The literal g32 proof is 26,420 bytes, uses a fresh
domain-separated C1 root, challenges, 32-bit grinding nonce and query set, and
passes five identical SBF runs plus all 12 general corruption cases. A direct
radix-4 frontier mutation rejects on host and SBF. The schedule-level
`TRANSCRIPT_KAT_EXPECTED` remains unchanged because the schedule and sampler
did not move; the transcript-bound input and resulting proof did.

The reusable kernel/API proposal is in `docs/solmath-zk-candidates.md`; raw
evidence is in `results/stage2/zk_kernel_probe.json`,
`results/stage2/radix4_g16.json`, `results/stage2/radix4_g32.json`, and
`results/stage2/poseidon2_probe.json`.

## Historical k80 RLC correction (kernel provenance; superseded as a layout)

The old `+54,720` k80 layout delta is deprecated. Its loop multiplied every
column by the same gamma, so it did not implement a sound gamma-power RLC. The
replacement `wide_rlc_probe.json` measures all `q * k` raw M31 contributions.
Precomputed powers cost 361,963 CU at q36/k80; a four-product lazy Mersenne dot
reduces it first to 236,170 CU. Delaying the 20 block-result additions until
one final reduction per QM31 limb reaches 220,386 CU. A fixed
`qm31_power_table::<80>` and stack-backed 80-value row reaches **202,031 CU**.
These are historical width-80 kernel measurements. The frozen k'=51
projection uses the separately measured fixed51 RLC value 131,759 CU; no
current projection scales from k80.
Per-query Horner, packed-pair/four variants, and a u128 whole-dot variant all
lose on SBF and stay out of the chosen path.

The exact k80/q36 wide-leaf marker is 11,231 CU. The associated synthetic path
marker is not added because the measured PCS already contains path hashing.

## Lookup candidate and integrated radix-4 PCS

The strict-slack projection uses one unintegrated statement change and one
integrated PCS change:

1. **10-bit fixed-table range lookup.** Six limbs reconstruct the two bounded
   values; one additional LogUp relation replaces 64 Boolean residuals. The
   isolated composition delta falls from 176,844 to 120,275 CU. The stress
   row at the top of the per-row linear bracket
   (`evaluator_lookup_range_stress_linear128`) measures **152,299 CU,
   +32,024 over the 70-term reading** — enough on its own to breach the
   strict ceiling, which is why the projection status is
   bracket-conditional. The semantic evaluator proves that the lookup
   preserves the integer-before-field check against wrap inflation. The
   fixed-table LogUp relation/helper oracle now passes seven teeth vectors,
   including the multiplicity-after-chi order attack (soundness note §8);
   C1/C2 and sumcheck wiring are still pending.
2. **Radix-4 minimal subtree.** Every PCS depth is even (10/8/6/4), matching
   the arity-4 fold. One 129-byte SHA call replaces up to three 65-byte binary
   calls. The real g16 comparison saves 76,587 CU. The literal g32 result saves
   35,704 CU because its transcript-derived query collisions/frontier differ;
   the ledger uses the g32 number, not the friendlier model or g16 proxy.

## Historical r4/k80 transcript-draw variance (`SUPERSEDED` by r2/k'=51)

Everything in this section is the pre-shrink registration and result. It is
retained to show why the shrink hunt ran; it is not the current gate state.

The 29,056-CU strict headroom is a single-transcript number. The artifacts
already show material draw-to-draw movement at fixed verifier code (the g16
binary proof measures 734,235 CU where the g32 binary proof measures 714,111;
the radix-4 saving swings 76,587 at g16 against 35,704 at g32), so until a
multi-seed run exists the honest sentence is: **29K headroom on one
transcript, with observed cross-draw movement of roughly 20K**.

The decider is `cargo run --release -p aspis-xtask -- stage2-variance-g16`,
and its acceptance criterion is pre-registered here, before any multi-seed
data exists:

> Let R = max - min of production `Verify` CU for the radix-4
> minimal-subtree variant over 16 fresh transcript draws (seed s in 1..=16;
> statement digest seed s, coefficient seed s) at fixed shape
> `capacity_lr10_q36_g16` with RawFibers and synthetic C2. The strict
> candidate stays green only if `1,041,944 + R <= 1,071,000`. The single
> measured g32 radix-4 draw (678,407 CU) may sit anywhere in its own draw
> distribution, including at its minimum, so the full observed fixed-shape
> range bounds a worst-case redraw under a stated g16-to-g32
> spread-transfer assumption: the query-index and frontier-collision
> mechanism is identical, and grinding bits enter only as a header byte and
> a threshold. `mean + 2*sigma` and the binary-mode spread are reported as
> secondary diagnostics, not binding. If the criterion fails,
> `projection_status` downgrades from `candidate_green` to
> `variance_conditional` and the failing margin is recorded in
> `feasibility_decision.json` before any integration nonce is ground.

Status: **run complete — the criterion FAILS.** Sixteen fresh draws
(`results/stage2/variance_g16.json`, five identical repetitions each, Agave
2.3.0) give radix-4 production-Verify CU spanning **639,859 to 695,645: a
range of 55,786 CU, 1.9x the 29,056-CU single-draw headroom.** The adjusted
projection 1,041,944 + 55,786 = **1,097,730 exceeds the strict ceiling by
26,730 CU.** The non-binding secondary diagnostic mean + 2 sigma = 26,311
would pass by only 2,745 CU; the pre-registered range criterion is the
binding one and no post-hoc switch is taken. Binary-mode spread is larger
still (62,048 over the same seeds; mean 713,570, sigma 14,915). The
measured single g32 draw (678,407) sits within 0.2% of the fixed-shape
radix-4 mean (676,171; sigma 13,155), so the headline number was not a
lucky draw — but a worst-case draw is ~+19K over the mean and the strict
slack claim does not survive it.

Consequence, per the pre-registration: `projection_status` is downgraded
from `candidate_green` to **`variance_conditional`** in
`feasibility_decision.json` before any integration nonce is ground. What
survives: even the worst observed draw stays 92,270 CU under the 1.19M
transaction target and 302,270 under the absolute 1.4M cap, so
one-transaction feasibility is not dead — the 10%-slack claim on an
arbitrary draw is. Closing the strict gate now requires either a further
named shrink of roughly 27K+ CU or an explicit, documented gate-rule
decision about per-draw variance; neither is assumed here.

g16 was used because sixteen fresh 16-bit grinds are affordable where
sixteen fresh 32-bit nonce searches are not; the transfer of the observed
spread to the g32 shape is an assumption named inside the criterion, and
the integrated g32 payment proof remains the final word.

## Historical r4/k80 projection ledger (`SUPERSEDED`)

This table is provenance for the first candidate only. The authoritative
current ledger follows it.

The 30,000-CU statement-sumcheck allowance remains synthetic. Totals below are
therefore feasibility projections, not integrated proof measurements.

| case | projected CU | vs 1.19M | vs strict 1.071M |
| --- | ---: | ---: | ---: |
| historical first shrink | 1,415,268 | +225,268 | +344,268 |
| measured math, current Boolean range/binary Merkle | 1,134,217 | -55,783 | +63,217 |
| plus 10-bit lookup candidate | 1,077,648 | -112,352 | +6,648 |
| **plus lookup and real radix-4 PCS** | **1,041,944** | **-148,056** | **-29,056** |

The final row saves 373,324 CU (26.38%) from the historical checkpoint. The
product gate remains
`red_pending_logup_wide_rlc_and_integrated_statement_proof`, and the
projection status is qualified by the corrections below.

### Current r2/k'=51 ledger with measured s2 overlay

| reading | projected CU | current status |
| --- | ---: | --- |
| s1 central / registered stress+full-range | 974,112 / 1,047,561 | historical base that closed the shrink hunt |
| q36/g32/s2 central / registered | **1,023,211 / 1,096,660** | current profile; strict-red by 25,660 |
| q36/g32/s2 anchor-corrected sensitivity | 1,058,112 | clears strict by 12,888; not binding |
| q34/g36/s2 central / registered | **978,732 / 1,052,181** | named recovery lever; 18,819 strict margin; not yet adopted |

## Historical post-review k'=83 corrections (`2026-07-10`, superseded by r2/k'=51)

Three checks ordered by review ran before integration; two failed and one
recounted a column budget. All three are recorded here and in
`feasibility_decision.json` before any integration nonce is ground.

1. **k' recount (soundness note §8).** The 80-column candidate trace did not
   reserve the lookup's committed columns: k' = 80 main + 1 multiplicity
   (C1) + copy helper h1 + range helper h2 (both C2) = **83**, pinned at
   k' <= 84 with one column of slack. Arithmetic consequences, pending
   integration measurement: the fixed-width RLC term scales 83/80 from
   202,031 to **209,607 CU** (+7,576) and the wide-leaf marker from 11,231
   to **11,652 CU** (+421). T5' recomputes to 117.6 bits and the amended
   union to 103.9453 algebraic / 102.9724 total — the t = 100 headline
   holds.
2. **Variance criterion (pre-registered above): FAILED**, range 55,786 CU.
3. **Bracket stress row: FAILED** the strict ceiling, +32,024 CU over the
   70-term reading.

Historical corrected ledger (all rows include the superseded k' = 83 correction):

| reading | projected CU | vs strict 1.071M | vs 1.19M |
| --- | ---: | ---: | ---: |
| central, 70 linear terms | 1,049,941 | **-21,059** | -140,059 |
| linear=128 bracket top | 1,081,965 | **+10,965 over** | -108,035 |
| worst-of-16 draw | 1,105,727 | **+34,727 over** | -84,273 |
| combined worst (stress + draw) | 1,137,751 | **+66,751 over** | -52,249 |

Reading: the strict ten-percent-slack ceiling survives only the central
reading. Closing the strict gate honestly now requires either a further
named shrink (>= ~11K CU for the bracket top, ~35K for the worst draw,
~67K combined) or an explicit, documented gate-rule decision on per-draw
variance. Neither is assumed. The 1.19M transaction target and the 1.4M
absolute cap cleared in every historical k83 reading. Current q36/s2 is
instead governed by the r2/k51 ledger above.

## Split fallback and next gate

`aspis-statement::split` still tests the three-transaction receipt state
machine: canonical order succeeds; PCS-before-statement, binding mix-and-match,
failed verification, wrong authority, expiry, inconsistent combined claim and
replay-after-consume reject. It is no longer forced by the latest projection,
but it remains the fallback if integrated one-transaction measurement misses.

The next gate is deliberately teeth-first:

1. rule explicitly on adopting q34/g36 versus another >=25,660-CU reclaim
   (or a gate-rule change), with the proof/KAT re-pin named;
2. integrate the tested `[0,1024)` LogUp main/helper columns and `sum(h)=0`
   claim into the C1/C2 statement proof;
3. integrate `qm31_power_table::<51>` (or the generic table specialized at
   51) and the fixed-width outer-lazy dot into
   real wide proof parsing;
4. generate one radix-4 payment proof and run the complete SBF transaction
   five times with both economic and proof-corruption attacks.

The machine-readable ledger is `results/stage2/feasibility_decision.json`.
