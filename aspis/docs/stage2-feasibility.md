# Stage 2 evaluator and feasibility decision

Date: `2026-07-10`

Status: **the no-proof SpendV0-min evaluator passes. The first
single-transaction projection failed, but measured cross-layer math work has
reopened it: the current strict candidate projects to 1,041,944 CU, 29,056
below the 1,071,000-CU ten-percent-slack ceiling. Radix-4 now verifies in a
literal q36/g32 proof; this is not a gate close because the LogUp lookup and
fixed-width wide RLC are not integrated into one payment proof.** The
three-transaction receipt remains the fallback.

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

| kernel/system | before CU | after CU | saved |
| --- | ---: | ---: | ---: |
| frozen q36/g32 PCS verifier, same 21,364-byte proof | 943,972 | **714,111** | **229,861 (24.35%)** |
| optimized binary -> real radix-4 q36/g32 PCS | 714,111 | **678,407** | **35,704 (5.00%)** |
| M31 inverse, per call | 1,226.47 | 346.97 syscall | 879.50 |
| QM31 square, per call | 360.93 | 291.54 | 69.39 |
| Poseidon2-M31 permutation | 24,047.75 | 22,705.25 | 1,342.50 |
| correct q36/k80 gamma-power RLC | 361,963 | **202,031** | **159,932** |
| low constraint composition | 176,844 | **120,275 lookup candidate** | **56,569** |
| g16 real binary -> radix-4 PCS | 734,235 | **657,648** | **76,587 (10.43%)** |

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

## RLC correction

The old `+54,720` k80 layout delta is deprecated. Its loop multiplied every
column by the same gamma, so it did not implement a sound gamma-power RLC. The
replacement `wide_rlc_probe.json` measures all `q * k` raw M31 contributions.
Precomputed powers cost 361,963 CU at q36/k80; a four-product lazy Mersenne dot
reduces it first to 236,170 CU. Delaying the 20 block-result additions until
one final reduction per QM31 limb reaches 220,386 CU. A fixed
`qm31_power_table::<80>` and stack-backed 80-value row reaches **202,031 CU**.
Per-query Horner, packed-pair/four variants, and a u128 whole-dot variant all
lose on SBF and stay out of the chosen path.

The exact k80/q36 wide-leaf marker is 11,231 CU. The associated synthetic path
marker is not added because the measured PCS already contains path hashing.

## Lookup candidate and integrated radix-4 PCS

The strict-slack projection uses one unintegrated statement change and one
integrated PCS change:

1. **10-bit fixed-table range lookup.** Six limbs reconstruct the two bounded
   values; one additional LogUp relation replaces 64 Boolean residuals. The
   isolated composition delta falls from 176,844 to 120,275 CU. The semantic
   evaluator now proves that it preserves the integer-before-field check
   against wrap inflation. The fixed-table LogUp relation/helper oracle now
   passes six teeth vectors; C1/C2 and sumcheck wiring are still pending.
2. **Radix-4 minimal subtree.** Every PCS depth is even (10/8/6/4), matching
   the arity-4 fold. One 129-byte SHA call replaces up to three 65-byte binary
   calls. The real g16 comparison saves 76,587 CU. The literal g32 result saves
   35,704 CU because its transcript-derived query collisions/frontier differ;
   the ledger uses the g32 number, not the friendlier model or g16 proxy.

## Projection ledger

The 30,000-CU statement-sumcheck allowance remains synthetic. Totals below are
therefore feasibility projections, not integrated proof measurements.

| case | projected CU | vs 1.19M | vs strict 1.071M |
| --- | ---: | ---: | ---: |
| historical first shrink | 1,415,268 | +225,268 | +344,268 |
| measured math, current Boolean range/binary Merkle | 1,134,217 | -55,783 | +63,217 |
| plus 10-bit lookup candidate | 1,077,648 | -112,352 | +6,648 |
| **plus lookup and real radix-4 PCS** | **1,041,944** | **-148,056** | **-29,056** |

The final row saves 373,324 CU (26.38%) from the historical checkpoint. It is
candidate-green but the product gate remains
`red_pending_logup_wide_rlc_and_integrated_statement_proof`.

## Split fallback and next gate

`aspis-statement::split` still tests the three-transaction receipt state
machine: canonical order succeeds; PCS-before-statement, binding mix-and-match,
failed verification, wrong authority, expiry, inconsistent combined claim and
replay-after-consume reject. It is no longer forced by the latest projection,
but it remains the fallback if integrated one-transaction measurement misses.

The next gate is deliberately teeth-first:

1. integrate the tested `[0,1024)` LogUp main/helper columns and `sum(h)=0`
   claim into the C1/C2 statement proof;
2. integrate `qm31_power_table::<80>` and the fixed-width outer-lazy dot into
   real wide proof parsing;
3. generate one radix-4 payment proof and run the complete SBF transaction
   five times with both economic and proof-corruption attacks.

The machine-readable ledger is `results/stage2/feasibility_decision.json`.
