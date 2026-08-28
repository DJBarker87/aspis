# V7 pair-forest withdrawal q16 counter-0 experiment

This is deterministic local LiteSVM/Apple-Metal release evidence. It is a
measurement candidate, not a selected security change. Production activation
remains blocked until the K1.6 analysis proves that choosing among valid final
34-bit work nonces according to the later public q16 schedule is already inside
the quantified adversarial grinding model.

## Exact phase isolation

The matched instrumented verifier changes total CU, but its consecutive
remaining-CU markers isolate the variable first-cap203 scan exactly:

| strict proof | q16-schedule CU | instrumented total CU |
|---|---:|---:|
| transfer, pair index 13 | 29,389 | 1,385,863 |
| withdrawal, pair index 13, unconstrained nonce | 232,351 | 1,603,198 |
| withdrawal, pair index 255, unconstrained nonce | 95,549 | 1,496,342 |
| withdrawal, pair index 13, counter 0 | 4,597 | 1,376,235 |
| withdrawal, pair index 255, counter 0 | 4,631 | 1,404,793 |

The terminal phase is not the cause: it costs 560,734 CU for transfer,
558,740 CU for same-page withdrawal, and 558,610 CU for rollover withdrawal.
The selected verifier still derives the exact first acceptable cap-203 schedule;
no counter is proof-carried or trusted.

## Exact non-instrumented TxV1 results

| operation | proof bytes | TxV1 bytes | combined CU | 1.4M headroom |
|---|---:|---:|---:|---:|
| withdrawal, same page, counter 0 | 30,824 | 964 | 1,367,025 | 32,975 |
| withdrawal, rollover, counter 0 | 30,772 | 997 | 1,395,583 | 4,417 |

Both execute all three 35/31/34-bit work checks, the selected verifier, exact
792-byte ASR8 binding, SPL `TransferChecked`, lane/history/nullifier settlement,
and exact token deltas (vault 10,000 to 9,750; destination 17 to 267). Simulation
and execution metadata are identical.

## Experimental honest-prover predicate and effort

The default path is unchanged. With
`ASPIS_V7_EXPERIMENTAL_COUNTER0_FINAL_NONCE=1`, the fixture generator repeatedly:

1. asks the existing miner for the minimum nonce at or above a cursor;
2. independently checks the ordinary 34-bit work predicate;
3. absorbs the nonce under the unchanged final-work transcript label;
4. derives the unchanged first-cap203 q16 schedule; and
5. accepts only when that schedule's first accepted counter is zero.

Both fixtures tested exactly two valid final-work nonces. Same-page mining ran
03:57:29--03:57:59 UTC (30 seconds total: 15s batch, 3s fold, 12s across two
final searches). Rollover ran 03:58:46--04:01:34 UTC (168 seconds total: 63s
batch, 5s fold, 100s across two final searches). These are single Apple-Metal
KAT measurements, not throughput promises.

Selected nonces and hashes are frozen in the adjacent JSON fixtures. The exact
combined evidence files are:

- `evidence/withdrawal-same-page-counter0-selected-txv1-1400000.json`
- `evidence/withdrawal-rollover-counter0-selected-txv1-1400000.json`
- `evidence/profile-selected-*-runtime3000000.json`

The rollover margin is too small for release even if the conditioning is
proved sound. A separate security-equivalent CU cut and its own source/invariant
proof are still required.
