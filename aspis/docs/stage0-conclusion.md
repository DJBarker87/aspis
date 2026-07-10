# Stage 0 Conclusion

Date: `2026-07-04`

Status: **CONDITIONAL GO to Stage 1** for one measured target; RED for the
old narrow-layout lr14 target and for Johnson q80.

> **Stage 1 supersession (`2026-07-10`):** this is a historical gate record.
> Stage 1 retired q32/g32, ruled q36/g32, enforced external/OOD relations,
> implemented the v3 C2 boundary, and measured the literal profile at
> 943,972 CU (1,175,086-CU combined projection; 14,914 CU left before
> unpriced constraint composition). See
> `aspis-soundness-note.md`; the numbers below remain the Stage 0 evidence.

## Conclusion

Stage 0 has a real continuation target:

- PCS substrate: native WHIR-style M31 v0, `raw_fibers`,
  `minimal_subtree`, `round_batch_inversion`
- statement layout target: `log_rows = 10`, `k = 64` wide rows
- verifier-query target: `q32` with `g32` grinding, capacity-labelled and
  still heuristic until Stage 1
- profile used for lower-row verifier measurement: `capacity_lr10_q32_g16`
  as a verifier-cost proxy; verifier-side `g32` overhead is one grinding hash
  and was already measured in `onchain_g32_summary.json`

This is not a public security claim. It is the target Stage 1 must either
justify or kill.

## Measured Facts

Source artifacts:

- `results/stage0/onchain_summary.json`
- `results/stage0/onchain_g32_summary.json`
- `results/stage0/onchain_layout_target_summary.json`
- `results/stage0/layout_sweep.json`

Native lr12/q40/g16 raw/minimal accepts at `1,063,093` CU. Johnson q80 and
the old lr14 narrow-layout diagnostic exceed the 1.4M CU cap. Proof-carried
round-local is out: it costs more bytes and more CU on native v0.

Lower-row PCS verifier costs:

| profile | status | verify CU | proof bytes | upload chunks | corruption |
| --- | --- | ---: | ---: | ---: | ---: |
| capacity_lr10_q40_g16 | accepted | 773,668 | 14,768 | 24 | 9/9 rejected |
| capacity_lr10_q36_g16 | accepted | 742,795 | 14,512 | 23 | 9/9 rejected |
| capacity_lr10_q32_g16 | accepted | 656,662 | 12,560 | 20 | 9/9 rejected |

Corrected layout-probe costs for `log_rows = 10`, `k = 64`, `q = 32`:

| component | CU |
| --- | ---: |
| wide leaf hashes | 8,987 |
| synthetic Merkle path loop | 60,051 |
| gamma-RLC recombination | 192,127 |

For projection, add wide leaf hashes plus gamma-RLC to measured PCS. Do not
add the synthetic Merkle path loop, because measured PCS verifier cost already
contains Merkle path verification.

## Projection

Against the `1,190,000` CU verify-transaction target:

| target | measured PCS CU | leaf+RLC CU | sumcheck estimate | projected CU | headroom |
| --- | ---: | ---: | ---: | ---: | ---: |
| lr10/k64/q40 | 773,668 | 201,114 | 30,000 | 1,004,782 | 185,218 |
| lr10/k64/q36 | 742,795 | 201,114 | 30,000 | 973,909 | 216,091 |
| lr10/k64/q32 | 656,662 | 201,114 | 30,000 | 887,776 | 302,224 |

The q32 target is the only one with enough headroom to plausibly absorb Stage
1 hardening plus Stage 2 constraint-composition evaluation without immediately
falling back to split verification. q36 remains a reserve target if Stage 1
does not accept q32. q40 fits only on paper and is too tight for the current
statement plan.

**The 302K headroom is not margin — it is a budget already spoken for three
times over.** The projection above prices the PCS, the gamma-RLC
recombination, and the sumcheck rounds. It does not price:

1. **Stage 1 hardening itself**: OOD absorptions, external `(z, v)`
   evaluation-claim binding, the second commitment phase required by the copy
   argument (design §13.8 as amended), and the added transcript work.
2. **Constraint-composition evaluation at the opened point**: with `k = 64`
   columns and Poseidon2's degree-5 relations this is hundreds to low
   thousands of QM31 operations — plausibly `50-150K` CU, unmeasured (the
   Stage 2 isolated-SBF measurement item).
3. **eq / public-input work**: small, but nonzero and currently unpriced.

Any Stage 1 or Stage 2 artifact quoting the q32 projection must call the
`302,224` CU figure a budget for these three unpriced items, not slack.

## Stage 1 Entry Condition

Stage 1 may start only under this explicit condition:

- the headline track is capacity-labelled / heuristic until the soundness
  note is complete
- q32/g32 is treated as a hypothesis to audit, not a claim
- if Stage 1 requires a query schedule whose measured projection leaves less
  than roughly `150K` CU of slack before constraint composition, the single
  transaction plan RED-stops and split verification becomes the named fallback

This closes Stage 0 as a conditional engineering GO, not as a security freeze.
