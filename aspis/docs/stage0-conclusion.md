# Stage 0 Conclusion

Date: `2026-07-04`

Status: **CONDITIONAL GO to Stage 1** for one measured target; RED for the
old narrow-layout lr14 target and for Johnson q80.

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

## Stage 1 Entry Condition

Stage 1 may start only under this explicit condition:

- the headline track is capacity-labelled / heuristic until the soundness
  note is complete
- q32/g32 is treated as a hypothesis to audit, not a claim
- if Stage 1 requires a query schedule whose measured projection leaves less
  than roughly `150K` CU of slack before constraint composition, the single
  transaction plan RED-stops and split verification becomes the named fallback

This closes Stage 0 as a conditional engineering GO, not as a security freeze.
