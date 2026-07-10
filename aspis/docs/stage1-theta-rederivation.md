# Stage 1 theta re-derivation under the revised conjecture — DRAFT FOR LINE-BY-LINE REVIEW

Status: **drafted `2026-07-10`, sent for review before hardening** (ruling
condition 1). Nothing here is quotable until the review lands. This is the
computation behind soundness-note §9.4 and the ratified headline
(t = 90 stated / 93.9 computed / q36/g32/s=2).

## 0. Correction found while drafting this document

Preparing the derivation for review surfaced an error in the optimizer
that produced §9.4's first-committed numbers: **T1' used
sum(domain_r / rho) where the correct numerator set is
sum(degree_r / rho) = sum(domain_r)** — a factor of 1/rho = 4, i.e. two
bits of unwarranted conservatism in T1'. The sanity anchor that catches
it: the refuted-form T1 must reproduce the frozen 111.5906 (it does, with
the corrected mapping; the buggy mapping gives 109.59). Corrected numbers
appear throughout this document; §9.4 is amended in the same commit.
Consequences of the correction: q36/s=2 moves 93.2 -> **93.89**; the
t=100 restore moves q45 -> **q43** (+7 queries, the review's original
5-8 band); and **option 3's "gate-forced" death no longer holds** — see
§6 below, which the ruling record must reflect honestly.

## 1. Inputs and provenance

| quantity | value | provenance |
| --- | --- | --- |
| rate rho | 2^-2 | frozen profile capacity_lr10_q36_g32 |
| binary entropy H(rho) | 0.811278 | definition |
| field size \|F\| = \|QM31\| | 2^124 | §1 |
| layer domains | 2^12, 2^10, 2^8, 2^6 | §1 fold schedule |
| degree bounds per round | 2^10, 2^8, 2^6, 2^4 | §4 table |
| S_T1 = sum(degree_r/rho) = sum(domain_r) | 5,440 = 2^12.41 | §3 T1 provenance paragraph |
| S_T2 = sum(degree_r - 1) | 1,356 = 2^10.41 | §3 T2 (STIR Lemma 4.5 shape) |
| S_T2sq = sum((degree_r - 1)^2) | 2^20.09 | tighter s=2 per-round union |
| grinding | g = 32 bits, query round only | §6 rule, unchanged |
| unchanged terms | T3 117.4, T4 120.7, T5' 118.36, T6 109.9, T7' 111.0, T8' ~121 | §3/§8 |
| measured PCS CU/query | 16,418 | query_trade_g16.json, 8-seed means |
| all-in CU/query (PCS + RLC + leaf at k'=51) | 20,332 | 16,418 + (131,759 + 9,143)/36 |
| draw-spread proxy | range 55,786 / half 27,893 | variance_g16.json, 16 seeds |
| s=2 CU | 5-12K bracket, PROBE PENDING | calibration rule applies |

## 2. The adopted conjecture and the term mapping

Adopted (note §9.3): S-two Conjectures 1-2 (ePrint 2026/532 App. A.5,
c1 = c2 = 1), transported to circle codes by the scaled-RS isometry.
At proximity parameter theta = 1 - rho - eta the list size is

    l(theta) = 2^(H(rho)/eta),

valid for theta below the Elias radius r_E(rho) at p = 2^31 - 1:
r_E = 0.7225 (solved from rho = 1 - H_p(r_E) with
H_p(t) = t + H_2(t)/log2(p)), so -log2(1 - theta) <= 1.850 bits/query is
the hard radius ceiling and every optimum below sits strictly inside it.

Mapping onto the note's terms — each line is a review target:

- **Query term.** Q(q, eta) = q * -log2(rho + eta) + g. Same shape as §4;
  only the radius moved (theta < r_E instead of capacity).
- **T1' (proximity gathering / folding).** Refuted form was
  sum_r (degree_r/rho) / |F| (numerators = domain sizes; frozen union
  111.5906). Revised: the S-two folding-error shape is
  l(theta) * (N/rho) * O(1) / |F| per fold with N the message length,
  i.e. the same numerators scaled by the list size:
  **T1'(eta) = l(theta) * S_T1 / |F|**, bits = 124 - H(rho)/eta - 12.41.
  Conservative reading: the S-two per-fold constant (3 * 2^-(k+1)) is
  dropped (<= 1), and no grinding credit is taken on this round (§6 rule;
  S-two grinds these rounds, we do not).
- **T2' (OOD binding).** Refuted form: C(L,2) * (sum_r (degree_r - 1)) /
  |F| at L <= 40 (STIR Lemma 4.5, s = 1). Revised: same proven formula
  with **L = l(theta)**, list bound now supplied by Conjecture 1 instead
  of the dead L <= 40 clause:
  **T2'(eta, s=1) = (l^2/2) * S_T2 / |F|**, bits = 124 - (2*H(rho)/eta
  - 1 + 10.41).
  **s = 2: per-round C(L,2) * ((degree_r - 1)/|F|)^2, union over rounds
  = (l^2/2) * S_T2sq / |F|^2**, bits = 248 - (2*H(rho)/eta - 1 + 20.09).
  (The first-committed run used (S_T2)^2 = 2^20.82 instead of
  S_T2sq = 2^20.09 — 0.7 bits conservative, immaterial since T2' at s=2
  is ~200 and never binds; retained as stated here.)
- **All other terms unchanged** (T3, T4, T5', T6, T7', T8' — none of
  their derivations route through the refuted radius; T7' is
  SZ/log-derivative, T5' is SZ, etc.).

System bits at (q, s, eta):

    algebraic_union = -log2( 2^-T1' + 2^-T2' + sum 2^-T_other )
    system          = -log2( 2^-algebraic_union + 2^-Q )

maximized over eta on the grid eta in [0.003, 0.22] step 10^-4.

## 3. Results (corrected)

| option | eta* | l(theta*) | query | T1' | T2' | alg union | **system** |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| q36/g32, s=1 | 0.071 | 2^11.3 | 90.9 | 100.2 | 91.9 | 91.9 | **90.34** |
| **q36/g32, s=2 (RATIFIED)** | 0.050 | 2^16.2 | 94.5 | 95.4 | 196.5 | 95.4 | **93.89** |
| q40/g32, s=2 | 0.064 | 2^12.7 | 98.8 | 98.9 | 203.6 | 98.9 | 97.88 |
| q43/g32, s=2 | 0.076 | 2^10.6 | 101.4 | 101.0 | 207.7 | 101.0 | **100.19** |
| q45/g32, s=2 | 0.086 | 2^9.5 | 102.9 | 102.1 | 209.9 | 102.1 | 101.44 |

Structure of the optimum: at s=1, T2' (quadratic in l) binds against the
query term; s=2 pushes T2' to ~200 for any plausible list size
(T2'(l = 2^40, s=2) = 148.9 — the review's spot-check, confirmed), after
which T1' (linear in l) and the query term co-bind. That is why s=2 is
worth +3.55 bits here (90.34 -> 93.89) when it was worth +0.99 under the
refuted accounting (gate_close.json s2 sensitivity block): the refuted
form had T2 at 103.99 co-binding with a 104-bit query term, while the
revised form makes T2' the s=1 bottleneck.

## 4. Cross-checks

1. **Frozen-number reproduction:** the refuted-form T1 with the corrected
   numerator set reproduces 111.5906 exactly; the same optimizer with
   l = 40 fixed and theta at capacity reproduces the frozen 103.9508 /
   102.9752 (§3) to four decimals.
2. **S-two consistency:** their Table 6 at beta = 2 (n = 2^20) chooses
   -log2(1-theta) = 1.73 conjectured bits/query. Our s=2 optimum at
   q36 sits at eta* = 0.050, -log2(1-theta*) = -log2(0.300) = 1.737 —
   independent accounting, same operating point.
3. **Review spot-checks (all confirmed):** CU slope ~20.3K/query all-in
   (measured 16.4K PCS + 3.9K statement q-scaling); s=2 kills T2' with
   headroom to l = 2^40; the q -> bits menu is concave as expected under
   list-factor optimization.
4. **Elias ceiling respected:** every eta* is > 1 - rho - r_E = 0.0275,
   i.e. every optimum sits strictly below the Elias radius; the
   conjecture is never applied outside its stated range.

## 5. What remains conjectural, and conservative choices

Conjectural: exactly Conjectures 1-2 of ePrint 2026/532 with c1 = c2 = 1,
transported to circle codes by the scaled-RS isometry (S-two §1.4), plus
the §9.3 open question (no KKH-style construction is known on
circle-group cosets; our n = 2^12 sits inside KKH's dimensional envelope
and the circle group is fully 2-adic). Everything else in the table is
either proven (T3-T8' derivations, STIR Lemma 4.5 shape) or measured.

Conservative-direction choices: s=2 T2' union computed with (S_T2)^2 in
the committed numbers (0.7 bits worse than the exact per-round union);
S-two per-fold constants <= 1 dropped from T1'; no grinding credit on any
algebraic round; the draw-spread proxy is the q36-shape 16-seed range
applied unchanged to costlier shapes.

## 6. Option economics at the r=2/k'=51 base (974,112 central) — corrected

All-in deltas: dq * 16,418 (PCS) + (131,759 + 9,143) * dq/36 (statement
q-scaling) + ~8K (s=2 bracket midpoint, probe pending).

| option | system bits | delta CU | central | +half-spread | +full-range | verdict vs live gates |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 1: q36/s=2 (RATIFIED) | 93.89 | ~+8K | 982,112 | 1,010,005 | 1,037,898 | strict 1,071,000 survives every reading |
| 2: q40/s=2 | 97.88 | ~+89K | 1,063,459 | 1,091,352 | 1,119,245 | strict central-only; 1.19M everywhere |
| 3: t=100 restore, q43/s=2 | 100.19 | ~+150K | 1,124,436 | 1,152,329 | 1,180,222 | strict dead; **1.19M clears every reading, worst-range by ~10K** |

**Honest record for option 3 (supersedes the "gate-forced" framing):**
under the erroneous T1', restoring t=100 needed q45 (+191K) and the
expected max-over-draws (~1,193K) breached the 1.19M gate — the ruling
message recorded its death as gate-forced on that arithmetic. Corrected,
the restore is q43 (+150K) and **clears the live gate on every reading,
by ~10K at worst-range (within the spread proxy's own uncertainty)**.
Option 3 therefore died **by ruling on the epistemic argument** — 150K
CU and the retirement of the strict ceiling to reprint a label whose
epistemic content changed in November — and not by gate arithmetic. The
ruling's other grounds (strict-line survival under option 1, the proven
floor kept whole) are unaffected by the correction.

## 7. Reproduction

The optimizer is 40 lines of Python recorded in the session transcript
and reproduced by:
grid eta in [0.003, 0.22] step 1e-4; term formulas exactly as §2;
constants exactly as §1. Any independent implementation matching §4's
cross-checks reproduces every number in §3 and §6.
