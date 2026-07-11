# Stage 1 theta re-derivation under the revised conjecture — AMENDED SENSITIVITY

Status: **reviewed and amended `2026-07-10`; finite-length constants gate
remains open.** The stated ruling remains `t = 90`, but no computed
revised-conjecture number is quotable yet. The binding known-coefficient
sensitivity is about **93.73 bits**; the earlier 93.89 is retained as the
unit-coefficient sensitivity. The only quotable floor remains 65.5 bits.
The deterministic source is `cargo run -p aspis-xtask --
stage1-theta-optimize`, which writes
`results/stage1/theta_optimizer.json`.

## 0. Correction found while drafting this document

Preparing the derivation for review surfaced an error in the optimizer
that produced §9.4's first-committed numbers: **T1' used
sum(domain_r / rho) where the correct numerator set is
sum(degree_r / rho) = sum(domain_r)** — a factor of 1/rho = 4, i.e. two
bits of unwarranted conservatism in T1'. The sanity anchor that catches
it: the refuted-form T1 must reproduce the frozen 111.5906 (it does, with
the corrected mapping; the buggy mapping gives 109.59). Corrected numbers
appear throughout this document; §9.4 is amended in the same commit.
Consequences of the correction under the unit-coefficient sensitivity:
q36/s=2 moved 93.2 -> **93.89** and the t=100 restore moved q45 -> q43.
The subsequent constants audit restores Table 4's first-fold factor 3/2,
moving the provisional sensitivity to **93.73** and the t=100 crossing to
q44. Separately, the gate audit restored the registered stress delta:
option 3 is gate-forced under the binding stress-plus-full-range rule even
at q43. Both correction layers are retained below rather than collapsed.

## 1. Inputs and provenance

| quantity | value | provenance |
| --- | --- | --- |
| rate rho | 2^-2 | frozen profile capacity_lr10_q36_g32 |
| binary entropy H(rho) | 0.811278 | definition |
| field size \|F\| = \|QM31\| | `(2^31-1)^4`, log2 = 123.9999999973 (124 in prose) | §1 |
| layer domains | 2^12, 2^10, 2^8, 2^6 | §1 fold schedule |
| degree bounds per round | 2^10, 2^8, 2^6, 2^4 | §4 table |
| S_T1 = sum(degree_r/rho) = sum(domain_r) | 5,440 = 2^12.41 | §3 T1 provenance paragraph |
| S_T2 = sum(degree_r - 1) | 1,356 = 2^10.41 | §3 T2 (STIR Lemma 4.5 shape) |
| S_T2sq = sum((degree_r - 1)^2) | 2^20.09 | tighter s=2 per-round union |
| grinding | g = 32 bits, query round only | §6 rule, unchanged |
| unchanged terms at frozen r2/k'=51, constraint registry open | T3 117.3853, T4 120.6781, T5' 118.3561, **T6 109.9125 and T7' 111.0000 at m_copy<=1024**; the endpoint-local m_copy=589 trace gives T6 110.7104 and T7' 4(589+1024)/\|F\| = 111.3445 sensitivities; T8' uses the preintegration eight-claim sensitivity 120.9999999973 | §3/§8; final m waits on randomized `ConstraintId` wiring, and final T8' is `(J+2)/|F|` until that registry freezes |
| measured PCS CU/query | 16,418 | query_trade_g16.json, 8-seed means |
| all-in CU/query (PCS + RLC + leaf at k'=51) | 20,332 | 16,418 + (131,759 + 9,143)/36 |
| draw-spread proxy | range 55,786 / half 27,893 | variance_g16.json, 16 seeds |
| registered stress delta | 17,663 | r2/k'=51 projection, `feasibility_decision.json` |
| anchor-corrected draw sensitivity | 17,238 | sensitivity only; registered 55,786 remains binding |
| s=2 CU | **+49,099 measured** (s1 86,815; s2 135,914; 5/5 identical) | `s2_ood_probe.json`; contamination-free isolated transcript/relation A/B, no query/Merkle noise |

## 2. The adopted conjecture and the term mapping

Source statement (note §9.3): S-two Conjectures 1-2 (ePrint 2026/532
App. A.5). This sensitivity assumes their transport to the exact Aspis circle
protocol; the scaled-RS isometry identifies the underlying full code but does
not by itself prove the candidate's grouped folds, custom MLE binding, OOD
sample denominator, or BCS accounting. At
proximity parameter theta = 1 - rho - eta, Conjecture 1 states

    l(theta) <= c1 * 2^(c2 * H(rho)/eta), c1,c2 >= 1.

The optimizer's substitution

    l(theta) = 2^(H(rho)/eta),

therefore pins the **stronger Aspis sensitivity assumption c1=c2=1**; it
is not implied by the paper's existential constants. Conjecture 2 states
`a = l(theta)*n + o(n)` and supplies no finite-n bound for `o(n)`. The
optimizer neglects that term, as S-two's examples do, but this is not a
bound at our `n <= 2^12`; it blocks promotion from sensitivity to a
computed security value.

The radius side is valid for theta below the Elias radius r_E(rho) at
p = 2^31 - 1:
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
  The unit-coefficient reproduction is
  **T1'(eta) = l(theta) * S_T1 / |F|**, bits = log2(|F|) -
  H(rho)/eta - log2(5,440). It is not the binding sensitivity after source
  enumeration: S-two Table 4's FRI-folding row has coefficient
  `3*2^-(k+1)`, which is **3/2 at k=0**, not <=1. The four source factors
  are 3/2, 3/4, 3/8, and 3/16. Applying them exactly gives weighted
  numerator 7,020; retaining 3/2 and clamping the later sub-unit factors
  to one gives the conservative-known numerator
  `1.5*4096 + 1024 + 256 + 64 = 7,488`. The latter produces the provisional
  93.73-bit sensitivity. This still neglects Conjecture 2's unbounded
  finite-length `o(n)`, so it is not a headline. No grinding credit is
  taken on this round (§6 rule; S-two grinds these rounds, we do not).
- **T2' (OOD binding).** Refuted form: C(L,2) * (sum_r (degree_r - 1)) /
  |F| at L <= 40 (STIR Lemma 4.5, s = 1). Revised: same proven formula
  with **L = l(theta)**, list bound now supplied by Conjecture 1 instead
  of the dead L <= 40 clause:
  **T2'(eta, s=1) = (l^2/2) * S_T2 / |F|**, bits = 124 - (2*H(rho)/eta
  - 1 + 10.41).
  **s = 2: per-round C(L,2) * ((degree_r - 1)/|F|)^2, union over rounds
  = (l^2/2) * S_T2sq / |F|^2**, bits = 248 - (2*H(rho)/eta - 1 + 20.09).
  Two variants are emitted, not conflated: the exact per-round union uses
  `S_T2sq = 1,115,748` (`log2=20.09`); the registered-conservative
  square-of-sum sensitivity uses `(S_T2)^2 = 1,838,736`
  (`log2=20.81`), worsening T2' by exactly 0.720703 bits. T2' at s=2 is
  near 200 and never binds, so system bits agree to the printed precision.
- **All other terms unchanged** (T3, T4, T5', T6, T7', T8' — none of
  their derivations route through the refuted radius; T7' is
  SZ/log-derivative, T5' is SZ, etc.).

The union is stated in the **success per unit adversary work** metric.
T1'/T2'/T3-T8' are per-attempt probabilities; Q includes the query
success probability and g-bit grinding work. Converting both branches to
that common metric is what licenses their union—Q is not silently being
unioned with a differently normalized per-attempt term.

System bits at (q, s, eta):

    algebraic_union = -log2( 2^-T1' + 2^-T2' + sum 2^-T_other )
    system          = -log2( 2^-algebraic_union + 2^-Q )

maximized over eta on the grid eta in [0.003, 0.22] step 10^-4.

## 3. Results (corrected and source-enumerated)

The first table is the deterministic reproduction under the original
unit-coefficient sensitivity. It is retained because it catches the
factor-of-rho bug and explains the 93.89 record; it is not current.

| option | eta* | l(theta*) | query | T1' | T2' | alg union | **system** |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| q36/g32, s=1 | 0.071 | 2^11.3 | 90.9 | 100.2 | 91.9 | 91.9 | **90.34** |
| q36/g32, s=2 (unit-coefficient sensitivity) | 0.0501 | 2^16.2 | 94.5 | 95.4 | 196.5 | 95.4 | **93.89** |
| q40/g32, s=2 | 0.064 | 2^12.7 | 98.8 | 98.9 | 203.6 | 98.9 | 97.88 |
| q43/g32, s=2 | 0.076 | 2^10.6 | 101.4 | 101.0 | 207.7 | 101.0 | **100.19** |
| q45/g32, s=2 | 0.086 | 2^9.5 | 102.9 | 102.1 | 209.9 | 102.1 | 101.44 |

Binding known-coefficient sensitivity (T1 numerator 7,488; conservative
square-of-sum T2; exact eta grid ticks are in the JSON artifact):

| option | eta* | system bits | interpretation |
| --- | ---: | ---: | --- |
| q36/g32, s=1 | 0.0715 | 90.3374 | unchanged to quote precision; T2' binds |
| **q36/g32, s=2** | **0.0510** | **93.7263** | **provisional sensitivity; t=90 ruling unchanged** |
| q40/g32, s=2 | 0.0652 | 97.6560 | if selected, state t=95, not 97 |
| q43/g32, s=2 | 0.0778 | 99.9251 | does not cross t=100 |
| q44/g32, s=2 | 0.0823 | 100.5642 | first provisional t=100 crossing; more CU than q43 |

Structure of the optimum: at s=1, T2' (quadratic in l) binds against the
query term; s=2 pushes T2' to ~200 for any plausible list size
(`T2'(l = 2^40, s=2)` is 148.91 bits on the exact per-round union and
148.19 on the conservative square-of-sum union), after
which T1' (linear in l) and the query term co-bind. That is why s=2 is
worth 3.39 bits in the binding known-coefficient sensitivity (90.34 ->
93.73), while the historical unit-coefficient reproduction gains 3.55
bits (90.34 -> 93.89). Under the refuted accounting it was worth +0.99:
the refuted
form had T2 at 103.99 co-binding with a 104-bit query term, while the
revised form makes T2' the s=1 bottleneck.

## 4. Cross-checks

1. **Frozen-number reproduction:** the refuted-form T1 with the corrected
   numerator set reproduces 111.5906 exactly; the same optimizer with
   l = 40 fixed and theta at capacity reproduces the frozen 103.9508 /
   102.9752 (§3) to four decimals.
2. **S-two sensitivity consistency (not a finite-length bound):** their
   Table 6 at beta = 2 (n = 2^20) chooses
   -log2(1-theta) = 1.73 conjectured bits/query. Our s=2 optimum at
   q36 sits at eta* = 0.050, -log2(1-theta*) = -log2(0.300) = 1.737 —
   the unit-coefficient reproduction lands near the same operating point.
3. **Review spot-checks (all confirmed):** CU slope ~20.3K/query all-in
   (measured 16.4K PCS + 3.9K statement q-scaling); s=2 kills T2' with
   headroom to l = 2^40; the q -> bits menu is concave as expected under
   list-factor optimization.
4. **Elias ceiling respected:** every eta* is > 1 - rho - r_E = 0.0275,
   i.e. every optimum sits strictly below the Elias radius; the
   conjecture is never applied outside its stated range.

## 5. What remains conjectural, and conservative choices

No source constant is now implicit:

| source item | source location | optimizer treatment | status |
| --- | --- | --- | --- |
| list multiplier `c1 >= 1` | S-two App. A.5, Conjecture 1 | set to 1 | stronger Aspis sensitivity assumption; not implied |
| entropy multiplier `c2 >= 1` | S-two App. A.5, Conjecture 1 | set to 1 | stronger Aspis sensitivity assumption; not implied |
| finite-length remainder in `a=l*n+o(n)` | S-two App. A.5, Conjecture 2 | omitted | **unbounded at our n by the source; blocks quotation** |
| fold coefficient `3*2^-(k+1)` | S-two Table 4, FRI-folding row | k=0 retains 3/2; k=1,2,3 are clamped upward from 3/4,3/8,3/16 to one | conservative-known numerator 7,488 |
| old capacity/list claim | Crites–Stewart ePrint 2025/2046, Theorem 2 | no numerical constant imported | refutation anchor only; historical form remains dead |
| circle-code transport | S-two §1.4 scaled-RS isometry plus `stage2-circle-soundness-transport.md` | full-code/subcode Johnson facts identified; grouped-fold, MLE-binding, OOD-domain and BCS protocol transport still assumed | domain-specific conjectural step; blocks quotation |

Thus 93.7263 is conditional on `c1=c2=1`, zero finite-length remainder,
and the stated Table-4 mapping. It is a **provisional sensitivity**, not a
security value. The ratification trigger is concrete: pin a finite-n upper
bound for Conjecture 2's remainder and the circle-code transport, encode
both in the runner, and re-run the menu. If the resulting q36/g32/s2 value
falls below 90, reopen the stated headline; otherwise t=90 may be promoted
with the resulting computed value. Until then, 65.5 is the only quotable
floor.

Conservative-direction choices that are actually bounded: s=2 T2' uses
`(S_T2)^2` (0.720703 bits worse than the exact per-round union); Table 4's
three sub-unit factors are clamped to one; no grinding credit is applied to
an algebraic round; and the registered q36 16-seed full range is applied
unchanged to costlier shapes. The smaller anchor-corrected draw is emitted
only as sensitivity.

## 6. Historical option arithmetic at the r=2/k'=51 component base

All-in deltas: `dq * 16,418` (PCS) + `(131,759 + 9,143) * dq/36`
(statement q-scaling) + **49,099 measured s2 transcript/relation CU**.

This table is retained as the note-first security-menu ruling input, not as a
live product projection. The corrected two-helper PCS scaffold subsequently
measured +113,876.5 CU mean and still excludes the exact 49-column C1 seam,
k'=51 recombination, payment constraints, hiding, and g32. Because it overlaps
different partial components, it cannot be added to these rows; exact-wide
integration must establish a new product total.

The binding budget statistic is the registered conservative
`central + 17,663 stress + 55,786 full draw range`. The 17,238
anchor-corrected draw is shown only as a sensitivity. The measured s2 delta
supersedes the entire 5-12K estimate; it is added exactly once.

| option | provisional system sensitivity | central with measured s2 | registered stress+full-range | anchor-corrected sensitivity | verdict |
| --- | ---: | ---: | ---: | ---: | --- |
| 1: q36/s2, t=90 ruling | **93.73** | **1,023,211** | **1,096,660** | 1,058,112 | historical component sensitivity; retired as a live product total |
| strict-line recovery lever: q34/g36/s2 | 94.08 | **978,732** | **1,052,181** | 1,013,633 | historical recovery sensitivity; deliberate second transcript knob, not priced exact-wide v4 |
| 2: q40/s2 | 97.66 | 1,104,539 | 1,177,988 | 1,139,440 | strict dead; 1.19M registered clears by 12,012; if chosen, state t=95 |
| q43/s2 old unit-coefficient crossing comparison | 99.93 under binding coefficients | 1,165,535 | **1,238,984** | **1,200,436** | 1.19M fails under both draw readings |
| 3: first provisional t=100 crossing, q44/s2 | 100.56 | 1,185,867 | **1,259,316** | **1,220,768** | 1.19M fails under both draw readings |

**Option 3 ruling, corrected:** it is dead by the epistemic ruling and now
also exceeds 1.19M under both registered and anchor-corrected draw readings.
The measured s2 line removes the earlier gate-marginal ambiguity.

The stated t=90 security ruling survives. Product feasibility is now red and
unpriced until exact-wide integration. q34/g36/s2 remains the named recovery
lever because it saved 44,479 CU in the old component model while gaining
0.3494 provisional bits, but that margin is no longer asserted. It remains
held because changing q/g is a second transcript knob with a deliberate
proof/KAT re-pin, not a number silently substituted into the current profile.

Historical provenance: the factor-of-rho run put the crossing at q45 and
about +191K; the corrected unit-coefficient run put it at q43/+150K. Both
are superseded by the constants enumeration, but retaining them explains
the ruling trail.

## 7. Reproduction

Run:

    cargo run -p aspis-xtask -- stage1-theta-optimize

The checked-in Rust runner grids eta ticks 30..2200 inclusive with
denominator 10,000, records the exact winning tick and deterministic
smallest-eta tie break, uses `4*log2(2^31-1)` rather than rounded field
bits, and emits `results/stage1/theta_optimizer.json`. Its unit tests pin
the frozen anchor, factor-of-rho signature, both T2 variants, q34 gain,
and registered q43 gate arithmetic.

**Process provenance.** This checkpoint retains the three-leg review
process: author-built reproduction anchors, an independent arithmetic
reproduction, and an adversarial protocol/encoding pass. The third pass
reproduced all four optimizer menu values independently and also found the
`lambda^0` tag/first-limb collision that both prior passes missed. That is
not extra evidence for the conjecture; it is evidence that arithmetic
review and protocol-soundness review catch different error classes, and is
the reason neither leg is being collapsed at publication freeze.
