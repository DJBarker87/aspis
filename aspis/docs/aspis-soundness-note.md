# Aspis soundness note (Stage 1) — DRAFT, section-by-section review in progress

Status: **DRAFT**. Sections are sent for line-by-line review as they are
written and nothing here is frozen until the whole note survives review
(working rule: no soundness claim frozen without the written reduction being
challenged line by line). Section status ledger:

| section | status |
| --- | --- |
| 1. Protocol as implemented | reviewed; constants corrected |
| 2. The assumption + canonical challenge order | reviewed; **gamma-ordering fix applied** |
| 3. Field-ceiling lemma | reviewed; T7 harmonized, model paragraph added, honest margin stated |
| 4. Per-round query budget | **reviewed, approved** (q38 labeled extrapolated; T1 pinning is a §4 open item) |
| 5. Copy-argument soundness term | reviewed line-by-line; hardened with resolutions |
| 6. Grinding + Fiat-Shamir model | reviewed; binding-term sentence inverted, work-metric phrasing fixed |
| 7. Proven-vs-conjectured ledger | **reviewed, cleared** — T2 split into conjectured/proven forms, proven threshold restated at 2^-109; note is at complete-draft |

Headline decision this note serves (design §13.3, decided 2026-07-04): the
public claim is frozen at **t = 100 bits, capacity-conjectured**; §3 is the
justification. Layout this note is written for (design §13.8 as amended):
lr10, k ~ 64-80 wide rows, rounds-per-row blocks, boundary interface columns,
LogUp copy check, second commitment phase. Query schedule ruled by §4:
**q36/g32** (q32/g32 retired at 96 bits; q38 is the inline contingency).

---

## 1. The protocol as implemented

Everything in this section describes the code at this revision
(`aspis-core`), not a paper protocol. Envelope: `aspis-core/src/proof.rs`
(16-byte header binding profile id, log_rows, log_blowup, query count,
grinding bits, payload and Merkle-mode flags, round count, final-poly
length; then roots, final polynomial, grinding nonce, per-layer openings;
fixed layout, trailing bytes reject).

Fields. M31 = GF(2^31 - 1); CM31 = M31[i]/(i^2+1); QM31 = CM31[u]/(u^2-(2+i)).
|QM31| = (2^31 - 1)^4, log2 = 124 - 2.7e-9 (call it 2^124 with the deficit
noted once here and never again).

Domain. Evaluation domain of the committed polynomial (degree < 2^10 at the
lr10 target, M31 coefficients) is a coset of the order-2^12 subgroup of the
M31 circle group (unit circle in CM31, order 2^31, generator (2, 1268011823));
coset offset has order 2^13. Rate rho_0 = 2^-2.

Fold schedule (lr10). 4 committed rounds, each folding 2 variables (arity 4,
x -> x^4 on the domain): layer domains 2^12 -> 2^10 -> 2^8 -> 2^6, then a
final domain of size 2^4 on which the explicit final polynomial
(4 QM31 coefficients, shipped in clear) is evaluated directly. Leaves pack
whole arity-4 fibers (stride N/4); layer-0 values are CM31, all later layers
QM31 (late lift at the first challenge). **Degree and domain both shrink 4x
per round, so the rate is 2^-2 at every layer — flat, not improving. §4 is
computed for this schedule.**

Transcript order as implemented today (v0 base): absorb(header) ->
absorb(statement digest) -> per round r: absorb(root_r), sample alpha_r ->
absorb(final polynomial) -> grinding check (g leading zero bits), absorb
(nonce) -> derive query positions (exact-uniform masking over the
power-of-two fiber count). One query set, sampled once, traced through all
rounds; each query opens one fiber per layer, the verifier refolds locally
(alpha_r, alpha_r^2; denominators batch-inverted per round) and compares
against the next layer's opened slot, terminating against the final
polynomial. Grinding is a single g-bit check before query derivation; there
is no per-round PoW (recorded divergence, `whir-p3-divergence.md`).

What Stage 1 adds on top of this implemented base: OOD samples per round,
the externally supplied (z, v) evaluation claim, the second commitment phase
for the copy argument, the statement-layer sumcheck, and the challenge-order
requirements of §2.

## 2. The assumption, stated once — and the canonical challenge order

All conjectured terms in this note rest on exactly one assumption, named
here and nowhere re-derived:

> **Capacity conjecture (folded Reed-Solomon over the CM31 circle-coset
> domain).** For the code ensemble produced by the implemented fold schedule
> (arity-4 folding of RS-type evaluations over cosets of 2^k circle
> subgroups), proximity gathering and query soundness behave up to the code
> capacity bound: a codeword delta-far from the code, delta up to 1 - rho,
> survives one uniformly sampled traced query with probability at most
> (1 - delta), i.e. one query yields -log2(rho_worst) bits; and the per-round
> folding/gathering error terms carry denominators |QM31| with the constants
> tabulated in §4.

Everything labelled `conjectured (capacity)` in the ledger (§7) depends on
this and only this. Terms that do not depend on it (sumcheck SZ, RLC
batching, copy-argument compression, zerocheck reduction, Merkle binding
under SHA-256 collision resistance, grinding in the ROM) are labelled
separately. The Johnson-regime alternative is dead for a different reason
(§3): the field ceiling makes its target unreachable anyway, which retires
the johnson_q80 profile without resolving the whir-p3 divergence in its
favor.

**Canonical challenge order for the full (hardened + statement) protocol.**
This order is normative; every implementation change is checked against it,
and the adversarial suite enforces it with failing tests, not prose:

```text
C1 (main witness incl. boundary interface columns; + OOD absorptions)
  -> lambda, chi            (copy-argument compression and evaluation point)
C2 (LogUp helper column h)
  -> mu                     (claim batching)
  -> r                      (zerocheck eq point)
  -> sumcheck messages, round by round (absorb before each round challenge)
  -> CLAIMED COLUMN EVALUATIONS {v_1..v_k} and h-claims ABSORBED
  -> gamma                  (RLC batching)
  -> PCS opening of w* = sum gamma^i w_i at z (the sumcheck terminal point)
```

The bolded step is load-bearing and was caught in review, not design: if
gamma is squeezed before the claimed evaluations {v_i} are absorbed, the
prover sees gamma first and must satisfy only the single linear constraint
sum(gamma^i v_i) = w*(z) — one equation, k free variables. He fixes k-1 of
the v_i to make eq(r,z) * C(v_1..v_k) match his final sumcheck message and
solves the last one from the RLC constraint; the constraint-composition
check is fully bypassed and the entire statement layer evaporates. Same
class as the inflation bug: invisible in every honest-prover test, fatal
against a real one. Likewise C1 -> (lambda, chi) is load-bearing, not
stylistic: the phi values are fixed before chi exists, which is what makes
chi hitting a committed phi a completeness event rather than an attack
surface (§5). The Stage 1 adversarial suite gains a **challenge-order
family**: gamma-before-claims and chi-before-C1 transcripts must reject.

## 3. The field-ceiling lemma (why the headline is t = 100)

**Model paragraph (the frame the table lives in).** The protocol is an
interactive argument compiled by Fiat-Shamir with SHA-256 modeled as a
random oracle; the adversary's resource is its hash-query budget, and
"lambda bits of security" means no attacker achieves success probability /
work ratio better than 2^-lambda. The terms below are round-by-round
(state-restoration) errors: each is the probability that one adversarial
attempt at the corresponding challenge produces a false-accepting
continuation, and FS security is governed by the worst round an attacker
can grind at. The union bound below is conservative — it sums the rounds
instead of taking the max. Two hash assumptions sit UNDER this model and get
their own §7 ledger lines because they are assumptions, not terms: SHA-256
as a random oracle for the transcript, and >= 100-bit collision resistance
for Merkle binding.

**Lemma (informal).** Every algebraic soundness term of the full target
system has denominator |QM31| ~ 2^124, and grinding offsets none of them.
Union-bounded, the system's achievable soundness on this field tower is
roughly 106-112 bits before a single query is spent. Therefore 128 bits was
never reachable on M31/CM31/QM31, and the headline claim is frozen at
t = 100, capacity-conjectured.

Enumeration (lr10 / k' <= 82 / fused sumcheck; numerator shapes first, then
the value at the target parameters, in bits below zero):

| # | term | shape | bits |
| --- | --- | --- | ---: |
| T1 | per-round proximity gathering (4 rounds) | c_r * N_0 / \|F\|, N_0 = 2^12 | ~106-112 (constants pinned in §4) |
| T2 | OOD binding, 1 sample x 4 rounds | R * l * 2^lr / \|F\| — **l is the decoding-list size and is regime-dependent** (see §7: conjectured form shown here assumes capacity-small l) | 112 (conjectured form) |
| T3 | fused sumcheck Schwartz-Zippel | nu * d / \|F\|, nu = 10, d <= 7 | 117.9 |
| T4 | zerocheck eq-reduction (sample r) | nu / \|F\| | 120.7 |
| T5 | gamma-RLC batching over k' <= 82 columns | (k'-1) / \|F\| | 117.7 |
| T6 | copy-argument tuple compression (lambda) | m * w / \|F\| (worst m = 2^10, w = 17) | 109.9 |
| T7 | copy-argument pole/SZ (chi) | 4m / \|F\| | 112 |
| T8 | claim-batching challenge (mu) | (#claims) / \|F\| | ~122 |
| T9 | challenge-sampler statistical distance | fixed by rejection sampling | 0 after fix (was ~25) |

On T1's counting: the four rounds' domains are 2^12, 2^10, 2^8, 2^6, so the
true sum is ~1.33 * 2^12 / |F|, about 1.6 bits better than the 4 * 2^12
used in the bracket. The overcount is **deliberate conservatism**; if §4's
constant-pinning needs the 1.6 bits back, they are real.

Union of T1-T8: dominated by T1 and T6, total ~2^-106 .. 2^-109 of algebraic
error before queries. t = 128 would require every enumerated term to vanish
— not a parameter choice, a different field tower.

**The honest final number.** The query term joins the union — in the
success-per-unit-work metric, where both categories denominate in hashes
(§6): success/work <= 2^-106..-109 + 2^-32 * 2^-72 ~ **2^-103.7
worst-case**. The claim's true margin over t = 100 is ~3.5-4 bits, not the
table's 6-9 — the 6-9 figure is the algebraic ceiling alone and must not be
quoted as the system margin.

Grinding does not appear in the table by construction: the PoW sits before
query derivation and raises the price of re-rolling the query challenge
only; T1-T8 are information-theoretic per-attempt bounds and re-grinding
does not improve any of them. §6 does the careful version.

Corroboration from outside this repo (context, not proof): the WHIR-JB
reference runs 128-bit settings on Goldilocks3 (~192-bit field) and
structurally fails on Goldilocks2; the M31 circle-STARK ecosystem targets
~96-100 bits. The ~124-bit field ceiling also matches the ~124-bit collision
resistance of the 8-limb Poseidon2-M31 digest (design §13.2), so the whole
system lands on one coherent ~100-bit label with no weakest-link asymmetry.

**Finding (T9, fixed in Stage 1 hardening): the implemented QM31 challenge
sampler is not statistically close enough to uniform for a 2^-100 claim.**
`Transcript::challenge_qm31` takes 31 bits per limb and folds the value P to
0, putting excess mass 2^-30 - 1/p ~ 2^-31 on zero: per-limb total variation
~2^-31. The generic bound |P_biased(A) - P_uniform(A)| <= SD applies to
every event, so with ~50 limbs per proof the union cost is ~2^-25 additive —
formally swamping every other term despite corresponding to no attack.
Widening the sample does not fix it (u128 reduction still leaves ~2^-97 per
limb). The fix is **rejection sampling** (the SampleInBall pattern from
FIPS 204), with two implementation requirements that are part of the spec,
not optional detail:

1. Retries consume **fresh transcript bytes deterministically** — append a
   retry counter to the squeeze input; never re-hash the same input, else
   every retry returns the same rejected value and the loop cannot
   terminate.
2. The SBF verifier bounds the retry loop (8 per limb) and **rejects the
   proof on exhaustion**. Per-limb exhaustion probability is (2^-31)^8 =
   2^-248, a completeness event (§6), which is the correct trade on a
   CU-metered chain versus an unmetered loop.

## 4. Per-round query budget — q36/g32 ruled, q32 retired, q38 contingency

Computed for the schedule **as implemented** (§1): 4 committed arity-4
rounds at lr10, degree and domain both shrinking 4x per round.

| layer | domain | degree bound | rho_i | bits/traced query |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 2^12 | 2^10 | 2^-2 | 2 |
| 1 | 2^10 | 2^8 | 2^-2 | 2 |
| 2 | 2^8 | 2^6 | 2^-2 | 2 |
| 3 | 2^6 | 2^4 | 2^-2 | 2 |
| final | 2^4 | 2^2 (explicit) | 2^-2 | — |

**The rate is flat.** There is no per-round rate improvement, so there is
nothing for later rounds to credit: a word that survives folding is caught
by a traced query only at the capacity rate of its loosest layer, and all
layers are equally loose. Per-round query sets — the machinery that exploits
improving rates in WHIR's domain-halving schedule — are therefore
arithmetically empty here, not merely unimplemented: restructuring the fold
(domain-halving) and crediting later rounds are one option, not two, and
that option is a protocol restructure with unmeasured CU. It is declined for
this note; if a future revision adopts domain-halving, this section is
recomputed from scratch.

Query soundness under the capacity conjecture with one traced query set:
attack success per grinding attempt <= rho^q = 2^-2q, each attempt costs
2^g hashes, so the query term contributes **2q + g bits** in the
work/success metric.

| schedule | query bits | verdict | measured PCS CU (lr10) | projection | headroom vs 1.19M |
| --- | ---: | --- | ---: | ---: | ---: |
| q32/g32 | 96 | **retired — 4 bits short of t=100** | 656,662 (measured) | 887,776 | 302,224 |
| **q36/g32** | **104** | **ruled: the Stage 1 schedule** | 742,795 (measured) | 973,909 | 216,091 |
| q38/g32 | 108 | inline contingency (see below) | ~785,900 (**extrapolated**) | ~1,016,975 | ~173,000 |

The q32 -> q36 promotion costs **+86,133 CU** on the measured lr10 slope
(887,776 -> 973,909; headroom 302K -> 216K, already re-labelled in the
Stage 0 conclusion as a budget for three unpriced items). **Contingency,
carried inside this section rather than as a new fork:** if T1's
constant-pinning lands at the bad end of the ~106-112 bracket, q38 (108
query bits) is the escape hatch at roughly +43K CU more on the same
measured slope (~21.5K CU per query). If q38's projection cannot absorb the
Stage 2 constraint-composition measurement, the split-verification fallback
from the Stage 0 conclusion triggers — that ladder is unchanged. The q38 row is
extrapolated, not measured: linearity of the CU slope beyond q36 is assumed
and gets measured only if the contingency fires.

**§4 open item (an experiment, not a ledger entry):** pin, against the
pinned upstream `WizardOfMenlo/whir` reference, with one reproduction
artifact under `results/stage1/`: (a) T1's per-round gathering constants,
and (b) T2's exact OOD term shape — whether the list size enters as l or as
l^2 * (d / |F|) (the dependence is certain, the exponent is not). One
artifact, two constants. This is the one place the 1.6
deliberate-conservatism bits of §3 may be spent. §7 records the outcomes'
status; the work and the artifact live here, per the house rule that every
number traces to a script.

## 5. Copy-argument soundness term (LogUp multiset copy check)

Reviewed line by line before hardening; resolutions from review are folded
in.

**Setting.** Witness table of N = 2^10 rows, k main columns, containing
sequential Poseidon2 chains. Each cross-row link j has a producer row
emitting a w-limb state and a consumer row receiving it. Interface tuples
(tag_j, d_j), d_j in M31^w, and **tag_j a verifier-computable layout
constant** — tags are fixed by the wiring, never witness, else multiset
equality fails to pin which output feeds which input.

**Selectors.** Block-periodic evaluation suffices; **no committed selector
columns.** A selector depending only on within-block position (low b bits of
the row index, b = 4-5) has an MLE that factors into an O(2^b)-term
evaluation at the sumcheck point. Edge rows break strict periodicity —
chain heads with no consumer, tails with no producer, and the ~5 non-Merkle
permutations with a different block pattern — and are handled as explicit
corrections: sel = periodic part +/- sum over exceptional rows of
eq(row_i, x), costing O(exceptions * nu) verifier field ops and nothing
committed. **"Wiring regularity + enumerated exceptions" is hereby a Stage 2
layout constraint** so this paragraph stays true.

**Protocol.** (1) Commit main witness including boundary columns —
commitment C1. (2) Sample lambda (tuple compression) and chi (evaluation
point). (3) Compress: phi_j = tag_j + sum_i lambda^i d_{j,i}. (4) Commit the
helper column h with h_row = sel_P/(chi - phi_P(row)) - sel_C/(chi -
phi_C(row)) — commitment C2, the second phase. (5) Row-local relation fused
into the zerocheck: h * (chi - phi_P) * (chi - phi_C) = sel_P * (chi -
phi_C) - sel_C * (chi - phi_P); each phi is degree 1 in committed values, so
the relation is degree 3, under the d <= 7 sumcheck budget with Poseidon2's
degree-5 S-box (+eq) still binding. (6) One extra batched claim:
sum_rows h = 0.

**Soundness terms.**

- **E1, compression (lambda): <= m*w / |F|.** If the tuple multisets differ,
  consider Q(lambda, X) = prod_{j in P}(X - phi_j(lambda)) - prod_{j in C}
  (X - phi_j(lambda)). Distinct (tag, d) tuples give distinct degree-<=w
  polynomials phi_j(lambda); monic linear factorizations over the integral
  domain F[lambda] are unique, so Q is not identically zero; its
  X-coefficients are polynomials in lambda of degree <= m*w;
  Schwartz-Zippel over lambda gives m*w / |F|. The pairwise m^2*w union
  bound is unnecessary, and it is exactly the UFD argument that makes it so.
- **E2, evaluation (chi): <= 4m / |F|, kept deliberately loose.** The
  logarithmic-derivative lemma applies (multiplicities <= 2^10 << char =
  2^31 - 1): if the compressed multisets differ, sum_P 1/(X - phi) -
  sum_C 1/(X - phi) is a nonzero rational function with numerator degree
  <= 2m - 1; chi must also avoid the <= 2m poles, where the row relation
  degenerates. Sharpening below 4m buys nothing that survives the union
  (E2 sits ~2 bits below E1 in every layout reading); the effort goes to
  pinning T1's constants instead. One subtlety worth its sentence: chi
  hitting a committed phi value is a **completeness** event only because C1
  precedes chi in the canonical order — the phi's are fixed before chi
  exists. That is why C1 -> (lambda, chi) -> C2 is load-bearing, not
  stylistic (§2).
- **E3, helper relation and total-sum:** enforced by the fused
  zerocheck/sumcheck; they add degree (3 + eq, non-binding) and one batched
  claim (T8 increments) but **no new denominators**.

**Numbers.** Worst layout reading (every rounds-block row interface,
m = 2^10, w = 17): E1 ~ 2^-109.9, E2 ~ 2^-112. Chain-boundaries-only
reading (m ~ 40, w = 9): both <= 2^-114. Realistic middle for the record:
at k ~ 64, ~3-4 Poseidon2 rounds fit per row, so ~6-7 rows per permutation
and m ~ 240-300 at w = 17, giving m*w ~ 2^-111.8. **All readings sit inside
the §3 ceiling with the union bracket unchanged, so the m-choice is a
CU/bytes/columns decision, not a soundness one** — and on-chain it is
nearly free either way: h is committed at full column length regardless of
how many entries are nonzero, so the CU delta reduces to w mul-adds per
interface side in the phi evaluations at opened rows. §5 carries the worst
case (m = 2^10); Stage 2's layout freeze documents the real (m, w) and does
not optimize for it.

**Cost of the second phase (C2), to be priced by the hardening
measurement:** one extra root absorb; one extra opening per query in the
phase-2 tree (q ~ 36 over 2^10 leaves — order tens of K CU and ~6-8 KB with
multiproof sharing); one extra gamma term per query in the RLC. If Stage 3's
masking polynomial also needs a post-challenge commitment, both share the
one phase-2 tree; that decision is taken in the hiding note, not silently.

## 6. Grinding, the Fiat-Shamir model, and what grinding does NOT cover

**What grinding offsets: the query term, only, by construction.** The PoW
sits after all absorptions and before query derivation, so each fresh
sample of the query challenge costs the adversary 2^g expected hash
queries. In the work/success metric this adds g bits to the query term
(2q + g, §4). It offsets **no algebraic term**: T1-T8 are per-attempt
information-theoretic bounds on challenges (alpha_r, lambda, chi, mu, r,
gamma) that sit before the PoW in the transcript; re-rolling them is free
of the PoW and bounded by their own denominators, and grinding after them
cannot retroactively improve them.

**The model, carefully (this is the paragraph §3's table lives in).**
SHA-256 is modeled as a random oracle; an adversary with hash budget Q
attacks the FS-compiled protocol by state restoration: pick any prefix of
the transcript, re-roll the next challenge, keep the best continuation.
Security is therefore governed round by round: the attack cost/success
ratio against round i is at least 1/eps_i hash queries (one query per
attempt, eps_i the round's per-attempt error), and 2^g per attempt for the
query round. The system's bits in the work/success metric are then
min_i(-log2 eps_i) over the rounds, which the §3 union bounds conservatively
from below by summing.

**Which term binds — stated the honest way around.** In the work metric the
query round binds (104 < 106-109), but that must not be read as "the
conjectured term is last in line": the query term's 2-bits-per-query rate
IS the capacity conjecture — T1 is the conjecture's algebraic-validity face
and the query rate is its radius face, one conjecture wearing two hats,
which is why §7 puts them on a single shared line. Under proven accounting
on the same schedule (Johnson radius 1 - sqrt(rho) - eta at rho = 2^-2,
delta ~ 0.475 after slack), a traced query buys ~0.93 bits and q36/g32
proves roughly 65-68 bits, not 104. The correct sayable sentence is the
inversion: **every term this note proves clears 2^-109 — T6 at the
deliberately-carried worst-case layout is the binding proven term at
2^-109.9, and sits at ~2^-111.8 under the expected Stage 2 layout, so this
threshold is revisited upward when the layout freezes; T2 is excluded from
the sentence's scope pending its regime resolution (§7) — the binding term
is the single conjectured one, at 104 work-bits; the system's security
equals the capacity conjecture's truth, with no weaker proven link
anywhere.**

**Sampler completeness (from the §3 T9 fix).** Rejection sampling with a
bounded retry loop (8 per limb, fresh transcript bytes per retry via a
retry counter in the squeeze input) rejects an honest proof only if some
limb exhausts all retries: per-limb probability (2^-31)^8 = 2^-248, and
under ~50 limbs per proof the honest-rejection probability is < 2^-242.
This is a completeness event, not a soundness term; it appears here and
nowhere in the §3 table.

**The honest final margin, restated as the one-line summary a reader takes
away:** adversary success **per unit of adversary work** <= 2^-106..-109
(algebraic union, ~1 hash per attempt) + 2^-32 * 2^-72 (query term at
q36/g32, 2^32 hashes per attempt) ~ 2^-103.7 worst-case; the frozen
headline t = 100 holds with ~3.5-4 bits of margin, conditional on the
capacity conjecture (§2) and the two SHA-256 assumptions (§7); the proven
floor on the same schedule is ~65-68 bits (§7). No other number in this
note is the system's security level.

## 7. Proven-vs-conjectured ledger

One line per term. `proven` lines are proven **within the model**, i.e.
conditional on the two assumption lines above them; nothing on a `proven`
line is conditional on the conjecture line.

| item | label | bits / basis |
| --- | --- | --- |
| SHA-256 as a random oracle (Fiat-Shamir transcript) | **assumption** | model floor for every line below |
| SHA-256 collision resistance for Merkle binding | **assumption** | >= 100 bits claimed (128-bit birthday bound) |
| Capacity conjecture — one line, two faces: T1 gathering terms AND the 2-bits/query rate | **conjectured** | T1 ~106-112 (constants: §4 open item); query term 104 work-bits at q36/g32 |
| **Proven floor, same schedule, Johnson-radius accounting** | **proven** | **~65-68 bits**: delta <= 1 - sqrt(rho) - eta, rho = 2^-2, delta ~ 0.475 -> ~0.93 bits/traced query; 36 x 0.93 + 32 ~ 65.5 |
| T2 OOD binding, capacity-l form (the §3 table's 112) | **conjecture-conditional** | 112 — the OOD constant carries the decoding-list size l, which is small only under the capacity conjecture; internally consistent with the conjectured headline, NOT a clean proven line |
| T2 OOD binding, Johnson-l proven form | proven (pending shape pinning, §4 open item) | l ~ 1/(2 * eta * sqrt(rho)) ~ 40 provable; lands ~2^-101..-107 depending on l vs l^2 * (d/\|F\|) shape; either way 30+ bits above the proven floor |
| T3 fused sumcheck | proven (SZ) | 117.9 |
| T4 zerocheck eq-reduction | proven (SZ) | 120.7 |
| T5 gamma-RLC batching | proven (SZ; conditional on gamma-after-claims order, enforced by test) | 117.7 |
| T6 copy-argument compression | proven (UFD + SZ) | 109.9 (worst layout m = 2^10) |
| T7 copy-argument pole/SZ | proven (log-derivative lemma) | 112 (deliberately loose 4m) |
| T8 claim batching | proven (SZ) | ~122 |
| T9 challenge sampler | fixed by construction (rejection sampling, exact uniform) | 0 soundness cost; completeness < 2^-242 |
| Grinding g32 | proven (ROM work accounting, §6) | +32 bits on the query term only |
| **Headline** | **conditional** | **t = 100, capacity-conjectured; success/work <= 2^-103.7 worst-case; proven floor ~65-68** |

The proven-floor line follows house precedent (the WHIR-UD gate reported
"lower 58.0 / upper 100.0"): the positive result does not get a lower
standard than the negatives, and the number a hostile reviewer would
compute anyway is computed here, with the derivation shown. Any public
quotation of the headline carries all three numbers of the last line or
none of them.

T2's split is itself a record of this section doing its job: in draft 1 the
capacity-l constant wore a `proven` label — exactly the contamination class
this ledger exists to prevent — and was caught in review before the note
hardened. The proven floor is untouched by the split either way: even the
pessimistic Johnson-l form at ~2^-101 sits thirty-plus bits above 65.5.

---

## Appendix: hardening implementation queue (order fixed in review)

1. **Rejection sampler** (T9): smallest diff, kills the only formal blocker,
   unblocks re-measuring real transcripts. Fresh bytes per retry via squeeze
   counter; 8-retry bound on SBF, reject on exhaustion. **IMPLEMENTED**:
   `challenge_qm31` now rejection-samples (word-stream retries, bounded 8 per
   limb, `VerifyError::ChallengeSampleExhausted` code 13); output is
   word-identical to the old sampler except on a P-hit, so existing
   transcripts and artifacts remain valid. A known-answer transcript vector
   is pinned (`TRANSCRIPT_KAT_EXPECTED`, host test `transcript_kat_pinned`,
   SBF instruction `TranscriptKat`, runner `stage0-transcript-kat`) so a
   silent host/chain divergence costs a test failure, not a week.
2. **(z, v) claim binding + challenge-order tests** together: they touch the
   same transcript code, and the failing tests (gamma-before-claims,
   chi-before-C1) are what make the §2 ordering fix permanent.
3. **OOD absorptions** (T2).
4. **Second commitment phase** (C2, §5) last: the largest envelope change,
   and everything before it is prerequisite-free.

Each step re-measures CU on the gate profiles and updates the §4 projection
table; the Stage 1 gate cannot close on projections alone.
