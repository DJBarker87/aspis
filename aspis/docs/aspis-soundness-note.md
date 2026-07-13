# Aspis soundness note — frozen PCS evidence, reopened security instantiation

Status: **PCS evidence frozen; Stage 1 security gate REOPENED on finite-
length constants (`2026-07-10`)**. The r2/k'=51 s1 base passed its budget.
The isolated s2 OOD/transcript probe adds 49,099 CU, but its historical
1,096,660 q36 arithmetic is superseded as a product projection: the corrected
two-helper PCS scaffold measures +113,876.5 CU on average and still excludes
the exact-wide C1/RLC and payment statement. Stage 2 is red and unpriced until
those components are integrated; q34/g36 remains a held protocol lever. The
t=90 ruling is retained; 93.73 is provisional sensitivity
only, and 65.5 is the sole quotable floor until §9.4's finite-n gate closes.
Section status ledger:

| section | status |
| --- | --- |
| 1. Protocol as implemented | reviewed; constants corrected |
| 2. The assumption + canonical challenge order | reviewed; ordering implemented and teeth-demonstrated |
| 3. Field-ceiling lemma | reviewed; upstream T1/T2 pin integrated, honest margin recomputed |
| 4. Per-round query budget | **reviewed, approved** (q38 labeled extrapolated; upstream constants pinned) |
| 5. Copy-argument soundness term | reviewed line-by-line; hardened with resolutions |
| 6. Grinding + Fiat-Shamir model | reviewed; binding terms and work metric updated from the pin |
| 7. Proven-vs-conjectured ledger | reviewed; exact T2 shape and T1 Johnson floor integrated |
| 8. Stage 2 range-lookup amendment | drafted `2026-07-10` with the multiplicity-order teeth vector; pre-integration |
| 9. Capacity-conjecture refutation (CS25/KKH26) | **STAGE 1 REOPENED `2026-07-10`**: t=90 ruling stands; computed revised-conjecture value remains unquotable pending a finite-n bound; provisional known-coefficient sensitivity 93.73 |

Current decision (design §13.3, amended 2026-07-10): keep the stated
**t = 90** position at q36/g32/s2, but do not attach a computed conjectured
value until the finite-length constants gate in §9.4 closes. The provisional
known-Table-4 sensitivity is 93.73; 93.89 is the earlier unit-coefficient
reproduction. Neither is quotable security. The only current quotable floor
is 65.5 bits. Layout this note is written for (design §13.8 as amended):
lr10, r2/k'=51 wide rows, rounds-per-row blocks, boundary interface columns,
LogUp copy check, second commitment phase.

---

## 1. The protocol as implemented

Everything in this section describes the code at this revision
(`aspis-core`), not a paper protocol. Envelope v3:
`aspis-core/src/proof.rs` (16-byte header binding profile id, log_rows,
log_blowup, query count, grinding bits, payload and Merkle-mode flags, round
count, final-poly length, and claim/C2 flags; C1 root; optional C2 root and
helper claim; one OOD value and degree-6 relation polynomial per round;
final polynomial, grinding nonce, and per-layer openings. A C2 proof opens
both authenticated trees at layer zero and gamma-combines them before the
existing folds; fixed layout and trailing bytes reject).

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

Transcript order as implemented today: absorb(header) -> absorb(statement
digest) -> absorb C1; for a two-phase proof sample lambda then chi, construct
and absorb C2, absorb the optional main and helper `(z,v)` evaluations, then
sample gamma -> for round zero (whose C1 was already absorbed), and then each
later root r: sample beta_r uniformly from QM31 excluding CM31, read and
absorb the claimed OOD value y_r, sample the claim-batching challenge mu_r,
read/check/absorb the degree-6 relation polynomial G_r, sample alpha_r ->
absorb(final polynomial) -> grinding check (g leading zero bits),
absorb(nonce) -> derive query positions (exact-uniform masking over the
power-of-two fiber count). One query set, sampled once, is traced through all
rounds; each query opens one fiber per layer, the verifier refolds locally
(alpha_r, alpha_r^2; denominators batch-inverted per round) and compares
against the next layer's opened slot, terminating against the final
polynomial. Grinding is a single g-bit check before query derivation; there
is no per-round PoW (recorded divergence, `whir-p3-divergence.md`).

For C2 proofs the polynomial entering the invariant is
`w*(X)=w_C1(X)+gamma*h_C2(X)`. If public evaluations are present, the
relation begins with `w*(z)=v_C1+gamma*v_C2`; it then adds each
`mu_r * f_r(beta_r)=mu_r*y_r`, and is reduced by G_r at alpha_r to the next
coefficient vector. After four rounds the verifier evaluates the accumulated
structured weights on the four explicit final coefficients. False external
claims and false OOD values now reject at their first inconsistent boundary;
the tests also cover mix-and-match, corruption, old-envelope, and absorption
order. The prover exposes a generic post-`(lambda,chi)` C2 builder; the Stage
1 measurement uses a named synthetic challenge-dependent helper solely to
price/authenticate the interface. Stage 2 supplies the actual LogUp helper
and constraint composition; the synthetic helper proves no payment or copy
relation.

## 2. The assumption, stated once — and the canonical challenge order

> **REFUTATION NOTICE (`2026-07-10`, §9).** The conjecture below is the
> frozen Stage 1 statement. Its general form — behavior up to the capacity
> radius 1 - rho with a fixed small list — was **disproved** by Crites and
> Stewart (ePrint 2025/2046, Nov 2025; the WHIR mutual-correlated-agreement
> lineage this note descends from), with the failure radius pushed below
> the Elias radius on smooth 2-adic domains by Krachun–Kazanin–Haböck
> (ePrint 2026/782, Apr 2026). No attack at these parameters is known. The
> replacement assumption, the re-derived numbers, and the headline
> consequence are in §9; the block below must not be quoted as current.

All conjectured terms in this note rest on exactly one assumption, named
here and nowhere re-derived:

> **Capacity conjecture (folded Reed-Solomon over the CM31 circle-coset
> domain) — REFUTED AS STATED, see §9.** For the code ensemble produced by
> the implemented fold schedule
> (arity-4 folding of RS-type evaluations over cosets of 2^k circle
> subgroups), proximity gathering and query soundness behave up to the code
> capacity bound: a codeword delta-far from the code, delta up to 1 - rho,
> survives one uniformly sampled traced query with probability at most
> (1 - delta), i.e. one query yields -log2(rho_worst) bits; the per-round
> folding/gathering error uses the pinned upstream unique-shaped constant
> `k/rho`; and the effective decoding list has size `L <= 40` for the OOD
> binding step. The last two clauses are part of the conjecture, not facts
> proved by upstream WHIR for the capacity radius (§4).

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
surface (§5). The Stage 1 adversarial suite contains a **challenge-order
family**: gamma-before-claims, chi-before-C1, and OOD-after-alpha transcripts
all reject under the production verifier. With the explicitly test-only
`insecure-test-ordering` feature, three deliberately weakened verifier
schedules accept the identical corresponding bytes. This is the evidence
that each vector has teeth; the feature is absent from the SBF build. The v4
extension adds second-OOD-after-alpha and gamma-before-second-helper-claim
vectors with the same canonical-reject/weakened-accept evidence.

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
roughly 104-112 bits before a single query is spent. Therefore 128 bits was
never reachable on M31/CM31/QM31, and the headline claim is frozen at
t = 100, capacity-conjectured.

Enumeration (lr10 / k' <= 82 / fused sumcheck; numerator shapes first, then
the value at the target parameters, in bits below zero. These are the FROZEN
Stage 1 values; the Stage 2 statement protocol amends T5, T7, and T8 — see
§8, which supersedes those three rows for any integrated payment proof):

| # | term | shape | bits |
| --- | --- | --- | ---: |
| T1 | per-round proximity gathering (4 rounds) | sum_r (k_r / rho) / \|F\|, k_r = 2^(10-2r), rho = 1/4 | 111.59 (capacity conjecture's unique-shaped clause) |
| T2 | OOD binding, 1 sample x 4 rounds | C(L,2) * sum_r(k_r-1) / \|F\|, L <= 40 | 103.99 (formula pinned; list bound conjecture-conditional at capacity) |
| T3 | relation + fused statement sumchecks | nu * d / \|F\|, conservatively nu <= 14, d <= 7 | 117.4 |
| T4 | zerocheck eq-reduction (sample r) | nu / \|F\| | 120.7 |
| T5 | gamma-RLC batching over k' <= 82 columns | (k'-1) / \|F\| | 117.7 |
| T6 | copy-argument tuple compression (lambda) | m * w / \|F\| (worst m = 2^10, w = 17) | 109.9 |
| T7 | copy-argument pole/SZ (chi) | 4m / \|F\| | 112 |
| T8 | claim-batching challenge (mu) | (#claims) / \|F\| | ~122 |
| T9 | challenge-sampler statistical distance | fixed by rejection sampling | 0 after fix (was ~25) |

On T1's counting: the pinned upstream unique-decoding branch is
`log2(|F|) - (log2(k) + log2(1/rho))`. Applied round by round, its
numerators are exactly the four domain sizes 2^12, 2^10, 2^8, 2^6. Their
union is 111.5906 bits. This is the constant now stated inside the capacity
conjecture; upstream does not provide a capacity branch and therefore does
not prove that substitution.

T2's shape is no longer a range. Pinned upstream WHIR uses STIR Lemma 4.5 as
`C(L,2) * ((degree-1)/|F|)^s`. With one sample in each round, L = 40, and
degree bounds 1024, 256, 64, 16, the four-round union is 103.9875 bits.
The formula is proved conditional on a list-size bound; `L <= 40` at the
capacity radius is an explicit clause of this note's conjecture.

Union of T1-T8 is 103.9508 algebraic bits before queries, dominated by T2.
t = 128 would require every enumerated term to vanish — not a parameter
choice, a different field tower.

**T1 provenance is load-bearing here.** `103.9508` is not evaluated at the
favorable end of an unresolved 106-112 bracket. The deterministic artifact
`results/stage1/upstream_soundness_pin.json` pins the unique-shaped
four-round union to **111.5906090612 bits** from
`WizardOfMenlo/whir@10aa7d0bae3663fd149b6b88b6eff2209b867970`; use of that
constant at the capacity radius remains one of the three explicitly
conjectural clauses. Removing T2 from the stated union leaves a 109.2649-bit
residue (dominated by T6, not T1). Sensitivity only: replacing the pinned T1
term by the old bracket's 106-bit endpoint would produce 103.6444 algebraic
bits and 102.8113 total bits, a 2.8113-bit margin. The gate artifact records
both the pinned result and this counterfactual; it no longer labels the
pinned case as an unqualified “worst case.”

**The honest final number.** The query term joins the union — in the
success-per-unit-work metric, where both categories denominate in hashes
(§6): success/work <= 2^-103.9508 + 2^-32 * 2^-72 =
**2^-102.9752 worst-case**. The claim's true margin over t = 100 is about
2.98 bits; the 103.95 figure is the algebraic union alone and must not be
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

| schedule | query bits | verdict | PCS CU / basis | projection | headroom vs 1.19M |
| --- | ---: | --- | ---: | ---: | ---: |
| q32/g32 | 96 | **retired — 4 bits short of t=100** | not remeasured with C2 (dead schedule) | — | — |
| **q36/g32** | **104** | **ruled and Stage-1 measured** | **943,972 literal, v3 C2 + relations enforced** | **1,175,086** | **14,914** |
| q38/g32 | 108 | soundness contingency only after a material CU shrink | >943,972 planning floor (**not measured, not a bound**) | >1,175,086 | <14,914 |

**Literal Stage 1 measurement.** The `2026-07-10` Agave 2.3.0 run in
`results/stage1/onchain_hardening_summary.json` uses envelope v3 with the
canonical C1/C2/gamma prefix, one OOD evaluation, and one interleaved relation
polynomial per round. The literal `capacity_lr10_q36_g32` proof accepts in
five identical runs at **943,972 CU**, 21,364 bytes (34 upload chunks; 22,435
aggregate upload CU); all twelve on-chain corruption/binding cases reject,
including `second_phase_root_corruption`, `ood_value_corruption`, and
`sumcheck_corruption`. The host/SBF transcript KAT also matches
(`results/stage0/transcript_kat.json`, 25,426 CU for the diagnostic
instruction). The exact proof fixture is pinned under `results/stage1/proofs/`
with SHA-256 `1557b82d4e4a35117104951e3e026d423b57e46c462bb314f4f701408ef2f805`.

The old g16 proxy rationale was incomplete. The grinding threshold check is
constant-cost, but `grinding_bits` is in the transcript-bound header, so
g16 -> g32 changes query collisions and the minimal-subtree shape. In this
binding-only run literal q36/g32 was 5,538 CU above q36/g16 (743,060 versus
737,522), demonstrating the effect. The enforced literal row is therefore
authoritative; the q32 row stays a planning proxy because that schedule is
already dead.

The projection adds the existing 231,114-CU wide-leaf/RLC + statement-
sumcheck budget to the literal PCS result: **1,175,086 CU, leaving only
14,914 CU (1.25%)**. This is not enough to price unknown Stage 2 constraint
composition and fails the design's 10% slack condition. q38 improves only the
query term (not the 103.99-bit OOD term) and necessarily costs more, so it is
no longer an executable inline contingency at the current CU level. Stage 2
therefore begins with the direct evaluator and isolated SBF composition
measurement; a fit requires a named shrink, otherwise the split-verification
fallback from the Stage 0 conclusion triggers.

**§4 upstream pin (CLOSED experiment; RELABELED `2026-07-10`, §9).** The
pinned upstream WHIR accounting predates the Crites–Stewart refutation of
the WHIR mutual-correlated-agreement conjecture: this pin is a
**consistency check against a superseded document, not a validity
source**. Its constants remain the record of what was computed and from
where; their epistemic weight is set by §9. The reproduction command
`cargo run -p aspis-xtask -- stage1-soundness-pin` writes
`results/stage1/upstream_soundness_pin.json`, pinned to
`WizardOfMenlo/whir@10aa7d0bae3663fd149b6b88b6eff2209b867970`. It resolves
both requested constants:

- T1's upstream unique-shaped four-round union is 111.5906 bits. The
  upstream Johnson/list-decoding branch is only 73.6534 bits without its
  per-fold PoW. Upstream has no capacity branch, so 111.5906 remains a named
  clause of the Aspis capacity conjecture, never an upstream-proven result.
- T2 uses `C(L,2)`, resolving the draft's exponent question in favor of the
  quadratic list-size form. At the pinned Johnson choice `eta = 0.025`,
  `L = 40`, one sample per Aspis round unions to 103.9875 bits.

The artifact also records per-round values and list-size sensitivity. This
closes the experiment while narrowing, rather than upgrading, the claim.

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
point). (3) Compress:
`phi_j(lambda) = tag_j + sum_{i=0}^{w-1} lambda^(i+1) d_{j,i}`. The tag is
the constant coefficient and every data limb starts at `lambda^1`; this
prevents a tag change from cancelling a change in `d_{j,0}`. (4) Commit the
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
  (X - phi_j(lambda)). With the explicit index range `0 <= i < w`, distinct
  `(tag, d)` tuples give distinct degree-`<= w`
  polynomials phi_j(lambda); monic linear factorizations over the integral
  domain F[lambda] are unique, so Q is not identically zero; its
  X-coefficients are polynomials in lambda of degree <= m*w;
  Schwartz-Zippel over lambda gives m*w / |F|. The pairwise m^2*w union
  bound is unnecessary, and it is exactly the UFD argument that makes it so.
  **Degree recount after the exponent shift:** the ledger already booked
  degree `w`, not `w-1`, so the bound and its 110.85-bit frozen-shape value
  do not move. Using `m*(w+1)` would double-count the tag: it is a
  coefficient, not an additional lambda degree.
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

**Stage 2 pointer:** the fixed-table range lookup shares chi with this
argument, commits its multiplicity column in C1 and its helper h2 in C2,
and adds term E4 plus an executable multiplicity-order teeth vector — §8.

**Measured cost of the second phase (C2):** the helper already uses
`minimal_subtree`, not 36 individual depth-10 paths. It is a separate tree
(soundness requires C1 before chi and C2 after chi), but its queried leaves
share the deterministic multiproof frontier. Even with that sharing, C2
adds 142,447 CU and 6,148 proof bytes: 801,525 -> 943,972 CU and 15,216 ->
21,364 bytes. Separate individual paths would be materially larger and are
not a remaining reclaim. If Stage 3's masking polynomial also needs a
post-challenge commitment, both can share the phase-2 tree; that decision is
taken in the hiding note, not silently.

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

**Which term binds — stated the honest way around.** In the capacity work
metric T2 and the query round co-bind at 103.9875 and 104 bits. They are two
faces of the same conjectural regime: the query rate assumes capacity-radius
behavior, while T2 additionally assumes the effective list bound `L <= 40`.
T1's unique-shaped 111.5906-bit union is the third clause of that conjecture.
Under proven accounting on the same schedule (Johnson radius
`1 - sqrt(rho) - eta` at rho = 2^-2, delta ~ 0.475 after slack), a traced
query buys ~0.93 bits and q36/g32 proves about 65.5 bits, not 104. The pinned
upstream Johnson T1 branch unions to 73.6534 bits without per-fold PoW, so it
still clears that proven query floor by about 8 bits; T2 at L = 40 is
103.9875 bits. The correct sayable sentence is therefore: **the proven floor
on this schedule is the 65.5-bit Johnson query term; the conditional
capacity headline is jointly controlled by the capacity query rate and its
effective-list-size premise, and no term may be silently transferred from
one regime to the other.**

**OOD sample count decision (third review touch): freeze `s = 1` for v3 —
SUPERSEDED `2026-07-10` (§9), and the reason the value changed is the
record.** Under the now-refuted accounting, `s=2` bought 0.9878
conditional bits (T2 at 103.99 co-bound with the 104-bit query term, so
removing it barely moved the union) and was correctly declined against
its engineering cost. Under the adopted revised conjecture the list size
is provisionally modeled with `l(theta) = 2^(H(rho)/eta)`, T2' becomes quadratic in `l` and is the
**binding s=1 term**, so the identical protocol change is now worth
**+3.39 bits (90.34 -> 93.73 at q36/g32)** in the known-coefficient
sensitivity. The contamination-free isolated SBF A/B measures **+49,099
CU** (s1 86,815; s2 135,914; 5/5 identical), superseding the 5-12K
estimate. The earlier probe was 56 CU higher because it generated synthetic
values inside the timed path; fixed canonical bytes remove that work. The earlier
unit-coefficient reproduction was +3.55 / 93.89. `s = 2` is ADOPTED for
the v4 payment envelope (§9.4 ruling), independently of whether the
finite-length sensitivity is ultimately promotable.
Normative Fiat-Shamir position of the second sample: each round carries
two sequential (beta, y, mu) triples — root_r -> (beta_r1, y_r1, mu_r1)
-> (beta_r2, y_r2, mu_r2) -> sumcheck poly -> alpha_r — both values
entering the relation accumulator, +16 bytes per round per sample. The
existing OOD challenge-order teeth vector (`ood_claim_after_fold_
challenge`) extends with a second-triple variant (value-2 absorbed after
alpha must reject; weakened schedule accepts). The bounded subfield-
sampler completeness doubles retries: still < 2^-183 over four rounds.
Its CU appears as a named line in the v4 integration measurement.
<!-- retired-numbers: allow-start id=s1-ood-history -->
Historical paragraph retained below for provenance:

At the
pinned constants, `s=1` gives 102.9752 total bits and 2.9752 bits over the
headline. Two samples per round would push T2 to about 218.3031 bits and make
the 109.2649-bit non-T2 residue the algebraic limiter; after the 104-bit query
term the total would be about 103.9630 bits, a 0.9878-bit gain. It would not
improve the 65.5-bit proven floor. The v3 product projection has only 14,914
CU before unpriced composition, and `s=2` requires nonzero extra transcript,
weight-evaluation, proof, KAT, and literal-g32 remeasurement work. Therefore
the extra conditional bit is declined until a material CU reclaim lands or
the pinned T1/list premise changes. Under the frozen `s=1`, **T2 and the
query term jointly bind within 0.0125 bits**; neither may be described as
comfortably non-binding.
<!-- retired-numbers: allow-end id=s1-ood-history -->

**Sampler completeness (from the §3 T9 fix).** Rejection sampling with a
bounded retry loop (8 per limb, fresh transcript bytes per retry via a
retry counter in the squeeze input) rejects an honest proof only if some
limb exhausts all retries: per-limb probability (2^-31)^8 = 2^-248, and
under ~50 limbs per proof the honest-rejection probability is < 2^-242.
OOD points additionally reject the CM31 subfield and retry at most three
times: exhaustion is below 2^-186 per round and below 2^-184 over four
rounds. These are completeness events, not soundness terms; they appear here
and nowhere in the §3 table.

**The honest final margin, restated as the one-line summary a reader takes
away — SUPERSEDED BY §9 for any current quotation:** adversary success
**per unit of adversary work** <= 2^-103.9508
(algebraic union, ~1 hash per attempt) + 2^-32 * 2^-72 (query term at
q36/g32, 2^32 hashes per attempt) = 2^-102.9752 worst-case; the frozen
headline t = 100 holds with about 2.98 bits of margin, conditional on the
three-clause capacity conjecture (§2) and the two SHA-256 assumptions (§7);
the proven floor on the same schedule is about 65.5 bits (§7). No other
number in this note is the system's security level. **The §2 conjecture
was subsequently refuted as stated; under the adopted revised conjecture
this paragraph's headline arithmetic does not survive at q36 — §9 carries
the current numbers, and only the proven-floor clause of this summary
remains quotable unchanged.**

## 7. Proven-vs-conjectured ledger

One line per term. `proven` lines are proven **within the model**, i.e.
conditional on the two assumption lines above them; nothing on a `proven`
line is conditional on the conjecture line.

| item | label | bits / basis |
| --- | --- | --- |
| SHA-256 as a random oracle (Fiat-Shamir transcript) | **assumption** | model floor for every line below |
| SHA-256 collision resistance for Merkle binding | **assumption** | >= 100 bits claimed (128-bit birthday bound) |
| Capacity conjecture — query radius, T1 gathering constant, effective list bound | **REFUTED AS STATED (`2026-07-10`, §9)** | general up-to-capacity form disproved (CS25 ePrint 2025/2046; KKH ePrint 2026/782 below Elias on smooth 2-adic domains); `L <= 40` at capacity is dead (Elias 1957 forces q^Omega(eta n) beyond list capacity); historical values retained one row down |
| (historical Stage 1 values under the refuted form) | superseded | historical query term 104 work-bits; T1 unique-shaped union 111.5906; effective OOD list `L <= 40` |
| **Revised conjecture source: S-two Conjectures 1-2 (ePrint 2026/532 App. A.5)** | **conjectured; finite-length instantiation not ratified** | source has `l <= c1*2^(c2*H(rho)/eta)`, existential `c1,c2>=1`, and `a=l*n+o(n)` with no finite-n remainder bound. Under the stronger Aspis assumptions `c1=c2=1`, zero remainder, and conservative-known Table-4 numerator 7,488, q36/g32/s2 is a **93.73-bit provisional sensitivity only** — §9 |
| **Proven floor, same schedule, Johnson-radius accounting** | **proven** | **~65.5 bits**: delta <= 1 - sqrt(rho) - eta, rho = 2^-2, delta ~ 0.475 -> ~0.93 bits/traced query; 36 x 0.93 + 32 ~ 65.5 |
| T1 proximity gaps, pinned Johnson branch without per-fold PoW | proven for the pinned upstream model; mapped conservatively to the Aspis round sizes | 73.6534-bit four-round union; above the 65.5-bit proven query floor, far below the capacity-shaped T1 clause |
| T2 OOD formula | proven conditional on a decoding-list bound | `C(L,2) * ((degree-1)/\|F\|)^s`; exact quadratic shape pinned in §4 |
| T2 OOD binding at capacity | **conjecture-conditional** | 103.9875-bit four-round union at the conjectured `L <= 40`, one sample per round |
| T2 OOD binding at Johnson radius | proven conditional on the pinned Johnson list bound | eta = 0.025, L = 40; same 103.9875-bit union |
| T3 relation + fused statement sumchecks | proven (SZ) | 117.4 (conservative 14 rounds x degree 7) |
| T4 zerocheck eq-reduction | proven (SZ) | 120.7 |
| T5 gamma-RLC batching | proven (SZ; canonical gamma-after-claims order implemented for the generic C2 interface) | 117.7 |
| T6 copy-argument compression | proven shape (UFD + SZ), constraint registry open | current bound 109.91 at m<=1024,w=17; the endpoint-local m=589 trace layout gives a 110.7104 sensitivity. The hardened `lambda^(i+1)` encoding does not move degree `mw` |
| T7 copy-argument pole/SZ | proven (log-derivative lemma) | 112 (deliberately loose 4m) |
| T8 claim batching | proven shape, final count open | final payment term `(J+2)/|F|`; the exact eight-claim value `4log2(p)-3 = 120.9999999973` is preintegration sensitivity only until `ConstraintId` freezes |
| T9 challenge sampler | fixed by construction (rejection sampling, exact uniform) | 0 soundness cost; field-sampler completeness < 2^-242, OOD-subfield completeness < 2^-184 |
| Grinding g32 | proven (ROM work accounting, §6) | +32 bits on the query term only |
| Stage 2 statement amendment (T5', T7' incl. E4, T8', multiplicity-order line) | partial: LogUp terms proven; constraint registry open | 103.9453 algebraic / 102.9724 total is the retired eight-claim preintegration sensitivity; final payment union waits on exact `J` (§8); Stage 1 rows above unchanged |
| **Headline** | **t=90 ruling retained; computed value gated** | provisional known-coefficient sensitivity 93.73 at q36/g32/s2, but no computed revised-conjecture number is quotable until the finite-n remainder/transport assumption is pinned. **Only the ~65.5 proven floor is currently quotable.** Historical refuted-capacity values remain provenance only |

The proven-floor line follows house precedent (the WHIR-UD gate reported
"lower 58.0 / upper 100.0"): the positive result does not get a lower
standard than the negatives, and the number a hostile reviewer would
compute anyway is computed here, with the derivation shown. **Quotation
rule, amended `2026-07-10`: until the finite-length gate closes, only the
65.5-bit proven floor may be quoted. After it closes, any public quotation
of the headline carries FOUR elements or none — the stated headline, the
then-ratified computed conjectured bits, the proven floor, and the revised-
conjecture plus finite-length citation. A provisional sensitivity is never
substituted into that four-element form.**

T2's split is itself a record of this section doing its job: in draft 1 the
capacity-list constant wore a `proven` label and its dependence was written
as linear. The upstream pin corrected both errors: the formula is proven,
the capacity list bound is not, and the exact dependence is `C(L,2)`. The
proven floor remains the 65.5-bit query term; the pinned Johnson T1 branch is
the next proven term at 73.6534 bits.

---

## 8. Stage 2 amendment — fixed-table range lookup behind the shared chi (`2026-07-10`)

Second occurrence of code-before-note, recorded as such: the range-lookup
helper algebra and its teeth corpus landed in `aspis-statement` before this
section existed. This amendment closes that gap **before integration**, while
the diff is small. Everything here is normative for the Stage 2 payment
protocol; the frozen Stage 1 synthetic-C2 milestone and its §3 numbers are
unchanged.

**Protocol delta.** SpendV0-min replaces 64 Boolean range residuals with one
fixed-table LogUp: six 10-bit limbs (three per bounded value) are looked up
in the verifier-known table `[0, 1024)` and six linear reconstruction
constraints rebuild the two values, preserving the integer-before-field
check. New committed data: one **multiplicity column in C1** (consumer
weights over the 2^10 table rows) and one **range helper column h2 in C2**.
The table itself is never committed: consumer values are the row-index
function, whose multilinear evaluation `index(x) = sum_i 2^i x_i` the
verifier computes at the terminal point in O(nu) operations. Producer-side
weights are verifier-computable 0/1 layout selectors, like §5's.

**Challenge decision: the range lookup shares chi (and its FS position) with
the copy argument.** The alternative — a fresh chi_2 with its own transcript
position and its own challenge-order teeth vector — is declined: it adds an
FS position without removing any term, and batched-LogUp practice draws all
lookup denominators from one challenge. Sharing is sound by a union bound
because the two arguments cannot pay each other's debts: they live in
**separate helper columns with separate batched total-sum claims**
(`sum(h1) = 0` and `sum(h2) = 0`), so a deficit in the copy multiset cannot
cancel against a surplus in the range multiset regardless of value
collisions. lambda is not used by the range lookup at all (single-limb
values need no tuple compression); T6 is untouched.

**Canonical order, extended (normative).** The §2 order gains one
load-bearing line: **the multiplicity column and every range-checked limb
are C1 columns, committed before chi exists.** The teeth are executable, not
prose: `logup_multiplicity_after_chi_weakened_order_accepts` in the
evaluator corpus demonstrates that if multiplicities could be chosen after
chi, four fractional multiplicities solving the M31-linear system
`sum_v m_v/(chi - v) = 1/(chi - w)` cancel an out-of-table producer `w` and
**every check accepts** — local relations and both total sums. Same failure
class as gamma-before-claims: invisible to honest-prover tests, fatal
against a real adversary. The constructor is
`aspis_statement::forge_post_chi_multiplicities`; the canonical order is
what makes the construction unbuildable.

**New soundness terms.**

- **E4, range-lookup pole/SZ (chi): <= 4m / |F|, m = 2^10, kept
  deliberately loose like E2.** Let D(X) = sum_i sel_i/(X - q_i) -
  sum_v m_v/(X - v) over the committed producer limbs and multiplicities.
  If any weight-1 producer limb w lies outside the table, D has a pole at w
  whose residue is the **integer count of producer entries at w**, in
  [1, 2^10] and therefore nonzero mod 2^31 - 1; consumer poles sit only on
  table values, so D is not identically zero. D has at most N + T poles and
  numerator degree at most N + T - 1 (N = 2^10 producer rows, T = 2^10
  table entries); chi must avoid both sets, and 4m covers 2(N + T) with
  room. The checks force D(chi) = 0 (each row's local relation pins h2's
  row to its term; sum(h2) = 0 sums them), so a false lookup survives with
  probability at most E4.
- **Below-characteristic condition, stated precisely.** The log-derivative
  argument needs the **producer-side aggregate count per value** to be
  nonzero mod char: it is an integer in [1, 2^10], and 2^10 << 2^31 - 1 by
  construction (`TooManyRangeQueries` caps queries at table size). Committed
  consumer multiplicities need no integrality condition at all — a
  non-member producer pole has no consumer pole to hide behind, which is
  exactly what the post-chi teeth vector shows becomes false the moment
  multiplicities can depend on chi.
- **Completeness poles.** chi hitting an active committed value
  (`ActivePole`) requires chi in the base subfield containing limbs and
  table, probability <= 2^-62 per proof; a completeness event of the §6
  class, not a soundness term.

**Amended enumeration (supersedes §3's T5/T7/T8 for the Stage 2 statement
protocol).**

| # | term | shape | bits |
| --- | --- | --- | ---: |
| T5' | selected joint gamma/fresh-kappa column + two-point batching: k' / \|F\| = 124 - log2(k') bits | frozen k' = 51 (pin <= 52) -> 118.3276; the prior 50/\|F\| value was column-only before the two-point rule froze | 118.3276 |
| T7' | copy pole/SZ (E2) + range pole/SZ (E4), shared chi, union | 4(m_copy + 1024) / \|F\|; current m_copy <= 2^10 worst case. The endpoint-local m_copy=589 trace sensitivity is 111.3445 bits | 111 |
| T8' | statement/claim batching | `(J + 2) / \|F\|`, where `J` is the frozen `ConstraintId` residual count and the two extra lanes are `sum(h1)=0`, `sum(h2)=0` | **OPEN until the constraint registry freezes**; the earlier eight-claim value `4log2(p)-3 = 120.9999999973` is a preintegration sensitivity only |

T5' is now stated parametrically after the `2026-07-12` fresh-kappa ruling;
any future layout change instantiates the formula and does not rewrite the
line. Both 51 column evaluations at both points are absorbed before gamma;
kappa is sampled after gamma. For fixed false claims,
`E0(gamma) + kappa E1(gamma)` is a nonzero bivariate polynomial of total
degree at most 51, so Schwartz--Zippel contributes `51/|F|`. The extra
`1/|F|` is explicit here and is not charged again to T8.

The k' recount that forced the first T5' rewrite: the 80-column candidate
main trace did not reserve the lookup's committed columns, so k' = 80
(main) + 1 (multiplicity, C1) + 1 (copy helper h1, C2) + 1 (range helper
h2, C2) = 83, briefly pinned <= 84. **§3's "k' <= 82" is false for the
integrated statement and must not be quoted for it.** The k83 reading and
its scaled RLC costs are superseded by the layout freeze below (r=2,
k' = 51, measured kernels); they are retained here as provenance for the
projection corrections recorded in `stage2-feasibility.md`.

**Integration correction (`2026-07-10`, note-first).** The synthetic
composition probe used one deterministic accumulator and therefore did not
establish the final `#claims <= 8` premise. A malicious trace can cancel
independent residual families unless every stable `ConstraintId` is batched
with verifier-sampled powers of `mu`; the two helper total-sum claims must be
separate lanes as well. Consequently the final term is `(J+2)/|F|`, and `J`
must be emitted by the checked-in constraint registry before a payment-proof
union is quoted. The previous **103.9453 algebraic / 102.9724 total** values
remain a preintegration eight-claim sensitivity, not an integrated-statement
soundness number. T3 is unchanged (the range relation is degree 3, inside
d <= 7; the fused Poseidon/selector/eq statement sumcheck remains within its
degree-7 envelope); T4 and T6 are unchanged.

**Envelope consequence: version 4.** The Stage 2 C2 phase carries **two**
helper columns, so the C2 layer-0 leaf widens from 4 QM31 (64 bytes) to
8 QM31 (128 bytes) per opened fiber, and the C2 claimed-evaluation field
carries two values **at each statement evaluation point**. The row-local
absorption layout requires the ordinary terminal point `z` plus the fixed
low-bit-shifted point `z xor 11`; therefore the final statement framing
absorbs 49 C1 + 2 C2 values at each point (102 field values total) before
gamma. Fresh kappa does not double T5': for any fixed false transcript, at
least one of the two claim-vector difference polynomials in gamma is nonzero,
and the selected `E0(gamma) + kappa E1(gamma)` polynomial has total degree at
most 51, so acceptance is bounded by `51/|F|`. It does make the current
single-point scalar-C1 PCS scaffold KAT
explicitly non-final. That is a fixed-layout change: the payment envelope
bumps to **v4** and v3 remains the frozen Stage 1 format. The gamma
combination generalizes to `w* = sum_i gamma^i w_i + gamma^k1 h1 +
gamma^(k1+1) h2` with all claims absorbed before gamma exactly as today.
The v4 gamma-before-second-helper-claim teeth vector rejects canonically and
accepts only under its matching deliberately weakened test schedule; the
sum(h) = 0 claims are batched into the fused statement sumcheck and add no
denominators (E3). The schedule-level transcript KAT moved with the v4
absorptions; that deliberate named re-pin is recorded in
`transcript_kat_repin_ledger.json` like the four before it, not a constant
edited to green the suite.

**What integration may still change.** Exact leaf packing for the wide C1
row, the selector reading for which cells are range-checked, and the final
(m, w) for §5 are layout-freeze decisions; if any of them moves a number in
this section, this section is re-dated before the gate note quotes it.

**Layout freeze (`2026-07-10`, state-transition and endpoint-local trace
shape ratified; randomized constraint registry open): r = 2 rounds per row,
k' = 51, pin k' <= 52.** The freeze record states plainly what the shrink
hunt found: **the previous freeze candidate (k80 / r=4) was broken.**
Six-row blocks do not factor over the low bits of the Boolean cube, so
§5's verifier-evaluable O(2^b) selector claim was FALSE for that shape —
integration on it would have needed committed selector columns (k' up,
costs up) or produced silently wrong evaluations. No probe in the suite
could have caught it; it was caught by note-work, the second defect
intercepted that way after the gamma-ordering bug. The frozen shape is
the one on which this note is true as written: 49 Poseidon2 permutations
in 2^4-aligned 16-row blocks (11 constraint-active + 5 padding rows),
**539 constraint-active rows and 784 allocated rows** inside the 2^10 trace;
position-in-block is a function of the low 4 bits of the row index.

Frozen-shape facts, with the integration correction stated before constraint
code lands:

- **m recount (condition ii), TRACE FOUNDATION CLOSED / CONSTRAINT REGISTRY
  OPEN:** the endpoint-local trace implementation contains **m=589** links:
  490 intra-permutation, 25 sponge continuations, 19 prior-Merkle-output
  links, 6 semantic ingress/reuse links, and 49 source-to-absorption links.
  Executable tests require every tuple cell to live on its declared endpoint,
  require unique producer rows and tags `producer_row+1`, and replay every
  equality. A fresh SBF build passes without a stack-frame warning. This is
  still a trace/layout foundation, not the randomized constraint registry;
  until every endpoint is registered and evaluated, T6 keeps the existing
  m <= 2^10 binding bound. The superseded m=534 number remains state-only
  provenance.
- **Absorption wiring (ratified note-first and implemented in the trace):**
  for block `b`, source row `S_b = 808+b` and absorption row
  `R_b = 16b+11` are row-local endpoints. `R_b[0..8]` is the chunk consumed
  by round zero through the fixed XOR-11 low-bit shift. Each Merkle source row
  materializes both halves locally as
  `left=(1-bit)current+bit*sibling`,
  `right=bit*current+(1-bit)sibling`, copies `left||right` into the even
  absorption row, then uses that row's producer side to copy its right half
  into the odd absorption row. This preserves one producer and one consumer
  per row and avoids a third evaluation point: the statement needs only the
  ordinary terminal point and its fixed XOR-11 absorption shift. No tuple
  limb may dereference another row and no witness-dependent selector/tag is
  permitted. The mechanical
  trace count is **m=589**: 490 intra-permutation + 25 sponge continuations
  + 19 prior-Merkle-output links + 6 semantic ingress/reuse links + 49
  source-to-absorption links. At w=17 this gives T6 **110.7104 bits**; the
  copy-pole component is **112.7979 bits**. Public anchor/nullifier/output,
  asset, fee, and balance remain direct randomized residuals, not fake copy
  entries. The m<=1024 line remains binding until the randomized
  `ConstraintId` registry wires and evaluates these endpoints. T7' must also
  retain the independent 1024-row range term: at this trace count its
  sensitivity is `4*(589+1024)/|F|` = **111.3445 bits**, not `8*589/|F|`.
- **Selector form (condition iii), amended note-first:** position 11 in each
  block is reserved for the committed absorbed chunk so the round-0 relation
  can access it through one low-bit XOR shift. Positions 12..15 and the
  full/partial row classes (positions 0..1 external-initial, 2..8 internal,
  9..10 external-final) are all functions of position-in-block, hence inside
  the periodic part; exceptions proper remain the chain-structural rows
  only. **Positions 12..15 are constraint-dead and excluded from both copy
  multisets; position 11 is absorption-only and never a Poseidon transition
  row.** A dead row leaking into the producer multiset, or an absorption row
  escaping its witness/public binding, is a silent soundness hole; both
  classes require executable vectors before the constraint registry freezes.
- **T5' instantiation (fresh-kappa ruling, `2026-07-12`):**
  4log2(p) - log2(51) = **118.3276 bits**; amended union
  unchanged at 103.9453 algebraic / 102.9724 total (T5' is invisible at
  four decimals next to T2).
- **Freeze confirmation (condition iv):** multi-seed g16 means (>= 8
  fresh draws) at the integrated v4 shape, per the registered evidence
  standard — never a single draw.

LogUp-GKR helper elimination was priced against verified sources and
rejected as a net ~175K-CU loss on SBF; the analysis and abandon
criterion are recorded in the hunt document. The T3 nu <= 14 sumcheck
budget is a conservative allowance; at lr10 the zerocheck runs nu = 10
rounds and the nu = 14 pessimistic sumcheck probe reading is
**sensitivity-only, excluded from every gate statistic**.

---

## 9. Stage 1 reopened — the capacity conjecture is refuted as stated (`2026-07-10`)

Every citation in this section was fetched and read on `2026-07-10`; local
copies are archived with the session record. This section supersedes the
§2 conjecture block, the §3/§6 headline arithmetic, and the §7 capacity
rows for any current quotation. The frozen Stage 1 text is retained above
as the historical record.

### 9.1 What happened, from the primary sources

- **Crites–Stewart, "On Reed–Solomon Proximity Gaps Conjectures," ePrint
  2025/2046 (received 2025-11-05, revised 2025-12-19)** disproves, as
  stated up to capacity: the BCIKS correlated-agreement conjecture
  (Conjecture 8.4, J.ACM'23), the **WHIR mutual-correlated-agreement
  conjecture (Conjecture 4.12)** — the exact lineage this note's §2
  descends from — and the DEEP-FRI list-decodability conjecture
  (Conjecture 2.3; its failure follows from Elias 1957: beyond
  list-decoding capacity every list is q^Omega(eta n)). The constructions
  are counting arguments, **domain-agnostic** (any evaluation domain, any
  field, q >= n): there is no escape by domain structure from CS25.
  Failure in the band between the Elias radius and capacity is total (an
  explicit pair u0, u1 = x^k with every lambda in F_q close to the code).
  Their Section 5 lifts failure from a subfield to every extension:
  **sampling challenges from QM31 does not help; the characteristic
  entropy H_p at p = 2^31 - 1 governs.** Concurrent refutations:
  Diamond–Gruen ePrint 2025/2010 (rate -> 0 families, all domains and
  characteristics) and BCHKS ePrint 2025/2055 (below).
- **Krachun–Kazanin–Haböck, "Failure of proximity gaps close to
  capacity," ePrint 2026/782 (received 2026-04-20)**, formalizing a
  December 2025 Ethereum-Foundation communication (independent write-up:
  Kambiré, arXiv:2604.09724): for smooth **2-adic multiplicative
  subgroups** of prime fields (the standard FRI domain shape), proximity
  gaps and list-decoding fail at capacity minus Theta(1/log n) — **below
  the Elias radius** — with lists/bad-challenge counts >= 2^(c/eta),
  i.e. exponential in the inverse gap. Structured smooth domains provably
  behave worse than random ones (random RS achieves the Elias radius:
  Goyal–Guruswami ePrint 2025/2054, STOC'26). The family needs
  p = Theta(n^beta), p ≡ 1 mod n, chosen per n; it does not assert
  failure for any one fixed prime.
- **BCHKS, "On Proximity Gaps for Reed–Solomon Codes," ePrint 2025/2055
  (2025-11-06; STOC 2026)** — the BCIKS-team response, both directions.
  Negative: unconditional characteristic-2 failure a constant below
  capacity; **explicit M31 instances** (q = 2^31 - 1, G = <-2> of order
  62, D = F_q^*, rate ~ 1/2: for ALL z, Delta(f + zg, C) <= 1/2 while the
  pair is 0.516-far) and a QM31-sized instance (q ~ 2^124, delta ~ 0.508);
  and a demonstrated attack on the ethSTARK toy problem (Theorem 1.17)
  showing DEEP-ALI soundness is governed by list-decodability. Positive:
  **correlated agreement with ZERO proximity loss up to the Johnson
  radius at error O(n/eta^5)/q** (down from O(n^2)), with curve/
  set-specific/weighted versions.
- **Haböck, "A note on mutual correlated agreement," ePrint 2025/2110
  (2025-11-17)**: WHIR-style **mutual** correlated agreement — the exact
  notion our folding schedule needs — is now a **theorem up to the
  Johnson radius**, no conjecture.
- **Fenzi–Sanso, ePrint 2025/2197**: at 31-bit base fields, rate 1/2,
  128-bit-conjectured parameters, an information-theoretic prover
  strategy reaches success ~2^-116.5 (~11.5-bit shortfall); explicitly
  flagged as likely computationally infeasible to realize. **No
  computationally efficient attack on any deployed system at production
  parameters is known**, and none of the counterexample families
  instantiates on circle-group domains (checked by full-text search
  across CS25, KKH26, Kambiré). A days-old SoK (Skatharoudis, ePrint
  2026/1367, abstract + excerpts only — full text unavailable at
  fetch time) frames the season's lesson as: the proven-vs-conjectured
  axis, not query count, is the load-bearing dimension.

### 9.2 What this refutes in this note

All three clauses of the §2 conjecture are struck as stated: clause 1
(capacity query radius) and clause 2 (the unique-shaped T1 constant used
at the capacity radius) fall with the WHIR lineage; clause 3 (`L <= 40`
at the capacity radius) was a DEEP-FRI-shaped assumption and is dead
outright — beyond the Elias radius, list sizes are exponential, and near
it they are 2^(Theta(1/eta)) (KKH). The §4 upstream T1/T2 pin is hereby a
**consistency check against a superseded document**; its constants
survive as provenance only. The §3 "field ceiling" framing survives in
direction (128 was never reachable) but its 104-112-bit algebraic band no
longer describes the conjectured regime.

### 9.3 The adopted replacement and our domain exposure, honestly

**Adopted: the S-two Conjectures 1 and 2 (Carmon–Goldberg–Haböck–Lerer–
Lesokhin–Papini–Samocha, ePrint 2026/532, Appendix A.5, March 2026)** —
the M31 circle-STARK camp's post-refutation statement: Reed–Solomon codes
over prime fields F_p, **arbitrary evaluation domains**, are
list-decodable and line-decodable up to the **Elias radius r_E(rho)**
(1 - rho - 1/log2(p) <= r_E < 1 - rho) with list size
**l(theta) <= c1 * 2^(c2*H(rho)/eta)** at theta = 1 - rho - eta for
existential constants `c1,c2 >= 1`. Aspis's `c1=c2=1` substitution is a
**strictly stronger sensitivity assumption**, not a value supplied by the
paper. Conjecture 2 additionally states `a = l(theta)*n + o(n)` and gives no
finite-length bound for that `o(n)` term; S-two's examples neglect it, but
that does not license setting it to zero at `n <= 2^12`. Extension-field alphabets over prime-field domains
are explicitly included (our QM31-over-M31 shape). Line-decodability
yields every correlated-agreement facet this note uses, including
WHIR-style mutual correlated agreement, asymptotically with the above
`l(theta)*n + o(n)` numerator rather than the finite expression previously
printed here.
CS25's own modifications (Elias-radius cap, characteristic entropy, +1/n
slack) are subsumed: they lack the exponential list-size correction that
KKH forces, so the S-two form is the survivor. S-two §1.4 supplies a
scaled-RS isometry for its full circle-code family, which is a plausible
transport route, but **not yet a completed transport for this protocol**.
The genuine-M31 candidate uses Aspis's direct tensor coefficient space, its
codimension-one circle-polynomial convention, grouped radix-4 folds, and a
rational secure-circle OOD sampler. The full-code isometry alone does not pin
that subcode identification, the fold/list-decoding correspondence, or the
degree/probability term induced by the rational sample set. Therefore no T1 or
T2 value transfers "verbatim" to the M31 candidate. The exact obligations are
tracked in `stage2-circle-soundness-transport.md`; until they close, the
finite-length/circle-transport quotation gate remains open.

**Exposure statement for our exact parameters, stated plainly rather
than buried:** the KKH family requires a 2-power multiplicative subgroup;
F_M31^x has 2-adicity 1, so KKH cannot instantiate on M31's
multiplicative group — but our evaluation domains live in the **circle
group of order p + 1 = 2^31, which is fully 2-adic**, and our size
regime (n = 2^12 at log2(p) = 31) sits inside KKH's dimensional envelope
(n <~ 2^12.9 at beta >= 12/5). Whether a KKH-style construction exists
on circle-group cosets is an **open question no paper addresses**. The
adopted conjecture already prices KKH-shaped behavior via the
exponential list bound, and the BCHKS M31 instances live on the full
multiplicative group at rate ~1/2, not on circle cosets — but the honest
label on our conjectured regime is: *domain-specific, refutation-adjacent,
open on our exact domain family*.

### 9.4 Re-derivation at the frozen statement shape

Under S-two Appendix A.5, Conjecture 1 gives
`l(theta) <= c1*2^(c2*H(rho)/eta)` for existential `c1,c2>=1`; Conjecture 2
gives `a=l(theta)*n+o(n)` without a finite-n remainder bound. The earlier
optimizer silently set `c1=c2=1` and the remainder to zero. Those are now
named stronger Aspis sensitivity assumptions, not source consequences.

Table 4 also supplies the FRI-folding factor `3*2^-(k+1)`. It is 3/2 on
the first fold, so the old claim that every dropped coefficient was <=1
was false. Retaining 3/2 and conservatively clamping the later 3/4, 3/8,
and 3/16 factors to one changes T1's numerator from 5,440 to 7,488. The
checked-in runner records both mappings, both T2 union variants, and the
exact eta grid optima in `results/stage1/theta_optimizer.json`.

| option | eta* | known-coefficient sensitivity | CU reading | budget verdict |
| --- | ---: | ---: | ---: | --- |
| q36/g32, s=1 | 0.0715 | 90.3374 | frozen-shape base | strict survives |
| **q36/g32, s=2** | **0.0510** | **93.7263 provisional** | **+49,099 isolated s2 probe** | stated t=90 survives; old component projection strict-red, now retired as a live product total |
| q34/g36, s=2 reserve | 0.0522 | 94.0757 | old q36 arithmetic minus 44,479 | historical recovery sensitivity; deliberate second transcript knob, not priced on exact-wide v4 |
| q40/g32, s=2 | 0.0652 | 97.6560 | +130,427 incl. s2 | state t=95 if selected; 1.19M registered clears by 12,012 |
| q43/g32, s=2 | 0.0778 | 99.9251 | +191,423 incl. s2 | below t=100; both draw readings breach 1.19M |
| q44/g32, s=2 | 0.0823 | 100.5642 | +211,755 incl. s2 | first provisional t=100 crossing; both draw readings breach 1.19M |

The registered budget statistic remains conservative: central + 17,663
stress + 55,786 full draw range. On the preintegration component model, the
isolated s2 delta moved q36 to 1,023,211 central and **1,096,660
registered**, 25,660 above strict; the
anchor-corrected sensitivity is 1,058,112 and clears strict by 12,888 but
does not replace the rule. These are now historical arithmetic sensitivities,
not live product projections: the corrected two-helper PCS scaffold measures
+113,876.5 CU mean and still omits exact-wide payment work, so no additive
integrated total is currently sound. At q43, the old registered reading is
**1,238,984** and the
anchor sensitivity **1,200,436**: both exceed 1.19M. q44 is costlier.

The s2 decision remains the clear first move: it gains about 3.39 bits in
the binding known-coefficient sensitivity by removing the s1 T2' bottleneck.
The q34/g36 reserve gains **0.3494**, not 0.6-0.8, computed bits while
saving 44,479 CU and improving the proven floor. It now becomes the named
strict-line recovery lever in the old component sensitivity: 1,052,181
registered, 18,819 below strict. Exact-wide integration must reprice it. It
is held rather than silently substituted because q/g is a second transcript
knob requiring a deliberate proof/KAT re-pin.

**RULING (`2026-07-10`, amended after constants and gate audit): keep
option 1, stated t=90 at q36/g32/s2.** The provisional 93.73 sensitivity
is not quotable until a finite-n bound for Conjecture 2 and the circle-code
transport are ratified and encoded in the runner; only the 65.5 proven
floor is quotable meanwhile. The product gate is red and unpriced after the
corrected two-helper scaffold invalidated the old additive total; this does
not change the security ruling.
q34/g36/s2 is the pre-registered strict recovery lever, not the current
profile. Option 3 remains dead by the epistemic ruling and exceeds 1.19M
under both draw readings. The finite-length constants gate blocks quotation
or promotion of the 93.73 sensitivity, not implementation: after the atomic
P0+P1 hardening commit, transcript-bound v4 work may proceed under the
independent t=90 ruling.

<!-- retired-numbers: allow-start id=theta-ruling-history -->
Historical ruling trail, provenance only: the factor-of-rho run printed
93.2 and put the t=100 crossing at q45/+191K; correcting that bug produced
the unit-coefficient 93.89 and q43/+150K menu. Source-constant enumeration
supersedes both menus for current decisions.
<!-- retired-numbers: allow-end id=theta-ruling-history -->

### 9.5 The proven floor appreciated

Unchanged as the floor: ~65.5 bits (36 x 0.93 + 32). Strengthened in
lineage: mutual correlated agreement — previously the conjectural step
even below Johnson for WHIR-shaped folds — is now Haböck's theorem to
the Johnson radius, and BCHKS's zero-loss Johnson correlated agreement
at error O(n/eta^5)/q lets eta shrink at our tiny n = 2^12: a
preliminary re-derivation gives **~67.5-68.0 proven bits at q36/g32**
(eta ~ 0.002-0.005 balanced against the CA error term), and ~70 with the
q34/g36 reserve. These numbers are to be pinned by a dedicated
re-derivation before any public quotation; the direction is certain, the
decimals are not. Deployment context, for calibration: SP1's flagship
moved to the proven/unique-decoding regime entirely; StarkWare re-derived
under the same Conjectures 1-2 adopted here (their accounting: legacy
beta bits/query -> ~0.83-0.91 beta); RISC Zero's public docs still cite
the refuted forms unchanged.

### 9.6 Actions

Taken: §2 refutation notice; §4 pin relabel; §6 s2 adoption record; §7
quotation gate; the factor-of-rho correction; the S-two constants
enumeration; the deterministic `stage1-theta-optimize` runner/artifact; and
the registered q43 gate recount; and the measured +49,099-CU s2 A/B probe.
Pending: a finite-n bound for Conjecture
2's `o(n)` remainder plus the circle-code transport, encoded in the runner
(this gates quotation of a computed conjectured value, not v4 integration
under the t=90 ruling); the proven-floor re-pin (65.5
remains the only quotable floor until its derivation section exists,
citing BCHKS Theorem 1.5 and Haböck 2025/2110 specifically, non-theorem
steps marked); the KAT re-pin and §4 table rebuild at integration.
**Publication-freeze earmark, updated: q34/g36/s=2** — under the provisional
known-coefficient sensitivity the swap gains **0.3494 computed bits**, saves
44,479 CU, restores the registered strict line by 18,819 CU, and lifts the
preliminary proven floor toward ~70. It stays out of the current v4 profile
for one-knob discipline (one
transcript-shaped protocol change per integration); grinding twice
costs minutes.

### 9.7 Conjecture-watch contingency (pre-registered)

Honesty about the §9.3 open question without a response plan is
exposure, so the response is pre-registered now, while no construction
exists: **if a KKH-style counterexample is exhibited on circle-group
cosets at radii reaching our operating point** (theta* ~ 0.70 at
eta* ~ 0.050), the retreat ladder is, in order: (1) **primary: q40/g32/
s=2** (+81,328 CU versus current q36/s2; 1,177,988 registered; currently
97.66 only in the provisional sensitivity;
re-run the derivation and do not assume that value survives a new
construction);
(2) re-balance theta downward at q36 (costs headline bits, no CU) if the
new failure touches only radii above ~0.65; (3) **terminal cryptographic
retreat: proven-regime parameters** — Johnson-proven accounting (~67-68
proven bits after the re-pin), which no conjecture touches. This security
choice is independent of transaction transport. A one- versus multi-
transaction verifier changes the product claim to "across N transactions";
it does not make conjectured security proven or alter the Johnson line. If
the proven-regime implementation also needs receipt-bound transport, that is
priced as a separate product decision. The same cryptographic ladder applies
if the S-two conjectures are tightened (larger c1/c2) rather than broken.
This paragraph goes into the paper's limitations section verbatim alongside
the §9.3 disclosure.

## 10. Wide-leaf seam — M31-value recombination under a CM31 commitment is refuted (`2026-07-11`)

**The lever tested.** The wide-leaf + gamma-RLC seam is the dominant
reconciliation cost (measured 1,066,396 CU on the direct-canonical-byte path;
~69% of the integrated q36/g16 total, which exhausts the 1.4M meter on all
eight draws). Its per-query fiber is four slots x 49 CM31 C1 symbols = 392 M31
limbs (plus two QM31 C2 helpers x four slots), recombined per query across 36+
queries. The prior "fixed51" model priced one row of 51 M31 values per query — a
392/51 = 7.686x limb undercount (§ column-basis-audit calibration entry). The
question: can the gamma-RLC **recombination arithmetic** fold M31-valued witness
message-values while the **leaf commitment stays CM31** (correlated agreement
intact), separating the two?

**Verdict: NO. Recombination-basis and commitment-basis are welded by the
batched-opening argument; they are not two independent operations.** The one
assumption of this note (§2, capacity conjecture for folded RS **over the CM31
circle-coset domain**) states proximity gathering and query soundness for the
CM31 code. The batched opening forms `w* = sum gamma^i w_i` and runs ONE
proximity proof; correlated agreement is what binds all k columns to that one
opening. For that lemma to bind, the object (a) committed in the leaf, (b)
folded in the RLC, and (c) proven-close by FRI must be the **same** object.

**Trace (what the actual v4 path consumes — leaf-encoding, intrinsically CM31).**
`verify.rs::combine_exact_wide_sections` is fed `c1_leaf =
&values_section[..]` (call site verify.rs L1297-1300) — the authenticated
1,568-byte CM31 leaf bytes themselves, `value_bytes = first_phase_leaf_len(0) =
EXACT_WIDE_C1_FIBER_LEN = 49*4*8` — and folds them via
`qm31_cm31_dot4_prepared_bytes`, decoding each symbol as CM31 (8 bytes,
field.rs L741-744). It consumes leaf-encoding values, not a separate message
representation. Those symbols are **intrinsically CM31**: the encoder
`aspis-prover::coset_evaluate` lifts M31 coeffs, scales by a NON-real CM31 coset
offset (`CIRCLE_GEN`, nonzero b-limb), and runs a CM31 NTT (`ntt_cm31`), output
`Vec<CM31>`; for `f(T)=T` the codeword symbol is the non-real coset point
itself, `offset*omega^k = domain_point(geom,k)` — its second M31 limb is data,
not padding. There is no lossless M31 representation of the committed C1
symbols. The two C2 columns (gamma powers 49,50) are intrinsically QM31 (LogUp
helpers h1,h2, §5) — unfoldable as M31 regardless.

**Broken lemma.** The change voids the proximity-gathering / correlated-
agreement clause of the §2 capacity conjecture (over the CM31 code). Four
independent adversarial constructions (a-limb projection, native-M31 + CM31
wrapper, checkable derivation, conjugate-pair repack) each fail: they either
break binding, provide no recombination saving, or collapse to the raw-M31-leaf
PCS (the settled correlated-agreement break, with open circle-FRI transport).
The change does NOT lighten §5's LogUp terms (basis-independent, transport-doc
§4 T6/T7).

**Teeth vector (probability-1 forge of the CM31-commit / real-fold hybrid).**
Weakened verifier: keep the CM31 leaf and its radix-4 tree byte-identical
(1,568 B, both limbs canonical-checked and Merkle-bound), but replace the
gamma-RLC kernel with a real-only fold reading bytes `[offset..offset+4]` (the
a-limb) of each 8-byte symbol: `w*_a = sum gamma^i * a_i + gamma^49 h1 +
gamma^50 h2`. Adversary commits (before the C1 root, hence before gamma) each
`a_i(.)` = a genuine low-degree M31 circle codeword and each `b_i(.)` = a fixed
non-codeword pattern (e.g. all-ones column, canonical since 1<P). Then `w*_a`
is a codeword for every gamma, so FRI, per-fiber query consistency, and the
OOD/two-point binding of `w*_a(z)` accept with probability 1; the b-limbs are
canonical-checked but never read by the fold, never pushed into any FRI layer,
never OOD-evaluated. The committed CM31 word `W_i = a_i + b_i*i` is ~1-far from
the CM31 circle code (imaginary limbs are noise at ~every one of 4096 domain
points), and b is genuine message data, so the prover free-sets the CM31
OOD/sumcheck-terminal evaluations at z. Canonical (full-CM31) fold rejects:
`value_b` enters at field.rs L751-755. Same collapse class as the
gamma-before-claims bug (§2) — invisible in every honest-prover test, fatal
against a real one.

**Consequence.** No sound seam is cheaper than the CM31 recombination while
keeping the CM31 commitment. The measured 1,066,396-CU seam stands; the
non-additive current-CM31 reconciliation exhausts the 1.4M meter. The
**one-transaction full-depth 100-bit conjunction is measured-dead at the 1.4M
cap on this lever.** The separate native-M31 circle PCS (isolated best RLC
501,989 CU, § feasibility) is a genuinely different PCS with raw-M31 leaves and
an OPEN circle-FRI soundness transport (stage2-circle-soundness-transport.md
§4/§6) — it is NOT this lever and is not blessed here. No measurement probe is
written: a NO at the soundness gate is terminal (a cheaper seam that breaks the
opening soundness is worthless).

## 11. Wide-leaf seam — Avenue 1 (real-basis fold) column classification (`2026-07-11`)

**What was tested.** A research analysis proposed two levers on the ~1,066,396-CU
gamma-RLC seam: Avenue 3 (decompose the QM31 challenge action so recombination
accumulates in CM31 — representation-only, all columns) and Avenue 1 (fold the
RLC on real/imaginary components in an M31 basis, ~2x fewer ops — valid only for
columns whose witness is real-valued on the circle, i.e. conjugate-symmetric).
The report assumed all columns qualify for Avenue 1. This entry measures that.

**Column classification (semantic, from producers — not storage).**
- **49 C1 columns — REAL at the message level.** `SpendTraceV4.c1 = [Vec<M31>;
  49]` (trace_v4.rs). Cols 0-15 interface/state, 16-31 first-round output, 32-47
  second-round output are Poseidon2-over-M31 chains (poseidon2.rs: width-16,
  pow5 M31 S-box, M31 linear layers — no CM31/QM31 anywhere); Merkle-path,
  nullifier and key-schedule values are these same Poseidon2 columns at
  different rows. Col 48 is the M31 fixed-table multiplicity count. All C1 are
  committed BEFORE lambda/chi/gamma (prover lib.rs: absorb C1 root, then squeeze
  lambda/chi, then build C2), so none can be challenge-dependent or lifted.
  Their message polynomials have real M31 coefficients.
- **2 C2 columns — COMPLEX.** LogUp helpers h1 (copy), h2 (range):
  `build_logup_helper -> Vec<QM31>`, `h = sel/(chi - phi)` with chi a QM31
  challenge (logup.rs). Genuinely extension-field; no real representation.
- **0 UNCERTAIN.** No C1 column is genuinely CM31/QM31.

**Limb-weighted fraction (message level).** The 392 C1 seam limbs (49 x 4 slots
x 2 CM31 limbs) are 100% in message-REAL columns; the 2 QM31 C2 helpers add 32
COMPLEX limbs, so 392/424 = 92.45% REAL across the full 424-limb fiber.

**BUT the message-REAL fraction does NOT convert to Avenue-1 CU on the current
PCS. Avenue-1-exploitable fraction = 0%.** This is the storage-vs-semantic
distinction at the SYMBOL level, which the report missed in the opposite
direction. The gamma-RLC folds committed codeword SYMBOLS, not messages. The
current ordinary-univariate encoder evaluates each real-M31-coefficient message
over a NON-REAL CM31 coset (`coset_evaluate`/`ntt_cm31`, offset = CIRCLE_GEN
with nonzero b-limb), so every committed symbol f(offset*omega^k) is genuinely
COMPLEX; its imaginary limb is data, not padding (§10, column-basis-audit). The
message realness appears only as a GLOBAL symmetry conj(f(s_i)) = f(s_{N-1-i})
whose partner lives in the STRIDED partner fiber f_bar = F-1-f, not in the
queried leaf. Consequently, on the current CM31-leaf seam:
1. **Both limbs are unavoidable.** With CM31 leaves fixed (settled), the
   verifier parses, canonical-checks and Merkle-hashes all 392 M31 limbs/query
   regardless of fold basis. Avenue 1 cannot touch the parse/hash cost — the
   bulk of the 1,066->502 gap versus the M31-leaf candidate. The measured
   501,989-CU anchor combines the byte/type change with exact-49 loop bounds and
   one-time challenge-limb preparation; it must not be decomposed into a claimed
   pure-decode percentage. Avenue 1 with CM31 leaves still captures none of the
   mandatory imaginary-limb parse/hash work.
2. **Dropping the imaginary limb is invalid.** Owner-decision-packet fact 2:
   "Dropping the imaginary CM31 limb from the current ordinary-univariate Aspis
   PCS is not valid." Proximity binds to the full CM31 coset code, not the real
   subcode; a malicious prover commits a non-conjugate-symmetric word and the
   real-basis fold accepts it (the §10 probability-1 forge). The imaginary limbs
   are load-bearing.
3. **The real fold needs a different PCS.** Owner fact 1: M31 real symbols are
   valid ONLY under a genuine circle-polynomial PCS (circle FFT, M31 LEAVES,
   conjugate-adjacent slots, re-derived transport) — "not a serialization-only
   optimization." That changes the commitment (violates the CM31-leaf premise)
   and is the separate open-transport candidate, not a seam optimization.

**Avenue 3 is already realized; Avenue 1's arithmetic is counterproductive.**
`qm31_cm31_dot4_prepared_bytes` never does a full QM31 multiply in the hot loop:
gamma powers are pre-decomposed into six M31 Karatsuba components, the inner
loop does six M31 muls/symbol accumulating in M31 lanes (`sums[slot][6]`),
reconstructing QM31 once. That IS Avenue 3 — so its marginal reclaim over the
already-optimized seam is ~0. Avenue 1's naive real/imag split costs EIGHT
muls/symbol (worse than six) because the imaginary limb is a genuine nonzero
M31, not a structural zero. A ~2x mul count needs a structural-zero limb (fact 2
forbids) or a real M31 leaf (different PCS).

**Blended seam and integrated total.**
- Blended seam ~ 1,066,396 CU (MEASURED, unchanged): Avenue 1 = 0% exploitable
  on CM31 leaves; Avenue 3 ~ 0 marginal (already realized).
- Integrated q36/g16: >= 1,400,000 CU (MEASURED — the non-additive current-CM31
  reconciliation exhausts the 1.4M meter on all eight draws; the isolated seam
  alone leaves only 123,604 CU against 1.19M).
- Integrated q43/s=2: seam alone scales ~ 1,066,396 x 43/36 = 1,273,362 CU
  (PROJECTED) plus the second OOD sample and non-PCS terms — well above 1.4M.
- Against 1,190,000 and 1,400,000: fails at q36 and q43/s=2.

**Verdict: DEAD.** Not because the REAL fraction is low (it is ~100% at the
message level) but because the message-realness is inaccessible to the
symbol-folding seam on the current CM31-coset PCS: all 49 C1 codeword symbols
are irreducibly COMPLEX under the non-real coset, proximity binds to the full
CM31 code, and conjugate partners are strided out of the queried leaf — so the
imaginary limbs cannot be soundly dropped (owner fact 2); the 2 C2 helpers are
genuinely COMPLEX (QM31). The one-transaction full-depth 100-bit conjunction is
measured-dead at the 1.4M cap on the Avenue-1/3 levers.

**Soundness obligation for the REAL columns (note-first, NOT implemented — a
claim requiring external line-by-line review, stated with its gaps).** For a
real-basis fold to preserve the batched-opening binding, ALL of the following
must be established; none is proven here:
- (O1) The PCS must be the genuine circle-polynomial code with conjugate-adjacent
  slots (circle FFT, M31 leaves) so the real M31 value is the native symbol —
  NOT the current ordinary-univariate CM31 coset PCS. [Gap: full protocol change,
  owner fact 1; abandons the current CM31-leaf seam; OPEN circle-FRI transport,
  stage2-circle-soundness-transport §4/§6.]
- (O2) The batched-opening correlated agreement must be re-derived for the REAL
  (conjugate-symmetric) subcode C_real, binding the committed word into C_real
  rather than the full code. [Gap: this is the §2 capacity-conjecture
  proximity-gathering clause restated over C_real. It must rest on
  proven-Johnson accounting or a POST-CS25 revised-capacity form — NOT the
  refuted up-to-capacity form (§2 refutation notice, §9). The Johnson-vs-revised
  choice and constants are unverified.]
- (O3) The split-basis opening (C1 real M31 basis, C2 QM31 helpers complex)
  under one gamma-RLC must still bind h1,h2 to the same PCS opening that §5's
  copy argument relies on. [Modified lemma: the primary object is the §2
  capacity-conjecture proximity term; §5's E1/E2/E3 are basis-independent and
  unchanged (transport-doc §4 T6/T7), but §5's soundness DEPENDS on the joint
  gamma-RLC opening whose correlated agreement O2 revises — so §5 holds only if
  O2 holds for the split-basis fold. Unproven.]
Because O1 removes the current CM31-leaf seam entirely, this obligation does not
rescue the current path; it describes the separate circle-polynomial PCS whose
transport is already OPEN. Recorded so no future integration treats "the columns
are REAL" as sufficient for Avenue 1 on the current seam.

## 12. M31-leaf circle PCS transport — effort scope for the one-transaction claim (`2026-07-11`)

**Question scoped.** If the current CM31-coset seam is measured-dead (§11), the
only route to a one-transaction full-depth verifier under 1.4M is the genuine
circle-polynomial PCS with M31 leaves (seam 501,989 CU measured). What must its
soundness transport prove, what is already discharged, and is closing it an
afternoon or a multi-session effort?

**Two facts settled first, so soundness is the whole question.**
- **CU remains linear in the columns, but the implementation floor moved.** There is no sublinear-in-columns RLC (Stwo precedent:
  hoisted challenge-dependent constants and dedicated QM31xCM31 products give
  tower specialization but not sub-O(k) column folding). So the seam is
  fundamentally O(k'=51) columns, while exact-49 bounds and prepared limbs moved
  the measured implementation from 552,289 to 501,989 CU. Further arithmetic
  savings require literal SBF evidence; no sublinear claim is made.
- **The hardest CA primitive is now proven at Johnson.** Mutual correlated
  agreement is Haböck's theorem to the Johnson radius (2026; §9.5), and the 2026
  polynomial-generator MCA result makes acceptance-equivalent rewrites
  unconditional there. The scariest historical open item is discharged — but
  only up to Johnson.

**Correction to §11 phrasing.** "Raw-M31 leaves break correlated agreement" was
about GRAFTING M31 leaves onto the current ordinary-univariate CM31-coset PCS.
For the GENUINE circle-polynomial code, M31 leaves are the native commitment
(Stwo commits base-field columns) and their CA is the S-two circle-code MCA. So
M31 leaves are not an inherent blocker here; the blocker is the transport below.

**Tier 0 — schedulable proof work (multi-session, weeks; now tail-winded).**
These wire the S-two circle-code facts to Aspis's exact protocol shape; each
consumes the now-proven MCA primitive and becomes a bounded lemma AT JOHNSON.
(transport-audit stage2-circle-soundness-transport.md §6 obligations.)
- Grouped-fold theorem (obl 4): four committed arity-4 rounds with (alpha,
  alpha^2) from an 8-binary-reduction. [days]
- Two-phase batching CA (obl 5): 49 M31 C1 + 2 QM31 C2, second root, then gamma
  — the heterogeneous real/complex batch; dischargeable at Johnson via MCA.
  [days]
- MLE-evaluation reduction (obl 6): tensor relation + sumcheck bind both Boolean
  claims to the circle message (Protocol 4 insufficient). [days-weeks]
- Fiber-query CA (obl 9): consecutive four-slot leaves + q>>2 multi-round
  agreement. [days]
- OOD domains + degree correction (obl 7,8): C(QM31)\C(CM31), RS-order
  convention, two-sample product, condition (80) or L^+ (82)-(84). [days]
- BCS/ROM binding (obl 10): SHA-256, separate roots, radix-4, grinding position,
  state-restorable rounds vs S-two Theorem 22. [days]
- Local counts (obl 11): freeze J, copy endpoint registry, two-point rule,
  absorptions. [ongoing]
Realistic total: several weeks of real proof work; bounded, with the CA core
external-proven.

**Tier 1 — the 100-bit-class gate (NOT Aspis-schedulable).** Tier 0 is
unconditional only up to Johnson, and Johnson caps the level well below 100:
- Tier-0-only proven level ~ **67.5-68.0 bits** at q36/g32 (§9.5; proven floor
  65.5, lifted by MCA + BCHKS zero-loss Johnson CA at n=2^12; ~70 with q34/g36).
  The §3 field ceiling (~104-112 algebraic, ~102.98 total worst-case) makes 100
  UNREACHABLE in the proven regime.
- 100-bit-class requires the revised-capacity conjecture (S-two Conjectures 1&2,
  c1=c2=1, o(n)=0), which is "domain-specific, refutation-adjacent, open on our
  exact domain family" (§9.3): our circle group is fully 2-adic and inside KKH's
  dimensional envelope, and whether a KKH-style construction exists on
  circle-group cosets is an open question no paper addresses. It reaches t=100
  only at q44 (§9.4, costlier than q43), and its finite-n o(n) remainder for
  n<=2^12 is unbounded (must not be set to zero). This is a bet on external
  cryptography currently moving the wrong way — not an effort Aspis can drive.

**Tier 2 — quotation gate (folds into Tier 0/1).** Even the conjectural numbers
do NOT transfer verbatim: §9.3 — "no T1 or T2 value transfers verbatim to the
M31 candidate." The circle subcode identification, fold/list-decoding
correspondence, and rational-sample degree term must be re-derived for the exact
candidate before any value (proven or conjectural) may be quoted; until then the
finite-length/circle-transport quotation gate stays open.

**Verdict.** Not an afternoon. The effort bifurcates by the security label:
- **Proven ~67-bit one-transaction M31-leaf PCS: schedulable, ~weeks of Tier-0
  lemma work**, tractable because the MCA core is now proven. This is the §9.7
  terminal cryptographic retreat instantiated on the 501,989-CU seam — a
  conjecture-free "one transaction, full depth, ~67-bit proven, at 1.4M."
- **100-bit-class one-transaction: not schedulable** — gated on a
  refutation-adjacent conjecture Aspis cannot close, needing q44. Do not stake
  the headline on it.
Hiding and q43-seam measurement are worth an afternoon only AFTER Tier 0 closes
and the proven-~67 label is chosen; that is the only label where the seam fits
and the number is ours to keep.

## 13. External-report reconciliation — the conjugate-pair rewrite and §11 (`2026-07-11`)

An external expert analysis refined §11. It agrees on every strategic point
(392 serialized limbs compress to 196 INDEPENDENT M31 coordinates by conjugacy,
not to 49; the ~51-M31-mul target is dead; the packed-QM31 ~51 route needs a new
MCA/list-decoding proof; dropping any component is unsound; the regime must be
proven-Johnson or a revised list-decoding-capacity conjecture, never the refuted
up-to-capacity form). It makes ONE new claim and one correction to §11. Both are
verified against source below (workflow, high confidence).

**The correction to §11 (accepted).** §11 stated the real/imag split "costs
EIGHT muls/symbol, worse than six." That op-count is correct for splitting an
ARBITRARY CM31 symbol (two independent M31 limbs) — but it answers the wrong
question. The report's construction acts on a CONJUGATE PAIR of slots
`x=a+ib, xbar=a-ib`, which carries only TWO independent M31 values (a,b): then
`c+*x + c-*xbar = (c+ + c-)*a + i*(c+ - c-)*b` folds two reals at two L*F
products = 8 muls for the pair, versus two CM31 symbols at 6 = 12 — a real ~1/3
saving (`24(k-1) -> 16(k-1)`), soundness-neutral, leaves unchanged. So the
conjugate-pair rewrite is a VALID technique; §11's "worse" reasoning analyzed
arbitrary symbols, not conjugate pairs. §11's CONCLUSION nonetheless stands, for
the sharper reason below.

**The load-bearing precondition FAILS for the measured seam.** The rewrite
requires the four leaf slots to be two CM31-conjugate pairs (a+ib, a-ib) AT THE
RLC INPUT (the report's own falsifiers #1, #3). They are not. The measured
exact-wide path is an ordinary-univariate CM31 MULTIPLICATIVE-coset PCS: the
query decomposition (verify.rs `slot = i >> log_fiber_count`, L1245-1247) places
the four slots of fiber f at domain indices f, f+N/4, f+N/2, f+3N/4 — points
`{s, iota*s, iota^2*s, iota^3*s} = {s, is, -s, -is}` (iota = -i, order 4), a
multiplicative order-4 coset. Because offset has order 2N, s has order exactly
2N > 8, so s^2 is never in {1,-1,+-i} and conj(s)=s^-1 is NOT among the four
slots — the conjugate coset {+-s^-1, +-is^-1} lives in the PARTNER fiber
f_bar=F-1-f (column-basis-audit L200-217). Moreover the RLC kernel
(`qm31_cm31_dot4_prepared_bytes`) computes FOUR independent per-slot dot products
over the 49 COLUMNS (6 M31 muls/(col,slot), corroborating the 24(k-1) baseline)
and NEVER combines slots; the only slot-mixing stage, `fold_fiber` (verify.rs
L460-482), pairs ANTIPODES {s,-s}/{is,-is}, not conjugates. So there is no
`c+*x + c-*xbar` conjugate-pair operation anywhere to rewrite. Co-locating
conjugate pairs would require re-laying-out leaves (a two-to-one query map with
renewed soundness) — i.e. NOT "leaves unchanged."

**The report's 16(k-1) target is just the cost of M31 leaves.** Two conjugate
CM31 slots carry only 4 independent M31 values, folded at 4 muls = 16(k-1) — the
same count the M31-leaf circle candidate already computes (`qm31_m31_dot4`,
4 muls/symbol, 196 M31 leaf values), but with M31 leaves, which CHANGE the
commitment (§11/§12). And the report's `a+ib/a-ib` identity does not even
literally match that candidate: its leaves are two INDEPENDENT M31 reals
`f(P), f(conjP)` (the "conjugate" is a coordinate reflection (x,-y), not a
real/imag split of one CM31), so there is no imaginary part to factor out — the
candidate reaches 16(k-1) simply by committing M31 leaves. So the report's
saving, where it is real, is the CM31->M31-leaf commitment change, reachable on
NEITHER path as a leaves-unchanged rewrite. Same conclusion as §11/§12, by a
different route.

**Even hypothetically, it is marginal, not a rescue.** With CM31 leaves kept,
the verifier still decodes both limbs of all 392 M31 limbs/query — and byte
decode is ~89% of the reducible seam (§12 structural estimate, not a profiled
SBF probe). The rewrite touches only the ~11% multiply arithmetic, so ~1/3 of
that is ~39K CU on the 1,066,396 base — BELOW the report's own ~49K gap to 1.4M.
Only the most favorable reading (11% of the larger ~1.449M estimate) barely
exceeds 49K, and it requires both the multiply fraction to scale AND the rewrite
to apply. Since the precondition fails, the measured saving is 0.

**Net.** §11's verdict is UNCHANGED (DEAD for the measured exact-wide CM31 seam).
The report's contribution is a cleaner articulation of WHY (conjugate pairs carry
half the information) and a correction to §11's op-count framing — both recorded.
No soundness-neutral, leaves-unchanged saving exists on the current seam; the
report's 16(k-1) is the M31-leaf commitment change (§11/§12 route).

## 14. Johnson rate/query redesign — literal rate-1/16 result (`2026-07-12`)

The q74/g32 falsification measurement closes only the fixed rho=1/4
implementation fork. At the pinned eta=sqrt(rho)/20=0.025, the Johnson query
term needs q74 and the literal M31 proof reconciles to **1,873,746 CU**. The
monolithic instruction exhausts at 1.4M; the five-segment overlap ledger is
validated by the low-rate direct run below to within 7 CU.

The radix-4-compatible alternative rho=1/16 keeps the 1,024-coefficient
message, four arity-4 folds, and final four coefficients, while enlarging only
the evaluation/Merkle domains. With eta=0.0125,
`-log2(sqrt(rho)+eta)=1.929610672` bits/query, so q36/g32 gives **101.465984
query-round bits**. The literal 73,620-byte proof
`98697f1c...3982e2` accepts in 5/5 Agave simulations at **1,237,877 CU**,
leaving **162,123 CU** below the platform cap. Its independent segmented
reconciliation is 1,237,884 CU, a 7-CU calibration delta.

This reopens the PERFORMANCE fork; it does not close the SOUNDNESS fork. Under
the existing pinned Johnson formulas at rho=1/16:

| term | rate-1/16 result |
| --- | ---: |
| Johnson T1 rounds | 66.7465 / 70.7465 / 74.7465 / 78.7465 bits |
| Johnson T1 union, no per-fold PoW | **66.6534 bits** |
| T2 union, two OOD samples, L=160 | 214.2756 bits |
| q36/g32 query round | 101.4660 bits |

Thus the current no-per-fold-PoW protocol is still T1-bound near 66.65 bits.
The upstream-style per-fold-PoW illustration `[36,32,28,24]` would place each
T1 round at 102.7465 bits, their union at 100.7465, and the T1+q36 query union
at only 100.0618 bits before the remaining ledger. This vector is NOT adopted:
its state-restoration/BCS composition must be proved for the exact transcript,
its prover work is material, and the remaining terms leave essentially no
soundness slack. q37 or stronger per-fold work is the first sensible audit
row, and its verifier CU must be measured rather than assumed.

CU consequence: adding the measured central r2 constraint-composition delta
70,954 to the direct PCS gives 1,308,831 CU, leaving 91,169 CU before hiding,
PoW checks, and the atomic transition. That is a planning row, not an
integrated total, because composition has not yet been spliced into tag 28.
The one-transaction direction is therefore alive but narrow; receipt-bound N=2
remains the fallback until the rate-1/16 soundness and hiding gates close.

## 15. Payment-terminal algebra and generated copy routing (`2026-07-12`)

The production payment prefix now derives its ten-coordinate PCS point from
the payment zerocheck transcript. The verifier no longer accepts a
caller-supplied point. The frozen source registry has 252 constraints. The
first 250 have M31 values on Boolean trace rows and are packed four at a time
in the QM31 basis `(1,i,u,iu)`. This map is injective over M31, so a packed
Boolean-row residual is zero exactly when its four source residuals are zero.
The generic copy and range LogUp residuals remain separate because they are
already QM31-valued. Consequently its theta randomizes 65 polynomials and its
two helper-sum claims make 67 randomized claims, rather than the former 254.
The selected direct-range profile has a distinct exact shape: the range LogUp
is absent, its 30 bitness and three reconstruction residuals pack injectively
into nine QM31 lanes, and theta randomizes `63 + 1 + 9 = 73` lanes. Its one
surviving helper makes 74 claims. This is a protocol registry change, not an
implementation-only recount; the statement crate exposes the new constants,
but the Fiat--Shamir registry still requires a deliberate version/KAT repin.

The exceptional-copy terminal uses 48 fixed selector matrices: for each of
four endpoint slots, one weight matrix, one tag matrix, and ten tuple-pattern
matrices. If `h in QM31^64` and `l in QM31^16` are the tensor selector halves,
one table evaluates as

`h^T A_m l`.

The checked-in const generator derives every `A_m` from the independent
102-link exceptional layout, then repeatedly removes an exact rank-one outer
product. For

`A_m = sum_t u_{m,t} v_{m,t}^T`,

the SBF evaluator computes

`h^T A_m l = sum_t (h . u_{m,t}) (v_{m,t} . l)`.

Nineteen matrices are nonzero, their total M31 rank is 47, and the generated
factors have 674 nonzero scalar coefficients. No factor is hand-transcribed:
`build_copy_routing_factorization` is evaluated at compile time from
`EXCEPTIONAL_COPY_TERMINAL_LINKS`. The reference path independently walks the
full 592-link registry. The link fields and all ten column patterns are bound
to FNV-1a fingerprint `0x77973120f60be58b`; a const assertion fails the build
if the layout changes without an explicit review and repin. Because the
factorization regenerates from the frozen layout, adding hiding columns cannot
silently reuse stale factors.

Polynomial-identity guard: each test run reads uniform rejection-sampled M31
coordinates from `/dev/urandom` and compares the compiled evaluator with the
independent full-link walk at 50 fresh random QM31 points, random openings,
and random lambda values. The difference has total degree at most 27 in this
test surface, so 50 independent agreements have Schwartz--Zippel false-pass
probability below `2^-5900` if the implementations differ. A separate fixed
corpus covers lambda zero and one, single-column basis vectors, coupled
cross-column residuals, and Boolean padding rows. Boolean-only agreement is
not treated as an identity test.

The first fully labelled SBF run reports these verifier components (diagnostic
logging included): parse/decode 7,952 CU; prefix transcript/challenges 7,526;
ten-round sumcheck verification 54,019; point/evaluation absorption and gamma
2,495; opening assembly 568; selector tensor 48,865; Poseidon 125,583; fixed
relations 134,233; generated copy routing plus LogUp 146,168; range LogUp
7,552; packed theta batching 47,899; terminal wrapper 1,728; and unmarked
transaction/dispatch/return 1,547. Their sum is the measured 586,135 CU. The
six added pre-terminal markers account for the small increase over the
previously dark overhead; this row is a statement diagnostic, not an
overlap-subtracted PCS-plus-statement total.

## 16. Profile 15 rate-1/16 soundness reconciliation (`2026-07-12`)

Status: **not closed and not quotable.** This section audits the selected
one-mask profile against the implemented verifier. It supersedes §14's
planning arithmetic where the two disagree, but it does not turn the numeric
target in `results/stage2/rate16_hardened_soundness.json` into a theorem.

### 16.1 Do not conflate q36/g16 with the implemented profile

Profile 15 is `rho=1/16`, q36, final-query grinding g36, and four additional
fold-work checks `[39,35,31,27]`. It is not q36/g16. The relevant Johnson
query factors, at the pinned slacks, are:

| schedule | query-work term | immediate consequence |
| --- | ---: | --- |
| old `rho=1/4`, q36/g16 | 49.4660 bits | the old capacity-shaped q36/g16 measurement cannot support a Johnson claim above this |
| `rho=1/16`, q36/g16 | 85.4660 bits | still bounded by the no-fold-work T1 union below |
| `rho=1/16`, q36/g32 | 101.4660 bits | §14's unhardened Johnson-query row |
| **profile 15: `rho=1/16`, q36/g36** | **105.4660 bits** | current final-query target, before all other terms |

For the implemented arity-four generator, the MCA numerator carries the
factor `ell-1=3`. With no per-fold work this makes the four-round T1 union
**65.0685 bits**, not §14's 66.6534. With profile 15's fold-work vector, every
round is 104.1615 work-normalized bits and their union is **102.1615 bits**.
The correction is already present in `xtask/src/stage2_rate16_soundness.rs`;
the older §14 row omitted `log2(3)`.

The historical capacity calculation is not an alternative way to price these
rows. Its general up-to-capacity premise is refuted (§9), and the revised
circle/finite-length conjecture is still uninstantiated. At Johnson, the
profile-15 numbers remain conditional on the exact-candidate transport in
§16.4.
Even under the retired `rho=1/4` capacity arithmetic, q36/g16 contributes
only `36*2+16 = 88` query-work bits, so that measured schedule was never a
100-bit row.

### 16.2 Corrected local ledger for the one-mask construction

The current `aspis-rate16-hardened-soundness-v1` artifact is a useful target,
but it is stale with respect to profile 15. In particular, it omits the
degree-ten payment sumcheck, the zerocheck reduction, and the nonzero `eta`
binding event; it retains a two-helper/range-LogUp count that the direct-range
profile no longer has; and its `hiding/code-switch reserve` predates the
one-mask construction. The implemented local shapes are:

| item | profile-15 shape | bits | status |
| --- | --- | ---: | --- |
| T1 grouped-fold MCA | hardened artifact formula with generator factor 3 and fold work `[39,35,31,27]` | 102.1615 | **open exact circle/fold/BCS transport** |
| T2 two-sample OOD binding | current `L=160` target | 214.2756 | root bound only after the committed-list and exact accepted-domain invariant is proved |
| PCS relation sumchecks and eight OOD mixers | `32/|QM31|` | 119.0000 | local SZ shape; exact protocol reduction still belongs in the transport theorem |
| masked payment sumcheck | `10 rounds * degree 10 / |QM31|` | 117.3561 | local sumcheck bound; missing from the current artifact |
| zerocheck random point | `10/|QM31|` | 120.6781 | local multilinear identity bound; missing from the current artifact |
| constraint/helper batching | `(72+1)/|QM31|` | 117.8102 | 73 outer lanes give theta degree 72; the surviving `h1` helper adds an independent mu degree-1 event |
| mask/original binding | `1/|QM31|` in nonzero `eta` | 124.0000 | committed `H` and initial claim precede eta; add this affine event |
| gamma column batching | `50/|QM31|` | 118.3561 | 49 C1 + `h1` + `G`, ordinary powers 0..50 |
| two-point batching | `1/|QM31|` | 124.0000 | `second_point_scale` remains a separate generic challenge despite removal of mask kappa/delta/tau |
| copy tuple compression | `(594*17)/|QM31|` | 110.6982 | 592 base links plus the two direct-range reconstruction links, replacing the old 589/1024 placeholders |
| copy pole bound | `(4*594)/|QM31|` | 112.7857 | the direct-range profile has no range LogUp helper; its bit/reconstruction residuals are in theta |
| traced queries + final work | `(.25+.0125)^36 / 2^36` | 105.4660 | **open exact fiber-query/BCS transport** |

The selected direct-range constraint code packs the first 250 source residuals
into 63 tower coordinates, retains the extension-valued copy LogUp as lane 63,
and injectively packs the 30 M31 bitness plus three M31 reconstruction
residuals into nine consecutive lanes 64..72. The bitness formula is
`b^2-b`. One outer Horner evaluation therefore has exact theta degree **72**;
there is no nested 33-term theta polynomial and no degree-96 endpoint. The
profile-15 terminal then adds only `mu*h1`, under an independently sampled
challenge.

The statement metadata pins this as 284 total direct-profile source residuals
(250 base-field residuals, one copy-LogUp residual, and 33 direct-range
residuals), nine direct-range packed lanes, 73 constraint lanes, one helper,
theta degree 72, and 74 claims including `h1`.
The transcript still absorbs the legacy global `(version=2, sources=252,
claims=67, two zero helpers)` registry. That mismatch does not change the
algebra implemented here, but it must be resolved by a dedicated registry
version/count/helper framing and transcript KAT repin before profile 15 is
frozen or quoted. The global profile identifier is deliberately not bumped by
this intermediate optimization.

The previous **102.1567-bit** provisional union used the superseded degree-96
batching row and is stale pending regeneration of the complete local ledger.
Adding the 105.4660 query term and the 124/128-bit hash assumptions gives
**102.0180 bits before privacy failure**. This is a corrected parameter
sensitivity only. T1, T2, the query term, and BCS composition are not yet
transported, so 102.0180 is not a security claim.

The one-mask construction adds no separate code-switch or mask-proximity
protocol: `G` is the fifty-first ordinary column in the same scalar powers
generator. Its false-accept contribution is the `eta` line above plus the
unchanged PCS binding terms. A rank-deficient masking view is a privacy event,
not an argument-soundness event, and must not be hidden inside an invented
110-bit `code-switch reserve`.

### 16.3 The hiding rank event has no probability bound yet

The current test
`one_explicit_mask_and_c1_padding_remain_surjective_after_all_openings`
passes three fixed schedules. It proves that a full-rank minor exists at those
points; it does not prove a bad-point probability. Two concrete gaps prevent
turning it into the reserved `2^-110` line:

1. The test samples 36 **distinct** fibers. Production
   `Transcript::challenge_queries` samples with replacement. At 36 draws from
   4,096 fibers, the probability of at least one duplicate is approximately
   **0.142946**. Duplicates do not themselves imply leakage--the public view
   then has fewer independent coordinates--but the rank test must quotient
   repeated observations or the sampler must deliberately change to
   without-replacement sampling. The present test models neither exact case.
2. No explicit minor, determinant polynomial, or degree has been pinned. A
   generic Schwartz--Zippel argument over M31 can provide at most about 31
   bits before its degree loss, so it cannot justify a 110-bit privacy term.
   A valid closure needs either a structural full-rank proof for every allowed
   schedule, or an explicit QM31-defined minor of degree at most about `2^14`
   together with a proof that its variables are fresh uniform QM31 challenges.
   The M31-only C1 padding makes that field-of-definition step nonautomatic.

The tested view also omits the complete public transcript: later-layer sibling
slots, all OOD values and relation messages, final polynomial coefficients,
proof-account/log bytes, and Fiat--Shamir adaptivity. These are additional
linear observations even when the one path value is locally determined by a
layer-zero fiber. The mandatory next artifact is one exact-view matrix (with
duplicate-query quotienting) plus either a universal-rank proof or the explicit
minor/degree bound. Until then there is no numeric hiding-failure term to add.

### 16.4 Exact missing transport theorem and production check

The missing theorem is not merely "circle code is a scaled GRS code." The
required exact-candidate statement is:

> For the `L'_10` subcode on the 2^14 circle domain, with 49 M31 words embedded
> in QM31 and the two QM31 words `(h1,G)` committed under a second root before
> gamma, the generator `(1,gamma,...,gamma^50)` and each grouped fold
> `(1,alpha,alpha^2,alpha^3)` preserve Johnson-radius disagreement through the
> four actual circle/line subcodes; folding commutes with the relevant lists;
> the two adaptive OOD samples over `C(QM31) minus C(CM31)` and
> `QM31 minus CM31` bind the MLE relation; a four-slot fiber query has the claimed
> miss probability; and the exact radix-four SHA-256 Fiat--Shamir transcript
> with fold work and final work satisfies the stated state-restoration/BCS
> bound.

The scaled-GRS isometry establishes only the starting code/list fact. The
polynomial-generator MCA result supplies a core Johnson primitive, but the
grouped-fold/list-commutation, two-phase heterogeneous batching, custom MLE
relation/OOD invariant, fiber sampling, and BCS composition above are still
unwritten reductions. These are precisely why the artifact correctly keeps
`quotable_complete_system_claim=false`.

There is also a code-level gate: the only integrated profile-15 program tag is
`MeasurePaymentHidingProfile15`. It calls
`verify_payment_hiding_candidate_unmined_for_diagnostics_with_trace`, which
absorbs nonce bytes but deliberately skips all five PoW predicates. No spend
authorization path currently calls `verify_payment_hiding_candidate_segment`,
and no atomic state transition follows it. A closure run must use a genuinely
mined proof through the production verifier, corrupt each fold/final nonce in
teeth tests, and mutate the nullifier/state only after complete verification.
The diagnostic CU result is not that code check.

### 16.5 Closure order

1. Correct and regenerate the soundness artifact with every §16.2 term, the
   exact accepted OOD-domain sizes, registry version/count, and `m=594`.
2. Write the exact-candidate Johnson transport theorem in §16.4 and encode each
   premise as a conformance or adversarial test; do not promote isolated MCA.
3. Expand the rank artifact to the complete public view and close §16.3 with a
   universal-rank or explicit determinant-degree proof.
4. Add the production profile-15 instruction, mined-nonce corpus, final KAT,
   leakage inventory, and atomic-spend transition.
5. Only then quote the recomputed union and the one-instruction CU result.

---

## Appendix: hardening implementation queue (order fixed in review)

0. **Upstream constant pin** (§4 experiment): **CLOSED.** The deterministic
   `stage1-soundness-pin` runner and
   `results/stage1/upstream_soundness_pin.json` pin T1/T2 to
   `WizardOfMenlo/whir@10aa7d0`. The result narrowed the headline margin and
   corrected T2 to the `C(L,2)` form; it did not upgrade any capacity claim.
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
   **ROUND-TRIPPED**: the current v3 two-phase KAT matches on SBF (Agave
   2.3.0, `results/stage0/transcript_kat.json`, 25,426 CU). The complete pin
   history and reason for every Stage 1 re-pin is recorded in
   `results/stage1/transcript_kat_repin_ledger.json`: branch baseline
   `16eb0c...`, OOD binding `bef9b0...`, relation interleaving `e00bd5...`,
   and C2/order integration `26f091...`. Each new digest was first observed
   as the expected failing host KAT and then matched on SBF. This answers the
   re-pin question directly: all three changes were deliberate named
   protocol changes, not constants edited merely to green the suite. This
   item is CLOSED.
2. **(z, v) claim binding + enforcement. IMPLEMENTED.**
   `EvaluationClaim { z, v }` is a transcript-absorbed public input (label
   CLAIM, canonical position: after C2 and before gamma; header byte 15 is a
   claim/C2 bitfield, and claim-carrying v3 proofs require C2).
   Delivered rejections: claim mix-and-match, flag mismatch both ways
   (ClaimMissing/ClaimUnexpected, codes 14/15), point-dimension mismatch
   (ClaimShape, 16), gamma-before-claims ordering, and an honestly
   constructed proof carrying a false `v` (SumcheckBoundaryMismatch, code
   18). Program side: `VerifyWithClaim` instruction and instruction-path
   test.
3. **OOD absorption + enforcement** (T2): **IMPLEMENTED.** Envelope version
   3 carries one canonical QM31 value after each round root (and after the
   C2 prefix in round zero). The verifier derives `beta_r` after
   the root, rejection-samples outside the CM31 subfield, absorbs the value,
   samples its mix coefficient, and includes the relation in that round's
   sumcheck. Delivered tests: honest roundtrip, value corruption, pre-v3
   envelope, alpha-before-value order attack, bounded subfield-sampler
   exhaustion, and a false round-1 OOD evaluation rejected at boundary 1.
4. **Sumcheck/fold interleaving: IMPLEMENTED.** For every four-coefficient
   chunk, `A(X)=a0+a1X+a2X^2+a3X^3`; the dual weight polynomial is
   `B(X)=(b0+b3X+b2X^2+b1X^3)/4`. The degree-6 sum of `A*B` over the fourth
   roots equals the incoming dot product, while evaluation at `alpha_r`
   equals the relation on the exact arity-4 folded coefficients. Structured
   geometric/MLE weights avoid a full verifier vector. Final reduction is
   checked on the four explicit coefficients (EvaluationRelationMismatch,
   code 19). Host invariants, false-claim/OOD vectors, corruption, SBF KAT,
   and eleven pre-C2 on-chain negatives passed. The 801,525 CU / 15,216-byte
   result is therefore explicitly historical, not the gate-close number.
5. **Second commitment phase** (C2, §5): **IMPLEMENTED AT THE PCS
   INTERFACE.** C1 is absorbed before lambda/chi; the generic builder then
   produces C2; both trees are authenticated at the first opening; main and
   helper claims are absorbed before gamma; and the gamma-combined
   polynomial feeds the enforced relation accumulator and every fold.
   Honest generic/synthetic C2 roundtrips and C2 root/claim corruption tests
   pass. The three adversarial order vectors reject canonically and accept
   under their matching deliberately weakened test-only schedules. The
   Stage 1 artifact uses a synthetic helper only for interface cost; the real
   LogUp helper and its economic-attack corpus begin Stage 2.

The final step was remeasured on the literal gate profile and §4 is synced to
that artifact. The Stage 1 PCS protocol gate is closed. The Stage 2 product
feasibility gate is explicitly not: its opening measurement must recover or
fit within the remaining 14,914 CU, which is below the required slack.
