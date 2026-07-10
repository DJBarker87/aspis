# Aspis soundness note — Stage 1 frozen PCS milestone

Status: **FROZEN FOR THE STAGE 1 PCS MILESTONE (`2026-07-10`)**. The
capacity-conjectured headline is frozen with its caveats; Stage 2 payment
feasibility is not. The final C2 build leaves only 14,914 CU before unpriced
constraint composition, so this checkpoint is a protocol gate close and a
feasibility warning, not a claim that payments work. Section status ledger:

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

Headline decision this note serves (design §13.3, decided 2026-07-04): the
public claim is frozen at **t = 100 bits, capacity-conjectured**; §3 is the
justification. Layout this note is written for (design §13.8 as amended):
lr10, k ~ 64-80 wide rows, rounds-per-row blocks, boundary interface columns,
LogUp copy check, second commitment phase. Query schedule ruled by §4:
**q36/g32** (q32/g32 retired at 96 bits; q38 is the inline contingency).

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

All conjectured terms in this note rest on exactly one assumption, named
here and nowhere re-derived:

> **Capacity conjecture (folded Reed-Solomon over the CM31 circle-coset
> domain).** For the code ensemble produced by the implemented fold schedule
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
that each vector has teeth; the feature is absent from the SBF build.

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

**§4 upstream pin (CLOSED experiment).** The reproduction command
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

**OOD sample count decision (third review touch): freeze `s = 1` for v3.**
This is a deliberate product-budget decision, not an omitted option. At the
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
away:** adversary success **per unit of adversary work** <= 2^-103.9508
(algebraic union, ~1 hash per attempt) + 2^-32 * 2^-72 (query term at
q36/g32, 2^32 hashes per attempt) = 2^-102.9752 worst-case; the frozen
headline t = 100 holds with about 2.98 bits of margin, conditional on the
three-clause capacity conjecture (§2) and the two SHA-256 assumptions (§7);
the proven floor on the same schedule is about 65.5 bits (§7). No other
number in this note is the system's security level.

## 7. Proven-vs-conjectured ledger

One line per term. `proven` lines are proven **within the model**, i.e.
conditional on the two assumption lines above them; nothing on a `proven`
line is conditional on the conjecture line.

| item | label | bits / basis |
| --- | --- | --- |
| SHA-256 as a random oracle (Fiat-Shamir transcript) | **assumption** | model floor for every line below |
| SHA-256 collision resistance for Merkle binding | **assumption** | >= 100 bits claimed (128-bit birthday bound) |
| Capacity conjecture — query radius, T1 gathering constant, effective list bound | **conjectured** | query term 104 work-bits; T1 unique-shaped union 111.5906; effective OOD list `L <= 40` |
| **Proven floor, same schedule, Johnson-radius accounting** | **proven** | **~65.5 bits**: delta <= 1 - sqrt(rho) - eta, rho = 2^-2, delta ~ 0.475 -> ~0.93 bits/traced query; 36 x 0.93 + 32 ~ 65.5 |
| T1 proximity gaps, pinned Johnson branch without per-fold PoW | proven for the pinned upstream model; mapped conservatively to the Aspis round sizes | 73.6534-bit four-round union; above the 65.5-bit proven query floor, far below the capacity-shaped T1 clause |
| T2 OOD formula | proven conditional on a decoding-list bound | `C(L,2) * ((degree-1)/\|F\|)^s`; exact quadratic shape pinned in §4 |
| T2 OOD binding at capacity | **conjecture-conditional** | 103.9875-bit four-round union at the conjectured `L <= 40`, one sample per round |
| T2 OOD binding at Johnson radius | proven conditional on the pinned Johnson list bound | eta = 0.025, L = 40; same 103.9875-bit union |
| T3 relation + fused statement sumchecks | proven (SZ) | 117.4 (conservative 14 rounds x degree 7) |
| T4 zerocheck eq-reduction | proven (SZ) | 120.7 |
| T5 gamma-RLC batching | proven (SZ; canonical gamma-after-claims order implemented for the generic C2 interface) | 117.7 |
| T6 copy-argument compression | proven (UFD + SZ) | 109.9 (worst layout m = 2^10) |
| T7 copy-argument pole/SZ | proven (log-derivative lemma) | 112 (deliberately loose 4m) |
| T8 claim batching | proven (SZ) | ~122 |
| T9 challenge sampler | fixed by construction (rejection sampling, exact uniform) | 0 soundness cost; field-sampler completeness < 2^-242, OOD-subfield completeness < 2^-184 |
| Grinding g32 | proven (ROM work accounting, §6) | +32 bits on the query term only |
| Stage 2 statement amendment (T5', T7' incl. E4, T8', multiplicity-order line) | proven (SZ / log-derivative; teeth vector executable) | integrated-statement union 103.9453 algebraic, 102.9724 total (§8); Stage 1 rows above unchanged |
| **Headline** | **conditional** | **t = 100, capacity-conjectured; success/work <= 2^-102.9752 worst-case; proven floor ~65.5** |

The proven-floor line follows house precedent (the WHIR-UD gate reported
"lower 58.0 / upper 100.0"): the positive result does not get a lower
standard than the negatives, and the number a hostile reviewer would
compute anyway is computed here, with the derivation shown. Any public
quotation of the headline carries all three numbers of the last line or
none of them.

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
| T5' | gamma-RLC batching over k' <= 84 columns | (k'-1) / \|F\| | 117.6 |
| T7' | copy pole/SZ (E2) + range pole/SZ (E4), shared chi, union | 8m / \|F\|, m = 2^10 | 111 |
| T8' | claim batching | (#claims) / \|F\|, #claims <= 8 | ~121 |

The k' recount that forces T5': the 80-column candidate main trace did not
reserve the lookup's committed columns, so k' = 80 (main) + 1 (multiplicity,
C1) + 1 (copy helper h1, C2) + 1 (range helper h2, C2) = **83**; this note
pins k' <= 84 with one column of slack. **§3's "k' <= 82" is false for the
integrated statement and must not be quoted for it.** The RLC consequence
is priced in `stage2-feasibility.md`: the measured fixed-width kernel is
`qm31_power_table::<80>` and the integrated verifier RLCs 83 values per
query, so the 202,031-CU term scales by 83/80 (~+7,600 CU) and the k80
wide-leaf marker grows by 12 bytes per leaf; both are projection
corrections until integration measures them.

Recomputed union with T5', T7', T8' and all other terms unchanged:
**103.9453 algebraic bits** (was 103.9508); with the q36/g32 query term,
success/work <= 2^-103.9453 + 2^-104 = **2^-102.9724 worst-case** (was
2^-102.9752). The headline stays t = 100, capacity-conjectured, with ~2.97
bits of margin; T2 and the query term still co-bind and nothing moved
between regimes. T3 is unchanged (the range relation is degree 3, inside
d <= 7; no new sumcheck rounds beyond the nu <= 14 allowance); T4 and T6
are unchanged.

**Envelope consequence: version 4.** The Stage 2 C2 phase carries **two**
helper columns, so the C2 layer-0 leaf widens from 4 QM31 (64 bytes) to
8 QM31 (128 bytes) per opened fiber, and the C2 claimed-evaluation field
carries two values. That is a fixed-layout change: the payment envelope
bumps to **v4** and v3 remains the frozen Stage 1 format. The gamma
combination generalizes to `w* = sum_i gamma^i w_i + gamma^k1 h1 +
gamma^(k1+1) h2` with all claims absorbed before gamma exactly as today
(the existing gamma-before-claims vector covers the extended claim set; the
sum(h) = 0 claims are batched into the fused statement sumcheck and add no
denominators, E3). The schedule-level transcript KAT will move when the v4
absorptions land; that is a deliberate named re-pin recorded in
`transcript_kat_repin_ledger.json` like the four before it, not a constant
edited to green the suite.

**What integration may still change.** Exact leaf packing for the wide C1
row, the selector reading for which cells are range-checked, and the final
(m, w) for §5 are layout-freeze decisions; if any of them moves a number in
this section, this section is re-dated before the gate note quotes it.

**Selector-factoring correction (`2026-07-10`, shrink hunt).** The r=4
candidate packs permutations into 6-row blocks, and 6-row periodicity does
NOT factor over the low bits of the Boolean cube — §5's stated O(2^b)
block-periodic selector evaluation was silently false for that reading.
Power-of-two block alignment restores it: r=3 gives 2^3-aligned 8-row
blocks (392 rows), r=2 padded blocks are 2^4-aligned (784 rows); r=1
exceeds the 2^10 row cap. The shrink hunt's adopted candidate is the r=2
/ k' = 51 shape (`docs/stage2-shrink-hunt.md`); at its layout freeze the
k' pin moves to <= 52, T5' improves to ~118.3 bits, the copy multiset
recount (~490 links) stays inside the m = 2^10 worst-case reading, and
this section is re-dated. LogUp-GKR helper elimination was priced against
verified sources and rejected as a net ~175K-CU loss on SBF; the analysis
and abandon criterion are recorded in the hunt document.

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
