# Aspis soundness note (Stage 1) — DRAFT, section-by-section review in progress

Status: **DRAFT**. Sections are sent for line-by-line review as they are
written and nothing here is frozen until the whole note survives review
(working rule: no soundness claim frozen without the written reduction being
challenged line by line). Section status ledger:

| section | status |
| --- | --- |
| 1. Protocol as implemented | drafted, in review |
| 2. The assumption | drafted, in review |
| 3. Field-ceiling lemma | drafted, in review — one hardening item found (challenge sampler) |
| 4. Per-round query budget (q32/g32, q36 alongside) | stub — flat-rate finding recorded below |
| 5. Copy-argument soundness term | in chat review; hardens into this file only after line-by-line pass |
| 6. Grinding accounting | stub |
| 7. Proven-vs-conjectured ledger | stub |

Headline decision this note serves (design §13.3, decided 2026-07-04): the
public claim is frozen at **t = 100 bits, capacity-conjectured**; §3 is the
justification. Layout this note is written for (design §13.8 as amended):
lr10, k ~ 64-80 wide rows, rounds-per-row blocks, boundary interface columns,
LogUp copy check, second commitment phase.

---

## 1. The protocol as implemented

Everything in this section describes the code at this revision
(`aspis-core`), not a paper protocol. Envelope: `aspis-core/src/proof.rs`
(16-byte header binding profile id, log_rows, log_blowup, query count,
grinding bits, payload and Merkle-mode flags, round count, final-poly
length; then roots, final polynomial, grinding nonce, per-layer openings;
fixed layout, trailing bytes reject).

Fields. M31 = GF(2^31 - 1); CM31 = M31[i]/(i^2+1); QM31 = CM31[u]/(u^2-(2+i)).
|QM31| = (2^31 - 1)^4, log2 = 123.9999999978 (call it 2^124 with the deficit
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
QM31 (late lift at the first challenge).

Transcript order (Fiat-Shamir, SHA-256 duplex; syscall on-chain):
absorb(header) -> absorb(statement digest) -> for each round r: absorb(root_r),
sample alpha_r in QM31 -> absorb(final polynomial) -> grinding check on the
current state (g leading zero bits over hash(state, nonce)), absorb(nonce) ->
derive query positions (masked uniform over the power-of-two fiber count;
exact-uniform). One query set, sampled once, traced through all rounds; each
query opens one fiber per layer, the verifier refolds locally (challenges
alpha_r, alpha_r^2 for the two sub-steps; denominators batch-inverted per
round) and compares against the next layer's opened slot, terminating against
the final polynomial.

Grinding is a single g-bit check placed after all absorptions and before
query derivation. There is no per-round PoW (this is a recorded divergence
from both the reference v0 schedule and upstream WHIR; see
`whir-p3-divergence.md`).

What Stage 1 adds on top of this implemented base (audited here, implemented
as the note firms up): OOD samples per round, the externally supplied (z, v)
evaluation claim, the second commitment phase for the copy argument, and the
statement-layer sumcheck the PCS serves.

## 2. The assumption, stated once

All conjectured terms in this note rest on exactly one assumption, named
here and nowhere re-derived:

> **Capacity conjecture (folded Reed-Solomon over the CM31 circle-coset
> domain).** For the code ensemble produced by the implemented fold schedule
> (arity-4 folding of RS-type evaluations over cosets of 2^k circle
> subgroups), proximity gathering and query soundness behave up to the code
> capacity bound: a codeword delta-far from the code, delta up to 1 - rho,
> survives one uniformly sampled traced query with probability at most
> (1 - delta), i.e. one query yields -log2(rho_worst) bits; and the per-round
> folding/gathering error terms carry denominators |QM31| with the
> constants tabulated in section 4.

Everything labelled `conjectured (capacity)` in the ledger (section 7)
depends on this and only this. Terms that do not depend on it (sumcheck SZ,
RLC batching, copy-argument compression, zerocheck reduction, Merkle binding
under SHA-256 collision resistance, grinding in the ROM) are labelled
separately. The Johnson-regime alternative is dead for a different reason
(section 3): the field ceiling makes its target unreachable anyway, which
retires the johnson_q80 profile without needing to resolve the whir-p3
divergence in its favor.

## 3. The field-ceiling lemma (why the headline is t = 100)

**Lemma (informal).** Every algebraic soundness term of the full target
system has denominator |QM31| ~ 2^124, and grinding offsets none of them.
Union-bounded, the system's achievable soundness on this field tower is
roughly 106-112 bits before a single query is spent. Therefore 128 bits was
never reachable on M31/CM31/QM31, and the headline claim is frozen at
t = 100, capacity-conjectured, with the remaining 6-12 bits as union-bound
margin.

Enumeration (lr10 / k <= 82 / fused sumcheck; numerator shapes first, then
the value at the target parameters):

| # | term | shape | value (bits below 0) |
| --- | --- | --- | ---: |
| T1 | per-round proximity gathering (4 rounds) | c_r * N_0 / \|F\|, N_0 = 2^12 | ~106-112 (constants pinned in §4 against the upstream reference) |
| T2 | OOD binding, 1 sample x 4 rounds | R * 2^lr / \|F\| | 112 |
| T3 | fused sumcheck Schwartz-Zippel | nu * d / \|F\|, nu = 10, d <= 7 | 117.9 |
| T4 | zerocheck eq-reduction (sample r) | nu / \|F\| | 120.7 |
| T5 | gamma-RLC batching over k' <= 82 columns | (k'-1) / \|F\| | 117.7 |
| T6 | copy-argument tuple compression (lambda) | m * w / \|F\| (worst m = 2^10, w = 17) | 109.9 |
| T7 | copy-argument pole/SZ (z) | 2m / \|F\| | 113 |
| T8 | claim-batching challenge (mu) | (#claims) / \|F\| | ~122 |
| T9 | challenge-sampler statistical distance | see finding below | currently ~26 (!) — must be fixed, then 0 |

Union of T1-T8: dominated by T1 and T6, total ~2^-106 .. 2^-109. Ceiling
before queries: **~106-109 bits** (the bracket narrows when §4 pins T1's
constants; it does not move above ~115 under any reading of the gathering
constants). t = 100 leaves 6-9 bits of union-bound margin. t = 128 would
require every enumerated term to vanish — not a parameter choice, a
different field tower.

Grinding does not appear in this table by construction: a PoW placed before
query derivation raises the cost of resampling the query challenge only; T1-T8
are sampled from transcript states the prover must commit to before the PoW,
and re-grinding does not re-roll them cheaply — but even granting the
adversary free re-rolls of everything, each T_i is an information-theoretic
SZ/collision bound per transcript, and the union bound above is per-proof.
Section 6 does the careful version of this paragraph.

Corroboration from outside this repo (context, not proof): the WHIR-JB
reference implementation runs 128-bit settings on Goldilocks3 (~192-bit
field) and structurally fails on Goldilocks2 (~128-bit field); the M31
circle-STARK ecosystem (stwo) targets ~96-100 bits. The ~124-bit field
ceiling also matches the ~124-bit collision resistance of the 8-limb
Poseidon2-M31 digest (design §13.2), so the whole system lands on one
coherent ~100-bit label with no weakest-link asymmetry to apologize for.

**Finding (T9, must fix in Stage 1 hardening): the implemented QM31
challenge sampler is not statistically close enough to uniform for a
2^-100 claim.** `Transcript::challenge_qm31` takes 31 bits per limb and
folds the single value P to 0, giving each limb a 2^-32 statistical distance
from uniform (the point 0 has doubled mass). The generic bound
|P_biased(A) - P_uniform(A)| <= SD applies to every event, so with ~50 limbs
sampled per proof the union-bound cost is ~2^-26 additive — formally
swamping every other term in this table, even though it corresponds to no
known attack. Widening the sample does not fix it (a u128 reduction still
leaves ~2^-97 per limb). The fix is rejection sampling: resample the 32-bit
limb when the masked value equals P (expected retries 1 + 2^-31; verifier
cost unchanged in practice), making the sampler exactly uniform and T9
identically zero. This lands in the hardening implementation together with
OOD and the (z, v) interface.

## 4. Per-round query budget — STUB, one finding already recorded

To be drafted next (after §3 review). It must be computed for the schedule
as implemented, not the Phase 2 two-round shape, and the first honest look
already produces a discrepancy worth flagging before the table exists:

**Finding: the implemented fold schedule has FLAT rate, not improving
rate.** Each round folds degree by 4 AND domain by 4, so rho_i = 2^-2 at
every layer; there is no per-round rate improvement for later queries to
exploit. Under flat-rate capacity accounting with one traced query set,
query soundness is ~2 bits/query + g: q32/g32 = 96 bits — **4 bits short of
t = 100** — while q36/g32 = 104 clears it. The Phase 2-derived expectation
(q32 at t ~ 108-112) implicitly assumed an improving-rate schedule (rate
1/16 shapes). Three resolutions exist and the choice belongs to this
section's review: (a) accept q36/g32 as the target (measured 742,795 CU PCS
at q36 lr10, projection 973,909 CU — still >200K of budget); (b) restructure
the fold to WHIR's domain-halving shape so rho improves per round and
re-derive per-round query counts (protocol change, CU consequences
re-measured); (c) re-examine whether the traced-query accounting can credit
later rounds at all without per-round query sets. No number from this
section is usable until one of these is chosen in review.

## 5. Copy-argument soundness term — IN CHAT REVIEW

Being reviewed line by line before it hardens into this file (explicitly
requested workflow). The draft under review covers: interface tuple
definition (tag + w-limb state), lambda tuple-compression term (m*w/|F|),
z pole-collision/SZ term (2m/|F|), the helper-column relation folded into
the fused zerocheck, Fiat-Shamir ordering (interface columns committed
before lambda and z; helper column committed after — the second commitment
phase), and the insensitivity of all terms to the m = 40 vs m = 2^10 layout
reading.

## 6. Grinding accounting and what it does NOT cover — STUB

To be drafted after §4 settles the query schedule.

## 7. Proven-vs-conjectured ledger — STUB

One line per term, written last, after every section above survives review.
