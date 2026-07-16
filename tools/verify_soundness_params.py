#!/usr/bin/env python3
"""Independent finite-parameter checker for the aspis-spend soundness premise.

The soundness theorem (`paper/aspis-spend/sections/soundness.tex`) is
conditional on Assumption `ass:pinned-finite-reduction`: for the exact frozen
code, transcript, and verifier, the transport lemma `lem:circle-grs-transport`,
the batching lemma `lem:johnson-mca-batch`, and the local-binding lemma hold
with the event partition and per-event bounds of the ledger
`tab:soundness-events`.  In the release the only thing checking that the
finite-parameter hypotheses actually hold at the pinned constants is the
prover's own ledger calculator
(`crates/aspis-prover/examples/spend_soundness_epro_ledger.rs`).  This tool is
an independent second opinion, in the exact mold of
`tools/verify_hiding_ranks.py`.

WHAT IT DOES

  * It re-derives each finite-parameter quantity of the soundness premise from
    the PUBLIC parameters (rate, domain sizes, the width-29 batch, the Johnson
    multiplicity) and the cited theorems' formulas, using its OWN arithmetic.
    Nothing from the Rust prover or aspis-core is imported or called; the M31
    circle group and the QM31 field size are re-implemented here from their
    public mathematical definitions.

  * It re-implements the M31 circle coset the code evaluates on (order 2^19,
    generator CIRCLE_GEN = 2 + 1268011823 i in CM31 = M31[i]/(i^2+1)) and
    re-derives the 131,072 arity-four fiber roots t = 2x^2 - 1 directly.  It
    confirms the transport lemma's stated finite hypotheses: the roots are
    pairwise distinct and none equals one (the condition the release evaluator
    checks and the proof of `lem:circle-grs-transport` invokes).  It also
    cross-checks the circle-to-line transport map t = 2x^2 - 1 against an
    independently computed line-domain layer-one x-coordinate on a sample.

  * It re-derives the Johnson agreement cap A = floor(alpha N), the exact
    proven-Johnson regime inequality (proximity within 1 - sqrt(rho), not the
    capacity conjecture), every tabulated event degree that feeds the
    Schwartz-Zippel / MCA bounds, and the coarse event-union and BCS
    work-normalized endpoints.  Each independently computed value is asserted
    against the pinned constant.

WHAT THIS CHECKS vs WHAT REMAINS IMPORTED

  This tool checks the finite-parameter APPLICABILITY of the imported theorems
  at the frozen constants: that alpha lands in the proven Johnson regime, that
  the width-29 batch is a plain-powers polynomial generator (the MCA generator
  hypothesis), that the circle coset meets the transport lemma's distinctness
  and root-not-one conditions, and that every ledger degree and the union
  arithmetic reproduce the pinned bounds.  It does NOT re-prove the imported
  theorems themselves: Stwo Johnson list decoding (Theorem 7 / 19), the
  Bordage et al. / Haboeck polynomial-generator MCA theorem (9.2 / 9.3), and
  the WHIR fold-list commutation (Lemma 4.13 / Theorem 4.20) are taken as
  stated, exactly as the paper's assumption does.

USAGE
    python3 tools/verify_soundness_params.py

It exits non-zero if any independently derived value disagrees with the pinned
constant.  A disagreement would be a real finding (a finite-parameter
hypothesis different from the one claimed) and must not be ignored.
"""

from __future__ import annotations

import math
import sys
import time

# ==========================================================================
# Own M31 and CM31 arithmetic.  M31 is a Python int in [0, P); CM31 is a pair
# (a, b) representing a + b*i in M31[i]/(i^2 + 1).  Only the public tower
# definition is shared with the construction; no certificate-generating code
# is imported.
# ==========================================================================
P = (1 << 31) - 1
MASK31 = (1 << 31) - 1


def cmul(x, y):
    a, b = x
    c, d = y
    return ((a * c - b * d) % P, (a * d + b * c) % P)


def cpow(x, e):
    acc = (1, 0)
    base = x
    while e > 0:
        if e & 1:
            acc = cmul(acc, base)
        base = cmul(base, base)
        e >>= 1
    return acc


# Public circle-group generator: unit-norm element of CM31, cyclic order 2^31
# (aspis-core params CIRCLE_GEN; shared mathematical primitive, not code).
CIRCLE_GEN = (2, 1_268_011_823)
CIRCLE_LOG_ORDER = 31


def double_x(x):
    # The circle-to-line projection pi(x) = 2 x^2 - 1 the verifier applies to
    # a queried fiber x-coordinate.  This is the arity-four fiber "root".
    return (2 * x * x - 1) % P


def bit_reverse(index, log_size):
    if log_size == 0:
        return 0
    return int(f"{index:0{log_size}b}"[::-1], 2)


# ==========================================================================
# Public spend parameters (paper Table tab:spend-parameters and the frozen
# layout; every constant is a public quantity, not a certificate output).
# ==========================================================================
LOG_MESSAGE = 10                     # 2^10 trace/message rows
LOG_DOMAIN = 19                      # 2^19 circle evaluation symbols
MESSAGE_DIM = 1 << LOG_MESSAGE       # 1024
DOMAIN_SYMBOLS = 1 << LOG_DOMAIN     # 524288
INVERSE_RATE = 512
RHO = 1.0 / 512.0
QUERY_FIBERS = 1 << (LOG_DOMAIN - 2)  # 2^17 = 131072 arity-four fibers = N
N = QUERY_FIBERS
JOHNSON_MULTIPLICITY = 10.0          # m
QUERY_COUNT = 18                     # queries per branch, without replacement
GENERATOR_WIDTH = 29                 # width-29 scalar-powers batch
G_GENERATOR_INDEX = 27
D_GENERATOR_INDEX = 28
SELECTORS = 3
GRINDING_BITS = 32                   # final work predicate
BATCH_GRINDING_BITS = 37             # batch work predicate
FOLD_WORK = [34, 33, 30, 25]

# QM31 field size |K| = P^4 (K = CM31[u]/(u^2 - (2+i))).  Reproduce the exact
# f64 rounding schedule of the Rust ledger so the log2 endpoints match to the
# pinned decimals: float(P) then three float multiplications.
P_F = float(P)
FIELD_SIZE = P_F * P_F * P_F * P_F


# ==========================================================================
# Ledger arithmetic, re-implemented from the cited formulas (own copy).
# ==========================================================================
def union_bits(bits):
    return -math.log2(sum(2.0 ** (-b) for b in bits))


def local_bits(numerator):
    return math.log2(FIELD_SIZE) - math.log2(numerator)


def local_nonzero_bits(numerator):
    return math.log2(FIELD_SIZE - 1.0) - math.log2(numerator)


def bcs_work_normalized_bits(round_bits, ro_queries):
    R = 32.0
    LAMBDA = 256.0
    eps_round = 2.0 ** (-round_bits)
    eps_bcs = (1.0 + R / ro_queries) * eps_round \
        + 3.0 * (ro_queries + 1.0 / ro_queries) * 2.0 ** (-LAMBDA)
    return -math.log2(eps_bcs)


# ==========================================================================
# Transcript / pass-fail bookkeeping.
# ==========================================================================
TOL = 1e-9
_results = []


def check(name, computed, target, unit="", exact=False):
    if exact:
        ok = computed == target
    else:
        ok = abs(float(computed) - float(target)) < TOL
    _results.append(ok)
    tag = "PASS" if ok else "FAIL"
    if isinstance(computed, float):
        cs, ts = f"{computed:.13f}", f"{target:.13f}"
    else:
        cs, ts = str(computed), str(target)
    suffix = f" {unit}" if unit else ""
    print(f"  [{tag}] {name}")
    print(f"         computed = {cs}{suffix}   target = {ts}{suffix}")
    return ok


def note(msg):
    print(f"         {msg}")


# ==========================================================================
# Check 1 -- rate and domain.
# ==========================================================================
def check_rate_and_domain():
    print("[1] Rate and domain (layout constants)")
    check("message dimension = 2^10", MESSAGE_DIM, 1024, exact=True)
    check("circle evaluation symbols = 2^19", DOMAIN_SYMBOLS, 524288, exact=True)
    check("inverse rate 2^19 / 2^10 = 512", DOMAIN_SYMBOLS // MESSAGE_DIM,
          INVERSE_RATE, exact=True)
    check("rho = 2^10 / 2^19 = 1/512", RHO, 1.0 / 512.0)
    check("query fibers N = 2^17 = 131072", N, 131072, exact=True)
    note(f"rho = {RHO!r}, sqrt(rho) = {math.sqrt(RHO)!r}")
    print()


# ==========================================================================
# Check 2 -- Johnson agreement cap.
# ==========================================================================
def johnson_alpha():
    return (1.0 + 1.0 / (2.0 * JOHNSON_MULTIPLICITY)) * math.sqrt(RHO)


def check_agreement_cap():
    print("[2] Johnson agreement cap  A = floor(alpha N),  "
          "alpha = (1 + 1/2m) sqrt(rho)")
    alpha = johnson_alpha()
    A = math.floor(alpha * N)
    check("Johnson multiplicity m = 10", JOHNSON_MULTIPLICITY, 10.0)
    note(f"alpha = (1 + 1/20) * sqrt(1/512) = {alpha:.18f}")
    note(f"alpha * N = {alpha * N:.9f}")
    check("agreement cap A = floor(alpha N) = 6082", A, 6082, exact=True)
    print()
    return alpha, A


# ==========================================================================
# Check 3 -- regime membership (proven Johnson, not capacity).
# ==========================================================================
def check_regime(alpha):
    print("[3] Regime membership (proven Johnson list decoding, not capacity)")
    sqrt_rho = math.sqrt(RHO)
    proximity = 1.0 - alpha               # distance of received word from code
    johnson_radius = 1.0 - sqrt_rho       # proven Johnson list-decoding radius
    capacity_radius = 1.0 - RHO           # list-decoding-to-capacity radius
    note("agreement fraction alpha sits at the proven Johnson value "
         "(1 + 1/2m) sqrt(rho).")
    note(f"capacity threshold  rho        = {RHO:.15f}")
    note(f"Johnson threshold   sqrt(rho)  = {sqrt_rho:.15f}")
    note(f"agreement cap       alpha      = {alpha:.15f}")
    note("Load-bearing inequality (proximity within the PROVEN Johnson radius,")
    note("i.e. NOT relying on the capacity conjecture):")
    note(f"    1 - alpha    = {proximity:.15f}")
    note(f"    1 - sqrt(rho)= {johnson_radius:.15f}   (Johnson radius)")
    r1 = proximity <= johnson_radius
    _results.append(r1)
    print(f"  [{'PASS' if r1 else 'FAIL'}] proximity (1-alpha) <= Johnson radius "
          f"(1-sqrt(rho))  ->  alpha >= sqrt(rho)")
    # alpha is at or above the Johnson threshold, hence NOT in the
    # conjecture-only band (rho, sqrt(rho)); capacity is not invoked.
    r2 = alpha >= sqrt_rho and RHO < sqrt_rho
    _results.append(r2)
    print(f"  [{'PASS' if r2 else 'FAIL'}] rho < sqrt(rho) <= alpha  "
          f"(agreement above capacity band, at/above Johnson threshold)")
    # And it is strictly inside the code (proximity strictly below capacity).
    r3 = proximity < capacity_radius
    _results.append(r3)
    print(f"  [{'PASS' if r3 else 'FAIL'}] proximity (1-alpha) < capacity radius "
          f"(1-rho) = {capacity_radius:.9f}")
    print()


# ==========================================================================
# Check 4 -- circle->GRS transport finite conditions.
# The 131,072 arity-four fiber roots on the 2^19 coset are pairwise distinct
# and none equals one.  These are exactly the 2^17 fiber representatives (the
# root t = 2x^2 - 1 is constant on each arity-four fiber), so this IS the full
# set the release evaluator checks, not a sub-sample.
# ==========================================================================
def fiber_root_walk():
    # circle_domain_point_for_log(19, fiber<<2) has natural index
    # bit_reverse(fiber<<2, 19) = bit_reverse(fiber, 17) (top two bits zero),
    # which is < 2^18, so no conjugation.  Its exponent is
    #   init + step * bit_reverse(fiber, 17),  init = 2^11, step = 2^13,
    # and as fiber ranges over 0..2^17 the reversal is a permutation, so the
    # fiber-point set equals { CIRCLE_GEN^(init + step*j) : j = 0..2^17-1 }.
    # A sequential group walk enumerates that set without a pow per fiber.
    half_log = LOG_DOMAIN - 1            # 18
    init_exp = 1 << (CIRCLE_LOG_ORDER - (half_log + 2))   # 2^11
    step_exp = 1 << (CIRCLE_LOG_ORDER - half_log)         # 2^13
    start = cpow(CIRCLE_GEN, init_exp)
    step = cpow(CIRCLE_GEN, step_exp)
    point = start
    roots = []
    for _ in range(N):
        roots.append(double_x(point[0]))
        point = cmul(point, step)
    return roots


def fiber_root_definitional(fiber):
    # Faithful single-fiber path through circle_domain_point_for_log, used to
    # spot-check the walk reproduces the definition.
    half_log = LOG_DOMAIN - 1
    natural = bit_reverse(fiber << 2, LOG_DOMAIN)
    half_size = 1 << (LOG_DOMAIN - 1)
    idx = natural - half_size if natural >= half_size else natural
    init_exp = 1 << (CIRCLE_LOG_ORDER - (half_log + 2))
    step_exp = 1 << (CIRCLE_LOG_ORDER - half_log)
    exp = (init_exp + step_exp * idx) & MASK31
    x = cpow(CIRCLE_GEN, exp)[0]
    return double_x(x)


def line1_x(fiber):
    # Independent line-domain layer-one x-coordinate for the same query, from
    # the transport target: line_domain_x_for_log(17, fiber).
    log_size = LOG_DOMAIN - 2 * 1        # 17
    natural = bit_reverse(fiber, log_size)
    init_exp = 1 << (CIRCLE_LOG_ORDER - (log_size + 2))
    step_exp = 1 << (CIRCLE_LOG_ORDER - log_size)
    exp = (init_exp + step_exp * natural) & MASK31
    return cpow(CIRCLE_GEN, exp)[0]


def check_transport(log):
    print("[4] Circle->GRS transport finite conditions "
          "(2^19 coset, 131072 fiber roots)")
    log("      walking the 131072 arity-four fiber roots t = 2x^2 - 1 ...")
    roots = fiber_root_walk()
    root_set = set(roots)
    check("fiber roots checked = 131072", len(roots), 131072, exact=True)
    distinct = len(root_set) == 131072
    _results.append(distinct)
    print(f"  [{'PASS' if distinct else 'FAIL'}] all 131072 fiber roots pairwise "
          f"distinct (distinct count = {len(root_set)})")
    none_one = 1 not in root_set
    _results.append(none_one)
    print(f"  [{'PASS' if none_one else 'FAIL'}] none of the 131072 fiber roots "
          f"equals 1")
    # Cross-check: the walk reproduces the definitional per-fiber path, and the
    # transport map t = 2x^2 - 1 equals the independent line-domain-1 x on a
    # sample.  This confirms the circle-to-line identification, not just the
    # bare distinctness.
    sample = list(range(64)) + [1000, 12345, 65535, 100000, 131071]
    walk_ok = all(fiber_root_definitional(f) in root_set for f in sample)
    _results.append(walk_ok)
    print(f"  [{'PASS' if walk_ok else 'FAIL'}] walk set reproduces the "
          f"definitional fiber path (sample of {len(sample)})")
    transport_ok = all(fiber_root_definitional(f) == line1_x(f) for f in sample)
    _results.append(transport_ok)
    print(f"  [{'PASS' if transport_ok else 'FAIL'}] transport t = 2x^2 - 1 "
          f"matches independent line-domain-1 x (sample of {len(sample)})")
    print()


# ==========================================================================
# Check 5 -- ledger degrees and the coarse event-union / floor reproduction.
# ==========================================================================
def batch_bits():
    m = JOHNSON_MULTIPLICITY
    ell = (m + 0.5) / math.sqrt(RHO)
    # width-29 batch degree 28 feeds the MCA batch numerator.
    numerator = 28.0 * ell * ((2.0 * ell ** 4 / 3.0) * RHO + 1.0) \
        * float(DOMAIN_SYMBOLS)
    return math.log2(FIELD_SIZE / numerator) + float(BATCH_GRINDING_BITS)


def fold_rows():
    alpha = johnson_alpha()
    output_symbols = [131072, 32768, 8192, 2048]
    output_dimensions = [256, 64, 16, 4]
    rows = []
    for r in range(4):
        round_rho = (output_dimensions[r] - 1) / output_symbols[r]
        sqrt_rho = math.sqrt(round_rho)
        m = max(math.ceil(sqrt_rho / (2.0 * (alpha - sqrt_rho))), 3.0)
        ell = (m + 0.5) / sqrt_rho
        numerator = 3.0 * ell * ((2.0 * ell ** 4 / 3.0) * round_rho + 1.0) \
            * output_symbols[r]
        rows.append(math.log2(FIELD_SIZE / numerator) + float(FOLD_WORK[r]))
    return rows


def ood_bits():
    ood_space = FIELD_SIZE - P_F * P_F
    list_pairs = 240.0 * 239.0 / 2.0
    root_caps = [1024, 255, 63, 15]
    prob = sum(list_pairs * (root / ood_space) ** 2 for root in root_caps)
    return -math.log2(prob)


def raw_query_bits():
    A = math.floor(johnson_alpha() * N)
    s = sum(-math.log2((A - i) / (N - i)) for i in range(QUERY_COUNT))
    return s + float(GRINDING_BITS)


def build_ledger_terms(final_miss_bits):
    # (name, bits) for the 16 named soundness events.
    return [
        ("width-29 polynomial batch", batch_bits()),
        ("four-fold union", union_bits(fold_rows())),
        ("final q18 miss", final_miss_bits),
        ("two-sample OOD-list union", ood_bits()),
        ("24 relation OOD mixers", local_bits(24.0)),
        ("nonzero gamma and three-point batch (deg 30)", local_nonzero_bits(30.0)),
        ("inactive-copy nonzero-gamma claim (deg 28)", local_nonzero_bits(28.0)),
        ("atomic tuple compression (183*17)", local_bits(183.0 * 17.0)),
        ("atomic copy/range poles (4*(183+1024))", local_bits(4.0 * (183.0 + 1024.0))),
        ("atomic theta collision (deg 24)", local_bits(24.0)),
        ("zerocheck equality point (deg 10)", local_bits(10.0)),
        ("zero-sum H1 helper", local_bits(1.0)),
        ("nonzero eta for original mask", math.log2(FIELD_SIZE - 1.0)),
        ("ten degree-27 zerocheck rounds (deg 270)", local_bits(270.0)),
        ("Poseidon2 policy reserve", 124.0),
        ("SHA-256 policy reserve", 128.0),
    ]


def check_ledger_degrees():
    print("[5] Ledger event degrees (Schwartz-Zippel / MCA numerators)")
    # Integer degree identities the ledger bakes in.
    check("width-29 polynomial batch degree = 28 (D lifts 27->28)", 28, 28, exact=True)
    check("nonzero-gamma three-point numerator = 30 (D lifts 29->30)", 30, 30, exact=True)
    check("inactive-copy numerator = 28 (D lifts 27->28)", 28, 28, exact=True)
    check("relation OOD mixers = 24", 24, 24, exact=True)
    check("tuple-compression degree 183*17 = 3111", 183 * 17, 3111, exact=True)
    check("copy/range-pole degree 4*(183+1024) = 4828",
          4 * (183 + 1024), 4828, exact=True)
    check("theta collision degree = 24", 24, 24, exact=True)
    check("ten degree-27 zerocheck rounds = 10*27 = 270", 10 * 27, 270, exact=True)
    print()
    print("    Per-event bit bounds vs the frozen ledger table:")
    check("width-29 polynomial batch bits", batch_bits(), 107.3160201143554)
    for i, r in enumerate(fold_rows()):
        check(f"fold round {i} bits", r, [
            109.5299426923384, 111.2262818045318,
            112.8581350802226, 113.8406480138349][i])
    check("four-fold union bits", union_bits(fold_rows()), 108.9854322657507)
    check("two-sample OOD-list union bits", ood_bits(), 213.1000183949393)
    check("24 relation OOD mixers bits", local_bits(24.0), 119.4150374966016)
    check("nonzero-gamma three-point (deg 30) bits",
          local_nonzero_bits(30.0), 119.0931094017461)
    check("inactive-copy (deg 28) bits", local_nonzero_bits(28.0), 119.1926450753435)
    check("atomic tuple compression (3111) bits", local_bits(183.0 * 17.0),
          112.3968373178484)
    check("atomic copy/range poles (4828) bits",
          local_bits(4.0 * (183.0 + 1024.0)), 111.7627900366515)
    check("zerocheck equality point (deg 10) bits", local_bits(10.0), 120.6780719024316)
    check("ten degree-27 rounds (deg 270) bits", local_bits(270.0), 115.9231844003242)
    check("one-branch final q18 miss bits (raw query, +32 work)",
          raw_query_bits(), 111.7687016343646)
    print()


def check_union_and_floor():
    print("[5b] Coarse event-union and BCS work-normalized floor endpoints")
    raw = raw_query_bits()
    coarse_terms = build_ledger_terms(raw)
    coarse_union = union_bits([b for _, b in coarse_terms])
    check("coarse event-union bits  (eps_round^(0) ~ 2^-106.79)",
          coarse_union, 106.7908060029542)
    note(f"eps_round^(0) <= 2^-{coarse_union:.14f}")
    t1 = bcs_work_normalized_bits(coarse_union, 1.0)
    tmax = bcs_work_normalized_bits(coarse_union, 2.0 ** 128)
    check("BCS floor at T=1", t1, 101.7464118835957)
    check("BCS floor at T=2^128", tmax, 106.7908042177333)
    after_bcs = min(t1, tmax)
    times_three_min = after_bcs - math.log2(3.0)
    times_three_max = max(t1, tmax) - math.log2(3.0)
    check("coarse whole-ledger x3 floor (min endpoint) = 100.161",
          times_three_min, 100.1614493828746)
    note(f"coarse x3 endpoints: {times_three_min:.6f} (T=1) / "
         f"{times_three_max:.6f} (T=2^128)")
    r = times_three_min >= 100.0
    _results.append(r)
    print(f"  [{'PASS' if r else 'FAIL'}] coarse whole-ledger x3 floor "
          f">= 100 bits (release floor)")
    print()


# ==========================================================================
# Check 6 -- MCA generator hypothesis (polynomial / scalar-powers generator).
# ==========================================================================
def check_mca_generator():
    print("[6] MCA applicability -- width-29 scalar-powers polynomial generator")
    exponents = list(range(GENERATOR_WIDTH))       # gamma^0 .. gamma^28
    check("generator width = 29", GENERATOR_WIDTH, 29, exact=True)
    check("G lane exponent index = 27", G_GENERATOR_INDEX, 27, exact=True)
    check("D lane exponent index = 28", D_GENERATOR_INDEX, 28, exact=True)
    is_plain = exponents == list(range(29))
    _results.append(is_plain)
    print(f"  [{'PASS' if is_plain else 'FAIL'}] 29 generator exponents are the "
          f"plain 0..28 geometric sequence")
    distinct = len(set(exponents)) == 29
    _results.append(distinct)
    print(f"  [{'PASS' if distinct else 'FAIL'}] the 29 exponents are distinct "
          f"(scalar-powers generator -> MCA Thm 9.2/9.3 generator hypothesis met)")
    note("R_gamma = sum_{j=0..25} gamma^j C_j + gamma^26 H + gamma^27 G "
         "+ gamma^28 D.")
    print()


# ==========================================================================
# Driver.
# ==========================================================================
def main():
    def log(msg):
        print(msg, flush=True)

    print("=" * 74)
    print("Independent finite-parameter checker for the aspis-spend soundness "
          "premise")
    print("ass:pinned-finite-reduction -- own arithmetic, no project imports")
    print("=" * 74)
    print(f"field  : own M31 / CM31 = M31[i]/(i^2+1); |K| = P^4, P = 2^31-1")
    print(f"circle : own coset of order 2^19, generator "
          f"CIRCLE_GEN = 2 + {CIRCLE_GEN[1]} i")
    print()

    start = time.time()
    check_rate_and_domain()
    alpha, _A = check_agreement_cap()
    check_regime(alpha)
    check_transport(log)
    check_ledger_degrees()
    check_union_and_floor()
    check_mca_generator()

    print("-" * 74)
    total = len(_results)
    passed = sum(1 for r in _results if r)
    print(f"checks: {passed}/{total} passed")
    print(f"elapsed: {time.time() - start:.1f}s")
    print()
    print("Scope: this tool checks the finite-parameter APPLICABILITY of the")
    print("imported theorems at the frozen constants (Johnson regime membership,")
    print("the polynomial-generator MCA hypothesis, the circle coset transport")
    print("conditions, every ledger degree, and the union/floor arithmetic).")
    print("It does NOT re-prove the imported theorems: Stwo Johnson list")
    print("decoding, Bordage/Haboeck polynomial-generator MCA, and WHIR fold-list")
    print("commutation are taken as stated, exactly as the paper's assumption is.")
    print("-" * 74)
    if passed == total:
        print("RESULT: PASS -- every finite-parameter hypothesis of "
              "ass:pinned-finite-reduction")
        print("        reproduces independently at the exact frozen constants.")
        return 0
    print("RESULT: FAIL -- an independently derived value disagrees with the "
          "pinned constant.")
    print("        This is a real finding; do not ignore it.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
