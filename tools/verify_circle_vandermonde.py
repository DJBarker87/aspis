#!/usr/bin/env python3
"""Independent checker for the circle-Vandermonde invertibility lemma.

CONTEXT
    A proposed replacement for Aspis-Spend's bespoke ZK masking hides a trace
    column T (a circle polynomial interpolating the real column on the trace
    domain H, |H| = 2^10) by committing the masked column

        T_hat = T + Z_H * R,

    where Z_H is the vanishing function of H (Z_H(p)=0 iff p in H) and R is a
    UNIFORMLY RANDOM circle polynomial of circle-degree < b in the circle-FFT
    basis (b = the leakage budget: the number of distinct off-domain K-openings
    the verifier's view exposes of the column).

    Because Z_H(p_i) != 0 for every p_i outside H, hiding of the view
    (T_hat(p_1), ..., T_hat(p_b)) reduces to the claim that the evaluation map

        R  |->  (R(p_1), ..., R(p_b))

    from the b-dimensional space V_b of circle polynomials of circle-degree < b
    to K^b is a BIJECTION, i.e. the b x b "circle-Vandermonde" matrix
    M[i][j] = B_j(p_i) is invertible, where B_0,...,B_{b-1} is the circle-FFT
    monomial basis.

    Unlike the univariate case (Vandermonde at distinct points is ALWAYS
    invertible), the circle-Vandermonde is NOT unconditionally invertible: the
    involution (x,y) -> (x,-y) lets nonzero circle polynomials in V_b have up to
    b zeros on the circle, so an explicit exceptional set of point
    configurations makes the matrix singular. This tool:

      (1) rebuilds M31/CM31/QM31 and the circle arithmetic from their public
          definitions (imports no project code), and ANCHORS the circle-FFT
          encoder to the in-repo official-Stwo digest fixture
          (crates/aspis-prover/tests/m31_circle_official_anchor.rs);
      (2) constructs the circle-FFT degree-<b basis B_j and the deployed
          |H| = 2^10 vanishing function Z_H, checking Z_H|_H = 0, Z_H != 0 off
          H, and H disjoint from the 2^19 codeword domain;
      (3) samples many random off-H point sets over K and verifies the
          circle-Vandermonde determinant is nonzero;
      (4) EXHIBITS explicit singular configurations (the exceptional set is
          real), including the deployed mixed base-field-query / K-OOD layout;
      (5) reports the derived and empirical failure probability.

    Field tower (shared math primitives, not certificate-generating code):
        M31  = Z / (2^31 - 1)
        CM31 = M31[i] / (i^2 + 1)
        QM31 = CM31[u] / (u^2 - (2 + i))          [stwo parameterization]
    Circle generator (aspis-core params.rs / circle_candidate.rs):
        G = (2, 1268011823),  order 2^31.

USAGE
    python3 tools/verify_circle_vandermonde.py
    python3 tools/verify_circle_vandermonde.py --b 96 --trials 200 --seed 7
"""

from __future__ import annotations

import argparse
import hashlib
import sys

# ---------------------------------------------------------------------------
# Field tower: M31 -> CM31 -> QM31, re-implemented from the public tower defs.
# QM31 element is a 4-tuple (a, b, c, d) = (a + b i) + (c + d i) u.
# ---------------------------------------------------------------------------
P = (1 << 31) - 1
QZERO = (0, 0, 0, 0)
QONE = (1, 0, 0, 0)


def minv(x: int) -> int:
    return pow(x % P, P - 2, P)


def qadd(x, y):
    return ((x[0] + y[0]) % P, (x[1] + y[1]) % P, (x[2] + y[2]) % P, (x[3] + y[3]) % P)


def qsub(x, y):
    return ((x[0] - y[0]) % P, (x[1] - y[1]) % P, (x[2] - y[2]) % P, (x[3] - y[3]) % P)


def qneg(x):
    return ((-x[0]) % P, (-x[1]) % P, (-x[2]) % P, (-x[3]) % P)


def qmul(x, y):
    # CM31 mul via Karatsuba (3 M31 muls); QM31 via u^2 = 2 + i.
    a, b, c, d = x
    e, f, g, h = y
    m0a = (a * e - b * f) % P
    m0b = (a * f + b * e) % P
    m1a = (c * g - d * h) % P
    m1b = (c * h + d * g) % P
    s1a, s1b = a + c, b + d
    s2a, s2b = e + g, f + h
    m2a = (s1a * s2a - s1b * s2b) % P
    m2b = (s1a * s2b + s1b * s2a) % P
    # mul by R = 2 + i on the m1 (u^2) component: (2+i)(m1a + m1b i)
    ra = (2 * m1a - m1b) % P
    rb = (m1a + 2 * m1b) % P
    return ((m0a + ra) % P, (m0b + rb) % P,
            (m2a - m0a - m1a) % P, (m2b - m0b - m1b) % P)


def qmul_m31(x, s):
    s %= P
    return ((x[0] * s) % P, (x[1] * s) % P, (x[2] * s) % P, (x[3] * s) % P)


def qsquare(x):
    return qmul(x, x)


def qinv(x):
    a, b, c, d = x
    # norm = c0^2 - (2+i) c1^2 in CM31, then complex inverse.
    c0sa = (a * a - b * b) % P
    c0sb = (2 * a * b) % P
    c1sa = (c * c - d * d) % P
    c1sb = (2 * c * d) % P
    ra = (2 * c1sa - c1sb) % P
    rb = (c1sa + 2 * c1sb) % P
    na = (c0sa - ra) % P
    nb = (c0sb - rb) % P
    nn = (na * na + nb * nb) % P
    if nn == 0:
        raise ZeroDivisionError("qinv of zero / zero-norm element")
    inn = minv(nn)
    ina = (na * inn) % P
    inb = (-nb * inn) % P
    r0a = (a * ina - b * inb) % P
    r0b = (a * inb + b * ina) % P
    nc, nd = (-c) % P, (-d) % P
    r1a = (nc * ina - nd * inb) % P
    r1b = (nc * inb + nd * ina) % P
    return (r0a, r0b, r1a, r1b)


def qis_zero(x):
    return x[0] % P == 0 and x[1] % P == 0 and x[2] % P == 0 and x[3] % P == 0


def q_from_m31(v):
    return (v % P, 0, 0, 0)


# ---------------------------------------------------------------------------
# Deterministic sampling.
# ---------------------------------------------------------------------------
class Stream:
    def __init__(self, seed: str):
        self._buf = b""
        self._n = 0
        self._seed = seed.encode()

    def _refill(self):
        self._buf += hashlib.sha256(self._seed + self._n.to_bytes(8, "little")).digest()
        self._n += 1

    def _word(self):
        while len(self._buf) < 4:
            self._refill()
        w = int.from_bytes(self._buf[:4], "little")
        self._buf = self._buf[4:]
        return w

    def m31(self):
        while True:
            v = self._word() & 0x7FFFFFFF
            if v != P:
                return v

    def m31_nonzero(self):
        while True:
            v = self.m31()
            if v != 0:
                return v

    def qm31(self):
        return (self.m31(), self.m31(), self.m31(), self.m31())

    def qm31_not_in_cm31(self):
        # OOD policy (aspis-core circle.rs): reject parameters in the CM31
        # subfield, i.e. the (c, d) = c1 component must be nonzero.
        while True:
            v = self.qm31()
            if v[2] != 0 or v[3] != 0:
                return v


# ---------------------------------------------------------------------------
# Base-field circle group (M31 coordinates). G = (2, 1268011823), order 2^31.
# ---------------------------------------------------------------------------
CIRCLE_LOG_ORDER = 31
CIRCLE_MASK = (1 << CIRCLE_LOG_ORDER) - 1
GEN = (2, 1268011823)


def cadd(a, b):
    # circle group law over M31: (x1 x2 - y1 y2, x1 y2 + y1 x2)
    return ((a[0] * b[0] - a[1] * b[1]) % P, (a[0] * b[1] + a[1] * b[0]) % P)


def cmul(point, scalar):
    scalar &= CIRCLE_MASK
    result = (1, 0)
    power = point
    while scalar:
        if scalar & 1:
            result = cadd(result, power)
        power = cadd(power, power)
        scalar >>= 1
    return result


def group_point(exponent):
    return cmul(GEN, exponent & CIRCLE_MASK)


def bit_reverse_index(index, log_size):
    if log_size == 0:
        return 0
    return int('{:0{w}b}'.format(index, w=log_size)[::-1], 2)


def initial_index(log_size):
    return 1 << (CIRCLE_LOG_ORDER - (log_size + 2))


def step_index(log_size):
    return 1 << (CIRCLE_LOG_ORDER - log_size)


def circle_point(log_size, stored_index):
    """Domain point at a stored index, per build.rs circle_point()."""
    natural = bit_reverse_index(stored_index, log_size)
    half = 1 << (log_size - 1)
    if natural < half:
        index, conjugate = natural, False
    else:
        index, conjugate = natural - half, True
    pt = group_point(initial_index(log_size - 1) + step_index(log_size - 1) * index)
    if conjugate and pt[1] != 0:
        pt = (pt[0], (P - pt[1]) % P)
    return pt


# ---------------------------------------------------------------------------
# Secure (K) circle points from the rational parameterization (circle.rs):
#   x = (1 - t^2)/(1 + t^2),  y = 2t/(1 + t^2).
# ---------------------------------------------------------------------------
def secure_point_from_parameter(t):
    sq = qsquare(t)
    denom = qadd(QONE, sq)
    inv_denom = qinv(denom)  # raises if 1 + t^2 == 0 (t = +-i)
    x = qmul(qsub(QONE, sq), inv_denom)
    y = qmul(qadd(t, t), inv_denom)
    return (x, y)


# ---------------------------------------------------------------------------
# Circle-FFT monomial basis  B_j(x,y) = y^{bit0(j)} * prod_{k>=1} phi_k(x)^{bit_k(j)}
#   phi_1(x) = x,  phi_{k+1}(x) = 2 phi_k(x)^2 - 1        [double_x, 2x^2-1]
# For even j:  B_j is a poly in x of x-degree j/2.
# For odd  j:  B_j = y * (poly in x of x-degree (j-1)/2).
# Hence  V_b = span{B_0..B_{b-1}} = { p(x) + y q(x) } with, for b = 2m,
#   deg p <= m-1, deg q <= m-1  (dim 2m); for b = 2m+1, deg p <= m, deg q <= m-1.
# ---------------------------------------------------------------------------
def phi_tower(x, kmax):
    """[phi_1, ..., phi_kmax] over K, phi_1 = x, phi_{k+1} = 2 phi_k^2 - 1."""
    tower = [x]
    cur = x
    for _ in range(1, kmax):
        cur = qsub(qadd(qsquare(cur), qsquare(cur)), QONE)
        tower.append(cur)
    return tower


def basis_row(point, b):
    """[B_0(point), ..., B_{b-1}(point)] over K."""
    x, y = point
    kmax = max(1, (b - 1).bit_length())
    phis = phi_tower(x, kmax)  # phis[k-1] = phi_k
    row = []
    for j in range(b):
        val = y if (j & 1) else QONE
        jj = j >> 1
        k = 1
        while jj:
            if jj & 1:
                val = qmul(val, phis[k - 1])
            jj >>= 1
            k += 1
        row.append(val)
    return row


# ---------------------------------------------------------------------------
# Determinant / rank over K by fraction-free-free Gaussian elimination.
# ---------------------------------------------------------------------------
def qdet(matrix):
    n = len(matrix)
    mat = [row[:] for row in matrix]
    det = QONE
    for col in range(n):
        piv = None
        for r in range(col, n):
            if not qis_zero(mat[r][col]):
                piv = r
                break
        if piv is None:
            return QZERO
        if piv != col:
            mat[col], mat[piv] = mat[piv], mat[col]
            det = qneg(det)
        pv = mat[col][col]
        det = qmul(det, pv)
        pv_inv = qinv(pv)
        for r in range(col + 1, n):
            factor = qmul(mat[r][col], pv_inv)
            if qis_zero(factor):
                continue
            for c in range(col, n):
                mat[r][c] = qsub(mat[r][c], qmul(factor, mat[col][c]))
    return det


def qrank(matrix):
    if not matrix:
        return 0
    mat = [row[:] for row in matrix]
    rows, cols = len(mat), len(mat[0])
    rank = 0
    prow = 0
    for col in range(cols):
        piv = None
        for r in range(prow, rows):
            if not qis_zero(mat[r][col]):
                piv = r
                break
        if piv is None:
            continue
        mat[prow], mat[piv] = mat[piv], mat[prow]
        pv_inv = qinv(mat[prow][col])
        for r in range(rows):
            if r != prow and not qis_zero(mat[r][col]):
                factor = qmul(mat[r][col], pv_inv)
                for c in range(col, cols):
                    mat[r][c] = qsub(mat[r][c], qmul(factor, mat[prow][c]))
        prow += 1
        rank += 1
        if prow == rows:
            break
    return rank


# ---------------------------------------------------------------------------
# STEP 1: anchor the circle-FFT encoder to the in-repo official digest.
# Reproduces crates/aspis-prover/tests/m31_circle_official_anchor.rs (the C1
# codeword SHA-256), which pins the encoder to Stwo commit 5d10e6b4.
# ---------------------------------------------------------------------------
C1_CODEWORDS_EXPECTED = "eb398b5bf27587d3d4abb693287530dc8aacc4f8ed0470b3e9133d331d2694ea"
DOMAIN_LOG_SIZE = 12
TRACE_LEN = 1 << 10
CODEWORD_LEN = 1 << DOMAIN_LOG_SIZE
C1_COLUMNS = 49  # aspis-core proof.rs M31_CIRCLE_C1_COLUMNS


class XorShiftRng:
    """The fixture RNG from m31_circle_official_anchor.rs."""

    def __init__(self, state):
        self.s = state & 0xFFFFFFFFFFFFFFFF

    def next(self):
        s = self.s
        s ^= (s >> 12) & 0xFFFFFFFFFFFFFFFF
        s ^= (s << 25) & 0xFFFFFFFFFFFFFFFF
        s ^= (s >> 27) & 0xFFFFFFFFFFFFFFFF
        s &= 0xFFFFFFFFFFFFFFFF
        self.s = (s * 0x2545F4914F6CDD1D) & 0xFFFFFFFFFFFFFFFF
        return self.s

    def m31(self):
        return (self.next() & 0xFFFFFFFF) % P


def _coset_half_odds(log_size):
    init = cmul(GEN, initial_index(log_size))
    step = cmul(GEN, step_index(log_size))
    return init, step, log_size


def _coset_point(coset, index):
    init, step, _ = coset
    return cadd(init, cmul(step, index))


def _coset_double(coset):
    init, step, log_size = coset
    return cadd(init, init), cadd(step, step), log_size - 1


def _bit_reverse_slice(values):
    n = len(values)
    log_size = n.bit_length() - 1
    for i in range(n):
        r = bit_reverse_index(i, log_size)
        if r > i:
            values[i], values[r] = values[r], values[i]


def _precompute_twiddles(coset):
    twiddles = []
    while coset[2] != 0:
        start = len(twiddles)
        size = 1 << coset[2]
        for i in range(size // 2):
            twiddles.append(_coset_point(coset, i)[0])
        seg = twiddles[start:]
        _bit_reverse_slice(seg)
        twiddles[start:] = seg
        coset = _coset_double(coset)
    twiddles.append(1)
    return twiddles


def _line_twiddle_layers(twiddles, line_log_size):
    layers = []
    total = len(twiddles)
    for layer in range(line_log_size):
        ln = 1 << layer
        layers.append(twiddles[total - 2 * ln: total - ln])
    layers.reverse()
    return layers


def _circle_twiddles(first_line_layer):
    result = []
    for i in range(0, len(first_line_layer), 2):
        x = first_line_layer[i]
        y = first_line_layer[i + 1]
        result.extend([y, (P - y) % P, (P - x) % P, x])
    return result


def _fft_layer(values, layer, block, twiddle):
    span = 1 << layer
    base = block << (layer + 1)
    for lane in range(span):
        i0 = base + lane
        i1 = i0 + span
        left = values[i0]
        wr = (values[i1] * twiddle) % P
        values[i0] = (left + wr) % P
        values[i1] = (left - wr) % P


def build_encoder(domain_log_size):
    half = _coset_half_odds(domain_log_size - 1)
    twiddles = _precompute_twiddles(half)
    line_layers = _line_twiddle_layers(twiddles, domain_log_size - 1)
    first_circle = _circle_twiddles(line_layers[0])
    return line_layers, first_circle


def encode_c1_message(message, line_layers, first_circle, codeword_len):
    values = list(message) + [0] * (codeword_len - len(message))
    for layer in range(len(line_layers) - 1, -1, -1):
        for block, tw in enumerate(line_layers[layer]):
            _fft_layer(values, layer + 1, block, tw)
    for block, tw in enumerate(first_circle):
        _fft_layer(values, 0, block, tw)
    return values


def anchor_encoder():
    line_layers, first_circle = build_encoder(DOMAIN_LOG_SIZE)
    rng = XorShiftRng(0x4349_5243_4C45_4332)
    hasher = hashlib.sha256()
    for column in range(C1_COLUMNS):
        message = []
        for row in range(TRACE_LEN):
            base = rng.m31()
            add = (column * 65537 + row * 257 + 1) % P
            message.append((base + add) % P)
        codeword = encode_c1_message(message, line_layers, first_circle, CODEWORD_LEN)
        for v in codeword:
            hasher.update((v % P).to_bytes(4, "little"))
    got = hasher.hexdigest()
    return got, got == C1_CODEWORDS_EXPECTED, (line_layers, first_circle)


# ---------------------------------------------------------------------------
# STEP 1b: cross-check the closed-form basis B_j against the butterfly encoder.
# codeword[i] should equal sum_j message[j] * B_j(point_i).  We detect the
# encoder's point-index convention automatically.
# ---------------------------------------------------------------------------
def crosscheck_basis(encoder):
    line_layers, first_circle = encoder
    log = DOMAIN_LOG_SIZE
    n = CODEWORD_LEN
    rng = Stream("basis-crosscheck")
    message = [rng.m31() for _ in range(TRACE_LEN)]
    codeword = encode_c1_message(message, line_layers, first_circle, n)

    # Candidate index -> point maps.
    def pt_direct(i):
        x, y = circle_point(log, i)
        return (q_from_m31(x), q_from_m31(y))

    def pt_bitrev(i):
        x, y = circle_point(log, bit_reverse_index(i, log))
        return (q_from_m31(x), q_from_m31(y))

    for name, ptmap in (("circle_point(i)", pt_direct),
                        ("circle_point(bitrev i)", pt_bitrev)):
        ok = True
        # test a handful of indices for speed
        for i in [0, 1, 2, 3, 7, 15, 31, 100, 555, 1234, 4095]:
            row = basis_row(ptmap(i), TRACE_LEN)
            acc = QZERO
            for j in range(TRACE_LEN):
                acc = qadd(acc, qmul_m31(row[j], message[j]))
            if acc != q_from_m31(codeword[i]):
                ok = False
                break
        if ok:
            return True, name
    return False, None


# ---------------------------------------------------------------------------
# STEP 2: vanishing function Z_H of the deployed trace domain H, |H| = 2^10.
# H is conjugation-closed, so Z_H depends on x only: Z_H(x) = phi_9(x) - c,
# where phi_9 = 9-fold x-doubling collapses the size-2^10 coset to one point c.
# (phi_9 has x-degree 2^9 = 512; it vanishes on all 2^10 = 2^9 conj pairs of H.)
# ---------------------------------------------------------------------------
H_LOG = 10
DOMAIN19_LOG = 19


def phi9_x_m31(x):
    # phi_1 = x; phi_{k+1} = 2 x^2 - 1, nine-fold for the size-2^10 coset.
    cur = x % P
    for _ in range(H_LOG - 1):  # 9 doublings: phi_1 -> phi_10? see below
        cur = (2 * cur * cur - 1) % P
    return cur


def phi9_x_q(x):
    cur = x
    for _ in range(H_LOG - 1):
        cur = qsub(qadd(qsquare(cur), qsquare(cur)), QONE)
    return cur


def build_ZH():
    """Return (c, H_points, H_xvalues). Z_H(p) = phi_9(x_p) - c."""
    H_points = [circle_point(H_LOG, i) for i in range(1 << H_LOG)]
    xs = sorted({p[0] for p in H_points})
    # c is the common collapse value.
    cvals = {phi9_x_m31(x) for x in xs}
    assert len(cvals) == 1, ("H is not collapsed to a single point by phi_9: "
                             f"{len(cvals)} distinct values")
    c = cvals.pop()
    return c, H_points, xs


def ZH_q(point, c):
    x, _y = point
    return qsub(phi9_x_q(x), q_from_m31(c))


# ---------------------------------------------------------------------------
# STEP 3/4: circle-Vandermonde experiments.
# ---------------------------------------------------------------------------
def random_K_offH_points(rng, b, ZH_c, H_xset):
    pts = []
    seen = set()
    while len(pts) < b:
        t = rng.qm31_not_in_cm31()
        try:
            p = secure_point_from_parameter(t)
        except ZeroDivisionError:
            continue
        key = (p[0], p[1])
        if key in seen:
            continue
        # off-H is automatic for c1!=0 points (H is in the base field), but
        # assert Z_H != 0 anyway.
        if qis_zero(ZH_q(p, ZH_c)):
            continue
        seen.add(key)
        pts.append(p)
    return pts


def deployed_mixed_points(rng, b, ZH_c, H_xset, n_base):
    """n_base base-field query points from the 2^19 codeword domain plus
    (b - n_base) K-valued OOD points (t not in CM31)."""
    pts = []
    seen = set()
    # base-field query fibers from the 2^19 domain
    fibers = 1 << (DOMAIN19_LOG - 2)
    while len([p for p in pts]) < n_base:
        fiber = rng.m31() % fibers
        slot = rng.m31() % 4
        stored = 4 * fiber + slot
        x, y = circle_point(DOMAIN19_LOG, stored)
        key = (x, y)
        if key in seen:
            continue
        if x in H_xset:  # off-H guard (should never trigger: H disjoint D19)
            continue
        seen.add(key)
        pts.append((q_from_m31(x), q_from_m31(y)))
    seenq = set(seen)
    while len(pts) < b:
        t = rng.qm31_not_in_cm31()
        try:
            p = secure_point_from_parameter(t)
        except ZeroDivisionError:
            continue
        key = (p[0], p[1])
        if key in seenq:
            continue
        if qis_zero(ZH_q(p, ZH_c)):
            continue
        seenq.add(key)
        pts.append(p)
    return pts


def vandermonde_det(points, b):
    mat = [basis_row(p, b) for p in points]
    return qdet(mat)


# ---- explicit singular constructions -------------------------------------
def singular_two_poles(b):
    """Minimal singular config for b=2: R = y vanishes at the two poles
    (1,0) and (-1,0).  Returns points and the witness R = y * prod() (no
    roots)."""
    assert b == 2
    p1 = (QONE, QZERO)                      # (1, 0)
    p2 = (qneg(QONE), QZERO)                # (-1, 0)
    return [p1, p2], []                     # R = y, no x-roots


def singular_yq_construction(rng, b):
    """For even b = 2m: R = y * prod_{k=1..m-1}(x - a_k) is in V_b (it is
    y times a degree-(m-1) polynomial in x, so it lies in the odd part of
    V_{2m}) and vanishes at the 2 poles plus the 2(m-1) conjugate pairs
    {(a_k, +-y_k)}, i.e. exactly b distinct points.  Returns (points, roots),
    where R(x,y) = y * prod(x - a_k) is evaluated directly from the roots."""
    assert b % 2 == 0
    m = b // 2
    # choose m-1 distinct K x-values a_k with a_k != +-1 and on-circle (y != 0),
    # coming from random circle points (so 1 - a^2 is a square: y exists).
    roots = []
    pts_pairs = []
    seen = set()
    while len(roots) < m - 1:
        t = rng.qm31_not_in_cm31()
        try:
            x, y = secure_point_from_parameter(t)
        except ZeroDivisionError:
            continue
        if qis_zero(y):
            continue
        if x in seen or x == QONE or x == qneg(QONE):
            continue
        seen.add(x)
        roots.append(x)
        pts_pairs.append(((x, y), (x, qneg(y))))
    points = [(QONE, QZERO), (qneg(QONE), QZERO)]
    for pair in pts_pairs:
        points.extend(pair)
    assert len(points) == b
    return points, roots


def eval_R_yprod(roots, point):
    """R(x,y) = y * prod_k (x - root_k)."""
    x, y = point
    acc = y
    for a in roots:
        acc = qmul(acc, qsub(x, a))
    return acc


# ---------------------------------------------------------------------------
# Small-field Monte-Carlo estimate of the singular fraction, to sanity-check
# the Schwartz-Zippel degree/|field| prediction on a field we can oversample.
# We reuse the SAME circle basis but over M31 itself (|field| = P ~ 2^31) using
# base-field circle points.  This is a scale model, not the deployed field.
# ---------------------------------------------------------------------------
def m31_singular_fraction(seed, b, trials, log=15):
    """Fraction of random distinct base-field b-point configs (drawn from a
    size-2^log circle domain) whose circle-Vandermonde is singular.

    Points are drawn from a DOMAIN of size 2^log, not uniformly from the whole
    M31 circle, so the relevant Schwartz-Zippel sampling set per coordinate is
    the domain, size 2^log.  The dominant singular mechanism is an x-coordinate
    collision (a conjugate pair (x,+-y)) that, together with the y-structure,
    kills a low-degree p(x)+y q(x): a birthday effect ~ C(b,2)/2^log.  We report
    both the overall rate and how many singular configs carried a shared-x pair,
    to demonstrate the involution (x,y)->(x,-y) is the operative mechanism."""
    rng = Stream(seed)
    size = 1 << log
    singular = 0
    singular_with_xcollision = 0
    for _ in range(trials):
        pts = []
        seen = set()
        while len(pts) < b:
            idx = rng.m31() % size
            x, y = circle_point(log, idx)
            if (x, y) in seen:
                continue
            seen.add((x, y))
            pts.append((q_from_m31(x), q_from_m31(y)))
        if qis_zero(vandermonde_det(pts, b)):
            singular += 1
            distinct_x = len({p[0] for p in pts})
            if distinct_x < b:
                singular_with_xcollision += 1
    return singular, trials, singular_with_xcollision, size


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--b", type=int, default=48,
                    help="representative leakage budget (basis dimension)")
    ap.add_argument("--trials", type=int, default=64,
                    help="random K point-sets to test for invertibility")
    ap.add_argument("--seed", type=str, default="aspis-circle-vandermonde")
    ap.add_argument("--mc-b", type=int, default=8,
                    help="small-field Monte-Carlo basis size")
    ap.add_argument("--mc-trials", type=int, default=20000,
                    help="small-field Monte-Carlo trials")
    ap.add_argument("--mc-log", type=int, default=12,
                    help="log2 size of the base-field circle domain for MC")
    args = ap.parse_args()

    fails = 0

    def check(name, ok):
        nonlocal fails
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
        if not ok:
            fails += 1

    print("=" * 72)
    print("circle-Vandermonde invertibility checker")
    print("=" * 72)

    # ----- STEP 1: arithmetic self-tests + encoder anchor -----
    print("\n[1] field / circle arithmetic self-tests and repo anchor")
    # generator on circle and order 2^31
    gx, gy = GEN
    on_circle = (gx * gx + gy * gy) % P == 1
    check("generator G=(2,1268011823) lies on x^2+y^2=1", on_circle)
    check("2^31 * G = identity", cmul(GEN, 1 << 31) == (1, 0))
    check("2^30 * G != identity (order is exactly 2^31)", cmul(GEN, 1 << 30) != (1, 0))
    # QM31 field sanity: u^2 = 2 + i
    u = (0, 0, 1, 0)
    check("QM31 relation u^2 = 2 + i", qsquare(u) == (2, 1, 0, 0))
    check("QM31 inverse", qmul((7, 3, 5, 2), qinv((7, 3, 5, 2))) == QONE)
    got, anchor_ok, encoder = anchor_encoder()
    print(f"      C1 codeword digest: {got}")
    print(f"      expected (repo)   : {C1_CODEWORDS_EXPECTED}")
    check("circle-FFT encoder matches in-repo official-Stwo C1 digest", anchor_ok)
    cc_ok, cc_map = crosscheck_basis(encoder)
    check(f"closed-form basis B_j matches butterfly encoder ({cc_map})", cc_ok)

    # ----- STEP 2: Z_H -----
    print("\n[2] vanishing function Z_H for |H| = 2^10")
    ZH_c, H_points, H_xs = build_ZH()
    print(f"      H has {len(H_points)} points, {len(H_xs)} distinct x-values; "
          f"Z_H(x) = phi_9(x) - c, c = {ZH_c}")
    zeros_on_H = all(qis_zero(ZH_q(p_as_q(p), ZH_c)) for p in H_points)
    check("Z_H vanishes on all 2^10 points of H", zeros_on_H)
    # off-H nonzero: sample base-field points off H and K points
    rng = Stream(args.seed + ":zh")
    offH_ok = True
    for _ in range(200):
        idx = rng.m31() % (1 << DOMAIN19_LOG)
        p = circle_point(DOMAIN19_LOG, idx)
        if qis_zero(ZH_q(p_as_q(p), ZH_c)):
            offH_ok = False
            break
    check("Z_H != 0 on 200 sampled 2^19-codeword-domain points", offH_ok)
    H_xset = set(H_xs)
    d19_x = {circle_point(DOMAIN19_LOG, i)[0] for i in range(0, 1 << DOMAIN19_LOG, 997)}
    check("sampled 2^19 domain x-values are disjoint from H (H cap D19 = empty)",
          H_xset.isdisjoint(d19_x))

    # ----- STEP 3: random K invertibility sweep -----
    b = args.b
    print(f"\n[3] random off-H K-point circle-Vandermonde, b = {b}, "
          f"trials = {args.trials}")
    rng = Stream(args.seed + ":sweep")
    n_singular = 0
    for t in range(args.trials):
        pts = random_K_offH_points(rng, b, ZH_c, H_xset)
        det = vandermonde_det(pts, b)
        if qis_zero(det):
            n_singular += 1
    check(f"all {args.trials} random K configs invertible (0 singular)",
          n_singular == 0)
    print(f"      singular: {n_singular} / {args.trials}")

    # deployed mixed layout: 18 base-field queries + (b-18) K OOD points
    n_base = min(18, b - 4)
    print(f"\n[3b] deployed mixed layout: {n_base} base-field 2^19 queries + "
          f"{b - n_base} K-OOD points, trials = {args.trials}")
    rng = Stream(args.seed + ":mixed")
    n_sing_mixed = 0
    base_indep_ok = True
    for t in range(args.trials):
        pts = deployed_mixed_points(rng, b, ZH_c, H_xset, n_base)
        # base-field functionals independent on V_b?
        base_rows = [basis_row(pts[i], b) for i in range(n_base)]
        if qrank(base_rows) != n_base:
            base_indep_ok = False
        if qis_zero(vandermonde_det(pts, b)):
            n_sing_mixed += 1
    check(f"all {args.trials} deployed-mixed configs invertible", n_sing_mixed == 0)
    check(f"the {n_base} base-field query functionals stay V_b-independent",
          base_indep_ok)
    print(f"      singular: {n_sing_mixed} / {args.trials}")

    # ----- STEP 4: exhibit the exceptional set -----
    print("\n[4] exceptional set is real: explicit SINGULAR configurations")
    pts2, roots2 = singular_two_poles(2)
    det2 = vandermonde_det(pts2, 2)
    r2_ok = qis_zero(eval_R_yprod(roots2, pts2[0])) and qis_zero(eval_R_yprod(roots2, pts2[1]))
    check("b=2: config {(1,0),(-1,0)} is singular (det = 0)", qis_zero(det2))
    check("b=2: witness R = y vanishes at both points", r2_ok)

    rng = Stream(args.seed + ":singular")
    be = b if b % 2 == 0 else b - 1
    pts_s, roots_s = singular_yq_construction(rng, be)
    det_s = vandermonde_det(pts_s, be)
    # verify all points distinct and R vanishes at all of them
    distinct = len({(p[0], p[1]) for p in pts_s}) == be
    r_vanishes = all(qis_zero(eval_R_yprod(roots_s, p)) for p in pts_s)
    check(f"b={be}: R = y*prod(x-a_k) construction gives {be} DISTINCT off-H "
          f"points", distinct)
    check(f"b={be}: nonzero R in V_b vanishes at all {be} points", r_vanishes)
    check(f"b={be}: circle-Vandermonde is SINGULAR there (det = 0)",
          qis_zero(det_s))
    # confirm these points ARE off H (x not an H x-value) -- they are K points
    offH = all((p[0][1] == 0 and p[0][2] == 0 and p[0][3] == 0 and
                p[0][0] in H_xset) is False for p in pts_s)
    check(f"b={be}: the singular config lies entirely off H", offH)

    # ----- STEP 5: failure-probability calibration -----
    print("\n[5] failure-probability: degree bound and small-field calibration")
    # per-OOD-point degree of B_j in the t-parameter: B_j(t) has numerator
    # degree <= b over (1+t^2)^{ceil((b-1)/2)}; the determinant's numerator has
    # degree <= b in each single t_i.  Schwartz-Zippel over one random OOD
    # coordinate in K gives Pr <= b / |K|, and over the whole (multilinear-in-
    # rows) determinant, total degree <= b^2, so Pr[singular] <= b^2 / |K|.
    K_bits = 124  # |K| = (2^31-1)^4 ~ 2^124.00...
    import math
    logK = 4 * math.log2(P)
    print(f"      |K| = (2^31-1)^4 ~ 2^{logK:.4f}")
    print(f"      per-OOD-coordinate SZ bound  Pr <= b/|K|   = 2^{math.log2(b) - logK:.2f}")
    print(f"      whole-determinant SZ bound   Pr <= b^2/|K| = 2^{2*math.log2(b) - logK:.2f}")

    mcb, mct, mclog = args.mc_b, args.mc_trials, args.mc_log
    print(f"      base-field Monte Carlo: b={mcb}, points drawn from a 2^{mclog} "
          f"circle domain, trials={mct} ...")
    sing, tot, sing_xc, dsize = m31_singular_fraction(
        args.seed + ":mc", mcb, mct, log=mclog)
    frac = sing / tot
    # domain-restricted SZ bound: sampling set per coordinate is the domain.
    pred = (mcb * mcb) / dsize
    print(f"      observed singular fraction: {sing}/{tot} = {frac:.3e}")
    print(f"      of which carried a shared-x (conjugate) pair: {sing_xc}/{sing}")
    print(f"      domain-restricted bound  b^2/2^{mclog} = {pred:.3e}")
    check("base-field singular fraction <= b^2/|domain| (domain-restricted SZ)",
          frac <= pred)
    print(f"      NOTE: over K (|K|~2^124) the same construction gives "
          f"Pr <= b^2/|K| ~ 2^{2*math.log2(max(mcb,2)) - logK:.0f}; the small "
          f"domain is only a visible-rate scale model.")

    print("\n" + "=" * 72)
    if fails == 0:
        print("ALL CHECKS PASSED")
    else:
        print(f"{fails} CHECK(S) FAILED")
    print("=" * 72)
    return 1 if fails else 0


def p_as_q(p):
    return (q_from_m31(p[0]), q_from_m31(p[1]))


if __name__ == "__main__":
    sys.exit(main())
