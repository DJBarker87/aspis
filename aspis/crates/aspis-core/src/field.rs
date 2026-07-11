//! M31 -> CM31 -> QM31 field tower.
//!
//! Kernel choices are the Phase 2 winners, built in from the start:
//! - M31 reduction: `reference_canonical` (mask/shift double-fold, canonical output)
//! - CM31/QM31 multiplication: Karatsuba (3 submuls per level)
//! - lift policy: `late_lift_qm31` — committed layer-0 values stay CM31 and are
//!   lifted only when they meet a QM31 challenge; mixed-width kernels
//!   (`QM31 * CM31`) avoid full 4-limb products where one operand is base.

// These inherent names are deliberate in the verifier kernel: they keep field
// arithmetic explicit and identical in `no_std` host/SBF builds without
// introducing operator-trait dispatch into CU-sensitive call sites.
#![allow(clippy::should_implement_trait)]

/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;

/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);

/// 1/2 in M31 (P is odd, so (P+1)/2 = 2^30).
pub const M31_HALF: M31 = M31(0x4000_0000);
/// 1/4 in M31 (4 * 2^29 = 2^31 = 1 mod P).
pub const M31_QUARTER: M31 = M31(0x2000_0000);

#[inline(always)]
fn reduce_u64(x: u64) -> u32 {
    // reference_canonical: two mask/shift folds bring any u64 to at most
    // P+3, then one conditional subtract canonicalizes. Supporting the full
    // u64 range lets four maximal M31 products be accumulated before one
    // reduction: 4*(P-1)^2 < 2^64.
    let x = (x & P as u64) + (x >> 31);
    let x = (x & P as u64) + (x >> 31);
    let x = x as u32;
    if x >= P {
        x - P
    } else {
        x
    }
}

impl M31 {
    pub const ZERO: M31 = M31(0);
    pub const ONE: M31 = M31(1);

    #[inline(always)]
    pub fn add(self, rhs: M31) -> M31 {
        let s = self.0 + rhs.0;
        M31(if s >= P { s - P } else { s })
    }

    #[inline(always)]
    pub fn sub(self, rhs: M31) -> M31 {
        let s = self.0 + P - rhs.0;
        M31(if s >= P { s - P } else { s })
    }

    #[inline(always)]
    pub fn neg(self) -> M31 {
        if self.0 == 0 {
            M31(0)
        } else {
            M31(P - self.0)
        }
    }

    #[inline(always)]
    pub fn mul(self, rhs: M31) -> M31 {
        M31(reduce_u64(self.0 as u64 * rhs.0 as u64))
    }

    /// Reduce an integer known to fit below 2^62 into canonical M31 form.
    ///
    /// This is the lazy-accumulation boundary used by SBF-specialized linear
    /// layers: several additions or small-constant products can be performed
    /// in `u64` and canonicalized once instead of after every operation.
    #[inline(always)]
    pub fn reduce_u62(value: u64) -> M31 {
        debug_assert!(value < (1u64 << 62));
        M31(reduce_u64(value))
    }

    /// Canonically reduce any `u64`. This is used by four-term lazy dot
    /// products whose accumulator may exceed 2^62 but cannot overflow u64.
    #[inline(always)]
    pub fn reduce_u64(value: u64) -> M31 {
        M31(reduce_u64(value))
    }

    /// Reduce a full `u128` with four Mersenne folds. This supports whole-dot
    /// accumulation when SBF carry-chain additions beat repeated u64
    /// canonicalization.
    #[inline(always)]
    pub fn reduce_u128(value: u128) -> M31 {
        let mask = P as u128;
        let value = (value & mask) + (value >> 31);
        let value = (value & mask) + (value >> 31);
        let value = (value & mask) + (value >> 31);
        let value = (value & mask) + (value >> 31);
        let value = value as u32;
        M31(if value >= P { value - P } else { value })
    }

    /// Multiply by 2^shift with a shift and Mersenne reduction rather than a
    /// generic integer multiplication. `shift <= 30` keeps the pre-reduction
    /// value below 2^61 for a canonical input.
    #[inline(always)]
    pub fn mul_pow2(self, shift: u8) -> M31 {
        debug_assert!(shift <= 30);
        M31(reduce_u64((self.0 as u64) << shift))
    }

    #[inline(always)]
    pub fn double(self) -> M31 {
        self.add(self)
    }

    /// Division by two in canonical form. For odd x, `(x + P) / 2` is the
    /// unique field element whose double is x; this avoids a field multiply
    /// by the constant `M31_HALF`.
    #[inline(always)]
    pub fn half(self) -> M31 {
        if self.0 & 1 == 0 {
            M31(self.0 >> 1)
        } else {
            M31(((self.0 as u64 + P as u64) >> 1) as u32)
        }
    }

    pub fn pow(self, mut exp: u64) -> M31 {
        let mut base = self;
        let mut acc = M31::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            exp >>= 1;
        }
        acc
    }

    /// Multiplicative inverse via Fermat. Panics on zero.
    pub fn inv(self) -> M31 {
        assert!(self.0 != 0, "inverse of zero");
        self.pow(P as u64 - 2)
    }

    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Parse from 4 LE bytes; rejects non-canonical encodings (>= P).
    pub fn from_le_bytes(bytes: [u8; 4]) -> Option<M31> {
        let v = u32::from_le_bytes(bytes);
        if v >= P {
            None
        } else {
            Some(M31(v))
        }
    }

    pub fn to_le_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}

/// CM31 = M31[i] / (i^2 + 1). Element a + b*i.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}

impl CM31 {
    pub const ZERO: CM31 = CM31 {
        a: M31(0),
        b: M31(0),
    };
    pub const ONE: CM31 = CM31 {
        a: M31(1),
        b: M31(0),
    };

    #[inline(always)]
    pub fn new(a: M31, b: M31) -> CM31 {
        CM31 { a, b }
    }

    #[inline(always)]
    pub fn from_m31(a: M31) -> CM31 {
        CM31 { a, b: M31::ZERO }
    }

    #[inline(always)]
    pub fn add(self, rhs: CM31) -> CM31 {
        CM31 {
            a: self.a.add(rhs.a),
            b: self.b.add(rhs.b),
        }
    }

    #[inline(always)]
    pub fn sub(self, rhs: CM31) -> CM31 {
        CM31 {
            a: self.a.sub(rhs.a),
            b: self.b.sub(rhs.b),
        }
    }

    #[inline(always)]
    pub fn neg(self) -> CM31 {
        CM31 {
            a: self.a.neg(),
            b: self.b.neg(),
        }
    }

    /// Karatsuba complex multiplication: 3 M31 muls.
    #[inline(always)]
    pub fn mul(self, rhs: CM31) -> CM31 {
        let m0 = self.a.mul(rhs.a);
        let m1 = self.b.mul(rhs.b);
        let m2 = self.a.add(self.b).mul(rhs.a.add(rhs.b));
        CM31 {
            a: m0.sub(m1),
            b: m2.sub(m0).sub(m1),
        }
    }

    /// Complex squaring with two M31 multiplications instead of the three
    /// used by generic Karatsuba multiplication.
    #[inline(always)]
    pub fn square(self) -> CM31 {
        CM31 {
            a: self.a.add(self.b).mul(self.a.sub(self.b)),
            b: self.a.mul(self.b).double(),
        }
    }

    #[inline(always)]
    pub fn mul_m31(self, rhs: M31) -> CM31 {
        CM31 {
            a: self.a.mul(rhs),
            b: self.b.mul(rhs),
        }
    }

    #[inline(always)]
    pub fn double(self) -> CM31 {
        self.add(self)
    }

    #[inline(always)]
    pub fn half(self) -> CM31 {
        CM31 {
            a: self.a.half(),
            b: self.b.half(),
        }
    }

    /// Conjugation is inversion for unit-circle elements.
    #[inline(always)]
    pub fn conjugate(self) -> CM31 {
        CM31 {
            a: self.a,
            b: self.b.neg(),
        }
    }

    /// Multiply by i without base-field multiplications.
    #[inline(always)]
    pub fn mul_i(self) -> CM31 {
        CM31 {
            a: self.b.neg(),
            b: self.a,
        }
    }

    pub fn pow(self, mut exp: u64) -> CM31 {
        let mut base = self;
        let mut acc = CM31::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    /// Inverse via conjugate/norm: one M31 inversion + a few muls.
    pub fn inv(self) -> CM31 {
        self.inv_with(M31::inv)
    }

    /// Inverse with an injected base-field inversion backend. On SBF this
    /// lets the caller use `sol_big_mod_exp` without coupling the no_std
    /// verifier core to the Solana SDK.
    pub fn inv_with(self, inverse: fn(M31) -> M31) -> CM31 {
        let norm = self.a.mul(self.a).add(self.b.mul(self.b));
        let inv_norm = inverse(norm);
        CM31 {
            a: self.a.mul(inv_norm),
            b: self.b.neg().mul(inv_norm),
        }
    }

    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.a.is_zero() && self.b.is_zero()
    }

    pub fn from_le_bytes(bytes: &[u8]) -> Option<CM31> {
        let a = M31::from_le_bytes(bytes[0..4].try_into().ok()?)?;
        let b = M31::from_le_bytes(bytes[4..8].try_into().ok()?)?;
        Some(CM31 { a, b })
    }

    pub fn write_le_bytes(self, out: &mut [u8]) {
        out[0..4].copy_from_slice(&self.a.to_le_bytes());
        out[4..8].copy_from_slice(&self.b.to_le_bytes());
    }
}

/// QM31 = CM31[u] / (u^2 - (2 + i)). Element c0 + c1*u. (stwo parameterization)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}

/// The non-residue R = 2 + i used to define QM31.
#[inline(always)]
fn mul_by_r(x: CM31) -> CM31 {
    // (2 + i)(a + bi) = (2a - b) + (a + 2b) i
    CM31 {
        a: x.a.double().sub(x.b),
        b: x.a.add(x.b.double()),
    }
}

impl QM31 {
    pub const ZERO: QM31 = QM31 {
        c0: CM31 {
            a: M31(0),
            b: M31(0),
        },
        c1: CM31 {
            a: M31(0),
            b: M31(0),
        },
    };
    pub const ONE: QM31 = QM31 {
        c0: CM31 {
            a: M31(1),
            b: M31(0),
        },
        c1: CM31 {
            a: M31(0),
            b: M31(0),
        },
    };

    #[inline(always)]
    pub fn from_cm31(c0: CM31) -> QM31 {
        QM31 { c0, c1: CM31::ZERO }
    }

    #[inline(always)]
    pub fn add(self, rhs: QM31) -> QM31 {
        QM31 {
            c0: self.c0.add(rhs.c0),
            c1: self.c1.add(rhs.c1),
        }
    }

    #[inline(always)]
    pub fn sub(self, rhs: QM31) -> QM31 {
        QM31 {
            c0: self.c0.sub(rhs.c0),
            c1: self.c1.sub(rhs.c1),
        }
    }

    #[inline(always)]
    pub fn neg(self) -> QM31 {
        QM31 {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }

    #[inline(always)]
    pub fn half(self) -> QM31 {
        QM31 {
            c0: self.c0.half(),
            c1: self.c1.half(),
        }
    }

    /// Karatsuba extension multiplication: 3 CM31 muls + one mul-by-R.
    #[inline(always)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        let m0 = self.c0.mul(rhs.c0);
        let m1 = self.c1.mul(rhs.c1);
        let m2 = self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));
        QM31 {
            c0: m0.add(mul_by_r(m1)),
            c1: m2.sub(m0).sub(m1),
        }
    }

    /// Quadratic-extension squaring. The two component squares use the
    /// specialized CM31 kernel and the cross term needs one generic CM31
    /// multiplication: seven M31 products rather than nine.
    #[inline(always)]
    pub fn square(self) -> QM31 {
        let c0_square = self.c0.square();
        let c1_square = self.c1.square();
        QM31 {
            c0: c0_square.add(mul_by_r(c1_square)),
            c1: self.c0.mul(self.c1).double(),
        }
    }

    /// Late-lift kernel: QM31 * CM31 costs 2 CM31 muls instead of 3.
    #[inline(always)]
    pub fn mul_cm31(self, rhs: CM31) -> QM31 {
        QM31 {
            c0: self.c0.mul(rhs),
            c1: self.c1.mul(rhs),
        }
    }

    /// Late-lift kernel: QM31 * M31 costs 2 scalar CM31 scalings.
    #[inline(always)]
    pub fn mul_m31(self, rhs: M31) -> QM31 {
        QM31 {
            c0: self.c0.mul_m31(rhs),
            c1: self.c1.mul_m31(rhs),
        }
    }

    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    pub fn pow(self, mut exp: u64) -> QM31 {
        let mut base = self;
        let mut acc = QM31::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    /// Inverse in the quadratic extension over CM31:
    /// `(a + bu)^-1 = (a - bu) / (a^2 - (2+i)b^2)`.
    pub fn try_inv(self) -> Option<QM31> {
        if self.is_zero() {
            return None;
        }
        let norm = self.c0.square().sub(mul_by_r(self.c1.square()));
        let inverse_norm = norm.inv();
        Some(QM31 {
            c0: self.c0.mul(inverse_norm),
            c1: self.c1.neg().mul(inverse_norm),
        })
    }

    pub fn inv(self) -> QM31 {
        self.try_inv().expect("cannot invert zero in QM31")
    }

    pub fn from_le_bytes(bytes: &[u8]) -> Option<QM31> {
        let c0 = CM31::from_le_bytes(&bytes[0..8])?;
        let c1 = CM31::from_le_bytes(&bytes[8..16])?;
        Some(QM31 { c0, c1 })
    }

    pub fn write_le_bytes(self, out: &mut [u8]) {
        self.c0.write_le_bytes(&mut out[0..8]);
        self.c1.write_le_bytes(&mut out[8..16]);
    }
}

/// Precompute `[1, gamma, ..., gamma^(N-1)]` into a fixed-width table.
///
/// Const-sized storage lets SBF callers keep protocol-fixed RLC bases in one
/// stack/account buffer, avoiding allocator and capacity checks in the query
/// hot path. The table is challenge-specific and must be rebuilt whenever
/// `gamma` changes.
pub fn qm31_power_table<const N: usize>(gamma: QM31) -> [QM31; N] {
    let mut table = [QM31::ZERO; N];
    let mut power = QM31::ONE;
    for entry in &mut table {
        *entry = power;
        power = power.mul(gamma);
    }
    table
}

/// Dot product between QM31 weights and CM31 values. Six base-field dot
/// products are fused; four scalar products are accumulated per reduction.
/// This preserves the late-lift representation while removing three of four
/// canonical reductions from the wide-column RLC hot loop.
pub fn qm31_cm31_dot(weights: &[QM31], values: &[CM31]) -> QM31 {
    assert_eq!(weights.len(), values.len());
    let mut sums = [M31::ZERO; 6];
    for start in (0..weights.len()).step_by(4) {
        let end = core::cmp::min(start + 4, weights.len());
        let mut raw = [0u64; 6];
        for index in start..end {
            let value = values[index];
            for (component, weight) in [weights[index].c0, weights[index].c1]
                .into_iter()
                .enumerate()
            {
                let offset = component * 3;
                raw[offset] += weight.a.0 as u64 * value.a.0 as u64;
                raw[offset + 1] += weight.b.0 as u64 * value.b.0 as u64;
                raw[offset + 2] += weight.a.add(weight.b).0 as u64 * value.a.add(value.b).0 as u64;
            }
        }
        for index in 0..6 {
            sums[index] = sums[index].add(M31::reduce_u64(raw[index]));
        }
    }
    let component = |offset: usize| CM31 {
        a: sums[offset].sub(sums[offset + 1]),
        b: sums[offset + 2].sub(sums[offset]).sub(sums[offset + 1]),
    };
    QM31 {
        c0: component(0),
        c1: component(3),
    }
}

#[inline(always)]
fn finish_qm31_cm31_dot4(sums: [[M31; 6]; 4]) -> [QM31; 4] {
    core::array::from_fn(|slot| {
        let component = |offset: usize| CM31 {
            a: sums[slot][offset].sub(sums[slot][offset + 1]),
            b: sums[slot][offset + 2]
                .sub(sums[slot][offset])
                .sub(sums[slot][offset + 1]),
        };
        QM31 {
            c0: component(0),
            c1: component(3),
        }
    })
}

/// Four QM31-by-CM31 dot products with one shared weight vector.
///
/// The four value slices are independent fiber slots. Sharing the traversal
/// lets the kernel compute each weight's Karatsuba cross terms once, and the
/// outer accumulators defer canonical additions until the end of a bounded
/// column window. This is an arithmetic primitive only; callers define what
/// the four slots and weights represent.
pub fn qm31_cm31_dot4(weights: &[QM31], values: [&[CM31]; 4]) -> [QM31; 4] {
    for slot in values {
        assert_eq!(weights.len(), slot.len());
    }

    // Each inner raw accumulator contains at most four maximal M31 products,
    // so it fits in u64. A 256-column outer window contains at most 64
    // canonical block results per limb and therefore also fits comfortably.
    const OUTER_COLUMNS: usize = 256;
    let mut sums = [[M31::ZERO; 6]; 4];
    for outer_start in (0..weights.len()).step_by(OUTER_COLUMNS) {
        let outer_end = core::cmp::min(outer_start + OUTER_COLUMNS, weights.len());
        let mut outer = [[0u64; 6]; 4];
        for start in (outer_start..outer_end).step_by(4) {
            let end = core::cmp::min(start + 4, outer_end);
            let mut raw = [[0u64; 6]; 4];
            for index in start..end {
                let weight = weights[index];
                let weight_components = [
                    (weight.c0.a, weight.c0.b, weight.c0.a.add(weight.c0.b)),
                    (weight.c1.a, weight.c1.b, weight.c1.a.add(weight.c1.b)),
                ];
                for (slot, raw_slot) in raw.iter_mut().enumerate() {
                    let value = values[slot][index];
                    let value_sum = value.a.add(value.b);
                    for (component, (weight_a, weight_b, weight_sum)) in
                        weight_components.into_iter().enumerate()
                    {
                        let offset = component * 3;
                        raw_slot[offset] += weight_a.0 as u64 * value.a.0 as u64;
                        raw_slot[offset + 1] += weight_b.0 as u64 * value.b.0 as u64;
                        raw_slot[offset + 2] += weight_sum.0 as u64 * value_sum.0 as u64;
                    }
                }
            }
            for slot in 0..4 {
                for component in 0..6 {
                    outer[slot][component] += M31::reduce_u64(raw[slot][component]).0 as u64;
                }
            }
        }
        for slot in 0..4 {
            for component in 0..6 {
                sums[slot][component] =
                    sums[slot][component].add(M31::reduce_u64(outer[slot][component]));
            }
        }
    }

    finish_qm31_cm31_dot4(sums)
}

/// Karatsuba limbs for a protocol-fixed QM31 weight vector.
///
/// A verifier applies the same gamma powers to every authenticated query
/// fiber. Preparing `(a, b, a+b)` for both CM31 components once avoids
/// recomputing those challenge-dependent sums in every four-slot dot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedQm31Cm31Weights<const N: usize> {
    components: [[M31; 6]; N],
}

impl<const N: usize> PreparedQm31Cm31Weights<N> {
    #[inline(always)]
    fn components(weight: QM31) -> [M31; 6] {
        [
            weight.c0.a,
            weight.c0.b,
            weight.c0.a.add(weight.c0.b),
            weight.c1.a,
            weight.c1.b,
            weight.c1.a.add(weight.c1.b),
        ]
    }

    pub fn new(weights: &[QM31]) -> Self {
        assert_eq!(weights.len(), N);
        Self {
            components: core::array::from_fn(|index| Self::components(weights[index])),
        }
    }

    /// Prepare `[1, gamma, ..., gamma^(N-1)]` in one pass and return
    /// `gamma^N` for an immediately following protocol lane.
    pub fn geometric(gamma: QM31) -> (Self, QM31) {
        let mut power = QM31::ONE;
        let components = core::array::from_fn(|_| {
            let result = Self::components(power);
            power = power.mul(gamma);
            result
        });
        (Self { components }, power)
    }
}

/// Four QM31-by-CM31 dots using a weight vector prepared once per proof.
///
/// This has the same field result as [`qm31_cm31_dot4`]. It is specialized
/// for the common verifier shape where one Fiat-Shamir challenge determines
/// the weights and many authenticated fibers reuse them.
pub fn qm31_cm31_dot4_prepared<const N: usize>(
    weights: &PreparedQm31Cm31Weights<N>,
    values: [&[CM31; N]; 4],
) -> [QM31; 4] {
    // Four maximal M31 products fit in u64. Each 256-column window has at
    // most 64 reduced blocks, so its outer accumulator is far below u64::MAX.
    const OUTER_COLUMNS: usize = 256;
    let mut sums = [[M31::ZERO; 6]; 4];
    for outer_start in (0..N).step_by(OUTER_COLUMNS) {
        let outer_end = core::cmp::min(outer_start + OUTER_COLUMNS, N);
        let mut outer = [[0u64; 6]; 4];
        for start in (outer_start..outer_end).step_by(4) {
            let end = core::cmp::min(start + 4, outer_end);
            let mut raw = [[0u64; 6]; 4];
            for (relative, &weight) in weights.components[start..end].iter().enumerate() {
                let index = start + relative;
                for slot in 0..4 {
                    let value = values[slot][index];
                    let value_sum = value.a.add(value.b);
                    for component in 0..2 {
                        let offset = component * 3;
                        raw[slot][offset] += weight[offset].0 as u64 * value.a.0 as u64;
                        raw[slot][offset + 1] += weight[offset + 1].0 as u64 * value.b.0 as u64;
                        raw[slot][offset + 2] += weight[offset + 2].0 as u64 * value_sum.0 as u64;
                    }
                }
            }
            for slot in 0..4 {
                for component in 0..6 {
                    outer[slot][component] += M31::reduce_u64(raw[slot][component]).0 as u64;
                }
            }
        }
        for slot in 0..4 {
            for component in 0..6 {
                sums[slot][component] =
                    sums[slot][component].add(M31::reduce_u64(outer[slot][component]));
            }
        }
    }

    finish_qm31_cm31_dot4(sums)
}

/// Prepared four-slot dot directly over canonical little-endian CM31 bytes.
///
/// Wire order is slot-major: four consecutive slots of `N` CM31 values.
/// Decoding and arithmetic share one traversal, and canonicality failures are
/// accumulated into one final branch instead of materializing an intermediate
/// matrix with one `Option` branch per limb.
pub fn qm31_cm31_dot4_prepared_bytes<const N: usize>(
    weights: &PreparedQm31Cm31Weights<N>,
    bytes: &[u8],
) -> Option<[QM31; 4]> {
    if bytes.len() != 4 * N * 8 {
        return None;
    }

    const OUTER_COLUMNS: usize = 256;
    let mut invalid = 0u32;
    let mut sums = [[M31::ZERO; 6]; 4];
    for outer_start in (0..N).step_by(OUTER_COLUMNS) {
        let outer_end = core::cmp::min(outer_start + OUTER_COLUMNS, N);
        let mut outer = [[0u64; 6]; 4];
        for start in (outer_start..outer_end).step_by(4) {
            let end = core::cmp::min(start + 4, outer_end);
            let mut raw = [[0u64; 6]; 4];
            for (relative, &weight) in weights.components[start..end].iter().enumerate() {
                let index = start + relative;
                for (slot, raw_slot) in raw.iter_mut().enumerate() {
                    let offset = (slot * N + index) * 8;
                    let value_a = u32::from_le_bytes(bytes[offset..offset + 4].try_into().ok()?);
                    let value_b =
                        u32::from_le_bytes(bytes[offset + 4..offset + 8].try_into().ok()?);
                    invalid |= u32::from(value_a >= P) | u32::from(value_b >= P);
                    // Keep arithmetic bounded even for a rejected encoding;
                    // canonical inputs are unchanged by the mask.
                    let value_a = M31(value_a & P);
                    let value_b = M31(value_b & P);
                    let value_sum = value_a.add(value_b);
                    for component in 0..2 {
                        let limb = component * 3;
                        raw_slot[limb] += weight[limb].0 as u64 * value_a.0 as u64;
                        raw_slot[limb + 1] += weight[limb + 1].0 as u64 * value_b.0 as u64;
                        raw_slot[limb + 2] += weight[limb + 2].0 as u64 * value_sum.0 as u64;
                    }
                }
            }
            for slot in 0..4 {
                for component in 0..6 {
                    outer[slot][component] += M31::reduce_u64(raw[slot][component]).0 as u64;
                }
            }
        }
        for slot in 0..4 {
            for component in 0..6 {
                sums[slot][component] =
                    sums[slot][component].add(M31::reduce_u64(outer[slot][component]));
            }
        }
    }

    if invalid == 0 {
        Some(finish_qm31_cm31_dot4(sums))
    } else {
        None
    }
}

/// Prior four-products-per-reduction kernel with a canonical M31 addition
/// after every block. Retained for literal SBF comparison.
pub fn qm31_m31_dot_eager_outer(weights: &[QM31], values: &[M31]) -> QM31 {
    assert_eq!(weights.len(), values.len());
    let mut sums = [M31::ZERO; 4];
    for start in (0..weights.len()).step_by(4) {
        let end = core::cmp::min(start + 4, weights.len());
        let mut raw = [0u64; 4];
        for index in start..end {
            let value = values[index].0 as u64;
            let weight = weights[index];
            raw[0] += weight.c0.a.0 as u64 * value;
            raw[1] += weight.c0.b.0 as u64 * value;
            raw[2] += weight.c1.a.0 as u64 * value;
            raw[3] += weight.c1.b.0 as u64 * value;
        }
        for index in 0..4 {
            sums[index] = sums[index].add(M31::reduce_u64(raw[index]));
        }
    }
    QM31 {
        c0: CM31::new(sums[0], sums[1]),
        c1: CM31::new(sums[2], sums[3]),
    }
}

/// Dot product between QM31 weights and raw M31 trace columns. Four scalar
/// products are fused per inner reduction; those canonical block results are
/// then accumulated in u64 and reduced once per output limb.
///
/// For an 80-column opening each outer accumulator is below `20 * P`, so this
/// removes 76 canonical additions without widening the hot product loop.
pub fn qm31_m31_dot(weights: &[QM31], values: &[M31]) -> QM31 {
    assert_eq!(weights.len(), values.len());
    let mut sums = [0u64; 4];
    for start in (0..weights.len()).step_by(4) {
        let end = core::cmp::min(start + 4, weights.len());
        let mut raw = [0u64; 4];
        for index in start..end {
            let value = values[index].0 as u64;
            let weight = weights[index];
            raw[0] += weight.c0.a.0 as u64 * value;
            raw[1] += weight.c0.b.0 as u64 * value;
            raw[2] += weight.c1.a.0 as u64 * value;
            raw[3] += weight.c1.b.0 as u64 * value;
        }
        for index in 0..4 {
            sums[index] += M31::reduce_u64(raw[index]).0 as u64;
        }
    }
    QM31 {
        c0: CM31::new(M31::reduce_u64(sums[0]), M31::reduce_u64(sums[1])),
        c1: CM31::new(M31::reduce_u64(sums[2]), M31::reduce_u64(sums[3])),
    }
}

#[inline(always)]
fn finish_qm31_m31_dot4(sums: [[u64; 4]; 4]) -> [QM31; 4] {
    core::array::from_fn(|slot| QM31 {
        c0: CM31::new(
            M31::reduce_u64(sums[slot][0]),
            M31::reduce_u64(sums[slot][1]),
        ),
        c1: CM31::new(
            M31::reduce_u64(sums[slot][2]),
            M31::reduce_u64(sums[slot][3]),
        ),
    })
}

/// Four QM31-by-M31 dot products with one shared weight vector.
///
/// This is the raw-base-field analogue of [`qm31_cm31_dot4`]. It is an
/// arithmetic primitive only: callers decide whether the four slots describe
/// a genuine-circle PCS leaf, a diagnostic fixture, or another layout.
pub fn qm31_m31_dot4(weights: &[QM31], values: [&[M31]; 4]) -> [QM31; 4] {
    for slot in values {
        assert_eq!(weights.len(), slot.len());
    }

    // Four maximal M31 products fit in u64. A 256-column outer window has at
    // most 64 reduced blocks, keeping every outer accumulator far below the
    // u64 limit while avoiding one canonical addition per four-column block.
    const OUTER_COLUMNS: usize = 256;
    let mut sums = [[0u64; 4]; 4];
    for outer_start in (0..weights.len()).step_by(OUTER_COLUMNS) {
        let outer_end = core::cmp::min(outer_start + OUTER_COLUMNS, weights.len());
        let mut outer = [[0u64; 4]; 4];
        for start in (outer_start..outer_end).step_by(4) {
            let end = core::cmp::min(start + 4, outer_end);
            let mut raw = [[0u64; 4]; 4];
            for index in start..end {
                let weight = weights[index];
                let limbs = [weight.c0.a, weight.c0.b, weight.c1.a, weight.c1.b];
                for slot in 0..4 {
                    let value = values[slot][index].0 as u64;
                    for limb in 0..4 {
                        raw[slot][limb] += limbs[limb].0 as u64 * value;
                    }
                }
            }
            for slot in 0..4 {
                for limb in 0..4 {
                    outer[slot][limb] += M31::reduce_u64(raw[slot][limb]).0 as u64;
                }
            }
        }
        for slot in 0..4 {
            for limb in 0..4 {
                sums[slot][limb] += M31::reduce_u64(outer[slot][limb]).0 as u64;
            }
        }
    }
    finish_qm31_m31_dot4(sums)
}

/// Four QM31-by-M31 dots directly over canonical little-endian M31 bytes.
///
/// Wire order is slot-major: four consecutive slots of `N` M31 values.
/// Decoding and arithmetic share one traversal. Canonicality failures are
/// accumulated into one final branch, and rejected inputs are masked only to
/// keep the speculative arithmetic bounded before that branch.
pub fn qm31_m31_dot4_prepared_bytes<const N: usize>(
    weights: &[QM31; N],
    bytes: &[u8],
) -> Option<[QM31; 4]> {
    if bytes.len() != 4 * N * 4 {
        return None;
    }

    const OUTER_COLUMNS: usize = 256;
    let mut invalid = 0u32;
    let mut sums = [[0u64; 4]; 4];
    for outer_start in (0..N).step_by(OUTER_COLUMNS) {
        let outer_end = core::cmp::min(outer_start + OUTER_COLUMNS, N);
        let mut outer = [[0u64; 4]; 4];
        for start in (outer_start..outer_end).step_by(4) {
            let end = core::cmp::min(start + 4, outer_end);
            let mut raw = [[0u64; 4]; 4];
            for (relative, weight) in weights[start..end].iter().enumerate() {
                let index = start + relative;
                let limbs = [weight.c0.a, weight.c0.b, weight.c1.a, weight.c1.b];
                for (slot, raw_slot) in raw.iter_mut().enumerate() {
                    let offset = (slot * N + index) * 4;
                    let value = u32::from_le_bytes(bytes[offset..offset + 4].try_into().ok()?);
                    invalid |= u32::from(value >= P);
                    let value = (value & P) as u64;
                    for limb in 0..4 {
                        raw_slot[limb] += limbs[limb].0 as u64 * value;
                    }
                }
            }
            for slot in 0..4 {
                for limb in 0..4 {
                    outer[slot][limb] += M31::reduce_u64(raw[slot][limb]).0 as u64;
                }
            }
        }
        for slot in 0..4 {
            for limb in 0..4 {
                sums[slot][limb] += M31::reduce_u64(outer[slot][limb]).0 as u64;
            }
        }
    }

    if invalid == 0 {
        Some(finish_qm31_m31_dot4(sums))
    } else {
        None
    }
}

/// Normalized four-value circle-to-line followed by line fold.
///
/// Slot order is `(x,y), (x,-y), (-x,-y), (-x,y)`. `inv_2x` and `inv_2y`
/// are verifier-derived inverses of `2x` and `2y`; the third pair uses
/// `-inv_2y`. The normalization matches coefficient evaluation
/// `c0 + alpha*c1 + alpha^2*c2 + alpha^3*c3`, rather than the four-times
/// unnormalized inverse-butterfly convention used by some circle FFTs.
pub fn qm31_circle_to_line_fold4(values: [QM31; 4], alpha: QM31, inv_2x: M31, inv_2y: M31) -> QM31 {
    let positive = values[0]
        .add(values[1])
        .half()
        .add(alpha.mul(values[0].sub(values[1]).mul_m31(inv_2y)));
    let negative = values[2]
        .add(values[3])
        .half()
        .add(alpha.mul(values[2].sub(values[3]).mul_m31(M31::ZERO.sub(inv_2y))));
    positive
        .add(negative)
        .half()
        .add(alpha.square().mul(positive.sub(negative).mul_m31(inv_2x)))
}

/// Whole-vector variant of `qm31_m31_dot`: accumulate in u128 and reduce
/// each of the four output limbs once.
pub fn qm31_m31_dot_u128(weights: &[QM31], values: &[M31]) -> QM31 {
    assert_eq!(weights.len(), values.len());
    let mut sums = [0u128; 4];
    for (weight, value) in weights.iter().zip(values) {
        let value = value.0 as u128;
        sums[0] += weight.c0.a.0 as u128 * value;
        sums[1] += weight.c0.b.0 as u128 * value;
        sums[2] += weight.c1.a.0 as u128 * value;
        sums[3] += weight.c1.b.0 as u128 * value;
    }
    QM31 {
        c0: CM31::new(M31::reduce_u128(sums[0]), M31::reduce_u128(sums[1])),
        c1: CM31::new(M31::reduce_u128(sums[2]), M31::reduce_u128(sums[3])),
    }
}

/// QM31 dot product with the same four-products-per-reduction strategy. This
/// is the packed-four-column RLC kernel: four M31 trace columns embed
/// injectively into one QM31 value, then twenty packed values batch eighty
/// raw columns.
pub fn qm31_dot(weights: &[QM31], values: &[QM31]) -> QM31 {
    assert_eq!(weights.len(), values.len());
    let mut sums = [M31::ZERO; 9];
    for start in (0..weights.len()).step_by(4) {
        let end = core::cmp::min(start + 4, weights.len());
        let mut raw = [0u64; 9];
        for index in start..end {
            let weight = weights[index];
            let value = values[index];
            let pairs = [
                (weight.c0, value.c0),
                (weight.c1, value.c1),
                (weight.c0.add(weight.c1), value.c0.add(value.c1)),
            ];
            for (component, (left, right)) in pairs.into_iter().enumerate() {
                let offset = component * 3;
                raw[offset] += left.a.0 as u64 * right.a.0 as u64;
                raw[offset + 1] += left.b.0 as u64 * right.b.0 as u64;
                raw[offset + 2] += left.a.add(left.b).0 as u64 * right.a.add(right.b).0 as u64;
            }
        }
        for index in 0..9 {
            sums[index] = sums[index].add(M31::reduce_u64(raw[index]));
        }
    }
    let component = |offset: usize| CM31 {
        a: sums[offset].sub(sums[offset + 1]),
        b: sums[offset + 2].sub(sums[offset]).sub(sums[offset + 1]),
    };
    let m0 = component(0);
    let m1 = component(3);
    let m2 = component(6);
    QM31 {
        c0: m0.add(mul_by_r(m1)),
        c1: m2.sub(m0).sub(m1),
    }
}

/// Montgomery batch inversion over M31: one field inversion for the whole
/// batch plus 3(n-1) multiplications. Panics if any element is zero.
pub fn m31_batch_inverse(values: &[M31], out: &mut [M31]) {
    m31_batch_inverse_with(values, out, M31::inv)
}

/// M31 batch inversion with an injected single-inverse backend. This keeps
/// the prefix/suffix multiplication schedule identical while allowing SBF to
/// use its modular-exponentiation syscall once for the whole batch.
pub fn m31_batch_inverse_with(values: &[M31], out: &mut [M31], inverse: fn(M31) -> M31) {
    assert_eq!(values.len(), out.len());
    if values.is_empty() {
        return;
    }
    let mut accumulator = M31::ONE;
    for (index, value) in values.iter().enumerate() {
        out[index] = accumulator;
        accumulator = accumulator.mul(*value);
    }
    let mut inverse = inverse(accumulator);
    for index in (0..values.len()).rev() {
        let prefix = out[index];
        out[index] = prefix.mul(inverse);
        inverse = inverse.mul(values[index]);
    }
}

/// Quadratic-extension batch inversion with the same one-inverse Montgomery
/// trick as [`m31_batch_inverse`].
pub fn cm31_batch_inverse(values: &[CM31], out: &mut [CM31]) {
    cm31_batch_inverse_with(values, out, M31::inv)
}

/// Batch inversion with an injected M31 inversion backend. All prefix and
/// suffix work remains byte-identical; only the single base-field inverse is
/// delegated.
pub fn cm31_batch_inverse_with(values: &[CM31], out: &mut [CM31], inverse: fn(M31) -> M31) {
    assert_eq!(values.len(), out.len());
    if values.is_empty() {
        return;
    }
    // prefix products
    let mut acc = CM31::ONE;
    for (i, v) in values.iter().enumerate() {
        out[i] = acc;
        acc = acc.mul(*v);
    }
    let mut inv = acc.inv_with(inverse);
    for i in (0..values.len()).rev() {
        let prefix = out[i];
        out[i] = prefix.mul(inv);
        inv = inv.mul(values[i]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn m31_reduction_edges() {
        assert_eq!(M31(P - 1).add(M31(1)), M31(0));
        assert_eq!(M31(P - 1).mul(M31(P - 1)), M31(1)); // (-1)^2
        assert_eq!(M31(0).sub(M31(1)), M31(P - 1));
        // 2^31 mod P == 1
        assert_eq!(reduce_u64(1u64 << 31), 1);
        // P * P == 0 mod P; also the max pre-reduction product
        assert_eq!(reduce_u64((P as u64) * (P as u64)), 0);
        assert_eq!(
            reduce_u64((P as u64 - 1) * (P as u64 - 1)),
            1 // (-1)^2
        );
        assert_eq!(M31::reduce_u64(u64::MAX), M31((u64::MAX % P as u64) as u32));
        assert_eq!(
            M31::reduce_u128(u128::MAX),
            M31((u128::MAX % P as u128) as u32)
        );
    }

    #[test]
    fn m31_lazy_reduction_and_pow2_match_canonical_arithmetic() {
        for value in [0, 1, 2, 123_456_789, P - 2, P - 1] {
            let element = M31(value);
            for shift in 0..=30 {
                let expected = element.mul(M31::reduce_u62(1u64 << shift));
                assert_eq!(element.mul_pow2(shift), expected);
            }
            assert_eq!(element.half(), element.mul(M31_HALF));
            assert_eq!(element.half().double(), element);
        }

        let values = [M31(P - 1); 16];
        let lazy_sum = M31::reduce_u62(values.iter().map(|value| value.0 as u64).sum());
        let canonical_sum = values.iter().copied().fold(M31::ZERO, M31::add);
        assert_eq!(lazy_sum, canonical_sum);
    }

    #[test]
    fn m31_inverse() {
        for v in [1u32, 2, 3, 12345, P - 1, 0x4000_0000] {
            let x = M31(v);
            assert_eq!(x.mul(x.inv()), M31::ONE);
        }
        assert_eq!(M31_HALF.double(), M31::ONE);
    }

    #[test]
    fn cm31_field_axioms() {
        let x = CM31::new(M31(123456789), M31(987654321));
        let y = CM31::new(M31(555), M31(777777));
        // karatsuba vs schoolbook
        let school = CM31 {
            a: x.a.mul(y.a).sub(x.b.mul(y.b)),
            b: x.a.mul(y.b).add(x.b.mul(y.a)),
        };
        assert_eq!(x.mul(y), school);
        assert_eq!(x.square(), x.mul(x));
        assert_eq!(x.half(), x.mul_m31(M31_HALF));
        assert_eq!(x.mul_i(), x.mul(CM31::new(M31::ZERO, M31::ONE)));
        assert_eq!(x.mul(x.inv()), CM31::ONE);
    }

    #[test]
    fn qm31_field_axioms() {
        let x = QM31 {
            c0: CM31::new(M31(1), M31(2)),
            c1: CM31::new(M31(3), M31(4)),
        };
        let y = QM31 {
            c0: CM31::new(M31(5), M31(6)),
            c1: CM31::new(M31(7), M31(8)),
        };
        assert_eq!(x.square(), x.mul(x));
        assert_eq!(x.mul(x.inv()), QM31::ONE);
        assert_eq!(QM31::ZERO.try_inv(), None);
        assert_eq!(x.half(), x.mul_m31(M31_HALF));
        // u^2 = 2 + i
        let u = QM31 {
            c0: CM31::ZERO,
            c1: CM31::ONE,
        };
        let u2 = u.mul(u);
        assert_eq!(u2.c0, CM31::new(M31(2), M31(1)));
        assert_eq!(u2.c1, CM31::ZERO);
        // distributivity spot check
        let lhs = x.mul(y.add(u));
        let rhs = x.mul(y).add(x.mul(u));
        assert_eq!(lhs, rhs);
        // late-lift kernels agree with full mul
        let c = CM31::new(M31(999), M31(1000));
        assert_eq!(x.mul_cm31(c), x.mul(QM31::from_cm31(c)));
        assert_eq!(
            x.mul_m31(M31(77)),
            x.mul(QM31::from_cm31(CM31::from_m31(M31(77))))
        );

        let powers = qm31_power_table::<8>(x);
        let mut expected = QM31::ONE;
        for power in powers {
            assert_eq!(power, expected);
            expected = expected.mul(x);
        }
        assert_eq!(qm31_power_table::<0>(x), []);
    }

    #[test]
    fn batch_inverse_matches_individual() {
        let base_values = [M31(1), M31(123), M31(P - 1), M31(7)];
        let mut base_out = [M31::ZERO; 4];
        m31_batch_inverse(&base_values, &mut base_out);
        for (value, inverse) in base_values.iter().zip(base_out.iter()) {
            assert_eq!(value.mul(*inverse), M31::ONE);
        }
        let mut empty = [];
        m31_batch_inverse(&[], &mut empty);

        let values = [
            CM31::new(M31(1), M31(0)),
            CM31::new(M31(123), M31(456)),
            CM31::new(M31(P - 1), M31(31337)),
            CM31::new(M31(7), M31(7)),
        ];
        let mut out = [CM31::ZERO; 4];
        cm31_batch_inverse(&values, &mut out);
        for (v, inv) in values.iter().zip(out.iter()) {
            assert_eq!(v.mul(*inv), CM31::ONE);
        }
    }

    #[test]
    fn lazy_qm31_cm31_dot_matches_naive() {
        for len in [0usize, 1, 3, 4, 5, 16, 49, 80] {
            let weights = (0..len)
                .map(|index| QM31 {
                    c0: CM31::new(
                        M31((index as u32 * 97 + 3) % P),
                        M31((index as u32 * 193 + 5) % P),
                    ),
                    c1: CM31::new(
                        M31((index as u32 * 389 + 7) % P),
                        M31((index as u32 * 769 + 11) % P),
                    ),
                })
                .collect::<alloc::vec::Vec<_>>();
            let values = (0..len)
                .map(|index| {
                    CM31::new(
                        M31((index as u32 * 1_543 + 13) % P),
                        M31((index as u32 * 3_079 + 17) % P),
                    )
                })
                .collect::<alloc::vec::Vec<_>>();
            let naive = weights
                .iter()
                .zip(&values)
                .fold(QM31::ZERO, |sum, (weight, value)| {
                    sum.add(weight.mul_cm31(*value))
                });
            assert_eq!(qm31_cm31_dot(&weights, &values), naive);
        }
    }

    #[test]
    fn fused_qm31_cm31_dot4_matches_independent_and_naive_dots() {
        fn next(state: &mut u64) -> M31 {
            *state ^= *state >> 12;
            *state ^= *state << 25;
            *state ^= *state >> 27;
            M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
        }

        fn cm31(state: &mut u64) -> CM31 {
            CM31::new(next(state), next(state))
        }

        fn qm31(state: &mut u64) -> QM31 {
            QM31 {
                c0: cm31(state),
                c1: cm31(state),
            }
        }

        for seed in 1..=24u64 {
            for len in [0usize, 1, 3, 4, 5, 16, 49, 80, 257] {
                let mut state = seed
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .wrapping_add(len as u64 + 1);
                let weights = (0..len)
                    .map(|_| qm31(&mut state))
                    .collect::<alloc::vec::Vec<_>>();
                let slots: [alloc::vec::Vec<CM31>; 4] =
                    core::array::from_fn(|_| (0..len).map(|_| cm31(&mut state)).collect());
                let fused = qm31_cm31_dot4(&weights, [&slots[0], &slots[1], &slots[2], &slots[3]]);
                for slot in 0..4 {
                    let independent = qm31_cm31_dot(&weights, &slots[slot]);
                    let naive = weights
                        .iter()
                        .zip(&slots[slot])
                        .fold(QM31::ZERO, |sum, (weight, value)| {
                            sum.add(weight.mul_cm31(*value))
                        });
                    assert_eq!(
                        fused[slot], independent,
                        "seed={seed}, len={len}, slot={slot}"
                    );
                    assert_eq!(fused[slot], naive, "seed={seed}, len={len}, slot={slot}");
                }
            }
        }
    }

    #[test]
    fn prepared_qm31_cm31_dot4_matches_fused_across_outer_windows() {
        fn next(state: &mut u64) -> M31 {
            *state ^= *state >> 12;
            *state ^= *state << 25;
            *state ^= *state >> 27;
            M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
        }

        fn cm31(state: &mut u64) -> CM31 {
            CM31::new(next(state), next(state))
        }

        fn qm31(state: &mut u64) -> QM31 {
            QM31 {
                c0: cm31(state),
                c1: cm31(state),
            }
        }

        fn check<const N: usize>(seed: u64) {
            let mut state = seed;
            let weights: [QM31; N] = core::array::from_fn(|_| qm31(&mut state));
            let slots: [[CM31; N]; 4] =
                core::array::from_fn(|_| core::array::from_fn(|_| cm31(&mut state)));
            let prepared = PreparedQm31Cm31Weights::<N>::new(&weights);
            let expected = qm31_cm31_dot4(&weights, [&slots[0], &slots[1], &slots[2], &slots[3]]);
            assert_eq!(
                qm31_cm31_dot4_prepared(&prepared, [&slots[0], &slots[1], &slots[2], &slots[3]],),
                expected
            );
        }

        for seed in 1..=16u64 {
            check::<0>(seed);
            check::<1>(seed);
            check::<4>(seed);
            check::<49>(seed);
            check::<257>(seed);
        }
    }

    #[test]
    fn prepared_geometric_weights_match_power_table_and_return_next_power() {
        let gamma = QM31 {
            c0: CM31::new(M31(17), M31(19)),
            c1: CM31::new(M31(23), M31(29)),
        };
        let powers = qm31_power_table::<49>(gamma);
        let (geometric, next) = PreparedQm31Cm31Weights::<49>::geometric(gamma);
        assert_eq!(geometric, PreparedQm31Cm31Weights::new(&powers));
        assert_eq!(next, gamma.pow(49));
    }

    #[test]
    fn prepared_byte_dot_matches_values_and_rejects_noncanonical_limbs() {
        const N: usize = 49;
        let mut state = 0x8f31_50a2_d192_ed03u64;
        let mut next = || {
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
        };
        let weights: [QM31; N] = core::array::from_fn(|_| QM31 {
            c0: CM31::new(next(), next()),
            c1: CM31::new(next(), next()),
        });
        let values: [[CM31; N]; 4] =
            core::array::from_fn(|_| core::array::from_fn(|_| CM31::new(next(), next())));
        let mut bytes = alloc::vec![0u8; 4 * N * 8];
        for (slot, slot_values) in values.iter().enumerate() {
            for (index, value) in slot_values.iter().enumerate() {
                value.write_le_bytes(&mut bytes[(slot * N + index) * 8..][..8]);
            }
        }
        let prepared = PreparedQm31Cm31Weights::new(&weights);
        assert_eq!(
            qm31_cm31_dot4_prepared_bytes(&prepared, &bytes),
            Some(qm31_cm31_dot4_prepared(
                &prepared,
                [&values[0], &values[1], &values[2], &values[3]],
            ))
        );
        assert_eq!(
            qm31_cm31_dot4_prepared_bytes(&prepared, &bytes[..bytes.len() - 1]),
            None
        );
        for offset in [0usize, 4, (N + 7) * 8 + 4, (4 * N - 1) * 8] {
            let mut corrupted = bytes.clone();
            corrupted[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                qm31_cm31_dot4_prepared_bytes(&prepared, &corrupted),
                None,
                "noncanonical limb at byte {offset} accepted"
            );
        }
    }

    #[test]
    fn lazy_qm31_m31_dot_matches_naive() {
        for len in [0usize, 1, 3, 4, 5, 16, 80] {
            let weights = (0..len)
                .map(|index| QM31 {
                    c0: CM31::new(M31(index as u32 * 97 + 3), M31(index as u32 * 193 + 5)),
                    c1: CM31::new(M31(index as u32 * 389 + 7), M31(index as u32 * 769 + 11)),
                })
                .collect::<alloc::vec::Vec<_>>();
            let values = (0..len)
                .map(|index| M31(index as u32 * 1_543 + 13))
                .collect::<alloc::vec::Vec<_>>();
            let naive = weights
                .iter()
                .zip(&values)
                .fold(QM31::ZERO, |sum, (weight, value)| {
                    sum.add(weight.mul_m31(*value))
                });
            assert_eq!(qm31_m31_dot(&weights, &values), naive);
            assert_eq!(qm31_m31_dot_eager_outer(&weights, &values), naive);
            assert_eq!(qm31_m31_dot_u128(&weights, &values), naive);
        }
    }

    #[test]
    fn fused_qm31_m31_dot4_matches_independent_and_naive_dots() {
        fn next(state: &mut u64) -> M31 {
            *state ^= *state >> 12;
            *state ^= *state << 25;
            *state ^= *state >> 27;
            M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
        }

        fn qm31(state: &mut u64) -> QM31 {
            QM31 {
                c0: CM31::new(next(state), next(state)),
                c1: CM31::new(next(state), next(state)),
            }
        }

        for seed in 1..=24u64 {
            for len in [0usize, 1, 3, 4, 5, 16, 49, 80, 257] {
                let mut state = seed
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .wrapping_add(len as u64 + 1);
                let weights = (0..len)
                    .map(|_| qm31(&mut state))
                    .collect::<alloc::vec::Vec<_>>();
                let slots: [alloc::vec::Vec<M31>; 4] =
                    core::array::from_fn(|_| (0..len).map(|_| next(&mut state)).collect());
                let fused = qm31_m31_dot4(&weights, [&slots[0], &slots[1], &slots[2], &slots[3]]);
                for slot in 0..4 {
                    let independent = qm31_m31_dot(&weights, &slots[slot]);
                    let naive = weights
                        .iter()
                        .zip(&slots[slot])
                        .fold(QM31::ZERO, |sum, (weight, value)| {
                            sum.add(weight.mul_m31(*value))
                        });
                    assert_eq!(
                        fused[slot], independent,
                        "seed={seed}, len={len}, slot={slot}"
                    );
                    assert_eq!(fused[slot], naive, "seed={seed}, len={len}, slot={slot}");
                }
            }
        }
    }

    #[test]
    fn prepared_m31_byte_dot4_matches_values_and_rejects_noncanonical_limbs() {
        const N: usize = 49;
        let mut state = 0x8f31_50a2_d192_ed03u64;
        let mut next = || {
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
        };
        let weights: [QM31; N] = core::array::from_fn(|_| QM31 {
            c0: CM31::new(next(), next()),
            c1: CM31::new(next(), next()),
        });
        let values: [[M31; N]; 4] = core::array::from_fn(|_| core::array::from_fn(|_| next()));
        let mut bytes = alloc::vec![0u8; 4 * N * 4];
        for (slot, slot_values) in values.iter().enumerate() {
            for (index, value) in slot_values.iter().enumerate() {
                bytes[(slot * N + index) * 4..][..4].copy_from_slice(&value.0.to_le_bytes());
            }
        }
        let expected = qm31_m31_dot4(&weights, [&values[0], &values[1], &values[2], &values[3]]);
        assert_eq!(
            qm31_m31_dot4_prepared_bytes(&weights, &bytes),
            Some(expected)
        );
        assert_eq!(
            qm31_m31_dot4_prepared_bytes(&weights, &bytes[..bytes.len() - 1]),
            None
        );
        for offset in (0..4 * N).map(|index| index * 4) {
            let mut corrupted = bytes.clone();
            corrupted[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                qm31_m31_dot4_prepared_bytes(&weights, &corrupted),
                None,
                "noncanonical limb at byte {offset} accepted"
            );
        }
        let mut high_bit = bytes;
        high_bit[4..8].copy_from_slice(&u32::MAX.to_le_bytes());
        assert_eq!(
            qm31_m31_dot4_prepared_bytes(&weights, &high_bit),
            None,
            "high-bit noncanonical M31 accepted"
        );
    }

    #[test]
    fn normalized_circle_line_fold_matches_cubic_coefficient_evaluation() {
        fn q(seed: u32) -> QM31 {
            QM31 {
                c0: CM31::new(M31(seed % P), M31((seed * 3 + 1) % P)),
                c1: CM31::new(M31((seed * 5 + 2) % P), M31((seed * 7 + 3) % P)),
            }
        }

        for seed in 1..=32u32 {
            let x = M31(17 + seed);
            let y = M31(97 + 3 * seed);
            let inv_2x = x.double().inv();
            let inv_2y = y.double().inv();
            let coefficients = [q(seed), q(seed + 11), q(seed + 23), q(seed + 37)];
            let evaluate = |x_value: M31, y_value: M31| {
                coefficients[0]
                    .add(coefficients[1].mul_m31(y_value))
                    .add(coefficients[2].mul_m31(x_value))
                    .add(coefficients[3].mul_m31(x_value.mul(y_value)))
            };
            let minus_x = M31::ZERO.sub(x);
            let minus_y = M31::ZERO.sub(y);
            let values = [
                evaluate(x, y),
                evaluate(x, minus_y),
                evaluate(minus_x, minus_y),
                evaluate(minus_x, y),
            ];
            let alpha = q(seed + 101);
            let expected = coefficients[0]
                .add(alpha.mul(coefficients[1]))
                .add(alpha.square().mul(coefficients[2]))
                .add(alpha.square().mul(alpha).mul(coefficients[3]));
            assert_eq!(
                qm31_circle_to_line_fold4(values, alpha, inv_2x, inv_2y),
                expected,
                "seed={seed}"
            );

            // The raw inverse-butterfly convention omits both halves and is
            // therefore exactly four times the normalized coefficient fold.
            let raw_positive = values[0]
                .add(values[1])
                .add(alpha.mul(values[0].sub(values[1]).mul_m31(y.inv())));
            let raw_negative = values[2]
                .add(values[3])
                .add(alpha.mul(values[2].sub(values[3]).mul_m31(M31::ZERO.sub(y.inv()))));
            let raw = raw_positive.add(raw_negative).add(
                alpha
                    .square()
                    .mul(raw_positive.sub(raw_negative).mul_m31(x.inv())),
            );
            assert_eq!(raw.half().half(), expected, "raw normalization seed={seed}");
        }
    }

    #[test]
    fn lazy_qm31_dot_matches_naive() {
        for len in [0usize, 1, 3, 4, 5, 20, 80] {
            let values_for = |salt: u32| {
                (0..len)
                    .map(|index| QM31 {
                        c0: CM31::new(
                            M31((index as u32 * 97 + salt) % P),
                            M31((index as u32 * 193 + salt + 2) % P),
                        ),
                        c1: CM31::new(
                            M31((index as u32 * 389 + salt + 4) % P),
                            M31((index as u32 * 769 + salt + 6) % P),
                        ),
                    })
                    .collect::<alloc::vec::Vec<_>>()
            };
            let weights = values_for(3);
            let values = values_for(11);
            let naive = weights
                .iter()
                .zip(&values)
                .fold(QM31::ZERO, |sum, (weight, value)| {
                    sum.add(weight.mul(*value))
                });
            assert_eq!(qm31_dot(&weights, &values), naive);
        }
    }
}
