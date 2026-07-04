//! M31 -> CM31 -> QM31 field tower.
//!
//! Kernel choices are the Phase 2 winners, built in from the start:
//! - M31 reduction: `reference_canonical` (mask/shift double-fold, canonical output)
//! - CM31/QM31 multiplication: Karatsuba (3 submuls per level)
//! - lift policy: `late_lift_qm31` — committed layer-0 values stay CM31 and are
//!   lifted only when they meet a QM31 challenge; mixed-width kernels
//!   (`QM31 * CM31`) avoid full 4-limb products where one operand is base.

/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;

/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);

/// 1/2 in M31 (P is odd, so (P+1)/2 = 2^30).
pub const M31_HALF: M31 = M31(0x4000_0000);

#[inline(always)]
fn reduce_u64(x: u64) -> u32 {
    // reference_canonical: two mask/shift folds bring any x < 2^62 to [0, 2^31],
    // then one conditional subtract canonicalizes.
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

    #[inline(always)]
    pub fn double(self) -> M31 {
        self.add(self)
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

    pub fn pow(self, mut exp: u64) -> CM31 {
        let mut base = self;
        let mut acc = CM31::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            exp >>= 1;
        }
        acc
    }

    /// Inverse via conjugate/norm: one M31 inversion + a few muls.
    pub fn inv(self) -> CM31 {
        let norm = self.a.mul(self.a).add(self.b.mul(self.b));
        let inv_norm = norm.inv();
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

/// Montgomery batch inversion over CM31: one field inversion for the whole
/// batch plus 3(n-1) multiplications. This is the `round_batch_inversion`
/// kernel: the verifier gathers every fold denominator of a round and inverts
/// them together. Panics if any element is zero (fold denominators are coset
/// points, never zero).
pub fn cm31_batch_inverse(values: &[CM31], out: &mut [CM31]) {
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
    let mut inv = acc.inv();
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
    }

    #[test]
    fn batch_inverse_matches_individual() {
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
}
