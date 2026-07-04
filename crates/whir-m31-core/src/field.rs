use core::fmt::{Debug, Formatter};
use core::ops::{Add, Mul, Neg, Sub};

pub const M31_MODULUS: u32 = 0x7fff_ffff;
pub const M31_MODULUS_U64: u64 = M31_MODULUS as u64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LiftPolicy {
    EarlyQm31,
    LateQm31,
}

#[derive(Clone, Copy, Default, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct M31(u32);

#[derive(Clone, Copy, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Cm31 {
    pub c0: M31,
    pub c1: M31,
}

#[derive(Clone, Copy, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Qm31 {
    pub c0: Cm31,
    pub c1: Cm31,
}

pub type CM31 = Cm31;
pub type QM31 = Qm31;

impl Debug for Cm31 {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "Cm31({}, {})", self.c0.as_u32(), self.c1.as_u32())
    }
}

impl Debug for Qm31 {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Qm31({}, {}, {}, {})",
            self.c0.c0.as_u32(),
            self.c0.c1.as_u32(),
            self.c1.c0.as_u32(),
            self.c1.c1.as_u32()
        )
    }
}

impl M31 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    pub const fn from_u32_unchecked(value: u32) -> Self {
        Self(value)
    }

    pub fn from_canonical_u32(value: u32) -> Option<Self> {
        (value < M31_MODULUS).then_some(Self(value))
    }

    pub fn from_u64_reduce(value: u64) -> Self {
        Self(reduce_m31(value))
    }

    pub const fn as_u32(self) -> u32 {
        self.0
    }

    pub fn square(self) -> Self {
        Self(reduce_m31_square(self.0))
    }

    pub fn inverse(self) -> Self {
        assert!(self != Self::ZERO, "zero has no inverse");
        pow2147483645(self)
    }
}

impl From<u32> for M31 {
    fn from(value: u32) -> Self {
        Self::from_u64_reduce(value as u64)
    }
}

impl From<usize> for M31 {
    fn from(value: usize) -> Self {
        Self::from_u64_reduce(value as u64)
    }
}

impl Add for M31 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.0 + rhs.0;
        if sum >= M31_MODULUS {
            Self(sum - M31_MODULUS)
        } else {
            Self(sum)
        }
    }
}

impl Neg for M31 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self == Self::ZERO {
            self
        } else {
            Self(M31_MODULUS - self.0)
        }
    }
}

impl Sub for M31 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.0 >= rhs.0 {
            Self(self.0 - rhs.0)
        } else {
            Self(self.0 + M31_MODULUS - rhs.0)
        }
    }
}

impl Mul for M31 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(reduce_m31(self.0 as u64 * rhs.0 as u64))
    }
}

impl Cm31 {
    pub const ZERO: Self = Self::from_m31(M31::ZERO, M31::ZERO);
    pub const ONE: Self = Self::from_m31(M31::ONE, M31::ZERO);

    pub const fn from_m31(c0: M31, c1: M31) -> Self {
        Self { c0, c1 }
    }

    pub const fn from_u32_unchecked(c0: u32, c1: u32) -> Self {
        Self::from_m31(M31::from_u32_unchecked(c0), M31::from_u32_unchecked(c1))
    }

    pub fn square(self) -> Self {
        let a2 = self.c0.square();
        let b2 = self.c1.square();
        let ab = self.c0 * self.c1;
        Self {
            c0: a2 - b2,
            c1: ab + ab,
        }
    }

    pub fn conjugate(self) -> Self {
        Self {
            c0: self.c0,
            c1: -self.c1,
        }
    }

    pub fn norm(self) -> M31 {
        self.c0.square() + self.c1.square()
    }

    pub fn mul_schoolbook(self, rhs: Self) -> Self {
        let ac = self.c0 * rhs.c0;
        let bd = self.c1 * rhs.c1;
        let ad = self.c0 * rhs.c1;
        let bc = self.c1 * rhs.c0;
        Self {
            c0: ac - bd,
            c1: ad + bc,
        }
    }

    pub fn mul_karatsuba(self, rhs: Self) -> Self {
        let z0 = self.c0 * rhs.c0;
        let z2 = self.c1 * rhs.c1;
        let z1 = (self.c0 + self.c1) * (rhs.c0 + rhs.c1) - z0 - z2;
        Self {
            c0: z0 - z2,
            c1: z1,
        }
    }

    pub fn mul_m31(self, rhs: M31) -> Self {
        Self {
            c0: self.c0 * rhs,
            c1: self.c1 * rhs,
        }
    }

    pub fn inverse(self) -> Self {
        let inv = self.norm().inverse();
        self.conjugate().mul_m31(inv)
    }
}

impl From<M31> for Cm31 {
    fn from(value: M31) -> Self {
        Self::from_m31(value, M31::ZERO)
    }
}

impl Add for Cm31 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
        }
    }
}

impl Neg for Cm31 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            c0: -self.c0,
            c1: -self.c1,
        }
    }
}

impl Sub for Cm31 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
        }
    }
}

impl Mul for Cm31 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_karatsuba(rhs)
    }
}

pub const QM31_NON_RESIDUE: Cm31 = Cm31::from_u32_unchecked(2, 1);

impl Qm31 {
    pub const ZERO: Self = Self::from_cm31(Cm31::ZERO, Cm31::ZERO);
    pub const ONE: Self = Self::from_cm31(Cm31::ONE, Cm31::ZERO);

    pub const fn from_cm31(c0: Cm31, c1: Cm31) -> Self {
        Self { c0, c1 }
    }

    pub const fn from_u32_unchecked(a: u32, b: u32, c: u32, d: u32) -> Self {
        Self {
            c0: Cm31::from_u32_unchecked(a, b),
            c1: Cm31::from_u32_unchecked(c, d),
        }
    }

    pub fn from_m31_array(limbs: [M31; 4]) -> Self {
        Self {
            c0: Cm31::from_m31(limbs[0], limbs[1]),
            c1: Cm31::from_m31(limbs[2], limbs[3]),
        }
    }

    pub fn to_m31_array(self) -> [M31; 4] {
        [self.c0.c0, self.c0.c1, self.c1.c0, self.c1.c1]
    }

    pub fn square(self) -> Self {
        let a2 = self.c0.square();
        let b2 = self.c1.square();
        let ab = self.c0 * self.c1;
        Self {
            c0: a2 + QM31_NON_RESIDUE * b2,
            c1: ab + ab,
        }
    }

    pub fn conjugate(self) -> Self {
        Self {
            c0: self.c0,
            c1: -self.c1,
        }
    }

    pub fn mul_reference(self, rhs: Self) -> Self {
        let ac = self.c0 * rhs.c0;
        let bd = self.c1 * rhs.c1;
        let ad = self.c0 * rhs.c1;
        let bc = self.c1 * rhs.c0;
        Self {
            c0: ac + QM31_NON_RESIDUE * bd,
            c1: ad + bc,
        }
    }

    pub fn mul_optimized(self, rhs: Self) -> Self {
        let z0 = self.c0 * rhs.c0;
        let z2 = self.c1 * rhs.c1;
        let z1 = (self.c0 + self.c1) * (rhs.c0 + rhs.c1) - z0 - z2;
        Self {
            c0: z0 + QM31_NON_RESIDUE * z2,
            c1: z1,
        }
    }

    pub fn mul_cm31(self, rhs: Cm31) -> Self {
        Self {
            c0: self.c0 * rhs,
            c1: self.c1 * rhs,
        }
    }

    pub fn mul_m31(self, rhs: M31) -> Self {
        self.mul_cm31(Cm31::from(rhs))
    }

    pub fn inverse(self) -> Self {
        let b2 = self.c1.square();
        let denom = self.c0.square() - (QM31_NON_RESIDUE * b2);
        let inv = denom.inverse();
        Self {
            c0: self.c0 * inv,
            c1: (-self.c1) * inv,
        }
    }
}

impl From<M31> for Qm31 {
    fn from(value: M31) -> Self {
        Self::from_cm31(Cm31::from(value), Cm31::ZERO)
    }
}

impl From<Cm31> for Qm31 {
    fn from(value: Cm31) -> Self {
        Self::from_cm31(value, Cm31::ZERO)
    }
}

impl Add for Qm31 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
        }
    }
}

impl Neg for Qm31 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            c0: -self.c0,
            c1: -self.c1,
        }
    }
}

impl Sub for Qm31 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
        }
    }
}

impl Mul for Qm31 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_optimized(rhs)
    }
}

pub fn local_interpolant_m31(values: [M31; 4]) -> [M31; 4] {
    let a00 = values[0];
    let a10 = values[1];
    let a01 = values[2];
    let a11 = values[3];
    [a00, a10 - a00, a01 - a00, a11 - a10 - a01 + a00]
}

pub fn local_interpolant_qm31(values: [Qm31; 4]) -> [Qm31; 4] {
    let a00 = values[0];
    let a10 = values[1];
    let a01 = values[2];
    let a11 = values[3];
    [a00, a10 - a00, a01 - a00, a11 - a10 - a01 + a00]
}

pub fn eval_local_block_m31(coeffs: [M31; 4], x: Qm31, y: Qm31, policy: LiftPolicy) -> Qm31 {
    match policy {
        LiftPolicy::EarlyQm31 => {
            let c0 = Qm31::from(coeffs[0]);
            let cx = Qm31::from(coeffs[1]);
            let cy = Qm31::from(coeffs[2]);
            let cxy = Qm31::from(coeffs[3]);
            c0 + x * cx + y * cy + (x * y) * cxy
        }
        LiftPolicy::LateQm31 => {
            Qm31::from(coeffs[0])
                + x.mul_m31(coeffs[1])
                + y.mul_m31(coeffs[2])
                + (x * y).mul_m31(coeffs[3])
        }
    }
}

pub fn eval_local_block_qm31(coeffs: [Qm31; 4], x: Qm31, y: Qm31) -> Qm31 {
    coeffs[0] + x * coeffs[1] + y * coeffs[2] + (x * y) * coeffs[3]
}

pub fn block_value_from_qm31_coeffs(coeffs: [Qm31; 4], offset: usize) -> Qm31 {
    let x = if offset & 0x1 == 0 {
        Qm31::ZERO
    } else {
        Qm31::ONE
    };
    let y = if offset & 0x2 == 0 {
        Qm31::ZERO
    } else {
        Qm31::ONE
    };
    eval_local_block_qm31(coeffs, x, y)
}

fn reduce_m31_square(value: u32) -> u32 {
    reduce_m31(value as u64 * value as u64)
}

fn reduce_m31(value: u64) -> u32 {
    let mut folded = value;
    while folded > (M31_MODULUS_U64 << 1) {
        folded = (folded & M31_MODULUS_U64) + (folded >> 31);
    }
    if folded >= M31_MODULUS_U64 {
        folded -= M31_MODULUS_U64;
    }
    if folded >= M31_MODULUS_U64 {
        folded -= M31_MODULUS_U64;
    }
    folded as u32
}

fn pow2147483645(v: M31) -> M31 {
    let t0 = sqn::<2>(v) * v;
    let t1 = sqn::<1>(t0) * t0;
    let t2 = sqn::<3>(t1) * t0;
    let t3 = sqn::<1>(t2) * t0;
    let t4 = sqn::<8>(t3) * t3;
    let t5 = sqn::<8>(t4) * t3;
    sqn::<7>(t5) * t2
}

fn sqn<const N: usize>(mut value: M31) -> M31 {
    let mut i = 0;
    while i < N {
        value = value.square();
        i += 1;
    }
    value
}

#[cfg(test)]
mod tests {
    use super::*;

    fn next_word(state: &mut u64) -> u64 {
        *state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        *state
    }

    #[test]
    fn direct_reduction_matches_reference_modulo() {
        let mut state = 1_u64;
        for _ in 0..20_000 {
            let a = next_word(&mut state) & ((1_u64 << 31) - 1);
            let b = next_word(&mut state) & ((1_u64 << 31) - 1);
            let value = a * b;
            assert_eq!(reduce_m31(value), (value % M31_MODULUS_U64) as u32);
        }
    }

    #[test]
    fn cm31_karatsuba_matches_schoolbook() {
        let mut state = 7_u64;
        for _ in 0..10_000 {
            let a = Cm31::from_u32_unchecked(
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
            );
            let b = Cm31::from_u32_unchecked(
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
            );
            assert_eq!(a.mul_karatsuba(b), a.mul_schoolbook(b));
        }
    }

    #[test]
    fn qm31_optimized_matches_reference() {
        let mut state = 19_u64;
        for _ in 0..8_000 {
            let a = Qm31::from_u32_unchecked(
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
            );
            let b = Qm31::from_u32_unchecked(
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
                (next_word(&mut state) % M31_MODULUS_U64) as u32,
            );
            assert_eq!(a.mul_optimized(b), a.mul_reference(b));
        }
    }

    #[test]
    fn conjugation_and_norm_behave() {
        let value = Cm31::from_u32_unchecked(11, 17);
        let conj = value.conjugate();
        assert_eq!(value * conj, Cm31::from(value.norm()));

        let secure = Qm31::from_u32_unchecked(5, 7, 9, 13);
        let secure_conj = secure.conjugate();
        let denom = secure.c0.square() - (QM31_NON_RESIDUE * secure.c1.square());
        assert_eq!(secure * secure_conj, Qm31::from(denom));
    }

    #[test]
    fn inverse_round_trips() {
        let a = M31::from(19u32);
        assert_eq!(a * a.inverse(), M31::ONE);

        let b = Cm31::from_u32_unchecked(3, 9);
        assert_eq!(b * b.inverse(), Cm31::ONE);

        let c = Qm31::from_u32_unchecked(3, 5, 7, 9);
        assert_eq!(c * c.inverse(), Qm31::ONE);
    }

    #[test]
    fn local_interpolant_matches_raw_values_on_booleans() {
        let raw = [
            Qm31::from_u32_unchecked(1, 0, 0, 0),
            Qm31::from_u32_unchecked(2, 0, 0, 0),
            Qm31::from_u32_unchecked(3, 0, 0, 0),
            Qm31::from_u32_unchecked(5, 0, 0, 0),
        ];
        let coeffs = local_interpolant_qm31(raw);
        for index in 0..4 {
            assert_eq!(block_value_from_qm31_coeffs(coeffs, index), raw[index]);
        }
    }

    #[test]
    fn late_lift_matches_early_lift_for_m31_blocks() {
        let coeffs = local_interpolant_m31([
            M31::from(3u32),
            M31::from(11u32),
            M31::from(19u32),
            M31::from(23u32),
        ]);
        let x = Qm31::from_u32_unchecked(5, 7, 9, 13);
        let y = Qm31::from_u32_unchecked(17, 19, 29, 31);
        assert_eq!(
            eval_local_block_m31(coeffs, x, y, LiftPolicy::LateQm31),
            eval_local_block_m31(coeffs, x, y, LiftPolicy::EarlyQm31)
        );
    }
}
