use std::io::{self, Write};

use stwo::core::circle::{CirclePointIndex, Coset};
use stwo::core::fields::m31::{M31, P};
use stwo::core::fields::qm31::SecureField;
use stwo::core::fri::fold_line;
use stwo::core::poly::line::{LineDomain, LinePoly};
use stwo::core::utils::{bit_reverse, bit_reverse_index};
use stwo::prover::backend::CpuBackend;
use stwo::prover::line::LineEvaluation;

const DOMAIN: &[u8] = b"aspis:host:stwo-line-fri-corpus:v1";
const GROUP_MASK: usize = (1usize << 31) - 1;

#[derive(Clone, Copy)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
        self.0
    }

    fn m31(&mut self) -> M31 {
        M31((self.next() as u32) % P)
    }

    fn qm31(&mut self) -> SecureField {
        SecureField::from_m31(self.m31(), self.m31(), self.m31(), self.m31())
    }
}

fn q(values: [u32; 4]) -> SecureField {
    SecureField::from_u32_unchecked(values[0], values[1], values[2], values[3])
}

fn coords(value: SecureField) -> [u32; 4] {
    value.to_m31_array().map(|value| value.0)
}

fn evaluate(coefficients: &[SecureField], domain: LineDomain) -> Vec<SecureField> {
    let poly = LinePoly::new(coefficients.to_vec());
    (0..domain.size())
        .map(|index| {
            let natural = bit_reverse_index(index, domain.log_size());
            poly.eval_at_point(domain.at(natural).into())
        })
        .collect()
}

fn interpolate(domain: LineDomain, evaluations: &[SecureField]) -> Vec<SecureField> {
    LineEvaluation::<CpuBackend>::new(domain, evaluations.iter().copied().collect())
        .interpolate()
        .to_vec()
}

fn fold_queries(positions: &[usize], folds: u32) -> Vec<usize> {
    let mut positions = positions.to_vec();
    positions.sort_unstable();
    positions.dedup();
    let mut result = Vec::new();
    for position in positions {
        let position = position >> folds;
        if result.last().copied() != Some(position) {
            result.push(position);
        }
    }
    result
}

fn put_u32(bytes: &mut Vec<u8>, value: usize) {
    bytes.extend_from_slice(&(value as u32).to_le_bytes());
}

fn put_q(bytes: &mut Vec<u8>, value: SecureField) {
    for coordinate in value.to_m31_array() {
        bytes.extend_from_slice(&coordinate.0.to_le_bytes());
    }
}

fn put_qs(bytes: &mut Vec<u8>, values: &[SecureField]) {
    put_u32(bytes, values.len());
    for &value in values {
        put_q(bytes, value);
    }
}

fn put_usizes(bytes: &mut Vec<u8>, values: &[usize]) {
    put_u32(bytes, values.len());
    for &value in values {
        put_u32(bytes, value);
    }
}

fn corpus() -> Vec<u8> {
    let mut bytes = DOMAIN.to_vec();
    let mut rng = Rng(0x4c49_4e45_4652_4934);
    for case in 0..12usize {
        let log_size = 2 + (case as u32 % 7);
        let initial_index = if case % 3 == 0 {
            1usize << (31 - (log_size + 2))
        } else {
            (rng.next() as usize & GROUP_MASK) | 1
        };
        let mut domain = LineDomain::new(Coset::new(CirclePointIndex(initial_index), log_size));
        let mut coefficients = (0..domain.size()).map(|_| rng.qm31()).collect::<Vec<_>>();
        let mut evaluations = evaluate(&coefficients, domain);
        let mut queries = vec![
            0,
            1,
            2,
            3,
            domain.size() / 3,
            domain.size() / 2,
            domain.size() - 1,
            rng.next() as usize % domain.size(),
            rng.next() as usize % domain.size(),
        ];
        queries.sort_unstable();
        queries.dedup();

        put_u32(&mut bytes, case);
        put_u32(&mut bytes, log_size as usize);
        put_u32(&mut bytes, initial_index);
        put_qs(&mut bytes, &coefficients);
        put_qs(&mut bytes, &evaluations);
        put_usizes(&mut bytes, &queries);
        for index in 0..domain.size() {
            let natural = bit_reverse_index(index, domain.log_size());
            put_u32(&mut bytes, domain.at(natural).0 as usize);
        }

        while domain.log_size() >= 2 {
            let alpha = rng.qm31();
            put_q(&mut bytes, alpha);
            let (first_domain, first) = fold_line(&evaluations, domain, alpha);
            let (next_domain, next) = fold_line(&first, first_domain, alpha * alpha);
            coefficients = interpolate(next_domain, &next);
            evaluations = next;
            domain = next_domain;
            queries = fold_queries(&queries, 2);

            put_u32(&mut bytes, domain.log_size() as usize);
            put_u32(&mut bytes, domain.coset().initial_index.0);
            put_qs(&mut bytes, &coefficients);
            put_qs(&mut bytes, &evaluations);
            put_usizes(&mut bytes, &queries);
        }
    }
    bytes
}

fn show() {
    let domain = LineDomain::new(Coset::half_odds(3));
    let natural = [
        q([1, 2, 3, 4]),
        q([5, 7, 11, 13]),
        q([17, 19, 23, 29]),
        q([31, 37, 41, 43]),
        q([47, 53, 59, 61]),
        q([67, 71, 73, 79]),
        q([83, 89, 97, 101]),
        q([103, 107, 109, 113]),
    ];
    let mut stored = natural.to_vec();
    bit_reverse(&mut stored);
    let alpha = q([127, 131, 137, 139]);
    let evaluations = evaluate(&stored, domain);
    let (domain1, fold1) = fold_line(&evaluations, domain, alpha);
    let (domain2, fold2) = fold_line(&fold1, domain1, alpha * alpha);
    let folded_coefficients = interpolate(domain2, &fold2);

    println!("x={:?}", (0..domain.size()).map(|i| domain.at(bit_reverse_index(i, 3)).0).collect::<Vec<_>>());
    println!("eval={:?}", evaluations.into_iter().map(coords).collect::<Vec<_>>());
    println!("fold1={:?}", fold1.into_iter().map(coords).collect::<Vec<_>>());
    println!("fold2={:?}", fold2.into_iter().map(coords).collect::<Vec<_>>());
    println!("coeff2={:?}", folded_coefficients.into_iter().map(coords).collect::<Vec<_>>());
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("show") {
        show();
    } else {
        io::stdout().write_all(&corpus()).unwrap();
    }
}
