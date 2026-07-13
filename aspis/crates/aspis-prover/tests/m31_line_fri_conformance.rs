#[path = "support/m31_line_fri_reference.rs"]
mod line_fri;

use aspis_core::field::{CM31, M31, P, QM31};
use line_fri::{
    bit_reverse, bit_reverse_index, evaluate_line_poly, evaluate_on_domain,
    fold_adjacent_natural_arity4, fold_line, fold_line_arity4, fold_line_coefficients_arity4,
    fold_line_fiber4, fold_queries, lift, scale, LineDomain, STWO_LINE_FRI_CORPUS_DOMAIN,
    STWO_REFERENCE_COMMIT,
};
use sha2::{Digest, Sha256};

const GROUP_MASK: usize = (1usize << 31) - 1;
const OFFICIAL_CORPUS_SHA256: [u8; 32] = [
    0x62, 0x3d, 0xf4, 0x4f, 0xe1, 0xd5, 0xf9, 0xc5, 0x09, 0x0e, 0x2b, 0x13, 0x01, 0x87, 0x8f, 0x43,
    0x08, 0xf1, 0xc6, 0x03, 0x03, 0x14, 0xc5, 0x15, 0x96, 0x4e, 0x6b, 0x6e, 0x91, 0x88, 0x01, 0xd8,
];

const OFFICIAL_X_BIT_REVERSED: [u32; 8] = [
    1_179_735_656,
    967_747_991,
    1_241_207_368,
    906_276_279,
    1_415_090_252,
    732_393_395,
    2_112_881_577,
    34_602_070,
];
const OFFICIAL_EVALUATIONS: [[u32; 4]; 8] = [
    [2_050_460_445, 1_621_393_214, 987_369_631, 182_601_986],
    [881_735_737, 1_347_325_488, 1_457_813_322, 1_358_185_272],
    [2_144_020_592, 1_959_998_540, 1_822_144_424, 1_397_437_748],
    [1_372_394_555, 1_520_680_523, 35_373_177, 1_364_737_696],
    [1_407_536_563, 1_500_747_131, 2_031_962_867, 1_578_661_056],
    [1_057_190_745, 1_409_218_935, 1_933_881_962, 1_080_251_264],
    [1_058_194_856, 282_106_502, 883_008_744, 252_189_861],
    [765_884_750, 1_095_947_918, 1_585_864_132, 1_375_869_737],
];
const OFFICIAL_FOLD1: [[u32; 4]; 4] = [
    [1_338_831_821, 706_543_085, 1_523_944_011, 46_017_266],
    [2_000_472_756, 558_988_542, 399_535_224, 731_127_624],
    [1_074_422_920, 1_921_025_455, 1_349_044_097, 156_763_639],
    [2_028_689_916, 1_108_473_140, 1_022_439_234, 1_213_613_118],
];
const OFFICIAL_FOLD2: [[u32; 4]; 2] = [
    [1_791_673_657, 156_816_650, 2_000_504_088, 2_112_974_310],
    [153_418_649, 1_165_133_557, 1_613_259_006, 1_640_413_761],
];
const OFFICIAL_FOLDED_COEFFICIENTS: [[u32; 4]; 2] = [
    [972_546_153, 1_734_716_927, 1_806_881_547, 802_952_212],
    [1_691_378_085, 654_984_166, 1_913_460_500, 1_506_974_762],
];

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

    fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m31(), self.m31()),
            c1: CM31::new(self.m31(), self.m31()),
        }
    }
}

fn q(values: [u32; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31(values[0]), M31(values[1])),
        c1: CM31::new(M31(values[2]), M31(values[3])),
    }
}

fn coordinates(value: QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

fn put_u32(bytes: &mut Vec<u8>, value: usize) {
    bytes.extend_from_slice(&(value as u32).to_le_bytes());
}

fn put_q(bytes: &mut Vec<u8>, value: QM31) {
    let mut encoded = [0u8; 16];
    value.write_le_bytes(&mut encoded);
    bytes.extend_from_slice(&encoded);
}

fn put_qs(bytes: &mut Vec<u8>, values: &[QM31]) {
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

/// Byte-for-byte reproduction of a corpus generated with official Stwo at
/// `STWO_REFERENCE_COMMIT`. The official generator evaluated `LinePoly`, ran
/// `core::fri::fold_line` twice per round, and interpolated every result.
fn official_corpus_bytes() -> Vec<u8> {
    let mut bytes = STWO_LINE_FRI_CORPUS_DOMAIN.to_vec();
    let mut rng = Rng(0x4c49_4e45_4652_4934);
    for case in 0..12usize {
        let log_size = 2 + (case as u32 % 7);
        let initial_index = if case % 3 == 0 {
            1usize << (31 - (log_size + 2))
        } else {
            (rng.next() as usize & GROUP_MASK) | 1
        };
        let mut domain = LineDomain::new(initial_index, log_size);
        let mut coefficients = (0..domain.size()).map(|_| rng.qm31()).collect::<Vec<_>>();
        let mut evaluations = evaluate_on_domain(&coefficients, domain);
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
            let (next_domain, next) = fold_line_arity4(&evaluations, domain, alpha);
            coefficients = fold_line_coefficients_arity4(&coefficients, alpha);
            evaluations = next;
            domain = next_domain;
            queries = fold_queries(&queries, domain.log_size() + 2, 2);

            put_u32(&mut bytes, domain.log_size() as usize);
            put_u32(&mut bytes, domain.initial_index());
            put_qs(&mut bytes, &coefficients);
            put_qs(&mut bytes, &evaluations);
            put_usizes(&mut bytes, &queries);
        }
    }
    bytes
}

#[test]
fn official_stwo_vectors_pin_domain_folds_interpolation_and_full_corpus() {
    assert_eq!(STWO_REFERENCE_COMMIT.len(), 40);
    let domain = LineDomain::half_odds(3);
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
    let evaluations = evaluate_on_domain(&stored, domain);
    let (domain1, fold1) = fold_line(&evaluations, domain, alpha);
    let (domain2, fold2) = fold_line(&fold1, domain1, alpha.square());
    let folded_coefficients = fold_line_coefficients_arity4(&stored, alpha);

    assert_eq!(
        (0..domain.size())
            .map(|index| domain.at(bit_reverse_index(index, 3)).0)
            .collect::<Vec<_>>(),
        OFFICIAL_X_BIT_REVERSED
    );
    assert_eq!(
        evaluations
            .iter()
            .copied()
            .map(coordinates)
            .collect::<Vec<_>>(),
        OFFICIAL_EVALUATIONS
    );
    assert_eq!(
        fold1.iter().copied().map(coordinates).collect::<Vec<_>>(),
        OFFICIAL_FOLD1
    );
    assert_eq!(
        fold2.iter().copied().map(coordinates).collect::<Vec<_>>(),
        OFFICIAL_FOLD2
    );
    assert_eq!(
        folded_coefficients
            .iter()
            .copied()
            .map(coordinates)
            .collect::<Vec<_>>(),
        OFFICIAL_FOLDED_COEFFICIENTS
    );
    assert_eq!(evaluate_on_domain(&folded_coefficients, domain2), fold2);

    // Mechanical bridge to Aspis's unchanged adjacent low-bit MLE fold.
    let natural_folded = fold_adjacent_natural_arity4(&natural, alpha);
    let mut bridged = natural_folded;
    bit_reverse(&mut bridged);
    assert_eq!(folded_coefficients, scale(&bridged, M31(4)));

    assert_eq!(
        <[u8; 32]>::from(Sha256::digest(official_corpus_bytes())),
        OFFICIAL_CORPUS_SHA256
    );
}

#[test]
fn line_domain_boundaries_match_doubling_and_reject_duplicate_x_cosets() {
    for log_size in [0u32, 1, 2, 3, 8, 29] {
        let domain = LineDomain::half_odds(log_size);
        assert_eq!(domain.size(), 1usize << log_size);
        let sample_count = core::cmp::min(domain.size(), 16);
        let mut sampled = Vec::new();
        for index in 0..sample_count {
            let x = domain.at(index);
            assert!(!sampled.contains(&x));
            sampled.push(x);
            if log_size > 0 {
                let square = x.mul(x);
                assert_eq!(domain.double().at(index), square.add(square).sub(M31::ONE));
            }
        }
    }

    let invalid = std::panic::catch_unwind(|| LineDomain::new(0, 2));
    assert!(invalid.is_err());
}

#[test]
fn randomized_arity4_bridge_queries_and_terminal_polynomial_conform() {
    let mut rng = Rng(0x5354_574f_4c49_4e45);
    for case in 0..48usize {
        let log_size = 2 + (case as u32 % 7);
        let initial_index = if case % 4 == 0 {
            1usize << (31 - (log_size + 2))
        } else {
            (rng.next() as usize & GROUP_MASK) | 1
        };
        let mut domain = LineDomain::new(initial_index, log_size);
        let mut natural = (0..domain.size()).map(|_| rng.qm31()).collect::<Vec<_>>();
        let mut stored = natural.clone();
        bit_reverse(&mut stored);
        let mut evaluations = evaluate_on_domain(&stored, domain);
        let mut queries = vec![
            0,
            1,
            2,
            3,
            domain.size() / 2,
            domain.size() - 1,
            rng.next() as usize % domain.size(),
            rng.next() as usize % domain.size(),
        ];
        queries.sort_unstable();
        queries.dedup();
        let mut raw_scale = M31::ONE;
        let mut round = 0usize;

        while domain.log_size() >= 2 {
            let alpha = match (case + round) % 4 {
                0 => QM31::ZERO,
                1 => QM31::ONE,
                _ => rng.qm31(),
            };
            let previous_domain = domain;
            let previous_evaluations = evaluations.clone();
            let (next_domain, next_evaluations) =
                fold_line_arity4(&previous_evaluations, previous_domain, alpha);

            for (index, values) in previous_evaluations.chunks_exact(4).enumerate() {
                assert_eq!(
                    fold_line_fiber4(
                        values.try_into().unwrap(),
                        previous_domain,
                        index * 4,
                        alpha,
                    ),
                    next_evaluations[index]
                );
            }

            stored = fold_line_coefficients_arity4(&stored, alpha);
            natural = fold_adjacent_natural_arity4(&natural, alpha);
            raw_scale = raw_scale.mul(M31(4));
            let mut bridged = natural.clone();
            bit_reverse(&mut bridged);
            bridged = scale(&bridged, raw_scale);
            assert_eq!(
                stored, bridged,
                "storage bridge failed in case {case}, round {round}"
            );
            assert_eq!(
                evaluate_on_domain(&stored, next_domain),
                next_evaluations,
                "coefficient/evaluation fold failed in case {case}, round {round}"
            );

            let next_queries = fold_queries(&queries, previous_domain.log_size(), 2);
            for &query in &next_queries {
                assert_eq!(
                    fold_line_fiber4(
                        previous_evaluations[query * 4..query * 4 + 4]
                            .try_into()
                            .unwrap(),
                        previous_domain,
                        query * 4,
                        alpha,
                    ),
                    next_evaluations[query]
                );
            }

            domain = next_domain;
            evaluations = next_evaluations;
            queries = next_queries;
            round += 1;
        }

        for &query in &queries {
            let natural_index = bit_reverse_index(query, domain.log_size());
            assert_eq!(
                evaluations[query],
                evaluate_line_poly(&stored, lift(domain.at(natural_index)))
            );
        }
        assert_eq!(evaluations, evaluate_on_domain(&stored, domain));
    }
}
