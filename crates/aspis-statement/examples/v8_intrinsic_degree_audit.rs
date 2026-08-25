//! Focused V8 gate for the intrinsic per-variable degree of the exact
//! production atomic-v3 unmasked terminal.
//!
//! This is not a new prover or arithmetization. It supplies a concrete family
//! of committed affine column MLEs to the production terminal, restricts each
//! sumcheck variable to `t = 0, 1, ...`, and computes exact forward
//! differences in QM31. Together with the source upper bound of 27, a nonzero
//! 27th difference is an executable lower-bound witness.

use aspis_core::field::{CM31, M31, QM31};
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_selected_constraint_composition_compiled_v3,
    atomic_state_only_selected_unmasked_terminal_value_compiled_v3,
};
use aspis_statement::state_only_poseidon::{successor_point, xor12_point};
use aspis_statement::{AtomicPaymentStatementV4, SpendPublic};

const VARIABLES: usize = 10;
const TERMINAL_COLUMNS: usize = 28;
const TERMINAL_POINTS: usize = 3;
const TERMINAL_CLAIMS: usize = TERMINAL_COLUMNS * TERMINAL_POINTS;
const SAMPLES: usize = 31;

fn lift(value: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(value)))
}

fn q(seed: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(seed * 17 + 1), M31(seed * 17 + 3)),
        c1: CM31::new(M31(seed * 17 + 5), M31(seed * 17 + 7)),
    }
}

/// A literal multilinear committed column. Affine columns are sufficient to
/// expose the degree-25 two-round Poseidon term while keeping the witness
/// construction auditable.
fn affine_column(point: &[QM31; VARIABLES], column: usize, family: u32) -> QM31 {
    point.iter().copied().enumerate().fold(
        q(family + 101 * column as u32 + 1),
        |value, (variable, x)| {
            value.add(x.mul(q(family + 103 * column as u32 + 29 * variable as u32 + 7)))
        },
    )
}

fn claims_at(point: &[QM31; VARIABLES], family: u32) -> [QM31; TERMINAL_CLAIMS] {
    let points = [*point, successor_point(point), xor12_point(point)];
    let mut claims = [QM31::ZERO; TERMINAL_CLAIMS];
    for (point_index, opening_point) in points.iter().enumerate() {
        for column in 0..16 {
            claims[point_index * TERMINAL_COLUMNS + column] =
                affine_column(opening_point, column, family);
        }
    }
    // The unmasked terminal consumes H1 only at z (selected column 26).
    claims[26] = affine_column(point, 31, family + 10_000);
    claims
}

fn statement(family: u32) -> AtomicPaymentStatementV4 {
    let digest = |offset: u32| core::array::from_fn(|lane| M31(offset + lane as u32 + 1));
    AtomicPaymentStatementV4 {
        pool: [0x51; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: digest(family + 100),
            nullifier: digest(family + 200),
            output_commitment: digest(family + 300),
            asset_id: M31(family + 401),
            fee: 17,
        },
        output_anchor: digest(family + 500),
        deployment_domain: [0x71; 32],
    }
}

fn terminal_at(variable: usize, t: u32, family: u32) -> QM31 {
    let mut point: [QM31; VARIABLES] =
        core::array::from_fn(|coordinate| q(family + 701 + 37 * coordinate as u32));
    point[variable] = lift(t);
    let claims = claims_at(&point, family);
    let zerocheck_point =
        core::array::from_fn(|coordinate| q(family + 2_003 + 41 * coordinate as u32));
    atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
        &statement(family),
        &claims,
        &point,
        q(family + 3_001),
        q(family + 3_101),
        q(family + 3_201),
        &zerocheck_point,
        q(family + 3_301),
    )
    .expect("valid focused degree-audit fixture")
}

fn composition_at(variable: usize, t: u32, family: u32) -> QM31 {
    let mut point: [QM31; VARIABLES] =
        core::array::from_fn(|coordinate| q(family + 701 + 37 * coordinate as u32));
    point[variable] = lift(t);
    atomic_state_only_selected_constraint_composition_compiled_v3(
        &statement(family),
        &claims_at(&point, family),
        &point,
        q(family + 3_001),
        q(family + 3_101),
        q(family + 3_201),
    )
    .expect("valid focused composition degree-audit fixture")
}

fn forward_difference(mut values: Vec<QM31>, order: usize) -> Vec<QM31> {
    for _ in 0..order {
        values = values.windows(2).map(|pair| pair[1].sub(pair[0])).collect();
    }
    values
}

fn measured_degree(values: &[QM31]) -> usize {
    (0..values.len())
        .rev()
        .find(|&order| {
            forward_difference(values.to_vec(), order)
                .iter()
                .any(|value| !value.is_zero())
        })
        .unwrap_or(0)
}

fn hex(value: QM31) -> String {
    let mut bytes = [0u8; 16];
    value.write_le_bytes(&mut bytes);
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() {
    let families = [11u32, 97, 211];
    let mut maximum_composition = 0usize;
    let mut maximum_terminal = 0usize;
    println!("fixture=exact-production-atomic-v3-unmasked-terminal");
    println!("algorithm=exact-QM31-forward-differences-over-t=0..30");
    for family in families {
        for variable in 0..VARIABLES {
            let composition_values = (0..SAMPLES as u32)
                .map(|t| composition_at(variable, t, family))
                .collect::<Vec<_>>();
            let composition_degree = measured_degree(&composition_values);
            maximum_composition = maximum_composition.max(composition_degree);
            let composition_delta26 = forward_difference(composition_values.clone(), 26)[0];
            let composition_delta27 = forward_difference(composition_values, 27)[0];
            let values = (0..SAMPLES as u32)
                .map(|t| terminal_at(variable, t, family))
                .collect::<Vec<_>>();
            let degree = measured_degree(&values);
            maximum_terminal = maximum_terminal.max(degree);
            let delta27 = forward_difference(values.clone(), 27)[0];
            let delta28 = forward_difference(values, 28)[0];
            assert_eq!(
                composition_degree, 26,
                "composition degree changed for family {family}, variable {variable}"
            );
            assert!(!composition_delta26.is_zero());
            assert!(composition_delta27.is_zero());
            assert_eq!(
                degree, 27,
                "terminal degree changed for family {family}, variable {variable}"
            );
            assert!(!delta27.is_zero());
            assert!(delta28.is_zero());
            println!(
                "family={family} variable={variable} composition_degree={composition_degree} composition_delta26={} composition_delta27={} terminal_degree={degree} terminal_delta27={} terminal_delta28={}",
                hex(composition_delta26),
                hex(composition_delta27),
                hex(delta27),
                hex(delta28),
            );
        }
    }
    println!("maximum_composition_individual_degree={maximum_composition}");
    println!("maximum_terminal_individual_degree={maximum_terminal}");
    assert_eq!(
        maximum_composition, 26,
        "production constraint composition did not attain degree 26"
    );
    assert_eq!(
        maximum_terminal, 27,
        "production terminal did not attain degree 27"
    );
}
