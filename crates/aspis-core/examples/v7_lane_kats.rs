use aspis_core::field::{M31, QM31};
use aspis_core::v7_lane_zeta::{
    qm31_from_limbs, qm31_limbs, split_tensor_restriction, stage_a_coefficients,
    stage_a_zeta_table, stage_b_coefficients, stage_b_zeta_table, width29_batch,
};
use aspis_core::v7_profile::{
    ALGEBRA_PROFILE_SHA256_HEX, STAGE_A_SOURCE_LANES, STAGE_B_QM31_LANES,
};
use std::fmt::Write;

fn m31_array_json(values: &[M31]) -> String {
    let mut out = String::from("[");
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        write!(&mut out, "{}", value.0).unwrap();
    }
    out.push(']');
    out
}

fn qm31_json(value: QM31) -> String {
    m31_array_json(&qm31_limbs(value))
}

fn main() {
    let mut stage_a = [M31::ZERO; STAGE_A_SOURCE_LANES];
    for (lane, value) in stage_a.iter_mut().enumerate() {
        *value = M31((17 * lane as u32 * lane as u32 + 31 * lane as u32 + 7) % 2_147_483_647);
    }
    let stage_b = [
        qm31_from_limbs([M31(101), M31(103), M31(107), M31(109)]),
        qm31_from_limbs([M31(113), M31(127), M31(131), M31(137)]),
        qm31_from_limbs([M31(139), M31(149), M31(151), M31(157)]),
    ];
    let gamma = qm31_from_limbs([M31(163), M31(167), M31(173), M31(179)]);
    let stage_a_coefficients = stage_a_coefficients(&stage_a);
    let stage_b_coefficients = stage_b_coefficients(&stage_b);
    let stage_a_table = stage_a_zeta_table(&stage_a);
    let stage_b_table = stage_b_zeta_table(&stage_b);
    let split = split_tensor_restriction(&stage_a_table, &stage_b_table, gamma);
    let direct = width29_batch(&stage_a, &stage_b, gamma);
    assert_eq!(split, direct);

    println!("{{");
    println!("  \"schema\": \"aspis-v7-lane-kat\",");
    println!("  \"revision\": \"r0-phase1-algebra\",");
    println!(
        "  \"algebra_profile_sha256\": \"{}\",",
        ALGEBRA_PROFILE_SHA256_HEX
    );
    println!("  \"stage_a_source\": {},", m31_array_json(&stage_a));
    println!(
        "  \"stage_a_coefficients_padded\": {},",
        m31_array_json(&stage_a_coefficients)
    );
    println!(
        "  \"stage_a_zeta_table\": {},",
        m31_array_json(&stage_a_table)
    );
    println!(
        "  \"stage_b_source_limbs\": [{},{},{}],",
        qm31_json(stage_b[0]),
        qm31_json(stage_b[1]),
        qm31_json(stage_b[2])
    );
    println!(
        "  \"stage_b_coefficients_padded\": {},",
        m31_array_json(&stage_b_coefficients)
    );
    println!(
        "  \"stage_b_zeta_table\": {},",
        m31_array_json(&stage_b_table)
    );
    println!("  \"gamma_limbs\": {},", qm31_json(gamma));
    println!("  \"split_tensor_result_limbs\": {},", qm31_json(split));
    println!("  \"literal_width29_result_limbs\": {}", qm31_json(direct));
    println!("}}");

    let _ = STAGE_B_QM31_LANES;
}
