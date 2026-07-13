//! Deterministic reproduction of the revised-theta sensitivity menu.
//!
//! The runner deliberately emits both OOD-union variants and both known
//! folding-coefficient mappings.  None of the revised-theta rows is a
//! finite-length security claim: S-two Conjecture 2 leaves an `o(n)` term
//! without a finite-n bound.

use serde::Serialize;

const M31_MODULUS: u64 = (1_u64 << 31) - 1;
const RHO: f64 = 0.25;
const DOMAINS: [u64; 4] = [4096, 1024, 256, 64];
const DEGREES: [u64; 4] = [1024, 256, 64, 16];
const ETA_TICK_MIN: u32 = 30;
const ETA_TICK_MAX: u32 = 2200;
const ETA_DENOMINATOR: f64 = 10_000.0;

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum T2Union {
    ExactPerRoundSumOfSquares,
    ConservativeSquareOfSum,
}

#[derive(Serialize)]
pub(crate) struct ThetaArtifact {
    schema: &'static str,
    generated_by: &'static str,
    deterministic: bool,
    status: Status,
    inputs: Inputs,
    source_constant_enumeration: SourceConstants,
    historical_term_set: HistoricalTerms,
    amended_term_set: AmendedTerms,
    optimizer: Optimizer,
    idealized_unit_coefficient_results: Vec<Optimum>,
    table4_known_coefficient_sensitivity: Vec<Optimum>,
    t2_variant_comparison_q36_s2: Vec<Optimum>,
    q34_g36_earmark: Q34Earmark,
    gate_economics: GateEconomics,
}

#[derive(Serialize)]
struct Status {
    quotable_security_value: bool,
    only_quotable_floor_bits: f64,
    reason: &'static str,
    provisional_value_label: &'static str,
    provisional_q36_g32_s2_bits: f64,
}

#[derive(Serialize)]
struct Inputs {
    rho: f64,
    binary_entropy_rho: f64,
    m31_modulus: u64,
    field_bits: f64,
    rounded_field_bits_used_in_prose: f64,
    domains: [u64; 4],
    degrees: [u64; 4],
    s_t1_corrected_unit_coefficients: u64,
    s_t1_buggy_factor_of_rho: u64,
    s_t1_table4_exact_coefficients: f64,
    s_t1_table4_conservative_known_bound: f64,
    s_t2: u64,
    s_t2_exact_sum_of_squares: u64,
    s_t2_conservative_square_of_sum: u64,
    t2_variant_gap_bits: f64,
}

#[derive(Serialize)]
struct SourceConstants {
    conjecture_1: &'static str,
    c1: ConstantAssumption,
    c2: ConstantAssumption,
    conjecture_2: &'static str,
    finite_length_remainder: ConstantAssumption,
    table4_folding_coefficients: Vec<FoldCoefficient>,
    mapping_status: &'static str,
}

#[derive(Serialize)]
struct ConstantAssumption {
    source: &'static str,
    value_used: Option<f64>,
    status: &'static str,
}

#[derive(Serialize)]
struct FoldCoefficient {
    fold_index_k: u32,
    source_factor: f64,
    numerator: u64,
    exact_weighted_numerator: f64,
    conservative_known_weighted_numerator: f64,
    treatment: &'static str,
}

#[derive(Serialize)]
struct HistoricalTerms {
    label: &'static str,
    t1_bits_reproduced: f64,
    t1_bits_buggy_signature: f64,
    t2_bits_reproduced: f64,
    t3_bits: f64,
    t4_bits: f64,
    t5_bits_kprime82: f64,
    t6_bits_worst_m1024_w17: f64,
    t7_bits_worst_m1024: f64,
    t8_bits_four_claim_bound: f64,
    algebraic_union_bits_recomputed: f64,
    system_bits_q36_g32_recomputed: f64,
    recorded_anchor_algebraic_bits: f64,
    recorded_anchor_system_bits: f64,
}

#[derive(Serialize)]
struct AmendedTerms {
    label: &'static str,
    t3_bits_nu14_d7: f64,
    t4_bits_nu10: f64,
    t5_prime_bits_kprime51: f64,
    t6_current_bits_worst_m1024_w17: f64,
    t6_trace_layout_m589_sensitivity_bits: f64,
    t6_state_only_m534_sensitivity_bits: f64,
    t7_prime_current_bits_mcopy1024_range1024_union: f64,
    t7_prime_trace_m589_range_m1024_sensitivity_bits: f64,
    t7_prime_historical_8m534_superseded_bits: f64,
    t8_prime_bits_eight_claim_preintegration_sensitivity: f64,
    final_constraint_id_count: Option<u64>,
    constraint_batching_status: &'static str,
    note: &'static str,
}

#[derive(Serialize)]
struct Optimizer {
    eta_min: f64,
    eta_max: f64,
    eta_step: f64,
    exact_grid_ticks_inclusive: [u32; 2],
    tie_break: &'static str,
    objective: &'static str,
}

#[derive(Clone, Serialize)]
struct Optimum {
    label: String,
    q: u32,
    grinding_bits: u32,
    ood_samples: u32,
    t1_numerator_sum: f64,
    t2_union: T2Union,
    eta_tick: u32,
    eta: f64,
    theta: f64,
    list_exponent_log2: f64,
    query_bits: f64,
    t1_prime_bits: f64,
    t2_prime_bits: f64,
    unchanged_union_bits: f64,
    algebraic_union_bits: f64,
    system_bits: f64,
}

#[derive(Serialize)]
struct Q34Earmark {
    baseline: Optimum,
    earmark: Optimum,
    computed_system_gain_bits: f64,
    measured_pcs_saving_cu: u64,
    q_linear_statement_saving_cu: u64,
    total_projected_saving_cu: u64,
    prior_recorded_gain: &'static str,
    disposition: &'static str,
}

#[derive(Serialize)]
struct GateEconomics {
    status: &'static str,
    gate_cu: u64,
    strict_gate_cu: u64,
    r2_kprime51_central_cu: u64,
    s2_probe_source: &'static str,
    s1_isolated_probe_cu: u64,
    s2_isolated_probe_cu: u64,
    measured_s2_delta_cu: u64,
    registered_stress_delta_cu: u64,
    registered_draw_range_cu: u64,
    anchor_corrected_draw_sensitivity_cu: u64,
    q36_s2_central_cu: u64,
    q36_s2_registered_combined_worst_cu: u64,
    q36_s2_strict_gate_margin_cu: i64,
    q36_s2_anchor_corrected_sensitivity_cu: u64,
    q36_s2_anchor_strict_margin_cu: i64,
    q34_g36_s2_central_cu: u64,
    q34_g36_s2_registered_combined_worst_cu: u64,
    q34_g36_s2_strict_gate_margin_cu: i64,
    q34_g36_s2_anchor_corrected_sensitivity_cu: u64,
    q43_query_only_delta_cu: u64,
    q43_total_delta_with_measured_s2_cu: u64,
    q43_registered_combined_worst_cu: u64,
    q43_registered_margin_cu: i64,
    q43_anchor_corrected_sensitivity_cu: u64,
    q43_anchor_corrected_sensitivity_margin_cu: i64,
    q44_registered_combined_worst_cu: u64,
    q44_anchor_corrected_sensitivity_cu: u64,
    verdict: &'static str,
}

fn entropy_binary(x: f64) -> f64 {
    -x * x.log2() - (1.0 - x) * (1.0 - x).log2()
}

fn field_bits() -> f64 {
    4.0 * (M31_MODULUS as f64).log2()
}

fn union_bits(bits: &[f64]) -> f64 {
    -bits.iter().map(|b| 2.0_f64.powf(-b)).sum::<f64>().log2()
}

fn unchanged_terms() -> [f64; 6] {
    [
        field_bits() - (14.0_f64 * 7.0).log2(),
        field_bits() - 10.0_f64.log2(),
        field_bits() - 50.0_f64.log2(),
        field_bits() - (1024.0_f64 * 17.0).log2(),
        field_bits() - (8.0_f64 * 1024.0).log2(),
        field_bits() - 8.0_f64.log2(),
    ]
}

fn evaluate(
    q: u32,
    grinding_bits: u32,
    samples: u32,
    t1_sum: f64,
    t2_union: T2Union,
    eta_tick: u32,
) -> Optimum {
    let eta = eta_tick as f64 / ETA_DENOMINATOR;
    let h = entropy_binary(RHO);
    let list_exponent = h / eta;
    let query_bits = q as f64 * (RHO + eta).log2().abs() + grinding_bits as f64;
    let t1_bits = field_bits() - list_exponent - t1_sum.log2();
    let s_t2 = DEGREES.iter().map(|d| d - 1).sum::<u64>() as f64;
    let s_t2_sq = DEGREES.iter().map(|d| (d - 1) * (d - 1)).sum::<u64>() as f64;
    let t2_numerator = match (samples, t2_union) {
        (1, _) => s_t2,
        (2, T2Union::ExactPerRoundSumOfSquares) => s_t2_sq,
        (2, T2Union::ConservativeSquareOfSum) => s_t2 * s_t2,
        _ => panic!("optimizer supports only s=1 or s=2"),
    };
    let t2_bits = samples as f64 * field_bits() - (2.0 * list_exponent - 1.0) - t2_numerator.log2();
    let unchanged = unchanged_terms();
    let unchanged_union = union_bits(&unchanged);
    let mut algebraic = vec![t1_bits, t2_bits];
    algebraic.extend(unchanged);
    let algebraic_union = union_bits(&algebraic);
    let system = union_bits(&[algebraic_union, query_bits]);
    Optimum {
        label: String::new(),
        q,
        grinding_bits,
        ood_samples: samples,
        t1_numerator_sum: t1_sum,
        t2_union,
        eta_tick,
        eta,
        theta: 1.0 - RHO - eta,
        list_exponent_log2: list_exponent,
        query_bits,
        t1_prime_bits: t1_bits,
        t2_prime_bits: t2_bits,
        unchanged_union_bits: unchanged_union,
        algebraic_union_bits: algebraic_union,
        system_bits: system,
    }
}

fn optimize(
    label: &str,
    q: u32,
    grinding_bits: u32,
    samples: u32,
    t1_sum: f64,
    t2_union: T2Union,
) -> Optimum {
    let mut best = evaluate(q, grinding_bits, samples, t1_sum, t2_union, ETA_TICK_MIN);
    for tick in (ETA_TICK_MIN + 1)..=ETA_TICK_MAX {
        let candidate = evaluate(q, grinding_bits, samples, t1_sum, t2_union, tick);
        if candidate.system_bits > best.system_bits {
            best = candidate;
        }
    }
    best.label = label.to_string();
    best
}

pub(crate) fn theta_optimizer_artifact() -> ThetaArtifact {
    let h = entropy_binary(RHO);
    let s_t1 = DOMAINS.iter().sum::<u64>();
    let s_t1_buggy = s_t1 * 4;
    let s_t2 = DEGREES.iter().map(|d| d - 1).sum::<u64>();
    let s_t2_sq = DEGREES.iter().map(|d| (d - 1) * (d - 1)).sum::<u64>();
    let s_t2_conservative = s_t2 * s_t2;
    let table4_source = [1.5, 0.75, 0.375, 0.1875];
    let table4_exact = DOMAINS
        .iter()
        .zip(table4_source)
        .map(|(n, c)| *n as f64 * c)
        .sum::<f64>();
    let table4_conservative = 1.5 * DOMAINS[0] as f64 + DOMAINS[1..].iter().sum::<u64>() as f64;

    let t1_historical = field_bits() - (s_t1 as f64).log2();
    let t2_historical = field_bits() - ((40.0_f64 * 39.0 / 2.0) * s_t2 as f64).log2();
    let historical_terms = [
        t1_historical,
        t2_historical,
        field_bits() - (14.0_f64 * 7.0).log2(),
        field_bits() - 10.0_f64.log2(),
        field_bits() - 81.0_f64.log2(),
        field_bits() - (1024.0_f64 * 17.0).log2(),
        field_bits() - 4096.0_f64.log2(),
        field_bits() - 4.0_f64.log2(),
    ];
    let historical_union = union_bits(&historical_terms);
    let historical_system = union_bits(&[historical_union, 104.0]);

    let menu = [
        ("q36_g32_s1", 36, 32, 1),
        ("q36_g32_s2", 36, 32, 2),
        ("q40_g32_s2", 40, 32, 2),
        ("q43_g32_s2", 43, 32, 2),
        ("q44_g32_s2", 44, 32, 2),
        ("q45_g32_s2_historical_menu_only", 45, 32, 2),
    ];
    let idealized = menu
        .iter()
        .map(|(label, q, g, s)| {
            optimize(
                label,
                *q,
                *g,
                *s,
                s_t1 as f64,
                T2Union::ExactPerRoundSumOfSquares,
            )
        })
        .collect::<Vec<_>>();
    let table4_sensitivity = menu
        .iter()
        .map(|(label, q, g, s)| {
            optimize(
                &format!("{label}_known_table4_conservative_t1"),
                *q,
                *g,
                *s,
                table4_conservative,
                T2Union::ConservativeSquareOfSum,
            )
        })
        .collect::<Vec<_>>();
    let t2_variants = [
        (
            "q36_g32_s2_exact_per_round_t2",
            T2Union::ExactPerRoundSumOfSquares,
        ),
        (
            "q36_g32_s2_conservative_square_of_sum_t2",
            T2Union::ConservativeSquareOfSum,
        ),
    ]
    .into_iter()
    .map(|(label, mode)| optimize(label, 36, 32, 2, s_t1 as f64, mode))
    .collect::<Vec<_>>();

    let baseline_q36 = optimize(
        "q36_g32_s2_baseline",
        36,
        32,
        2,
        table4_conservative,
        T2Union::ConservativeSquareOfSum,
    );
    let q34 = optimize(
        "q34_g36_s2_earmark",
        34,
        36,
        2,
        table4_conservative,
        T2Union::ConservativeSquareOfSum,
    );

    ThetaArtifact {
        schema: "aspis.stage1.theta_optimizer.v1",
        generated_by: "cargo run -p aspis-xtask -- stage1-theta-optimize",
        deterministic: true,
        status: Status {
            quotable_security_value: false,
            only_quotable_floor_bits: 65.5,
            reason: "93.73 is a provisional known-Table-4-coefficient sensitivity: c1=c2=1 is a stronger pinned assumption, Conjecture 2 supplies no finite-n bound for o(n), the circle-code/Table-4 mapping is not a theorem, and final T8' awaits the randomized ConstraintId count J.",
            provisional_value_label: "provisional_known_table4_sensitivity_pending_finite_length_assumption",
            provisional_q36_g32_s2_bits: table4_sensitivity
                .iter()
                .find(|row| row.q == 36 && row.ood_samples == 2)
                .expect("q36/s2 row")
                .system_bits,
        },
        inputs: Inputs {
            rho: RHO,
            binary_entropy_rho: h,
            m31_modulus: M31_MODULUS,
            field_bits: field_bits(),
            rounded_field_bits_used_in_prose: 124.0,
            domains: DOMAINS,
            degrees: DEGREES,
            s_t1_corrected_unit_coefficients: s_t1,
            s_t1_buggy_factor_of_rho: s_t1_buggy,
            s_t1_table4_exact_coefficients: table4_exact,
            s_t1_table4_conservative_known_bound: table4_conservative,
            s_t2,
            s_t2_exact_sum_of_squares: s_t2_sq,
            s_t2_conservative_square_of_sum: s_t2_conservative,
            t2_variant_gap_bits: (s_t2_conservative as f64 / s_t2_sq as f64).log2(),
        },
        source_constant_enumeration: SourceConstants {
            conjecture_1: "S-two ePrint 2026/532 Appendix A.5, Conjecture 1: l(theta) <= c1 * 2^(c2 * H(rho)/eta), c1,c2 >= 1.",
            c1: ConstantAssumption {
                source: "Conjecture 1 existential constant",
                value_used: Some(1.0),
                status: "stronger Aspis sensitivity assumption; not implied by S-two",
            },
            c2: ConstantAssumption {
                source: "Conjecture 1 existential constant",
                value_used: Some(1.0),
                status: "stronger Aspis sensitivity assumption; not implied by S-two",
            },
            conjecture_2: "S-two ePrint 2026/532 Appendix A.5, Conjecture 2: a = l(theta) * n + o(n).",
            finite_length_remainder: ConstantAssumption {
                source: "Conjecture 2 o(n)",
                value_used: None,
                status: "unbounded at finite n by the cited paper; neglected only for sensitivity; blocks a quotable computed headline",
            },
            table4_folding_coefficients: DOMAINS
                .iter()
                .zip(table4_source)
                .enumerate()
                .map(|(k, (n, factor))| FoldCoefficient {
                    fold_index_k: k as u32,
                    source_factor: factor,
                    numerator: *n,
                    exact_weighted_numerator: *n as f64 * factor,
                    conservative_known_weighted_numerator: *n as f64
                        * if k == 0 { factor } else { 1.0 },
                    treatment: if k == 0 {
                        "retain 3/2; it is greater than one"
                    } else {
                        "clamp the known sub-unit coefficient to one for a conservative sensitivity"
                    },
                })
                .collect(),
            mapping_status: "Table 4 coefficients are mapped as a sensitivity only; no finite-length o(n) bound or complete circle-code transport is claimed.",
        },
        historical_term_set: HistoricalTerms {
            label: "historical_refuted_capacity_form_reproduced_for_anchor_only",
            t1_bits_reproduced: t1_historical,
            t1_bits_buggy_signature: field_bits() - (s_t1_buggy as f64).log2(),
            t2_bits_reproduced: t2_historical,
            t3_bits: historical_terms[2],
            t4_bits: historical_terms[3],
            t5_bits_kprime82: historical_terms[4],
            t6_bits_worst_m1024_w17: historical_terms[5],
            t7_bits_worst_m1024: historical_terms[6],
            t8_bits_four_claim_bound: historical_terms[7],
            algebraic_union_bits_recomputed: historical_union,
            system_bits_q36_g32_recomputed: historical_system,
            recorded_anchor_algebraic_bits: 103.9508,
            recorded_anchor_system_bits: 102.9752,
        },
        amended_term_set: AmendedTerms {
            label: "r2_kprime51_constraint_registry_open_m_le1024",
            t3_bits_nu14_d7: unchanged_terms()[0],
            t4_bits_nu10: unchanged_terms()[1],
            t5_prime_bits_kprime51: unchanged_terms()[2],
            t6_current_bits_worst_m1024_w17: unchanged_terms()[3],
            t6_trace_layout_m589_sensitivity_bits: field_bits()
                - (589.0_f64 * 17.0).log2(),
            t6_state_only_m534_sensitivity_bits: field_bits() - (534.0_f64 * 17.0).log2(),
            t7_prime_current_bits_mcopy1024_range1024_union: unchanged_terms()[4],
            t7_prime_trace_m589_range_m1024_sensitivity_bits: field_bits()
                - (4.0_f64 * (589.0_f64 + 1024.0_f64)).log2(),
            t7_prime_historical_8m534_superseded_bits: field_bits()
                - (8.0_f64 * 534.0).log2(),
            t8_prime_bits_eight_claim_preintegration_sensitivity: unchanged_terms()[5],
            final_constraint_id_count: None,
            constraint_batching_status: "OPEN: final T8' is (J+2)/|F|; freeze the randomized ConstraintId registry before quoting a payment-proof union",
            note: "The endpoint-local trace foundation contains 589 copy links, including committed absorption sources, and gives a 110.71-bit T6 sensitivity. The final randomized constraint registry has not yet wired those endpoints, so T6/T7 retain m_copy<=1024 with the fixed 1024-row range table (109.91/111.00 bits). At m_copy=589, T7' is 4*(589+1024)/|F| = 111.34 bits; 8*589 would incorrectly shrink the independent range term. The m=534 T6 state-continuity reading and historical 8*534 T7 arithmetic are retained only as explicitly superseded provenance. The approximately-121 T8' row is an eight-claim preintegration sensitivity, not the final statement-batching term.",
        },
        optimizer: Optimizer {
            eta_min: ETA_TICK_MIN as f64 / ETA_DENOMINATOR,
            eta_max: ETA_TICK_MAX as f64 / ETA_DENOMINATOR,
            eta_step: 1.0 / ETA_DENOMINATOR,
            exact_grid_ticks_inclusive: [ETA_TICK_MIN, ETA_TICK_MAX],
            tie_break: "first (smallest eta) exact grid tick with maximal IEEE-754 f64 system_bits",
            objective: "maximize -log2(2^-query_bits + 2^-algebraic_union_bits)",
        },
        idealized_unit_coefficient_results: idealized,
        table4_known_coefficient_sensitivity: table4_sensitivity,
        t2_variant_comparison_q36_s2: t2_variants,
        q34_g36_earmark: Q34Earmark {
            computed_system_gain_bits: q34.system_bits - baseline_q36.system_bits,
            measured_pcs_saving_cu: 36_629,
            q_linear_statement_saving_cu: 7_850,
            total_projected_saving_cu: 44_479,
            baseline: baseline_q36,
            earmark: q34,
            prior_recorded_gain: "0.6-0.8 bits",
            disposition: "superseded: deterministic optimizer gives approximately 0.35 bits under the provisional known-Table-4-coefficient sensitivity",
        },
        gate_economics: GateEconomics {
            status: "HISTORICAL COMPONENT ARITHMETIC ONLY: retired as a live product projection; the exact-wide diagnostic overlaps the scalar scaffold path, so a product ruling waits on in-place reconciliation and the M31/CM31 basis audit",
            gate_cu: 1_190_000,
            strict_gate_cu: 1_071_000,
            r2_kprime51_central_cu: 974_112,
            s2_probe_source: "../stage2/s2_ood_probe.json",
            s1_isolated_probe_cu: 86_815,
            s2_isolated_probe_cu: 135_914,
            measured_s2_delta_cu: 49_099,
            registered_stress_delta_cu: 17_663,
            registered_draw_range_cu: 55_786,
            anchor_corrected_draw_sensitivity_cu: 17_238,
            q36_s2_central_cu: 1_023_211,
            q36_s2_registered_combined_worst_cu: 1_096_660,
            q36_s2_strict_gate_margin_cu: -25_660,
            q36_s2_anchor_corrected_sensitivity_cu: 1_058_112,
            q36_s2_anchor_strict_margin_cu: 12_888,
            q34_g36_s2_central_cu: 978_732,
            q34_g36_s2_registered_combined_worst_cu: 1_052_181,
            q34_g36_s2_strict_gate_margin_cu: 18_819,
            q34_g36_s2_anchor_corrected_sensitivity_cu: 1_013_633,
            q43_query_only_delta_cu: 142_324,
            q43_total_delta_with_measured_s2_cu: 191_423,
            q43_registered_combined_worst_cu: 1_238_984,
            q43_registered_margin_cu: -48_984,
            q43_anchor_corrected_sensitivity_cu: 1_200_436,
            q43_anchor_corrected_sensitivity_margin_cu: -10_436,
            q44_registered_combined_worst_cu: 1_259_316,
            q44_anchor_corrected_sensitivity_cu: 1_220_768,
            verdict: "These q36/q34 values are historical component sensitivities, not current product totals. q34/g36 remains a held second transcript knob. The q43/q44 security-menu ruling remains historical provenance; no one-transaction or transport-split product ruling is emitted by this optimizer.",
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::Path;

    #[test]
    fn reproduces_historical_anchor_and_bug_signature() {
        let artifact = theta_optimizer_artifact();
        assert!((artifact.historical_term_set.t1_bits_reproduced - 111.590609).abs() < 1e-6);
        assert!((artifact.historical_term_set.t1_bits_buggy_signature - 109.590609).abs() < 1e-6);
        assert!(
            (artifact.historical_term_set.system_bits_q36_g32_recomputed - 102.9752).abs() < 2e-4
        );
    }

    #[test]
    fn idealized_menu_and_gate_are_pinned() {
        let artifact = theta_optimizer_artifact();
        let q36_s2 = artifact
            .idealized_unit_coefficient_results
            .iter()
            .find(|row| row.label == "q36_g32_s2")
            .unwrap();
        let q43_s2 = artifact
            .idealized_unit_coefficient_results
            .iter()
            .find(|row| row.label == "q43_g32_s2")
            .unwrap();
        assert_eq!(q36_s2.eta_tick, 501);
        assert!((q36_s2.system_bits - 93.89).abs() < 0.02);
        assert_eq!(q43_s2.eta_tick, 765);
        assert!(q43_s2.system_bits > 100.19);
        assert_eq!(
            artifact.gate_economics.q36_s2_strict_gate_margin_cu,
            -25_660
        );
        assert_eq!(artifact.gate_economics.q43_registered_margin_cu, -48_984);
    }

    #[test]
    fn both_t2_variants_and_q34_gain_are_explicit() {
        let artifact = theta_optimizer_artifact();
        assert_eq!(artifact.t2_variant_comparison_q36_s2.len(), 2);
        assert!((artifact.inputs.t2_variant_gap_bits - 0.7207).abs() < 1e-3);
        assert!(artifact.q34_g36_earmark.computed_system_gain_bits > 0.3);
        assert!(artifact.q34_g36_earmark.computed_system_gain_bits < 0.4);
    }

    #[test]
    fn checked_in_artifact_matches_the_runner() {
        let expected = format!(
            "{}\n",
            serde_json::to_string_pretty(&theta_optimizer_artifact()).unwrap()
        );
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("results/stage1/theta_optimizer.json");
        assert_eq!(fs::read_to_string(path).unwrap(), expected);
    }
}
