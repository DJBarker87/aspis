//! Reproduction of the Stage 1 T1/T2 constants against one pinned upstream
//! WHIR revision. This module intentionally copies the small published
//! formulas, not upstream implementation code, so the resulting artifact is
//! deterministic and reviewable without a network checkout.

use aspis_core::field::P;
use aspis_core::params::{FOLD_VARS, PROFILE_CAPACITY_LR10_Q36_G32};
use serde::Serialize;

const UPSTREAM_REPOSITORY: &str = "https://github.com/WizardOfMenlo/whir";
const UPSTREAM_COMMIT: &str = "10aa7d0bae3663fd149b6b88b6eff2209b867970";
const UPSTREAM_COMMIT_DATE: &str = "2026-07-07T06:17:17+02:00";
const UPSTREAM_SOURCE: &str = "src/protocols/irs_commit.rs:251-288,574-596";
const UPSTREAM_PERMALINK: &str = "https://github.com/WizardOfMenlo/whir/blob/10aa7d0bae3663fd149b6b88b6eff2209b867970/src/protocols/irs_commit.rs#L251-L288";

#[derive(Serialize)]
pub(crate) struct SourcePin {
    repository: &'static str,
    commit: &'static str,
    commit_date: &'static str,
    source: &'static str,
    permalink: &'static str,
}

#[derive(Serialize)]
pub(crate) struct ProfilePin {
    name: &'static str,
    log_rows: u32,
    log_inverse_rate: u32,
    fold_variables_per_round: u32,
    rounds: u32,
    degree_bounds: Vec<u64>,
    qm31_field_bits: f64,
    johnson_slack: f64,
    johnson_list_size: f64,
}

#[derive(Serialize)]
pub(crate) struct RoundBits {
    round: u32,
    degree_bound: u64,
    bits: f64,
}

#[derive(Serialize)]
pub(crate) struct T1Pin {
    upstream_unique_formula: &'static str,
    upstream_list_decoding_formula: &'static str,
    unique_shaped_per_round: Vec<RoundBits>,
    unique_shaped_union_bits: f64,
    johnson_per_round: Vec<RoundBits>,
    johnson_union_bits: f64,
    interpretation: &'static str,
}

#[derive(Serialize)]
pub(crate) struct ListSensitivity {
    list_size: u64,
    union_bits: f64,
}

#[derive(Serialize)]
pub(crate) struct T2Pin {
    upstream_formula: &'static str,
    resolved_shape: &'static str,
    samples_per_round: u32,
    johnson_per_round: Vec<RoundBits>,
    johnson_union_bits: f64,
    list_size_sensitivity: Vec<ListSensitivity>,
    interpretation: &'static str,
}

#[derive(Serialize)]
pub(crate) struct SoundnessPin {
    schema: &'static str,
    source: SourcePin,
    profile: ProfilePin,
    t1_proximity_gaps: T1Pin,
    t2_ood_binding: T2Pin,
    conclusion: Vec<&'static str>,
}

fn union_bits(bits: impl IntoIterator<Item = f64>) -> f64 {
    let probability: f64 = bits.into_iter().map(|b| 2.0_f64.powf(-b)).sum();
    -probability.log2()
}

fn degree_bounds() -> Vec<u64> {
    let profile = &PROFILE_CAPACITY_LR10_Q36_G32;
    (0..profile.num_rounds())
        .map(|round| 1_u64 << (profile.log_rows - FOLD_VARS * round))
        .collect()
}

fn ood_union_bits(field_bits: f64, degrees: &[u64], list_size: f64) -> f64 {
    let pairs = list_size * (list_size - 1.0) / 2.0;
    if pairs == 0.0 {
        return f64::INFINITY;
    }
    union_bits(
        degrees
            .iter()
            .map(|&degree| field_bits - pairs.log2() - ((degree - 1) as f64).log2()),
    )
}

pub(crate) fn soundness_pin() -> SoundnessPin {
    let profile = &PROFILE_CAPACITY_LR10_Q36_G32;
    let degrees = degree_bounds();
    let field_bits = 4.0 * f64::from(P).log2();
    let log_inverse_rate = f64::from(profile.log_blowup);
    let rate = 2.0_f64.powf(-log_inverse_rate);
    // Exact parameter choice in the pinned upstream Config::new:
    // eta = sqrt(rho)/20 and L = 1/(2*eta*sqrt(rho)).
    let johnson_slack = rate.sqrt() / 20.0;
    let johnson_list_size = 1.0 / (2.0 * johnson_slack * rate.sqrt());

    let unique_shaped_per_round = degrees
        .iter()
        .enumerate()
        .map(|(round, &degree)| RoundBits {
            round: round as u32,
            degree_bound: degree,
            bits: field_bits - ((degree as f64).log2() + log_inverse_rate),
        })
        .collect::<Vec<_>>();
    let johnson_per_round = degrees
        .iter()
        .enumerate()
        .map(|(round, &degree)| RoundBits {
            round: round as u32,
            degree_bound: degree,
            bits: field_bits
                - (7.0 * 10.0_f64.log2() + 3.5 * log_inverse_rate + 2.0 * (degree as f64).log2()),
        })
        .collect::<Vec<_>>();

    let pairs = johnson_list_size * (johnson_list_size - 1.0) / 2.0;
    let johnson_ood_per_round = degrees
        .iter()
        .enumerate()
        .map(|(round, &degree)| RoundBits {
            round: round as u32,
            degree_bound: degree,
            bits: field_bits - pairs.log2() - ((degree - 1) as f64).log2(),
        })
        .collect::<Vec<_>>();

    let unique_union = union_bits(unique_shaped_per_round.iter().map(|r| r.bits));
    let johnson_union = union_bits(johnson_per_round.iter().map(|r| r.bits));
    let johnson_ood_union = union_bits(johnson_ood_per_round.iter().map(|r| r.bits));

    SoundnessPin {
        schema: "aspis-stage1-upstream-soundness-pin-v1",
        source: SourcePin {
            repository: UPSTREAM_REPOSITORY,
            commit: UPSTREAM_COMMIT,
            commit_date: UPSTREAM_COMMIT_DATE,
            source: UPSTREAM_SOURCE,
            permalink: UPSTREAM_PERMALINK,
        },
        profile: ProfilePin {
            name: profile.name,
            log_rows: profile.log_rows,
            log_inverse_rate: profile.log_blowup,
            fold_variables_per_round: FOLD_VARS,
            rounds: profile.num_rounds(),
            degree_bounds: degrees.clone(),
            qm31_field_bits: field_bits,
            johnson_slack,
            johnson_list_size,
        },
        t1_proximity_gaps: T1Pin {
            upstream_unique_formula: "bits = log2(|F|) - (log2(k) + log2(1/rho))",
            upstream_list_decoding_formula: "bits = log2(|F|) - (7*log2(10) + 3.5*log2(1/rho) + 2*log2(k))",
            unique_shaped_per_round,
            unique_shaped_union_bits: unique_union,
            johnson_per_round,
            johnson_union_bits: johnson_union,
            interpretation: "The pinned upstream has unique- and Johnson-decoding branches, but no capacity-conjecture branch. Aspis may cite the unique-shaped values only as part of its explicit capacity conjecture; they are not an upstream proof of capacity soundness. The Johnson branch is much lower and upstream compensates it with per-fold PoW, which Aspis does not implement.",
        },
        t2_ood_binding: T2Pin {
            upstream_formula: "(L choose 2) * (((degree - 1) / |F|)^samples)",
            resolved_shape: "quadratic in list size: (L choose 2), not linear in L",
            samples_per_round: 1,
            johnson_per_round: johnson_ood_per_round,
            johnson_union_bits: johnson_ood_union,
            list_size_sensitivity: [2_u64, 4, 8, 16, 40]
                .into_iter()
                .map(|list_size| ListSensitivity {
                    list_size,
                    union_bits: ood_union_bits(field_bits, &degrees, list_size as f64),
                })
                .collect(),
            interpretation: "At rho=1/4 the pinned Johnson choice gives eta=0.025 and L=40. One OOD sample in each of Aspis's four rounds must be unioned with the shrinking degree bounds; this resolves the draft's T2 shape question without treating the capacity list size as proven.",
        },
        conclusion: vec![
            "T2's exact pinned-upstream shape is the L-choose-2 form.",
            "The capacity conjecture must state an effective list-size bound; query-radius behavior alone is insufficient to instantiate T2.",
            "The pinned upstream does not prove Aspis's capacity-shaped T1 constants.",
            "Any Stage 1 headline must keep capacity soundness explicitly conjectural and must not relabel the unique-shaped T1 branch as proven.",
        ],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pinned_profile_and_johnson_constants_are_stable() {
        let pin = soundness_pin();
        assert_eq!(pin.profile.degree_bounds, vec![1024, 256, 64, 16]);
        assert!((pin.profile.johnson_list_size - 40.0).abs() < f64::EPSILON);
        assert!(pin.t1_proximity_gaps.unique_shaped_union_bits > 111.0);
        assert!(pin.t1_proximity_gaps.unique_shaped_union_bits < 112.0);
        assert!(pin.t1_proximity_gaps.johnson_union_bits > 73.0);
        assert!(pin.t1_proximity_gaps.johnson_union_bits < 74.0);
        assert!(pin.t2_ood_binding.johnson_union_bits > 103.0);
        assert!(pin.t2_ood_binding.johnson_union_bits < 105.0);
    }
}
