//! Machine-checkable Johnson/BCS ledger for the selected low-rate profiles.
//!
//! The transport inputs are source-pinned in
//! `docs/stage2-johnson-transport-closure-2026-07-12.md`.  Unlike the retired
//! artifact, this ledger includes the powers-generator batching round and its
//! dedicated pre-gamma work witness.  Later fold/query work is never credited
//! to that earlier round.

use aspis_core::field::P;
use serde::Serialize;

const TARGET_BITS: f64 = 100.0;
const JOHNSON_MULTIPLICITY: f64 = 10.0;
const HIDING_RESERVE_BITS: f64 = 110.0;
const BCS_INTERACTIVE_ROUND_FACTOR: f64 = 31.0;
const FOLD_POW_BITS: [u8; 4] = [39, 35, 31, 27];
const ROOT_CAPS: [u64; 4] = [1024, 255, 63, 15];
const RATE16_OOD_LIST_CAP: u64 = 160;
const RATE512_OOD_LIST_CAP: u64 = 240;
#[derive(Clone, Serialize)]
pub(crate) struct LedgerTerm {
    name: &'static str,
    probability_shape: &'static str,
    bits: f64,
    status: &'static str,
}

#[derive(Clone, Serialize)]
pub(crate) struct FoldRound {
    round: usize,
    output_symbols: u64,
    output_dimension: u64,
    gs_multiplicity: f64,
    gs_list_parameter: f64,
    unground_bits: f64,
    work_bits: u8,
    normalized_bits: f64,
}

#[derive(Serialize)]
pub(crate) struct JohnsonScenario {
    name: &'static str,
    rho: f64,
    scalar_columns: usize,
    codeword_symbols: u64,
    query_fibers: u64,
    maximum_agreement_fibers: u64,
    johnson_agreement_fraction: f64,
    agreement_formula: &'static str,
    gs_list_parameter: f64,
    ood_list_cap: u64,
    ood_root_caps: [u64; 4],
    ood_sample_space: f64,
    query_count: u16,
    query_work_bits: u8,
    batch_work_bits: u8,
    batching_bits_before_work: f64,
    batching_bits_after_work: f64,
    query_bits_after_work: f64,
    fold_rounds: Vec<FoldRound>,
    terms: Vec<LedgerTerm>,
    conservative_round_union_bits: f64,
    bcs_round_factor: f64,
    work_normalized_bcs_bits: f64,
    margin_over_target_bits: f64,
}

#[derive(Serialize)]
pub(crate) struct Rate16SoundnessArtifact {
    schema: &'static str,
    generated_by: &'static str,
    theorem_regime: &'static str,
    transport_status: &'static str,
    complete_system_claim_quotable: bool,
    target_bits: f64,
    field_bits: f64,
    scenarios: Vec<JohnsonScenario>,
    remaining_gates: Vec<&'static str>,
    source_note: &'static str,
}

fn union_bits(bits: impl IntoIterator<Item = f64>) -> f64 {
    let probability = bits
        .into_iter()
        .map(|bits| 2.0_f64.powf(-bits))
        .sum::<f64>();
    -probability.log2()
}

fn without_replacement_miss_bits(domain: u64, agreement: u64, queries: u16) -> f64 {
    (0..u64::from(queries))
        .map(|index| -((agreement - index) as f64 / (domain - index) as f64).log2())
        .sum()
}

fn batching_bits(rho: f64, columns: usize, symbols: u64, field_size: f64) -> f64 {
    let ell = (JOHNSON_MULTIPLICITY + 0.5) / rho.sqrt();
    let numerator =
        (columns - 1) as f64 * ell * ((2.0 * ell.powi(4) / 3.0) * rho + 1.0) * symbols as f64;
    (field_size / numerator).log2()
}

fn ood_union_bits(field_size: f64, list_cap: u64) -> f64 {
    let sample_space = field_size - f64::from(P).powi(2);
    let pairs = (list_cap * (list_cap - 1) / 2) as f64;
    let probability = ROOT_CAPS
        .into_iter()
        .map(|root| pairs * (root as f64 / sample_space).powi(2))
        .sum::<f64>();
    -probability.log2()
}

fn local_bits(field_bits: f64, numerator: f64) -> f64 {
    field_bits - numerator.log2()
}

/// S-two Lemma 4 specialized to the degree-three powers generator.  For an
/// output line code with domain `n`, dimension `k`, and agreement `alpha`,
/// the paper uses rho=(k-1)/n,
/// m=max(ceil(sqrt(rho)/(2*(alpha-sqrt(rho)))),3), and
/// ell=(m+1/2)/sqrt(rho), then bounds
/// `3*ell*((2*ell^4/3)*rho+1)*n/|QM31|`.
fn fold_bound(
    field_size: f64,
    output_symbols: u64,
    output_dimension: u64,
    alpha: f64,
) -> (f64, f64, f64) {
    let rho = (output_dimension - 1) as f64 / output_symbols as f64;
    let sqrt_rho = rho.sqrt();
    let m = (sqrt_rho / (2.0 * (alpha - sqrt_rho))).ceil().max(3.0);
    let ell = (m + 0.5) / rho.sqrt();
    let numerator = 3.0 * ell * ((2.0 * ell.powi(4) / 3.0) * rho + 1.0) * output_symbols as f64;
    (m, ell, (field_size / numerator).log2())
}

#[allow(clippy::too_many_arguments)]
fn scenario(
    name: &'static str,
    rho: f64,
    columns: usize,
    symbols: u64,
    query_fibers: u64,
    agreement_fibers: u64,
    query_count: u16,
    query_work_bits: u8,
    batch_work_bits: u8,
    ood_list_cap: u64,
    copy_links_for_bound: usize,
    zerocheck_degree_union: usize,
    field_size: f64,
    field_bits: f64,
) -> JohnsonScenario {
    let batching_before = batching_bits(rho, columns, symbols, field_size);
    let batching_after = batching_before + f64::from(batch_work_bits);
    let query_bits = without_replacement_miss_bits(query_fibers, agreement_fibers, query_count)
        + f64::from(query_work_bits);
    let johnson_agreement_fraction = (1.0 + 1.0 / (2.0 * JOHNSON_MULTIPLICITY)) * rho.sqrt();
    assert_eq!(
        agreement_fibers,
        (johnson_agreement_fraction * query_fibers as f64).floor() as u64
    );
    let output_dimensions = [256u64, 64, 16, 4];
    let fold_rounds = FOLD_POW_BITS
        .into_iter()
        .enumerate()
        .map(|(round, work_bits)| {
            let output_symbols = symbols / 4u64.pow((round + 1) as u32);
            let output_dimension = output_dimensions[round];
            let (gs_multiplicity, gs_list_parameter, unground_bits) = fold_bound(
                field_size,
                output_symbols,
                output_dimension,
                johnson_agreement_fraction,
            );
            FoldRound {
                round,
                output_symbols,
                output_dimension,
                gs_multiplicity,
                gs_list_parameter,
                unground_bits,
                work_bits,
                normalized_bits: unground_bits + f64::from(work_bits),
            }
        })
        .collect::<Vec<_>>();
    let terms = vec![
        LedgerTerm {
            name: "powers-generator batching",
            probability_shape: "S-two Thm.19 single-domain bound / 2^batch_work",
            bits: batching_after,
            status: "proven at Johnson; dedicated nonce must precede gamma",
        },
        LedgerTerm {
            name: "four arity-four fold rounds",
            probability_shape: "union of S-two Lemma 4 round bounds / 2^fold_work",
            bits: union_bits(fold_rounds.iter().map(|round| round.normalized_bits)),
            status: "proven at Johnson; WHIR list/fold commutation applied",
        },
        LedgerTerm {
            name: "two-sample OOD list binding",
            probability_shape: "sum_i C(L_ood,2)*(R_i/(|QM31|-|CM31|))^2; L_ood is scenario-pinned",
            bits: ood_union_bits(field_size, ood_list_cap),
            status: "proven root/list calculation",
        },
        LedgerTerm {
            name: "relation sumchecks and OOD mixers",
            probability_shape: "24/|QM31|",
            bits: local_bits(field_bits, 24.0),
            status: "local Schwartz-Zippel",
        },
        LedgerTerm {
            name: "gamma plus point-claim collision",
            probability_shape: "((scalar_columns-1)+2)/|QM31| for gamma and (1,kappa,kappa^2)",
            bits: local_bits(field_bits, (columns + 1) as f64),
            status: "local multivariate Schwartz-Zippel",
        },
        LedgerTerm {
            name: "copy-inactive combined zero claim",
            probability_shape: "(scalar_columns-1)/|QM31| for a nonzero gamma polynomial",
            bits: local_bits(field_bits, (columns - 1) as f64),
            status:
                "local Schwartz-Zippel; commitments and complete inactive-row sums precede gamma",
        },
        LedgerTerm {
            name: "copy tuple compression",
            probability_shape: "m*17/|QM31|",
            bits: local_bits(field_bits, (copy_links_for_bound * 17) as f64),
            status: "local UFD/SZ; exact state-only m is layout-bound",
        },
        LedgerTerm {
            name: "copy/range pole reserve",
            probability_shape: "8*1024/|QM31|",
            bits: local_bits(field_bits, 8.0 * 1024.0),
            status: "conservative local reserve",
        },
        LedgerTerm {
            name: "constraint registry reserve",
            probability_shape: "258/|QM31|",
            bits: local_bits(field_bits, 258.0),
            status: "replace by frozen state-only registry count",
        },
        LedgerTerm {
            name: "payment zerocheck",
            probability_shape: "sum of per-round individual degrees / |QM31|",
            bits: local_bits(field_bits, zerocheck_degree_union as f64),
            status: "local Schwartz-Zippel",
        },
        LedgerTerm {
            name: "distinct-fiber query miss",
            probability_shape: "C(A,q)/(C(N,q)*2^query_work)",
            bits: query_bits,
            status: "exact hypergeometric Johnson block count",
        },
        LedgerTerm {
            name: "Poseidon2 public digest collision",
            probability_shape: "assumed 124-bit target",
            bits: 124.0,
            status: "hash assumption",
        },
        LedgerTerm {
            name: "SHA-256 Merkle/transcript collision",
            probability_shape: "generic 128-bit collision target",
            bits: 128.0,
            status: "hash/ROM assumption",
        },
        LedgerTerm {
            name: "hiding/code-switch reserve",
            probability_shape: "implementation must instantiate <=2^-110",
            bits: HIDING_RESERVE_BITS,
            status: "reserved; privacy rank/FS proof not yet frozen",
        },
    ];
    let round_union = union_bits(terms.iter().map(|term| term.bits));
    let bcs_bits = round_union - BCS_INTERACTIVE_ROUND_FACTOR.log2();
    JohnsonScenario {
        name,
        rho,
        scalar_columns: columns,
        codeword_symbols: symbols,
        query_fibers,
        maximum_agreement_fibers: agreement_fibers,
        johnson_agreement_fraction,
        agreement_formula: "(1+1/(2m))*sqrt(rho), m=10; A=floor(fraction*fibers)",
        gs_list_parameter: (JOHNSON_MULTIPLICITY + 0.5) / rho.sqrt(),
        ood_list_cap,
        ood_root_caps: ROOT_CAPS,
        ood_sample_space: field_size - f64::from(P).powi(2),
        query_count,
        query_work_bits,
        batch_work_bits,
        batching_bits_before_work: batching_before,
        batching_bits_after_work: batching_after,
        query_bits_after_work: query_bits,
        fold_rounds,
        terms,
        conservative_round_union_bits: round_union,
        bcs_round_factor: BCS_INTERACTIVE_ROUND_FACTOR,
        work_normalized_bcs_bits: bcs_bits,
        margin_over_target_bits: bcs_bits - TARGET_BITS,
    }
}

pub(crate) fn rate16_soundness_artifact() -> Rate16SoundnessArtifact {
    let field_size = f64::from(P).powi(4);
    let field_bits = field_size.log2();
    let scenarios = vec![
        scenario(
            "profile15-rate16-width51-q36-g36-batch25",
            1.0 / 16.0,
            51,
            16_384,
            4_096,
            1_075,
            36,
            36,
            25,
            RATE16_OOD_LIST_CAP,
            1_024,
            270,
            field_size,
            field_bits,
        ),
        scenario(
            "state-only-rate16-width18-q36-g36-batch24",
            1.0 / 16.0,
            18,
            16_384,
            4_096,
            1_075,
            36,
            36,
            24,
            RATE16_OOD_LIST_CAP,
            102,
            270,
            field_size,
            field_bits,
        ),
        scenario(
            "state-only-rate32-width18-q29-g36-batch26",
            1.0 / 32.0,
            18,
            32_768,
            8_192,
            1_520,
            29,
            36,
            26,
            RATE16_OOD_LIST_CAP,
            102,
            270,
            field_size,
            field_bits,
        ),
        scenario(
            "state-only-rate16-width28-q36-g36-batch24",
            1.0 / 16.0,
            28,
            16_384,
            4_096,
            1_075,
            36,
            36,
            24,
            RATE16_OOD_LIST_CAP,
            102,
            270,
            field_size,
            field_bits,
        ),
        scenario(
            "state-only-rate32-width28-q29-g36-batch26",
            1.0 / 32.0,
            28,
            32_768,
            8_192,
            1_520,
            29,
            36,
            26,
            RATE16_OOD_LIST_CAP,
            102,
            270,
            field_size,
            field_bits,
        ),
        scenario(
            "state-only-rate512-width28-q16-g36-batch36",
            1.0 / 512.0,
            28,
            524_288,
            131_072,
            6_082,
            16,
            36,
            36,
            RATE512_OOD_LIST_CAP,
            102,
            270,
            field_size,
            field_bits,
        ),
    ];
    Rate16SoundnessArtifact {
        schema: "aspis-johnson-bcs-ledger-v3",
        generated_by: "cargo run --release -p aspis-xtask -- stage2-rate16-soundness",
        theorem_regime: "Johnson bound; S-two Thm.19/Lem.4/Thm.22 plus WHIR Lem.4.13",
        transport_status:
            "closed for scalar circle FFT subcode; implementation conformance remains tested",
        complete_system_claim_quotable: false,
        target_bits: TARGET_BITS,
        field_bits,
        scenarios,
        remaining_gates: vec![
            "freeze the redesigned state-only semantic/copy registry and replace conservative caps",
            "instantiate the 110-bit hiding reserve with complete-view rank and Fiat-Shamir ZK",
            "pin the new batch-nonce and state-only transcript KAT on host and SBF",
        ],
        source_note: "docs/stage2-johnson-transport-closure-2026-07-12.md",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn batching_and_query_rows_reproduce_the_source_pinned_numbers() {
        let artifact = rate16_soundness_artifact();
        let profile15 = &artifact.scenarios[0];
        assert!((profile15.batching_bits_before_work - 81.979_508_067_1).abs() < 1e-9);
        assert!((profile15.query_bits_after_work - 106.108_053_300_3).abs() < 1e-9);
        let state32 = &artifact.scenarios[2];
        assert!((state32.query_bits_after_work - 106.790_386_255_9).abs() < 1e-9);
        let selected16 = &artifact.scenarios[3];
        let selected32 = &artifact.scenarios[4];
        let selected512 = &artifact.scenarios[5];
        assert_eq!(selected16.scalar_columns, 28);
        assert_eq!(selected32.scalar_columns, 28);
        assert_eq!(selected512.scalar_columns, 28);
        assert_eq!(selected512.maximum_agreement_fibers, 6_082);
        assert_eq!(selected512.ood_list_cap, 240);
        assert!((selected512.batching_bits_before_work - 70.368_487_534_2).abs() < 1e-9);
        assert!((selected512.query_bits_after_work - 106.901_886_597_2).abs() < 1e-9);
        let expected_rate16_fold_bits = [
            88.029_931_954_9,
            90.726_265_969_4,
            95.358_066_268_2,
            101.339_993_314_8,
        ];
        for (round, expected) in selected16.fold_rounds.iter().zip(expected_rate16_fold_bits) {
            assert!((round.unground_bits - expected).abs() < 1e-9);
        }
        let expected_fold_bits = [
            75.529_942_692_3,
            78.226_281_804_5,
            82.858_135_080_2,
            88.840_648_013_8,
        ];
        for (round, expected) in selected512.fold_rounds.iter().zip(expected_fold_bits) {
            assert!((round.unground_bits - expected).abs() < 1e-9);
        }
    }

    #[test]
    fn every_selected_scenario_clears_100_after_the_conservative_bcs_factor() {
        let artifact = rate16_soundness_artifact();
        assert!(!artifact.complete_system_claim_quotable);
        for scenario in artifact.scenarios {
            assert!(
                scenario.work_normalized_bcs_bits > TARGET_BITS,
                "{}",
                scenario.name
            );
            assert!(scenario.margin_over_target_bits < 1.1, "{}", scenario.name);
        }
    }
}
