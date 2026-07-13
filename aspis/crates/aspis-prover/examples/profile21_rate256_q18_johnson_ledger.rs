//! Reproducible numeric ledger for the production-neutral log-11/q18 affine
//! slice candidate. This is not a production soundness claim: rank, wire and
//! transcript conformance remain explicit external gates.

const P: f64 = 2_147_483_647.0;
const FIELD_SIZE: f64 = P * P * P * P;
const FIELD_BITS: f64 = 123.999_999_997_312_77;
const RHO: f64 = 1.0 / 256.0;
const JOHNSON_MULTIPLICITY: f64 = 10.0;
const COLUMNS: usize = 28;
const CODEWORD_SYMBOLS: u64 = 524_288;
const QUERY_FIBERS: u64 = 131_072;
const QUERY_COUNT: u16 = 18;
const BATCH_WORK_BITS: u8 = 38;
const QUERY_WORK_BITS: u8 = 38;
const FOLD_WORK_BITS: [u8; 4] = [39, 35, 31, 27];
const OUTPUT_SYMBOLS: [u64; 4] = [131_072, 32_768, 8_192, 2_048];
const OUTPUT_DIMENSIONS: [u64; 4] = [512, 128, 32, 8];
const OOD_ROOT_CAPS: [u64; 4] = [2_048, 511, 127, 31];
const OOD_LIST_CAP: u64 = 240;

fn union_bits(bits: &[f64]) -> f64 {
    -bits
        .iter()
        .map(|bits| 2.0_f64.powf(-bits))
        .sum::<f64>()
        .log2()
}

fn local_bits(numerator: f64) -> f64 {
    FIELD_BITS - numerator.log2()
}

fn batching_bits() -> f64 {
    let ell = (JOHNSON_MULTIPLICITY + 0.5) / RHO.sqrt();
    let numerator = (COLUMNS - 1) as f64
        * ell
        * ((2.0 * ell.powi(4) / 3.0) * RHO + 1.0)
        * CODEWORD_SYMBOLS as f64;
    (FIELD_SIZE / numerator).log2() + f64::from(BATCH_WORK_BITS)
}

fn query_bits(agreement_cap: u64) -> f64 {
    let miss = (0..u64::from(QUERY_COUNT))
        .map(|index| -((agreement_cap - index) as f64 / (QUERY_FIBERS - index) as f64).log2())
        .sum::<f64>();
    miss + f64::from(QUERY_WORK_BITS)
}

fn fold_bound(output_symbols: u64, output_dimension: u64, alpha: f64) -> (f64, f64, f64) {
    let rho = (output_dimension - 1) as f64 / output_symbols as f64;
    let sqrt_rho = rho.sqrt();
    let multiplicity = (sqrt_rho / (2.0 * (alpha - sqrt_rho))).ceil().max(3.0);
    let ell = (multiplicity + 0.5) / sqrt_rho;
    let numerator = 3.0 * ell * ((2.0 * ell.powi(4) / 3.0) * rho + 1.0) * output_symbols as f64;
    (multiplicity, ell, (FIELD_SIZE / numerator).log2())
}

fn ood_bits() -> f64 {
    let sample_space = FIELD_SIZE - P * P;
    let pairs = (OOD_LIST_CAP * (OOD_LIST_CAP - 1) / 2) as f64;
    let probability = OOD_ROOT_CAPS
        .iter()
        .map(|root| pairs * (*root as f64 / sample_space).powi(2))
        .sum::<f64>();
    -probability.log2()
}

fn main() {
    // The S-two multiplicity parameter remains ten. It is unrelated to the
    // `11` in the exact FFT-space inclusion L'_11 subset L_11.
    let alpha = (1.0 + 1.0 / (2.0 * JOHNSON_MULTIPLICITY)) * RHO.sqrt();
    let agreement_cap = (alpha * QUERY_FIBERS as f64).floor() as u64;
    let batching = batching_bits();
    let query = query_bits(agreement_cap);
    let mut folds = Vec::with_capacity(4);
    for round in 0..4 {
        let (multiplicity, ell, unground) =
            fold_bound(OUTPUT_SYMBOLS[round], OUTPUT_DIMENSIONS[round], alpha);
        folds.push((
            multiplicity,
            ell,
            unground,
            unground + f64::from(FOLD_WORK_BITS[round]),
        ));
    }
    let fold_union = union_bits(
        &folds
            .iter()
            .map(|(_, _, _, normalized)| *normalized)
            .collect::<Vec<_>>(),
    );
    let ood = ood_bits();

    // Exact atomic-v3 local terms. The affine candidate removes the older
    // X/F/U source-switch terms; retaining that switch requires a new union.
    let terms = [
        batching,
        fold_union,
        ood,
        local_bits(24.0), // relation sumchecks and OOD mixers
        local_bits(29.0), // gamma plus three-point batching
        local_bits(27.0), // copy-inactive gamma polynomial
        local_bits(183.0 * 17.0),
        local_bits(4_828.0), // atomic copy/range poles
        local_bits(24.0),    // atomic theta composition
        local_bits(270.0),   // ten degree-27 zerocheck rounds
        query,
        124.0, // Poseidon2 assumption
        128.0, // SHA-256/ROM assumption
    ];
    let round_union = union_bits(&terms);
    let factor31 = round_union - 31.0_f64.log2();
    let factor33 = round_union - 33.0_f64.log2();
    let factor40 = round_union - 40.0_f64.log2();

    assert_eq!(agreement_cap, 8_601);
    assert!((batching - 109.868_487_186_522_46).abs() < 1e-9);
    assert!((query - 108.758_800_441_940_72).abs() < 1e-9);
    assert!((fold_union - 112.234_408_709_511_11).abs() < 1e-9);
    assert!((round_union - 107.936_721_322_488_21).abs() < 1e-9);
    assert!((factor31 - 102.982_525_012_101_33).abs() < 1e-9);
    assert!((factor33 - 102.892_327_203_129_75).abs() < 1e-9);

    println!(
        concat!(
            "{{\n",
            "  \"schema\": \"aspis.profile21.rate256_q18_johnson.v1\",\n",
            "  \"complete_system_claim_quotable\": false,\n",
            "  \"theorem_scope\": \"S-two Corollary 1, Theorem 19, and Lemma 4; Johnson regime\",\n",
            "  \"exact_code\": \"L'_11(QM31) subset L_11(QM31) on G'_19\",\n",
            "  \"rho\": {rho},\n",
            "  \"codeword_symbols\": {symbols},\n",
            "  \"query_fibers\": {fibers},\n",
            "  \"query_count\": {queries},\n",
            "  \"batch_work_bits\": {batch_work},\n",
            "  \"query_work_bits\": {query_work},\n",
            "  \"johnson_multiplicity\": {johnson_m},\n",
            "  \"johnson_agreement_fraction\": {alpha:.15},\n",
            "  \"maximum_agreement_fibers\": {agreement_cap},\n",
            "  \"batching_bits_after_g38\": {batching:.15},\n",
            "  \"query_bits_after_g38\": {query:.15},\n",
            "  \"fold_rounds\": [\n",
            "    {{\"round\":0,\"output_symbols\":131072,\"output_dimension\":512,\"multiplicity\":{f0_m:.0},\"list_parameter\":{f0_l:.15},\"unground_bits\":{f0_u:.15},\"work_bits\":39,\"normalized_bits\":{f0_n:.15}}},\n",
            "    {{\"round\":1,\"output_symbols\":32768,\"output_dimension\":128,\"multiplicity\":{f1_m:.0},\"list_parameter\":{f1_l:.15},\"unground_bits\":{f1_u:.15},\"work_bits\":35,\"normalized_bits\":{f1_n:.15}}},\n",
            "    {{\"round\":2,\"output_symbols\":8192,\"output_dimension\":32,\"multiplicity\":{f2_m:.0},\"list_parameter\":{f2_l:.15},\"unground_bits\":{f2_u:.15},\"work_bits\":31,\"normalized_bits\":{f2_n:.15}}},\n",
            "    {{\"round\":3,\"output_symbols\":2048,\"output_dimension\":8,\"multiplicity\":{f3_m:.0},\"list_parameter\":{f3_l:.15},\"unground_bits\":{f3_u:.15},\"work_bits\":27,\"normalized_bits\":{f3_n:.15}}}\n",
            "  ],\n",
            "  \"fold_union_bits\": {fold_union:.15},\n",
            "  \"ood_union_bits\": {ood:.15},\n",
            "  \"conservative_round_union_bits\": {round_union:.15},\n",
            "  \"after_bcs_factor31_bits\": {factor31:.15},\n",
            "  \"after_bcs_factor33_bits\": {factor33:.15},\n",
            "  \"after_bcs_factor40_bits\": {factor40:.15},\n",
            "  \"promotion_gates\": [\"exact affine q18 containment\", \"production wire and transcript KAT\", \"integrated verifier and mutation tests\"]\n",
            "}}"
        ),
        rho = RHO,
        symbols = CODEWORD_SYMBOLS,
        fibers = QUERY_FIBERS,
        queries = QUERY_COUNT,
        batch_work = BATCH_WORK_BITS,
        query_work = QUERY_WORK_BITS,
        johnson_m = JOHNSON_MULTIPLICITY,
        alpha = alpha,
        agreement_cap = agreement_cap,
        batching = batching,
        query = query,
        f0_m = folds[0].0,
        f0_l = folds[0].1,
        f0_u = folds[0].2,
        f0_n = folds[0].3,
        f1_m = folds[1].0,
        f1_l = folds[1].1,
        f1_u = folds[1].2,
        f1_n = folds[1].3,
        f2_m = folds[2].0,
        f2_l = folds[2].1,
        f2_u = folds[2].2,
        f2_n = folds[2].3,
        f3_m = folds[3].0,
        f3_l = folds[3].1,
        f3_u = folds[3].2,
        f3_n = folds[3].3,
        fold_union = fold_union,
        ood = ood,
        round_union = round_union,
        factor31 = factor31,
        factor33 = factor33,
        factor40 = factor40,
    );
}
