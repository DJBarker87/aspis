use anyhow::{anyhow, bail, Context, Result};
use serde::Serialize;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake128,
};
use std::{env, fs, path::PathBuf};

const Q: u32 = 8_380_417;
const N: usize = 256;
const SHAKE128_RATE_BYTES: usize = 168;
const KECCAK_F1600_ROUNDS: usize = 24;
const DEFAULT_RHO_HEX: &str = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";

#[derive(Clone, Copy)]
struct ParameterSet {
    name: &'static str,
    k: usize,
    l: usize,
}

const ML_DSA_44: ParameterSet = ParameterSet {
    name: "ML-DSA-44",
    k: 4,
    l: 4,
};

const ML_DSA_65: ParameterSet = ParameterSet {
    name: "ML-DSA-65",
    k: 6,
    l: 5,
};

#[derive(Serialize)]
struct PolyMetrics {
    row: usize,
    col: usize,
    accepted_coefficients: usize,
    total_attempts: usize,
    rejected_attempts: usize,
    squeezed_bytes: usize,
    shake128_permutations: usize,
    round_rows: usize,
}

#[derive(Serialize)]
struct AirModel {
    width: usize,
    rows: usize,
    total_cells: usize,
    note: &'static str,
}

#[derive(Serialize)]
struct AirModels {
    lane_floor: AirModel,
    lane_candidate_v0: AirModel,
    bit_floor: AirModel,
}

#[derive(Serialize)]
struct ParameterMetrics {
    parameter_set: &'static str,
    k: usize,
    l: usize,
    rho_hex: String,
    total_polynomials: usize,
    accepted_coefficients: usize,
    total_attempts: usize,
    total_rejections: usize,
    total_squeezed_bytes: usize,
    total_shake128_permutations: usize,
    total_round_rows: usize,
    average_attempts_per_polynomial: f64,
    max_attempts_single_polynomial: usize,
    max_rejections_single_polynomial: usize,
    air_models: AirModels,
    per_polynomial: Vec<PolyMetrics>,
}

#[derive(Serialize)]
struct Report {
    rho_hex: String,
    methodology: &'static str,
    reports: Vec<ParameterMetrics>,
}

fn coeff_from_three_bytes(bytes: [u8; 3]) -> Option<u32> {
    let mut b2 = bytes[2] as u32;
    if b2 > 127 {
        b2 -= 128;
    }
    let z = (1u32 << 16) * b2 + (1u32 << 8) * (bytes[1] as u32) + (bytes[0] as u32);
    (z < Q).then_some(z)
}

fn shake128_permutations_for_output(output_bytes: usize) -> usize {
    if output_bytes == 0 {
        0
    } else {
        1 + ((output_bytes - 1) / SHAKE128_RATE_BYTES)
    }
}

fn sample_rej_ntt_poly_metrics(rho: &[u8], row: usize, col: usize) -> Result<PolyMetrics> {
    let mut seed = Vec::with_capacity(34);
    seed.extend_from_slice(rho);
    seed.push(col as u8);
    seed.push(row as u8);

    let mut shake = Shake128::default();
    shake.update(&seed);
    let mut reader = shake.finalize_xof();

    let mut accepted_coefficients = 0usize;
    let mut total_attempts = 0usize;
    let mut rejected_attempts = 0usize;
    let mut buf = [0u8; 3];

    while accepted_coefficients < N {
        reader.read(&mut buf);
        total_attempts += 1;
        if coeff_from_three_bytes(buf).is_some() {
            accepted_coefficients += 1;
        } else {
            rejected_attempts += 1;
        }
    }

    let squeezed_bytes = total_attempts * 3;
    let shake128_permutations = shake128_permutations_for_output(squeezed_bytes);
    let round_rows = shake128_permutations * KECCAK_F1600_ROUNDS;

    Ok(PolyMetrics {
        row,
        col,
        accepted_coefficients,
        total_attempts,
        rejected_attempts,
        squeezed_bytes,
        shake128_permutations,
        round_rows,
    })
}

fn build_air_models(total_round_rows: usize) -> AirModels {
    let lane_floor_width = 25usize;
    let lane_candidate_width = 32usize;
    let bit_floor_width = 1600usize;

    AirModels {
        lane_floor: AirModel {
            width: lane_floor_width,
            rows: total_round_rows,
            total_cells: lane_floor_width * total_round_rows,
            note: "One field element per Keccak-f[1600] lane, one row per round. This is only a state-width floor.",
        },
        lane_candidate_v0: AirModel {
            width: lane_candidate_width,
            rows: total_round_rows,
            total_cells: lane_candidate_width * total_round_rows,
            note: "Candidate v0 layout: 25 lane columns plus 7 control/output columns for round/phase/squeeze bookkeeping.",
        },
        bit_floor: AirModel {
            width: bit_floor_width,
            rows: total_round_rows,
            total_cells: bit_floor_width * total_round_rows,
            note: "Bit-decomposed floor: 1600 boolean state bits with no extra control columns. This is a pessimistic width floor.",
        },
    }
}

fn measure_parameter_set(parameter_set: ParameterSet, rho: &[u8], rho_hex: &str) -> Result<ParameterMetrics> {
    let mut per_polynomial = Vec::with_capacity(parameter_set.k * parameter_set.l);

    for row in 0..parameter_set.k {
        for col in 0..parameter_set.l {
            per_polynomial.push(sample_rej_ntt_poly_metrics(rho, row, col)?);
        }
    }

    let total_polynomials = per_polynomial.len();
    let accepted_coefficients = per_polynomial
        .iter()
        .map(|entry| entry.accepted_coefficients)
        .sum();
    let total_attempts = per_polynomial.iter().map(|entry| entry.total_attempts).sum();
    let total_rejections = per_polynomial
        .iter()
        .map(|entry| entry.rejected_attempts)
        .sum();
    let total_squeezed_bytes = per_polynomial.iter().map(|entry| entry.squeezed_bytes).sum();
    let total_shake128_permutations = per_polynomial
        .iter()
        .map(|entry| entry.shake128_permutations)
        .sum();
    let total_round_rows = per_polynomial.iter().map(|entry| entry.round_rows).sum();
    let average_attempts_per_polynomial = total_attempts as f64 / total_polynomials as f64;
    let max_attempts_single_polynomial = per_polynomial
        .iter()
        .map(|entry| entry.total_attempts)
        .max()
        .unwrap_or(0);
    let max_rejections_single_polynomial = per_polynomial
        .iter()
        .map(|entry| entry.rejected_attempts)
        .max()
        .unwrap_or(0);
    let air_models = build_air_models(total_round_rows);

    Ok(ParameterMetrics {
        parameter_set: parameter_set.name,
        k: parameter_set.k,
        l: parameter_set.l,
        rho_hex: rho_hex.to_owned(),
        total_polynomials,
        accepted_coefficients,
        total_attempts,
        total_rejections,
        total_squeezed_bytes,
        total_shake128_permutations,
        total_round_rows,
        average_attempts_per_polynomial,
        max_attempts_single_polynomial,
        max_rejections_single_polynomial,
        air_models,
        per_polynomial,
    })
}

fn parse_args() -> Result<(String, Option<PathBuf>)> {
    let mut rho_hex = DEFAULT_RHO_HEX.to_owned();
    let mut out_path = None;
    let mut args = env::args().skip(1);

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--rho-hex" => {
                rho_hex = args
                    .next()
                    .ok_or_else(|| anyhow!("missing value for --rho-hex"))?;
            }
            "--out" => {
                let value = args
                    .next()
                    .ok_or_else(|| anyhow!("missing value for --out"))?;
                out_path = Some(PathBuf::from(value));
            }
            other => bail!("unknown argument: {other}"),
        }
    }

    Ok((rho_hex, out_path))
}

fn decode_rho(rho_hex: &str) -> Result<Vec<u8>> {
    let rho = hex::decode(rho_hex).with_context(|| format!("invalid rho hex: {rho_hex}"))?;
    if rho.len() != 32 {
        bail!("rho must be exactly 32 bytes, got {}", rho.len());
    }
    Ok(rho)
}

fn main() -> Result<()> {
    let (rho_hex, out_path) = parse_args()?;
    let rho = decode_rho(&rho_hex)?;

    let report = Report {
        rho_hex: rho_hex.clone(),
        methodology: "Exact FIPS 204 ExpandA/RejNTTPoly transcript measurement for a fixed rho. No STARK proof generation. Rows are projected as one row per Keccak-f[1600] round.",
        reports: vec![
            measure_parameter_set(ML_DSA_44, &rho, &rho_hex)?,
            measure_parameter_set(ML_DSA_65, &rho, &rho_hex)?,
        ],
    };

    let json = serde_json::to_string_pretty(&report)?;
    if let Some(out_path) = out_path {
        if let Some(parent) = out_path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&out_path, &json)?;
    }
    println!("{json}");
    Ok(())
}
