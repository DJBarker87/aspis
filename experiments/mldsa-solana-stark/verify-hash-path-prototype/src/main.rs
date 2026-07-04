use anyhow::{bail, Context, Result};
use serde::Serialize;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::{env, fs, path::PathBuf};

const N: usize = 256;
const Q: u32 = 8_380_417;
const D: usize = 13;
const TAU_44: usize = 39;
const LAMBDA_44: usize = 128;
const GAMMA1_44: i32 = 1 << 17;
const BETA_44: i32 = 78;
const OMEGA_44: usize = 80;
const K_44: usize = 4;
const L_44: usize = 4;
const SHAKE256_RATE_BYTES: usize = 136;
const KECCAK_F1600_ROUNDS: usize = 24;
const DEFAULT_RHO_HEX: &str = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
const DEFAULT_MESSAGE: &[u8] = b"ml-dsa verify hash path";

#[derive(Clone, Copy)]
struct ParameterSet {
    name: &'static str,
    k: usize,
    l: usize,
    d: usize,
    tau: usize,
    lambda: usize,
    gamma1: i32,
    gamma2: i32,
    beta: i32,
    omega: usize,
}

const ML_DSA_44: ParameterSet = ParameterSet {
    name: "ML-DSA-44",
    k: K_44,
    l: L_44,
    d: D,
    tau: TAU_44,
    lambda: LAMBDA_44,
    gamma1: GAMMA1_44,
    gamma2: ((Q - 1) / 88) as i32,
    beta: BETA_44,
    omega: OMEGA_44,
};

type PolyU32 = Vec<u32>;
type PolyI32 = Vec<i32>;
type PolyBin = Vec<u8>;

#[derive(Serialize)]
struct HashMetrics {
    label: &'static str,
    input_bytes: usize,
    output_bytes: usize,
    rate_bytes: usize,
    total_permutations: usize,
    round_rows: usize,
}

#[derive(Serialize)]
struct SampleInBallMetrics {
    seed_bytes: usize,
    sign_bytes: usize,
    position_bytes: usize,
    total_output_bytes: usize,
    total_permutations: usize,
    round_rows: usize,
    total_attempts: usize,
    rejected_attempts: usize,
    hamming_weight: usize,
    first_nonzero_positions: Vec<usize>,
}

#[derive(Serialize)]
struct FixtureSummary {
    parameter_set: &'static str,
    rho_hex: String,
    message_hex: String,
    message_len: usize,
    pk_len: usize,
    sig_len: usize,
    hint_ones: usize,
    w1_coeff_max: u32,
    z_max_abs: i32,
}

#[derive(Serialize)]
struct NegativeChecks {
    malformed_hint_leftover_rejected: bool,
    malformed_hint_non_monotone_rejected: bool,
    wrong_signature_length_rejected: bool,
    wrong_w1_mismatch_detected: bool,
}

#[derive(Serialize)]
struct EvaluationReport {
    methodology: &'static str,
    fixture: FixtureSummary,
    tr_hex: String,
    mu_hex: String,
    ctilde_hex: String,
    z_bound_ok: bool,
    ctilde_match: bool,
    hash_path_verdict: bool,
    tr_hash: HashMetrics,
    mu_hash: HashMetrics,
    ctilde_hash: HashMetrics,
    sample_in_ball: SampleInBallMetrics,
    total_hash_round_rows_excluding_expanda: usize,
    negative_checks: NegativeChecks,
}

struct Fixture {
    pk: Vec<u8>,
    sigma: Vec<u8>,
    message: Vec<u8>,
    w1_prime: Vec<PolyU32>,
    hint_ones: usize,
    w1_coeff_max: u32,
    z_max_abs: i32,
    rho_hex: String,
}

fn bitlen(mut value: u32) -> usize {
    let mut bits = 0usize;
    while value > 0 {
        bits += 1;
        value >>= 1;
    }
    bits.max(1)
}

fn integer_to_bits(mut value: u32, alpha: usize) -> Vec<u8> {
    let mut out = vec![0u8; alpha];
    for bit in out.iter_mut().take(alpha) {
        *bit = (value & 1) as u8;
        value >>= 1;
    }
    out
}

fn bits_to_integer(bits: &[u8]) -> u32 {
    let mut value = 0u32;
    for (i, bit) in bits.iter().enumerate() {
        value |= (*bit as u32) << i;
    }
    value
}

fn bits_to_bytes(bits: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; bits.len().div_ceil(8)];
    for (i, bit) in bits.iter().enumerate() {
        out[i / 8] |= *bit << (i % 8);
    }
    out
}

fn bytes_to_bits(bytes: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; bytes.len() * 8];
    for (i, byte) in bytes.iter().enumerate() {
        let mut value = *byte;
        for j in 0..8 {
            out[8 * i + j] = value & 1;
            value >>= 1;
        }
    }
    out
}

fn simple_bit_pack(poly: &[u32], b: u32) -> Vec<u8> {
    let width = bitlen(b);
    let mut bits = Vec::with_capacity(N * width);
    for coeff in poly {
        bits.extend(integer_to_bits(*coeff, width));
    }
    bits_to_bytes(&bits)
}

fn bit_pack(poly: &[i32], a: i32, b: i32) -> Vec<u8> {
    let width = bitlen((a + b) as u32);
    let mut bits = Vec::with_capacity(N * width);
    for coeff in poly {
        let encoded = (b - coeff) as u32;
        bits.extend(integer_to_bits(encoded, width));
    }
    bits_to_bytes(&bits)
}

fn simple_bit_unpack(bytes: &[u8], b: u32) -> PolyU32 {
    let width = bitlen(b);
    let bits = bytes_to_bits(bytes);
    (0..N)
        .map(|i| {
            let start = i * width;
            bits_to_integer(&bits[start..start + width])
        })
        .collect()
}

fn bit_unpack(bytes: &[u8], a: i32, b: i32) -> PolyI32 {
    let width = bitlen((a + b) as u32);
    let bits = bytes_to_bits(bytes);
    (0..N)
        .map(|i| {
            let start = i * width;
            b - bits_to_integer(&bits[start..start + width]) as i32
        })
        .collect()
}

fn hint_bit_pack(hints: &[PolyBin], ps: ParameterSet) -> Vec<u8> {
    let mut out = vec![0u8; ps.omega + ps.k];
    let mut index = 0usize;
    for (i, poly) in hints.iter().enumerate() {
        for (j, coeff) in poly.iter().enumerate() {
            if *coeff != 0 {
                out[index] = j as u8;
                index += 1;
            }
        }
        out[ps.omega + i] = index as u8;
    }
    out
}

fn hint_bit_unpack(encoded: &[u8], ps: ParameterSet) -> Option<Vec<PolyBin>> {
    if encoded.len() != ps.omega + ps.k {
        return None;
    }
    let mut hints = vec![vec![0u8; N]; ps.k];
    let mut index = 0usize;
    for i in 0..ps.k {
        let bound = encoded[ps.omega + i] as usize;
        if bound < index || bound > ps.omega {
            return None;
        }
        let first = index;
        while index < bound {
            if index > first && encoded[index - 1] >= encoded[index] {
                return None;
            }
            hints[i][encoded[index] as usize] = 1;
            index += 1;
        }
    }
    for value in &encoded[index..ps.omega] {
        if *value != 0 {
            return None;
        }
    }
    Some(hints)
}

fn pk_coeff_bound(ps: ParameterSet) -> u32 {
    (1u32 << (bitlen(Q - 1) - ps.d)) - 1
}

fn pk_len(ps: ParameterSet) -> usize {
    32 + ps.k * 32 * (bitlen(Q - 1) - ps.d)
}

fn sig_len(ps: ParameterSet) -> usize {
    (ps.lambda / 4) + ps.l * 32 * (1 + bitlen((ps.gamma1 - 1) as u32)) + ps.omega + ps.k
}

fn sig_hint_start(ps: ParameterSet) -> usize {
    (ps.lambda / 4) + ps.l * 32 * (1 + bitlen((ps.gamma1 - 1) as u32))
}

fn w1_bound(ps: ParameterSet) -> u32 {
    ((Q - 1) as i32 / (2 * ps.gamma2) - 1) as u32
}

fn w1_encode(w1: &[PolyU32], ps: ParameterSet) -> Vec<u8> {
    let bound = w1_bound(ps);
    let mut out = Vec::with_capacity(ps.k * 32 * bitlen(bound));
    for poly in w1 {
        out.extend(simple_bit_pack(poly, bound));
    }
    out
}

fn pk_encode(rho: &[u8; 32], t1: &[PolyU32], ps: ParameterSet) -> Vec<u8> {
    let mut out = Vec::with_capacity(pk_len(ps));
    out.extend_from_slice(rho);
    let bound = pk_coeff_bound(ps);
    for poly in t1 {
        out.extend(simple_bit_pack(poly, bound));
    }
    out
}

fn pk_decode(pk: &[u8], ps: ParameterSet) -> Result<([u8; 32], Vec<PolyU32>)> {
    if pk.len() != pk_len(ps) {
        bail!("pk length mismatch: expected {}, got {}", pk_len(ps), pk.len());
    }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&pk[..32]);
    let bound = pk_coeff_bound(ps);
    let poly_len = 32 * bitlen(bound);
    let mut t1 = Vec::with_capacity(ps.k);
    for i in 0..ps.k {
        let start = 32 + i * poly_len;
        t1.push(simple_bit_unpack(&pk[start..start + poly_len], bound));
    }
    Ok((rho, t1))
}

fn sig_encode(ctilde: &[u8], z: &[PolyI32], h: &[PolyBin], ps: ParameterSet) -> Vec<u8> {
    let mut out = Vec::with_capacity(sig_len(ps));
    out.extend_from_slice(ctilde);
    for poly in z {
        out.extend(bit_pack(poly, ps.gamma1 - 1, ps.gamma1));
    }
    out.extend(hint_bit_pack(h, ps));
    out
}

fn sig_decode(sig: &[u8], ps: ParameterSet) -> Result<(Vec<u8>, Vec<PolyI32>, Vec<PolyBin>)> {
    if sig.len() != sig_len(ps) {
        bail!("sig length mismatch: expected {}, got {}", sig_len(ps), sig.len());
    }
    let ctilde_len = ps.lambda / 4;
    let z_poly_len = 32 * (1 + bitlen((ps.gamma1 - 1) as u32));
    let ctilde = sig[..ctilde_len].to_vec();
    let mut z = Vec::with_capacity(ps.l);
    for i in 0..ps.l {
        let start = ctilde_len + i * z_poly_len;
        z.push(bit_unpack(
            &sig[start..start + z_poly_len],
            ps.gamma1 - 1,
            ps.gamma1,
        ));
    }
    let hint_start = sig_hint_start(ps);
    let hints = hint_bit_unpack(&sig[hint_start..], ps).context("malformed hint encoding")?;
    Ok((ctilde, z, hints))
}

fn shake256_hash(input: &[u8], out_len: usize, label: &'static str) -> (Vec<u8>, HashMetrics) {
    let mut shake = Shake256::default();
    shake.update(input);
    let mut reader = shake.finalize_xof();
    let mut out = vec![0u8; out_len];
    reader.read(&mut out);

    let total_permutations = (input.len() / SHAKE256_RATE_BYTES) + 1
        + out_len.saturating_sub(1) / SHAKE256_RATE_BYTES;
    let metrics = HashMetrics {
        label,
        input_bytes: input.len(),
        output_bytes: out_len,
        rate_bytes: SHAKE256_RATE_BYTES,
        total_permutations,
        round_rows: total_permutations * KECCAK_F1600_ROUNDS,
    };

    (out, metrics)
}

fn sample_in_ball(seed: &[u8], tau: usize) -> (Vec<i8>, SampleInBallMetrics) {
    let mut c = vec![0i8; N];

    let mut shake = Shake256::default();
    shake.update(seed);
    let mut reader = shake.finalize_xof();

    let mut sign_bytes = [0u8; 8];
    reader.read(&mut sign_bytes);
    let sign_bits = bytes_to_bits(&sign_bytes);

    let mut total_attempts = 0usize;
    let mut rejected_attempts = 0usize;

    for i in (N - tau)..N {
        let j = loop {
            let mut byte = [0u8; 1];
            reader.read(&mut byte);
            total_attempts += 1;
            let candidate = byte[0] as usize;
            if candidate <= i {
                break candidate;
            }
            rejected_attempts += 1;
        };

        c[i] = c[j];
        c[j] = if sign_bits[i + tau - N] == 0 { 1 } else { -1 };
    }

    let mut first_nonzero_positions = Vec::new();
    for (idx, coeff) in c.iter().enumerate() {
        if *coeff != 0 {
            first_nonzero_positions.push(idx);
            if first_nonzero_positions.len() == 12 {
                break;
            }
        }
    }

    let total_output_bytes = sign_bytes.len() + total_attempts;
    let total_permutations =
        (seed.len() / SHAKE256_RATE_BYTES) + 1 + total_output_bytes.saturating_sub(1) / SHAKE256_RATE_BYTES;

    (
        c.clone(),
        SampleInBallMetrics {
            seed_bytes: seed.len(),
            sign_bytes: sign_bytes.len(),
            position_bytes: total_attempts,
            total_output_bytes,
            total_permutations,
            round_rows: total_permutations * KECCAK_F1600_ROUNDS,
            total_attempts,
            rejected_attempts,
            hamming_weight: c.iter().filter(|coeff| **coeff != 0).count(),
            first_nonzero_positions,
        },
    )
}

fn build_t1(ps: ParameterSet) -> Vec<PolyU32> {
    let bound = pk_coeff_bound(ps);
    (0..ps.k)
        .map(|poly_idx| {
            (0..N)
                .map(|coeff_idx| (poly_idx as u32 * 257 + coeff_idx as u32 * 17 + 5) % (bound + 1))
                .collect()
        })
        .collect()
}

fn build_z(ps: ParameterSet) -> Vec<PolyI32> {
    (0..ps.l)
        .map(|poly_idx| {
            (0..N)
                .map(|coeff_idx| ((poly_idx as i32 * 37 + coeff_idx as i32 * 11) % 257) - 128)
                .collect()
        })
        .collect()
}

fn build_hints(ps: ParameterSet) -> Vec<PolyBin> {
    let positions: [&[usize]; K_44] = [&[1, 9, 17], &[33, 129], &[0, 128, 255], &[7]];
    let mut hints = vec![vec![0u8; N]; ps.k];
    for (poly_idx, poly_positions) in positions.iter().enumerate() {
        for position in *poly_positions {
            hints[poly_idx][*position] = 1;
        }
    }
    hints
}

fn build_w1_prime(ps: ParameterSet) -> Vec<PolyU32> {
    let bound = w1_bound(ps);
    (0..ps.k)
        .map(|poly_idx| {
            (0..N)
                .map(|coeff_idx| (poly_idx as u32 * 11 + coeff_idx as u32 * 7) % (bound + 1))
                .collect()
        })
        .collect()
}

fn build_fixture(rho_hex: &str) -> Result<Fixture> {
    let rho_vec = hex::decode(rho_hex).with_context(|| format!("invalid rho hex: {rho_hex}"))?;
    if rho_vec.len() != 32 {
        bail!("rho must be 32 bytes, got {}", rho_vec.len());
    }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&rho_vec);

    let ps = ML_DSA_44;
    let t1 = build_t1(ps);
    let z = build_z(ps);
    let hints = build_hints(ps);
    let w1_prime = build_w1_prime(ps);
    let pk = pk_encode(&rho, &t1, ps);
    let message = DEFAULT_MESSAGE.to_vec();

    let (tr, _) = shake256_hash(&pk, 64, "tr");
    let mut mu_input = Vec::with_capacity(tr.len() + message.len());
    mu_input.extend_from_slice(&tr);
    mu_input.extend_from_slice(&message);
    let (mu, _) = shake256_hash(&mu_input, 64, "mu");

    let w1_bytes = w1_encode(&w1_prime, ps);
    let mut ctilde_input = Vec::with_capacity(mu.len() + w1_bytes.len());
    ctilde_input.extend_from_slice(&mu);
    ctilde_input.extend_from_slice(&w1_bytes);
    let (ctilde, _) = shake256_hash(&ctilde_input, ps.lambda / 4, "ctilde");
    let sigma = sig_encode(&ctilde, &z, &hints, ps);

    let hint_ones = hints.iter().flatten().filter(|value| **value != 0).count();
    let w1_coeff_max = w1_prime.iter().flatten().copied().max().unwrap_or(0);
    let z_max_abs = z
        .iter()
        .flatten()
        .map(|value| value.abs())
        .max()
        .unwrap_or(0);

    Ok(Fixture {
        pk,
        sigma,
        message,
        w1_prime,
        hint_ones,
        w1_coeff_max,
        z_max_abs,
        rho_hex: rho_hex.to_owned(),
    })
}

fn make_malformed_hint_leftover_sigma(sigma: &[u8], ps: ParameterSet) -> Vec<u8> {
    let mut out = sigma.to_vec();
    let hint_start = sig_hint_start(ps);
    out[hint_start + ps.omega - 1] = 1;
    out
}

fn make_malformed_hint_non_monotone_sigma(sigma: &[u8], ps: ParameterSet) -> Vec<u8> {
    let mut out = sigma.to_vec();
    let hint_start = sig_hint_start(ps);
    out[hint_start] = 9;
    out[hint_start + 1] = 3;
    out[hint_start + ps.omega] = 2;
    out
}

fn evaluate_hash_path(fixture: &Fixture) -> Result<EvaluationReport> {
    let ps = ML_DSA_44;
    let (_rho, _t1) = pk_decode(&fixture.pk, ps)?;
    let (ctilde, z, _hints) = sig_decode(&fixture.sigma, ps)?;

    let (tr, tr_hash) = shake256_hash(&fixture.pk, 64, "tr");
    let mut mu_input = Vec::with_capacity(tr.len() + fixture.message.len());
    mu_input.extend_from_slice(&tr);
    mu_input.extend_from_slice(&fixture.message);
    let (mu, mu_hash) = shake256_hash(&mu_input, 64, "mu");

    let (_challenge, sample_metrics) = sample_in_ball(&ctilde, ps.tau);

    let w1_bytes = w1_encode(&fixture.w1_prime, ps);
    let mut ctilde_input = Vec::with_capacity(mu.len() + w1_bytes.len());
    ctilde_input.extend_from_slice(&mu);
    ctilde_input.extend_from_slice(&w1_bytes);
    let (ctilde_check, ctilde_hash) = shake256_hash(&ctilde_input, ps.lambda / 4, "ctilde_prime");

    let z_bound = ps.gamma1 - ps.beta;
    let z_bound_ok = z.iter().flatten().all(|coeff| coeff.abs() < z_bound);
    let ctilde_match = ctilde == ctilde_check;
    let hash_path_verdict = z_bound_ok && ctilde_match;
    let total_hash_round_rows_excluding_expanda = tr_hash.round_rows
        + mu_hash.round_rows
        + ctilde_hash.round_rows
        + sample_metrics.round_rows;

    let malformed_hint_leftover_rejected =
        sig_decode(&make_malformed_hint_leftover_sigma(&fixture.sigma, ps), ps).is_err();
    let malformed_hint_non_monotone_rejected =
        sig_decode(&make_malformed_hint_non_monotone_sigma(&fixture.sigma, ps), ps).is_err();
    let wrong_signature_length_rejected = sig_decode(&fixture.sigma[..fixture.sigma.len() - 1], ps).is_err();

    let mut wrong_w1 = fixture.w1_prime.clone();
    wrong_w1[0][0] = (wrong_w1[0][0] + 1) % (w1_bound(ps) + 1);
    let wrong_w1_bytes = w1_encode(&wrong_w1, ps);
    let mut wrong_ctilde_input = Vec::with_capacity(mu.len() + wrong_w1_bytes.len());
    wrong_ctilde_input.extend_from_slice(&mu);
    wrong_ctilde_input.extend_from_slice(&wrong_w1_bytes);
    let (wrong_ctilde, _) = shake256_hash(&wrong_ctilde_input, ps.lambda / 4, "wrong_ctilde_prime");
    let wrong_w1_mismatch_detected = wrong_ctilde != ctilde;

    Ok(EvaluationReport {
        methodology: "Exact FIPS 204 pkDecode/sigDecode plus SHAKE256 hash path for ML-DSA-44 Verify_internal. Arithmetic reconstruction is omitted; w1' is supplied as an external witness to isolate the remaining hash/challenge slice.",
        fixture: FixtureSummary {
            parameter_set: ps.name,
            rho_hex: fixture.rho_hex.clone(),
            message_hex: hex::encode(&fixture.message),
            message_len: fixture.message.len(),
            pk_len: fixture.pk.len(),
            sig_len: fixture.sigma.len(),
            hint_ones: fixture.hint_ones,
            w1_coeff_max: fixture.w1_coeff_max,
            z_max_abs: fixture.z_max_abs,
        },
        tr_hex: hex::encode(&tr),
        mu_hex: hex::encode(&mu),
        ctilde_hex: hex::encode(&ctilde),
        z_bound_ok,
        ctilde_match,
        hash_path_verdict,
        tr_hash,
        mu_hash,
        ctilde_hash,
        sample_in_ball: sample_metrics,
        total_hash_round_rows_excluding_expanda,
        negative_checks: NegativeChecks {
            malformed_hint_leftover_rejected,
            malformed_hint_non_monotone_rejected,
            wrong_signature_length_rejected,
            wrong_w1_mismatch_detected,
        },
    })
}

fn parse_args() -> Result<(String, Option<PathBuf>)> {
    let mut rho_hex = DEFAULT_RHO_HEX.to_owned();
    let mut out_path = None;
    let mut args = env::args().skip(1);

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--rho-hex" => {
                rho_hex = args.next().context("missing value for --rho-hex")?;
            }
            "--out" => {
                out_path = Some(PathBuf::from(args.next().context("missing value for --out")?));
            }
            other => bail!("unknown argument: {other}"),
        }
    }

    Ok((rho_hex, out_path))
}

fn main() -> Result<()> {
    let (rho_hex, out_path) = parse_args()?;
    let fixture = build_fixture(&rho_hex)?;
    let report = evaluate_hash_path(&fixture)?;
    let json = serde_json::to_string_pretty(&report)?;

    if let Some(out_path) = out_path {
        if let Some(parent) = out_path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(out_path, &json)?;
    }

    println!("{json}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hint_pack_roundtrip() {
        let hints = build_hints(ML_DSA_44);
        let packed = hint_bit_pack(&hints, ML_DSA_44);
        let decoded = hint_bit_unpack(&packed, ML_DSA_44).expect("roundtrip");
        assert_eq!(decoded, hints);
    }

    #[test]
    fn sample_in_ball_has_expected_weight() {
        let seed = vec![7u8; ML_DSA_44.lambda / 4];
        let (poly, metrics) = sample_in_ball(&seed, ML_DSA_44.tau);
        assert_eq!(metrics.hamming_weight, ML_DSA_44.tau);
        assert_eq!(poly.iter().filter(|coeff| **coeff != 0).count(), ML_DSA_44.tau);
    }

    #[test]
    fn fixture_hash_path_verdict_is_true() {
        let fixture = build_fixture(DEFAULT_RHO_HEX).expect("fixture");
        let report = evaluate_hash_path(&fixture).expect("report");
        assert!(report.hash_path_verdict);
        assert!(report.negative_checks.malformed_hint_leftover_rejected);
        assert!(report.negative_checks.malformed_hint_non_monotone_rejected);
        assert!(report.negative_checks.wrong_signature_length_rejected);
        assert!(report.negative_checks.wrong_w1_mismatch_detected);
    }
}
