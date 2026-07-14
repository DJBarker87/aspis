use aspis_core::transcript::{label, Transcript};
use aspis_prover::HOST_HASH;
use std::hint::black_box;
use std::time::Instant;

fn main() {
    let hashes = std::env::args()
        .nth(1)
        .and_then(|value| value.parse::<u64>().ok())
        .unwrap_or(10_000_000);
    let mut transcript = Transcript::new(HOST_HASH);
    transcript.absorb(label::PROFILE, b"aspis-pow-benchmark-v1");
    let started = Instant::now();
    for nonce in 0..hashes {
        black_box(transcript.grinding_ok(black_box(nonce), 63));
    }
    let seconds = started.elapsed().as_secs_f64();
    println!(
        "hashes={hashes} seconds={seconds:.6} rate_mh_s={:.3}",
        hashes as f64 / seconds / 1_000_000.0
    );
}
