use std::env;
use std::fs;

use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::state_only_masked_switch::{
    verify_state_only_masked_switch_diagnostic_unmined, MASKED_SWITCH_COEFFICIENTS,
};
use aspis_prover::state_only_masked_switch::build_state_only_masked_switch_diagnostic;
use sha2::{Digest, Sha256};

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

fn q(seed: u32, index: usize) -> QM31 {
    let a = seed.wrapping_add((index as u32 + 1).wrapping_mul(0x9e37_79b9)) & P;
    let b = seed.rotate_left(7).wrapping_add(index as u32 * 17 + 3) & P;
    let c = seed.rotate_left(13).wrapping_add(index as u32 * 29 + 5) & P;
    let d = seed.rotate_left(19).wrapping_add(index as u32 * 43 + 7) & P;
    QM31 {
        c0: CM31 {
            a: M31(a),
            b: M31(b),
        },
        c1: CM31 {
            a: M31(c),
            b: M31(d),
        },
    }
}

fn main() {
    let output = env::args()
        .nth(1)
        .unwrap_or_else(|| "results/stage2/proofs/state_only_masked_switch_p21_unmined.bin".into());
    let statement_digest = hash(&[b"aspis/state-only/profile21/masked-switch/fixture/v1"]);
    let x = core::array::from_fn::<_, MASKED_SWITCH_COEFFICIENTS, _>(|index| q(0x1357_2468, index));
    let f = core::array::from_fn::<_, MASKED_SWITCH_COEFFICIENTS, _>(|index| q(0x2468_1357, index));
    let built = build_state_only_masked_switch_diagnostic(&statement_digest, x, f, hash)
        .expect("build masked-switch diagnostic");
    let schedule =
        verify_state_only_masked_switch_diagnostic_unmined(&built.proof, &statement_digest, hash)
            .expect("verify masked-switch diagnostic");
    assert_eq!(schedule, built.schedule);
    fs::write(&output, &built.proof).expect("write proof");
    println!("proof={output}");
    println!("bytes={}", built.proof.len());
    let digest_hex = statement_digest
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    println!("statement_digest={digest_hex}");
    println!("xf_frontier_nodes={}", built.xf_frontier_nodes);
    println!("u_frontier_nodes={}", built.u_frontier_nodes);
    println!("queries={:?}", built.schedule.queries);
}
