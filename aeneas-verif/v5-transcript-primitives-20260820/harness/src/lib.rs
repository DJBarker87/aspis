#![allow(dead_code)]

use aspis_core::transcript::{QuerySampleError, Transcript};

// These are extraction roots only.  Each wrapper delegates to the unchanged
// production Transcript method and returns the updated value explicitly so
// Aeneas exposes the complete state transition in generated Lean.
pub fn extract_absorb(mut transcript: Transcript, label: u8, data: &[u8]) -> Transcript {
    transcript.absorb(label, data);
    transcript
}

pub fn extract_squeeze_block(mut transcript: Transcript) -> ([u8; 32], Transcript) {
    let block = transcript.squeeze_block();
    (block, transcript)
}

pub fn extract_queries_without_replacement(
    mut transcript: Transcript,
    count: usize,
    bound: u32,
    max_draws: usize,
) -> (Result<alloc::vec::Vec<u32>, QuerySampleError>, Transcript) {
    let result = transcript.challenge_queries_without_replacement(count, bound, max_draws);
    (result, transcript)
}

pub fn extract_grinding_ok(transcript: &Transcript, nonce: u64, bits: u8) -> bool {
    transcript.grinding_ok(nonce, bits)
}

extern crate alloc;
