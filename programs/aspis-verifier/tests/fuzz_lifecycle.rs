//! Fuzz-style state-machine harness for the proof-account lifecycle
//! (wire tags 0 init, 1 upload, 62 finalize, 64 close).
//!
//! Approach: proptest on the pinned stable toolchain drives the real
//! dispatcher over sequences of adversarial operations against one persistent
//! proof-account buffer, the same way the runtime would across transactions.
//!
//! Invariants asserted after every step:
//!  * No panic on any offset/length, including overlaps, duplicates,
//!    truncation, and near-`u32::MAX` offsets (no arithmetic overflow).
//!  * No partial-seal acceptance: once the account reads as finalized
//!    (magic present, authority field zeroed), every upload fails closed.
//!  * Offset bounds: an accepted upload writes only inside the declared proof
//!    region `[40, 40 + declared_len)` — the header and every byte past the
//!    declared region are left untouched.

use aspis_verifier::{id, process_spend_production_instruction, PROOF_ACCOUNT_HEADER_LEN};
use proptest::prelude::*;
use solana_program::{
    account_info::AccountInfo, clock::Epoch, program_error::ProgramError, pubkey::Pubkey,
};

const HEADER: usize = PROOF_ACCOUNT_HEADER_LEN; // 40
const MAGIC: [u8; 4] = *b"ASPU";
const AUTHORITY_OFFSET: usize = 8;
const BODY_CAP: usize = 128;
const ACCOUNT_LEN: usize = HEADER + BODY_CAP;

const AUTH_KEY: [u8; 32] = [9u8; 32];

#[derive(Clone, Debug)]
enum Op {
    Init { total_len: u32 },
    Upload { offset: u32, chunk: Vec<u8> },
    Finalize,
    Close,
}

fn op_strategy() -> impl Strategy<Value = Op> {
    let init = (0u32..256).prop_map(|total_len| Op::Init { total_len });
    let upload = (
        prop_oneof![
            0u32..(BODY_CAP as u32 + 16),
            Just(u32::MAX),
            Just(u32::MAX - 3),
            (u32::MAX - 160)..u32::MAX,
        ],
        proptest::collection::vec(any::<u8>(), 0..48),
    )
        .prop_map(|(offset, chunk)| Op::Upload { offset, chunk });
    prop_oneof![
        3 => upload,
        2 => init,
        1 => Just(Op::Finalize),
        1 => Just(Op::Close),
    ]
}

fn is_initialized(buf: &[u8]) -> bool {
    buf.len() >= HEADER && buf[0..4] == MAGIC
}

fn is_finalized(buf: &[u8]) -> bool {
    is_initialized(buf)
        && buf[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32]
            .iter()
            .all(|b| *b == 0)
}

fn declared_len(buf: &[u8]) -> Option<usize> {
    if !is_initialized(buf) {
        return None;
    }
    Some(u32::from_le_bytes(buf[4..8].try_into().unwrap()) as usize)
}

/// Encode one op into the production wire and run it against the persistent
/// proof buffer. The authority/refund accounts are always well-formed so that
/// happy paths are reachable; the adversarial content is the op parameters.
fn run_op(op: &Op, proof_buf: &mut Vec<u8>, proof_lamports: &mut u64) -> Result<(), ProgramError> {
    let program_id = id();
    let system_id = solana_program::system_program::id();
    let proof_key = Pubkey::new_from_array([1u8; 32]);
    let authority_key = Pubkey::new_from_array(AUTH_KEY);
    let refund_key = Pubkey::new_from_array([2u8; 32]);

    let (instruction_data, use_refund): (Vec<u8>, bool) = match op {
        Op::Init { total_len } => {
            let mut d = vec![0u8];
            d.extend_from_slice(&total_len.to_le_bytes());
            (d, false)
        }
        Op::Upload { offset, chunk } => {
            let mut d = vec![1u8];
            d.extend_from_slice(&offset.to_le_bytes());
            d.extend_from_slice(&(chunk.len() as u32).to_le_bytes());
            d.extend_from_slice(chunk);
            (d, false)
        }
        Op::Finalize => (vec![62u8], false),
        Op::Close => (vec![64u8], true),
    };

    let mut authority_lamports = 0u64;
    let mut authority_data: [u8; 0] = [];
    let mut refund_lamports = 5_000u64;
    let mut refund_data: [u8; 0] = [];

    let proof = AccountInfo::new(
        &proof_key,
        true,
        true,
        proof_lamports,
        proof_buf.as_mut_slice(),
        &program_id,
        false,
        Epoch::default(),
    );

    let second = if use_refund {
        AccountInfo::new(
            &refund_key,
            true,
            true,
            &mut refund_lamports,
            &mut refund_data,
            &system_id,
            false,
            Epoch::default(),
        )
    } else {
        AccountInfo::new(
            &authority_key,
            true,
            false,
            &mut authority_lamports,
            &mut authority_data,
            &program_id,
            false,
            Epoch::default(),
        )
    };

    let accounts = [proof, second];
    process_spend_production_instruction(&program_id, &accounts, &instruction_data)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn lifecycle_sequences_preserve_invariants(
        ops in proptest::collection::vec(op_strategy(), 1..14),
    ) {
        let mut buf = vec![0u8; ACCOUNT_LEN];
        let mut lamports = 1_000_000u64;

        for op in &ops {
            let before = buf.clone();
            let sealed_before = is_finalized(&before);
            let dlen_before = declared_len(&before);

            let result = run_op(op, &mut buf, &mut lamports);

            if let Op::Upload { .. } = op {
                // No partial-seal acceptance: a sealed account rejects uploads.
                if sealed_before {
                    prop_assert!(
                        result.is_err(),
                        "upload accepted against a finalized (sealed) account"
                    );
                }
                // An accepted upload stays strictly inside the declared region:
                // the header and everything past `40 + declared_len` is intact.
                if result.is_ok() {
                    prop_assert_eq!(&buf[..HEADER], &before[..HEADER], "upload mutated the header");
                    if let Some(d) = dlen_before {
                        let tail = HEADER.saturating_add(d).min(buf.len());
                        prop_assert_eq!(
                            &buf[tail..],
                            &before[tail..],
                            "upload wrote past the declared proof region"
                        );
                    }
                }
            }
        }
    }
}
