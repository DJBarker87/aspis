//! The deployment wire surface: entrypoint and minimal production dispatch.

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::atomic_payment;
use crate::lifecycle;
use crate::verify;

#[cfg(all(not(feature = "no-entrypoint"), feature = "spend-minimal-dispatch"))]
solana_program::entrypoint!(process_spend_production_instruction);

/// Parse exactly one fixed-width byte array from the production wire.
///
/// The historical Borsh enum is intentionally not referenced by the minimal
/// entrypoint.  Avoiding that reference lets the SBF linker discard every
/// superseded wire arm while retaining byte-for-byte wire compatibility for
/// the eight lifecycle tags used in production.
fn production_take<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<N>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(*head)
}

fn production_u32(input: &mut &[u8]) -> Result<u32, ProgramError> {
    Ok(u32::from_le_bytes(production_take::<4>(input)?))
}

fn production_u64(input: &mut &[u8]) -> Result<u64, ProgramError> {
    Ok(u64::from_le_bytes(production_take::<8>(input)?))
}

fn production_require_empty(input: &[u8]) -> ProgramResult {
    if input.is_empty() {
        Ok(())
    } else {
        Err(ProgramError::InvalidInstructionData)
    }
}

/// The deployment-only wire surface.
///
/// Accepted append-only tags:
///
/// - 0: initialize a fresh proof account;
/// - 1: upload one proof chunk;
/// - 59: production read-only verification;
/// - 60: production verification plus atomic state transition;
/// - 62: irreversibly finalize the proof account;
/// - 63: initialize a fresh atomic pool;
/// - 64: close a sealed proof account and refund every lamport; and
/// - 65: production verification plus the atomic state transition and an
///   atomic proof-account close and rent refund; and
/// - 67: complete v5 verification plus the retained-proof atomic state
///   transition, enabled by the default `v5-production-tag67` feature.
/// - 72: complete V6 one-fold verification plus the retained-proof atomic
///   state transition, enabled by `v6-production-tag72`.
/// - 73: complete compact V7 one-fold verification plus the retained-proof
///   atomic state transition, enabled by `v7-production-tag73`.
/// - 74: initialize an exact pending verifier-owned Pool authorization
///   receipt for one complete unsealed Tag-73 proof upload.
/// - 75: verify that Tag-73 proof and finalize its exact pending receipt.
/// - 76: close a canonical pending or finalized Pool authorization receipt
///   and refund its embedded authority.
/// - `ASVQ`: exact Pool-selected Tag-73 read-only profile dispatch, enabled by
///   `v7-pool-dispatch-profile`. This is a four-byte discriminator rather than
///   another numeric prefix because `ASVQ` is already the frozen CPI request.
///
/// Every other historical or diagnostic tag fails before account access.
pub fn process_spend_production_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    // A valid ASVQ is at least the 384-byte prefix plus one payload byte. The
    // length gate preserves the historical fixed 169-byte numeric tag-65 wire
    // even in the rare case its first public bytes spell `SVQ`.
    #[cfg(any(feature = "v7-pool-dispatch-profile", test))]
    if instruction_data.len()
        > aspis_statement::pool_v1::POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES
        && instruction_data
            .starts_with(&aspis_statement::pool_v1::POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC)
    {
        if instruction_data.len()
            == crate::v7_pool_native_dispatch::V7_POOL_NATIVE_TAG73_REQUEST_BYTES
        {
            return crate::v7_pool_native_dispatch::process_v7_pool_native_tag73_asvq_instruction(
                program_id,
                accounts,
                instruction_data,
            );
        }
        return crate::v7_pool_dispatch::process_v7_pool_tag73_asvq_instruction(
            program_id,
            accounts,
            instruction_data,
        );
    }

    let (&tag, mut wire) = instruction_data
        .split_first()
        .ok_or(ProgramError::InvalidInstructionData)?;

    match tag {
        0 => {
            let total_len = production_u32(&mut wire)?;
            production_require_empty(wire)?;
            lifecycle::init_proof(program_id, accounts, total_len)
        }
        1 => {
            let offset = production_u32(&mut wire)?;
            let chunk_len = production_u32(&mut wire)? as usize;
            if wire.len() != chunk_len {
                return Err(ProgramError::InvalidInstructionData);
            }
            lifecycle::upload_chunk(program_id, accounts, offset, wire)
        }
        59 => {
            let pool = production_take::<32>(&mut wire)?;
            let sequence = production_u64(&mut wire)?;
            let public_input = production_take::<104>(&mut wire)?;
            let output_anchor = production_take::<32>(&mut wire)?;
            let deployment_domain = production_take::<32>(&mut wire)?;
            let diagnostic_unmined = production_take::<1>(&mut wire)?[0];
            production_require_empty(wire)?;
            if diagnostic_unmined != 0 {
                return Err(ProgramError::InvalidInstructionData);
            }
            let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
            if proof_account.owner != program_id || proof_account.is_writable {
                return Err(ProgramError::IncorrectProgramId);
            }
            let pool_account = accounts.get(1).ok_or(ProgramError::NotEnoughAccountKeys)?;
            if pool_account.owner != program_id || pool_account.is_writable {
                return Err(ProgramError::IncorrectProgramId);
            }
            if pool_account.key.to_bytes() != pool {
                return Err(ProgramError::InvalidArgument);
            }
            let pool_state =
                atomic_payment::AtomicPoolStateV2::decode(&pool_account.try_borrow_data()?)?;
            if pool_state.deployment_domain != deployment_domain {
                return Err(ProgramError::Custom(
                    atomic_payment::ATOMIC_ERROR_DEPLOYMENT_DOMAIN_MISMATCH,
                ));
            }
            verify::verify_uploaded_atomic_spend_acceptance_v4(
                proof_account,
                pool,
                sequence,
                &public_input,
                output_anchor,
                deployment_domain,
            )
        }
        60 => {
            let current_anchor = production_take::<32>(&mut wire)?;
            let nullifier = production_take::<32>(&mut wire)?;
            let output_commitment = production_take::<32>(&mut wire)?;
            let output_anchor = production_take::<32>(&mut wire)?;
            let asset_id = production_u32(&mut wire)?;
            let fee = production_u32(&mut wire)?;
            let deployment_domain = production_take::<32>(&mut wire)?;
            production_require_empty(wire)?;
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
                deployment_domain,
            };
            atomic_payment::verify_and_apply_atomic_payment_state(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify::verify_uploaded_atomic_spend_production_statement_v4(
                        proof_account,
                        statement,
                    )
                },
            )
        }
        // Keep the frozen production API's explicit fail-closed result for
        // the former diagnostic mutation tag.  Returning the same custom
        // error preserves the published API behavior without rooting a
        // diagnostic verifier or CU-marker graph in the ELF.
        61 => Err(ProgramError::Custom(
            atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
        )),
        62 => {
            production_require_empty(wire)?;
            lifecycle::finalize_proof(program_id, accounts)
        }
        63 => {
            let sequence = production_u64(&mut wire)?;
            let anchor = production_take::<32>(&mut wire)?;
            let domain_tag_len = production_u32(&mut wire)? as usize;
            if wire.len() != domain_tag_len {
                return Err(ProgramError::InvalidInstructionData);
            }
            lifecycle::initialize_atomic_pool(program_id, accounts, sequence, anchor, wire)
        }
        64 => {
            production_require_empty(wire)?;
            lifecycle::close_proof(program_id, accounts)
        }
        65 => {
            let current_anchor = production_take::<32>(&mut wire)?;
            let nullifier = production_take::<32>(&mut wire)?;
            let output_commitment = production_take::<32>(&mut wire)?;
            let output_anchor = production_take::<32>(&mut wire)?;
            let asset_id = production_u32(&mut wire)?;
            let fee = production_u32(&mut wire)?;
            let deployment_domain = production_take::<32>(&mut wire)?;
            production_require_empty(wire)?;
            let public = atomic_payment::AtomicPaymentPublicInputs {
                current_anchor,
                nullifier,
                output_commitment,
                output_anchor,
                asset_id,
                fee,
                deployment_domain,
            };
            atomic_payment::verify_and_apply_atomic_payment_state_with_proof_refund(
                program_id,
                accounts,
                &public,
                |proof_account, statement, _statement_digest| {
                    verify::verify_uploaded_atomic_spend_production_statement_v4(
                        proof_account,
                        statement,
                    )?;
                    lifecycle::log_uploaded_proof_sha256(proof_account)
                },
            )
        }
        #[cfg(feature = "v5-production-tag67")]
        67 => crate::v5_full_transaction::process_v5_full_cu_transaction_with_verifier(
            program_id,
            accounts,
            instruction_data,
            crate::v5_cu_probe::verify_uploaded_v5_mode9_cu_fixture,
        ),
        #[cfg(feature = "v6-production-tag72")]
        72 => crate::v6_transaction::process_v6_atomic_instruction(
            program_id,
            accounts,
            instruction_data,
        ),
        #[cfg(feature = "v7-production-tag73")]
        73 => crate::v7_transaction::process_v7_atomic_instruction(
            program_id,
            accounts,
            instruction_data,
        ),
        #[cfg(feature = "v7-pool-dispatch-profile")]
        crate::v7_pool_receipt::V7_POOL_RECEIPT_INITIALIZE_TAG => {
            crate::v7_pool_receipt::process_v7_pool_receipt_initialize_instruction(
                program_id, accounts, wire,
            )
        }
        #[cfg(feature = "v7-pool-dispatch-profile")]
        crate::v7_pool_receipt::V7_POOL_RECEIPT_FINALIZE_TAG => {
            crate::v7_pool_receipt::process_v7_pool_receipt_finalize_instruction(
                program_id, accounts, wire,
            )
        }
        #[cfg(feature = "v7-pool-dispatch-profile")]
        crate::v7_pool_receipt::V7_POOL_RECEIPT_CLOSE_TAG => {
            crate::v7_pool_receipt::process_v7_pool_receipt_close_instruction(
                program_id, accounts, wire,
            )
        }
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atomic_payment;
    use crate::id;
    use crate::wire::AspisInstruction;

    #[test]
    fn spend_minimal_dispatch_preserves_required_borsh_wires_only() {
        let required = [
            AspisInstruction::InitProof { total_len: 61_599 },
            AspisInstruction::UploadChunk {
                offset: 17,
                chunk: vec![1, 2, 3, 4],
            },
            AspisInstruction::VerifyAtomicStateOnlySpendV4 {
                pool: [1u8; 32],
                sequence: 73,
                public_input: [2u8; 104],
                output_anchor: [3u8; 32],
                deployment_domain: [5u8; 32],
                diagnostic_unmined: false,
            },
            AspisInstruction::ApplyAtomicStateOnlySpendV4 {
                current_anchor: [1u8; 32],
                nullifier: [2u8; 32],
                output_commitment: [3u8; 32],
                output_anchor: [4u8; 32],
                asset_id: 17,
                fee: 1,
                deployment_domain: [5u8; 32],
            },
            AspisInstruction::FinalizeProof,
            AspisInstruction::InitializeAtomicPool {
                sequence: 0,
                anchor: [0u8; 32],
                domain_tag: b"devnet".to_vec(),
            },
            AspisInstruction::CloseFinalizedProof,
            AspisInstruction::ApplyAtomicStateOnlySpendV4WithProofRefund {
                current_anchor: [1u8; 32],
                nullifier: [2u8; 32],
                output_commitment: [3u8; 32],
                output_anchor: [4u8; 32],
                asset_id: 17,
                fee: 1,
                deployment_domain: [5u8; 32],
            },
        ];

        for instruction in required {
            let wire = borsh::to_vec(&instruction).unwrap();
            assert!(matches!(wire[0], 0 | 1 | 59 | 60 | 62 | 63 | 64 | 65));
            assert_eq!(
                process_spend_production_instruction(&id(), &[], &wire),
                Err(ProgramError::NotEnoughAccountKeys),
                "required tag {} was not parsed through the minimal wire",
                wire[0]
            );
        }

        let historical = borsh::to_vec(&AspisInstruction::Verify {
            statement_digest: [0u8; 32],
        })
        .unwrap();
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &historical),
            Err(ProgramError::InvalidInstructionData)
        );

        let mut trailing = borsh::to_vec(&AspisInstruction::FinalizeProof).unwrap();
        trailing.push(0);
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &trailing),
            Err(ProgramError::InvalidInstructionData)
        );

        let diagnostic = borsh::to_vec(&AspisInstruction::VerifyAtomicStateOnlySpendV4 {
            pool: [1u8; 32],
            sequence: 73,
            public_input: [2u8; 104],
            output_anchor: [3u8; 32],
            deployment_domain: [5u8; 32],
            diagnostic_unmined: true,
        })
        .unwrap();
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &diagnostic),
            Err(ProgramError::InvalidInstructionData)
        );

        let diagnostic_mutation =
            borsh::to_vec(&AspisInstruction::MeasureAtomicStateOnlySpendMutationV3 {
                current_anchor: [1u8; 32],
                nullifier: [2u8; 32],
                output_commitment: [3u8; 32],
                output_anchor: [4u8; 32],
                asset_id: 17,
                fee: 1,
            })
            .unwrap();
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &diagnostic_mutation),
            Err(ProgramError::Custom(
                atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
            ))
        );

        assert_eq!(
            process_spend_production_instruction(&id(), &[], &[66]),
            Err(ProgramError::InvalidInstructionData)
        );
        #[cfg(not(feature = "v5-production-tag67"))]
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &[67]),
            Err(ProgramError::InvalidInstructionData)
        );
        #[cfg(not(feature = "v6-production-tag72"))]
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &[72]),
            Err(ProgramError::InvalidInstructionData)
        );
        #[cfg(not(feature = "v7-production-tag73"))]
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &[73]),
            Err(ProgramError::InvalidInstructionData)
        );
        #[cfg(not(feature = "v7-pool-dispatch-profile"))]
        for tag in [
            crate::v7_pool_receipt::V7_POOL_RECEIPT_INITIALIZE_TAG,
            crate::v7_pool_receipt::V7_POOL_RECEIPT_FINALIZE_TAG,
            crate::v7_pool_receipt::V7_POOL_RECEIPT_CLOSE_TAG,
        ] {
            assert_eq!(
                process_spend_production_instruction(&id(), &[], &[tag]),
                Err(ProgramError::InvalidInstructionData)
            );
        }
    }

    #[cfg(feature = "v5-production-tag67")]
    #[test]
    fn tag67_production_routes_only_through_atomic_wrapper() {
        let program_id = id();
        let mut wire = vec![0u8; crate::v5_full_transaction::V5_FULL_CU_TRANSACTION_WIRE_BYTES];
        wire[0] = crate::v5_full_transaction::V5_FULL_CU_TRANSACTION_TAG;
        let nullifier = {
            use aspis_core::field::M31;

            (0..10_000u32)
                .find_map(|seed| {
                    let digest = core::array::from_fn(|index| M31(seed + index as u32 * 17));
                    let nullifier = aspis_statement::encode_digest_canonical(&digest);
                    let (_, bump) =
                        atomic_payment::atomic_nullifier_address(&program_id, &nullifier);
                    (bump == crate::v5_full_transaction::V5_NULLIFIER_PDA_BUMP).then_some(nullifier)
                })
                .expect("test nullifier with bump 255")
        };
        wire[33..65].copy_from_slice(&nullifier);
        assert_eq!(
            process_spend_production_instruction(&program_id, &[], &wire),
            Err(ProgramError::NotEnoughAccountKeys)
        );

        // Tag 66 remains unreachable when Tag 67 production dispatch is enabled.
        assert_eq!(
            process_spend_production_instruction(&program_id, &[], &[66]),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[cfg(feature = "v6-production-tag72")]
    #[test]
    fn tag72_production_routes_only_through_v6_atomic_parser() {
        let mut wire = vec![0u8; crate::v6_transaction::V6_ATOMIC_WIRE_BYTES];
        wire[0] = crate::v6_transaction::V6_PRODUCTION_TAG;
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &wire),
            Err(ProgramError::NotEnoughAccountKeys)
        );

        // The adjacent probe-only tags remain unreachable in production.
        for tag in [68u8, 69, 70, 71] {
            assert_eq!(
                process_spend_production_instruction(&id(), &[], &[tag]),
                Err(ProgramError::InvalidInstructionData)
            );
        }
    }

    #[cfg(feature = "v7-production-tag73")]
    #[test]
    fn tag73_production_routes_only_through_v7_atomic_parser() {
        let mut wire = vec![0u8; crate::v7_transaction::V7_ATOMIC_WIRE_BYTES];
        wire[0] = crate::v7_transaction::V7_PRODUCTION_TAG;
        assert_eq!(
            process_spend_production_instruction(&id(), &[], &wire),
            Err(ProgramError::NotEnoughAccountKeys)
        );
    }

    #[cfg(feature = "v7-pool-dispatch-profile")]
    #[test]
    fn tag74_to_76_route_only_through_pool_receipt_handlers() {
        for tag in [
            crate::v7_pool_receipt::V7_POOL_RECEIPT_INITIALIZE_TAG,
            crate::v7_pool_receipt::V7_POOL_RECEIPT_FINALIZE_TAG,
            crate::v7_pool_receipt::V7_POOL_RECEIPT_CLOSE_TAG,
        ] {
            assert_eq!(
                process_spend_production_instruction(&id(), &[], &[tag]),
                Err(ProgramError::NotEnoughAccountKeys),
                "receipt tag {tag} was not routed through its exact account gate"
            );
        }
    }
}
