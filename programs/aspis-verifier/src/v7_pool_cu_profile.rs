//! Local-only CU profile for the honest native Pool Tag-73 verifier.
//!
//! This module has its own mutually exclusive SBF entrypoint.  It is not
//! reachable from a production feature set and changes neither transcript
//! bytes nor accepted arithmetic.  The checkpoints exist solely to locate
//! the one-terminal transaction blocker with one preserved honest proof.

use aspis_core::field::{M31, QM31};
use aspis_core::state_only_hiding::StateOnlyHidingContext;
use aspis_core::v6_onefold::{
    fold_v6_onefold_queries, prepare_v6_onefold_coordinates, V6WireError,
};
use aspis_core::v6_query_batch::V6AuthenticatedQueryBatch;
use aspis_core::v6_transcript::{
    verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_and_diagnostic_trace,
    V6QueryBatchView, V6RelationDiagnosticPhase, V6SemanticView, V6TranscriptContext,
    V7TranscriptDiagnosticPhase,
};
use aspis_core::v7_onefold::{
    verify_and_gamma_combine_v7_openings_with_diagnostic_trace, V7CompactOneFoldWire,
    V7OpeningDiagnosticPhase,
};
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_verified_afterstate_v1, decode_pool_v1_pair_verifier_request_v1,
    decode_pool_v1_private_transfer_public_v1, decode_pool_v1_withdrawal_public_v1,
    encode_pool_v1_private_transfer_public_v1,
    evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1,
    pool_v1_pair_statement_digest_v1, pool_v1_private_transfer_copy_active_row_masks_compiled_v1,
    verifier_proof_body_digest_v1, verifier_statement_payload_digest_v1,
    PoolV1PrivateTransferPublicV1, PoolV1TransitionKind, POOL_V1_HISTORICAL_ANCHOR_VERSION,
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_PAIR_VERIFIER_REQUEST_MAGIC,
    POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS,
};
use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    log::{sol_log, sol_log_compute_units},
    program,
    program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::lifecycle::{proof_account_finalized, uploaded_proof_bounds};
use crate::v7_pool_native_dispatch::{
    validate_v7_pool_native_tag73_request_v1, V7PoolNativeTag73StatementV1,
    V7_POOL_NATIVE_TAG73_PROFILE_BINDING, V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
};

const PRESERVED_NATIVE_PROOF_BYTES: usize = 30_192;
const PRESERVED_NATIVE_FRONTIER_NODES: usize = 197;
const PRESERVED_NATIVE_PROOF_SHA256: [u8; 32] = [
    0x65, 0x6f, 0x25, 0x68, 0x90, 0x41, 0xae, 0x7f, 0x90, 0xc9, 0x46, 0x1f, 0x4d, 0xbe, 0x33, 0x36,
    0x47, 0x8e, 0x01, 0xe1, 0x97, 0x0f, 0xf0, 0x0c, 0x24, 0xd1, 0xe7, 0xd9, 0x0e, 0xd2, 0xe7, 0x2c,
];
const PRESERVED_NATIVE_STATEMENT_DIGEST: [u8; 32] = [
    0xe6, 0x3c, 0x56, 0x5e, 0x94, 0x25, 0x96, 0x2f, 0x73, 0xa6, 0x8c, 0xb0, 0x7e, 0x65, 0x83, 0x67,
    0x33, 0x62, 0x4b, 0x1b, 0x47, 0x4b, 0x42, 0x31, 0x07, 0x84, 0xb6, 0xa0, 0x60, 0xe0, 0x67, 0x36,
];
const PRESERVED_NATIVE_RECIPIENT_COMMITMENT: [M31; 8] = [
    M31(148_482_930),
    M31(1_116_651_461),
    M31(1_440_257_094),
    M31(1_397_310_823),
    M31(2_023_389_308),
    M31(165_313_146),
    M31(999_662_642),
    M31(1_651_087_734),
];

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_v7_pool_cu_profile_instruction);

#[inline(never)]
fn checkpoint(label: &'static str) {
    sol_log(label);
    sol_log_compute_units();
}

fn terminal_claims(view: &V6SemanticView<'_>) -> [QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS] {
    core::array::from_fn(|index| {
        let row = index / 28;
        let column = index % 28;
        view.point_claims[row][column]
    })
}

fn pool_inactive_schedule(active: &[u16; 64]) -> ([u8; 64], [u16; 64], usize) {
    let mut row_groups = [0u8; 64];
    let mut group_masks = [0u16; 64];
    let mut group_count = 0usize;
    for (row, active_mask) in active.iter().copied().enumerate() {
        let inactive_mask = !active_mask;
        let group = group_masks[..group_count]
            .iter()
            .position(|mask| *mask == inactive_mask)
            .unwrap_or_else(|| {
                let next = group_count;
                group_masks[next] = inactive_mask;
                group_count += 1;
                next
            });
        row_groups[row] = group as u8;
    }
    (row_groups, group_masks, group_count)
}

#[inline(never)]
fn log_transcript_phase(phase: V7TranscriptDiagnosticPhase) {
    let label = match phase {
        V7TranscriptDiagnosticPhase::TranscriptSetup => "aspis-v7-profile:transcript-setup",
        V7TranscriptDiagnosticPhase::SemanticSumcheck => "aspis-v7-profile:semantic-sumcheck",
        V7TranscriptDiagnosticPhase::PointClaims => "aspis-v7-profile:point-claims",
        V7TranscriptDiagnosticPhase::TerminalStart => "aspis-v7-profile:terminal-start",
        V7TranscriptDiagnosticPhase::TerminalEnd => "aspis-v7-profile:terminal-end",
        V7TranscriptDiagnosticPhase::Relation(relation) => match relation {
            V6RelationDiagnosticPhase::Start => "aspis-v7-profile:relation-start",
            V6RelationDiagnosticPhase::PreparedWeights => {
                "aspis-v7-profile:relation-prepared-weights"
            }
            V6RelationDiagnosticPhase::CircleSamples => "aspis-v7-profile:relation-circle-samples",
            V6RelationDiagnosticPhase::RelationFields => "aspis-v7-profile:relation-fields",
            V6RelationDiagnosticPhase::RoundZero => "aspis-v7-profile:relation-round-zero",
            V6RelationDiagnosticPhase::Final256 => "aspis-v7-profile:relation-final256",
            V6RelationDiagnosticPhase::Queries => "aspis-v7-profile:relation-queries",
            V6RelationDiagnosticPhase::QueryBatch => "aspis-v7-profile:relation-query-batch",
            V6RelationDiagnosticPhase::RoundOnePolynomial => {
                "aspis-v7-profile:relation-round-one-polynomial"
            }
            V6RelationDiagnosticPhase::RoundOneWeights => {
                "aspis-v7-profile:relation-round-one-weights"
            }
            V6RelationDiagnosticPhase::RoundOne => "aspis-v7-profile:relation-round-one-values",
            V6RelationDiagnosticPhase::RoundTwoPolynomial => {
                "aspis-v7-profile:relation-round-two-polynomial"
            }
            V6RelationDiagnosticPhase::RoundTwoWeights => {
                "aspis-v7-profile:relation-round-two-weights"
            }
            V6RelationDiagnosticPhase::RoundTwo => "aspis-v7-profile:relation-round-two-values",
            V6RelationDiagnosticPhase::RoundThreePolynomial => {
                "aspis-v7-profile:relation-round-three-polynomial"
            }
            V6RelationDiagnosticPhase::RoundThreeWeights => {
                "aspis-v7-profile:relation-round-three-weights"
            }
            V6RelationDiagnosticPhase::RoundThree => "aspis-v7-profile:relation-round-three-values",
            V6RelationDiagnosticPhase::Terminal => "aspis-v7-profile:relation-terminal",
        },
    };
    checkpoint(label);
}

#[inline(never)]
fn authenticate_and_fold_queries(
    wire: &V7CompactOneFoldWire<'_>,
    view: &V6QueryBatchView<'_>,
) -> Result<V6AuthenticatedQueryBatch, V6WireError> {
    checkpoint("aspis-v7-profile:query-fold-start");
    let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
    checkpoint("aspis-v7-profile:query-coordinates");
    let combined = verify_and_gamma_combine_v7_openings_with_diagnostic_trace(
        crate::verify::sbf_hashv,
        wire,
        view.queries,
        view.gamma_powers,
        |phase| {
            checkpoint(match phase {
                V7OpeningDiagnosticPhase::GammaCombined => "aspis-v7-profile:query-gamma-combined",
                V7OpeningDiagnosticPhase::LeavesHashed => "aspis-v7-profile:query-leaves-hashed",
                V7OpeningDiagnosticPhase::MerkleAuthenticated => {
                    "aspis-v7-profile:query-merkle-authenticated"
                }
            })
        },
    )?;
    checkpoint("aspis-v7-profile:query-authentication-gamma");
    let values = fold_v6_onefold_queries(&combined, &coordinates, view.alpha0);
    checkpoint("aspis-v7-profile:query-folded");
    Ok(V6AuthenticatedQueryBatch {
        values,
        line_x: coordinates.line_x,
    })
}

#[inline(never)]
fn verify_private_transfer_profile(
    program_id: &Pubkey,
    proof_account: &AccountInfo<'_>,
    proof: &[u8],
    frontier_nodes: usize,
    statement: &PoolV1PrivateTransferPublicV1,
    statement_digest: [u8; 32],
) -> ProgramResult {
    let wire = V7CompactOneFoldWire::parse_deferred_canonicality(proof, frontier_nodes)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    checkpoint("aspis-v7-profile:wire-parsed");
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding: V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
        statement_digest,
        attempt_id: proof_account.key.to_bytes(),
    };
    let (row_groups, group_masks, group_count) =
        pool_inactive_schedule(pool_v1_private_transfer_copy_active_row_masks_compiled_v1());
    checkpoint("aspis-v7-profile:inactive-schedule");
    let verified =
        verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_and_diagnostic_trace(
            crate::verify::sbf_hashv,
            &wire,
            &context,
            StateOnlyHidingContext::pool_v1_private_transfer(
                statement_digest,
                proof_account.key.to_bytes(),
            ),
            &row_groups,
            &group_masks[..group_count],
            true,
            |view| {
                evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                    statement,
                    &terminal_claims(view),
                    &view.point,
                    view.lambda,
                    view.chi,
                    view.batching.theta,
                    &view.batching.zerocheck_point,
                    view.batching.mu,
                    view.eta,
                )
                .is_ok_and(|expected| expected == view.terminal_claim)
            },
            |view| authenticate_and_fold_queries(&wire, view),
            log_transcript_phase,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let _ = verified;
    Ok(())
}

/// Measurement-only adapter from the existing honest native proof to the
/// proof-carried pair afterstate transport. The appended ASJA is deliberately
/// outside the proof transcript; this path measures composition only and is
/// unavailable in every production feature set.
#[inline(never)]
fn process_composed_one_terminal_profile(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    let [proof_account] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    if proof_account.owner != program_id
        || proof_account.is_signer
        || proof_account.is_writable
        || proof_account.executable
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let request = decode_pool_v1_pair_verifier_request_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if !matches!(
        request.binding.transition_kind,
        PoolV1TransitionKind::PrivateTransfer | PoolV1TransitionKind::Withdrawal
    ) || request.binding.verifier_program != program_id.to_bytes()
        || request.binding.profile_binding != V7_POOL_NATIVE_TAG73_PROFILE_BINDING
        || request.binding.release_binding != V7_POOL_NATIVE_TAG73_RELEASE_BINDING
        || request.binding.proof_account != proof_account.key.to_bytes()
        || request.binding.proof_body_length as usize
            != PRESERVED_NATIVE_PROOF_BYTES + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        || pool_v1_pair_statement_digest_v1(request.statement_payload, crate::verify::sbf_hashv)
            != request.binding.statement_digest
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let (
        outer_pool,
        deployment_domain,
        anchor_sequence,
        anchor_root,
        nullifier,
        asset_id,
        recipient_commitment,
        change_commitment,
    ) = match request.binding.transition_kind {
        PoolV1TransitionKind::PrivateTransfer => {
            let statement = decode_pool_v1_private_transfer_public_v1(request.statement_payload)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            (
                statement.pool,
                statement.deployment_domain,
                statement.anchor_sequence,
                statement.anchor_root,
                statement.nullifier,
                statement.asset_id,
                statement.recipient_commitment,
                statement.change_commitment,
            )
        }
        PoolV1TransitionKind::Withdrawal => {
            let statement = decode_pool_v1_withdrawal_public_v1(request.statement_payload)
                .map_err(|_| ProgramError::InvalidInstructionData)?;
            (
                statement.pool,
                statement.deployment_domain,
                statement.anchor_sequence,
                statement.anchor_root,
                statement.nullifier,
                statement.asset_id,
                PRESERVED_NATIVE_RECIPIENT_COMMITMENT,
                statement.change_commitment,
            )
        }
    };
    if outer_pool != request.binding.pool {
        return Err(ProgramError::InvalidInstructionData);
    }
    checkpoint("aspis-v7-profile:composed-request-validated");

    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (body_start, body_end) = uploaded_proof_bounds(&data)?;
    if body_end != data.len()
        || body_end - body_start
            != PRESERVED_NATIVE_PROOF_BYTES + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let split = body_start + PRESERVED_NATIVE_PROOF_BYTES;
    let proof = &data[body_start..split];
    let afterstate = &data[split..body_end];
    if verifier_proof_body_digest_v1(proof, crate::verify::sbf_hashv)
        != PRESERVED_NATIVE_PROOF_SHA256
        || decode_pool_v1_pair_verified_afterstate_v1(afterstate).is_err()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    checkpoint("aspis-v7-profile:proof-body-hash");

    // The preserved proof was produced for the legacy single-leaf Pool PDA.
    // All other public fields are taken from the outer pair instruction. This
    // one field substitution is part of the explicit unsound measurement
    // boundary and must never become a production adapter.
    let native_statement = PoolV1PrivateTransferPublicV1 {
        pool: solana_program::pubkey!("BZRi5jf2SdDMpJBJnLTHhM5EnwyzWLRDJhNYzeosRogf").to_bytes(),
        deployment_domain,
        anchor_sequence,
        anchor_root,
        nullifier,
        asset_id,
        recipient_commitment,
        change_commitment,
    };
    let native_payload = encode_pool_v1_private_transfer_public_v1(&native_statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let native_statement_digest = verifier_statement_payload_digest_v1(
        POOL_V1_HISTORICAL_ANCHOR_VERSION,
        &V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
        &V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
        &native_payload,
        crate::verify::sbf_hashv,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    if native_statement_digest != PRESERVED_NATIVE_STATEMENT_DIGEST {
        return Err(ProgramError::InvalidInstructionData);
    }
    checkpoint("aspis-v7-profile:native-statement-restored");
    verify_private_transfer_profile(
        program_id,
        proof_account,
        proof,
        PRESERVED_NATIVE_FRONTIER_NODES,
        &native_statement,
        native_statement_digest,
    )?;
    checkpoint("aspis-v7-profile:proof-accepted");
    program::set_return_data(afterstate);
    checkpoint("aspis-v7-profile:asja-return-set");
    Ok(())
}

pub fn process_v7_pool_cu_profile_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    checkpoint("aspis-v7-profile:entry");
    if instruction_data.get(..4) == Some(&POOL_V1_PAIR_VERIFIER_REQUEST_MAGIC) {
        return process_composed_one_terminal_profile(program_id, accounts, instruction_data);
    }
    let [proof_account] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    let validated = validate_v7_pool_native_tag73_request_v1(
        program_id,
        proof_account,
        instruction_data,
        crate::verify::sbf_hashv,
    )?;
    checkpoint("aspis-v7-profile:request-hashes");
    if proof_account.owner != program_id
        || proof_account.is_signer
        || proof_account.is_writable
        || proof_account.executable
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    if proof_end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let proof = &data[proof_start..proof_end];
    if proof.len() != validated.request.binding.proof_body_length as usize
        || verifier_proof_body_digest_v1(proof, crate::verify::sbf_hashv)
            != validated.request.binding.proof_body_digest
    {
        return Err(ProgramError::InvalidAccountData);
    }
    checkpoint("aspis-v7-profile:proof-body-hash");
    let V7PoolNativeTag73StatementV1::PrivateTransfer(statement) = validated.statement else {
        return Err(ProgramError::InvalidInstructionData);
    };
    verify_private_transfer_profile(
        program_id,
        proof_account,
        proof,
        validated.frontier_nodes,
        &statement,
        validated.request.binding.statement_digest,
    )?;
    checkpoint("aspis-v7-profile:complete");
    Ok(())
}
