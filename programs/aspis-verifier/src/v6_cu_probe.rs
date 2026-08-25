//! Isolated local-validator probe for the V6 packed parser and final evaluator.
//!
//! This module is never part of a production feature set. It measures the
//! exact no-allocation parser, compact-frontier counter, and all sixteen
//! packed final-256 evaluations against a sealed proof account.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::v6_onefold::{
    binary_frontier_nodes, evaluate_packed_final256_at_queries, fold_v6_onefold_queries,
    prepare_v6_onefold_coordinates, verify_and_gamma_combine_v6_binary_openings,
    verify_and_gamma_combine_v6_binary_openings_prepared, V6OneFoldWire, V6_QUERY_COUNT,
};
use aspis_core::v6_query_batch::V6AuthenticatedQueryBatch;
use aspis_core::v6_transcript::{
    verify_v6_transcript_and_relation_prepared,
    verify_v6_transcript_and_relation_prepared_with_diagnostic_trace, V6RelationDiagnosticPhase,
    V6SemanticView, V6TranscriptContext, V6TranscriptError,
};
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_group_masks_v3, atomic_state_only_copy_inactive_row_groups_v3,
    atomic_state_only_selected_masked_terminal_value_compiled_v3,
    atomic_state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace_v3,
};
use aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase;
use aspis_statement::{AtomicPaymentStatementV4, SpendPublic, STATE_ONLY_SELECTED_TERMINAL_CLAIMS};
use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    hash::hashv,
    log::{sol_log_compute_units, sol_log_data},
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

pub const V6_CU_PROBE_TAG: u8 = 68;
pub const V6_CU_PROBE_WIRE_BYTES: usize = 1 + 2 + 2 + V6_QUERY_COUNT * 4;
/// Full read-only algebra/PCS diagnostic. This remains unreachable from every
/// production build and deliberately substitutes `true` for the live
/// statement terminal while measuring all other V6 verification work.
pub const V6_FULL_CU_PROBE_TAG: u8 = 69;
pub const V6_FULL_CU_PROBE_WIRE_BYTES: usize = 1 + 2 + 2 + 1;
/// Exact semantic-terminal phase diagnostic. It shares the full probe wire,
/// runs the real terminal polynomial on transcript-derived inputs, and stops
/// before the PCS relation. It is unreachable from production builds.
pub const V6_TERMINAL_CU_PROBE_TAG: u8 = 70;
pub const V6_TERMINAL_CU_PROBE_WIRE_BYTES: usize = V6_FULL_CU_PROBE_WIRE_BYTES;
/// One-instruction core-verifier diagnostic: exact terminal, all three work
/// hashes, relation, Merkle authentication and one-fold checks. It still
/// excludes the atomic account wrapper/state write and is unreachable from
/// production builds.
pub const V6_INTEGRATED_CU_PROBE_TAG: u8 = 71;
pub const V6_INTEGRATED_CU_PROBE_WIRE_BYTES: usize = V6_FULL_CU_PROBE_WIRE_BYTES;
/// Complete diagnostic atomic wrapper around the uninstrumented V6 core.
/// This tag exists only under `v6-cu-probe`; production will use the same
/// wrapper and digest handoff after an honest proof fixture is available.
pub const V6_ATOMIC_CU_PROBE_TAG: u8 = 72;
const V6_ATOMIC_PUBLIC_WIRE_BYTES: usize = 4 * 32 + 2 * 4 + 32;
pub const V6_ATOMIC_CU_PROBE_WIRE_BYTES: usize =
    V6_FULL_CU_PROBE_WIRE_BYTES + V6_ATOMIC_PUBLIC_WIRE_BYTES;
pub const V6_PROBE_RELEASE_BINDING: [u8; 32] = [0x56; 32];
pub const V6_PROBE_STATEMENT_DIGEST: [u8; 32] = [0x53; 32];

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_v6_cu_probe_instruction);

fn read_u16(input: &mut &[u8]) -> Result<u16, ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<2>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(u16::from_le_bytes(*head))
}

fn read_u32(input: &mut &[u8]) -> Result<u32, ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<4>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(u32::from_le_bytes(*head))
}

fn read_array<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<N>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(*head)
}

fn qm31_bytes(value: QM31) -> [u8; 16] {
    let mut bytes = [0u8; 16];
    value.write_le_bytes(&mut bytes);
    bytes
}

/// Execute the real SBF SHA-256 syscall for every transcript operation. A
/// grinding call is uniquely shaped as `(32-byte state, 1-byte domain,
/// 8-byte nonce)`; only for that diagnostic call, clear the returned leading
/// bytes so the all-zero CU fixture can pass 34-bit work and continue. Work
/// hashes do not mutate transcript state, so every subsequent challenge is
/// identical to the production hash path.
fn sbf_hashv_accept_probe_work(inputs: &[&[u8]]) -> [u8; 32] {
    let mut digest = crate::verify::sbf_hashv(inputs);
    if inputs.len() == 3 && inputs[0].len() == 32 && inputs[1].len() == 1 && inputs[2].len() == 8 {
        digest[..5].fill(0);
    }
    digest
}

fn diagnostic_statement() -> AtomicPaymentStatementV4 {
    AtomicPaymentStatementV4 {
        pool: [0u8; 32],
        sequence: 0,
        spend: SpendPublic {
            anchor: [M31::ZERO; 8],
            nullifier: [M31::ZERO; 8],
            output_commitment: [M31::ZERO; 8],
            asset_id: M31::ZERO,
            fee: 0,
        },
        output_anchor: [M31::ZERO; 8],
        deployment_domain: [0u8; 32],
    }
}

fn terminal_claims(view: &V6SemanticView<'_>) -> [QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS] {
    core::array::from_fn(|index| {
        let row = index / 28;
        let column = index % 28;
        view.point_claims[row][column]
    })
}

#[inline(never)]
fn log_terminal_phase(phase: StateOnlyTerminalDiagnosticPhase) {
    match phase {
        StateOnlyTerminalDiagnosticPhase::Prepared => msg!("aspis-v6-terminal:prepared"),
        StateOnlyTerminalDiagnosticPhase::Poseidon => msg!("aspis-v6-terminal:poseidon"),
        StateOnlyTerminalDiagnosticPhase::SemanticInitial => {
            msg!("aspis-v6-terminal:semantic-initial")
        }
        StateOnlyTerminalDiagnosticPhase::SemanticAbsorption => {
            msg!("aspis-v6-terminal:semantic-absorption")
        }
        StateOnlyTerminalDiagnosticPhase::SemanticMerkle => {
            msg!("aspis-v6-terminal:semantic-merkle")
        }
        StateOnlyTerminalDiagnosticPhase::SemanticRange => {
            msg!("aspis-v6-terminal:semantic-range")
        }
        StateOnlyTerminalDiagnosticPhase::SemanticPublic => {
            msg!("aspis-v6-terminal:semantic-public")
        }
        StateOnlyTerminalDiagnosticPhase::CopyPatterns => {
            msg!("aspis-v6-terminal:copy-patterns")
        }
        StateOnlyTerminalDiagnosticPhase::CopyRouting => {
            msg!("aspis-v6-terminal:copy-routing")
        }
        StateOnlyTerminalDiagnosticPhase::Copy => msg!("aspis-v6-terminal:copy"),
        StateOnlyTerminalDiagnosticPhase::CompositionEquality => {
            msg!("aspis-v6-terminal:composition-equality")
        }
        StateOnlyTerminalDiagnosticPhase::Mask => msg!("aspis-v6-terminal:mask"),
        StateOnlyTerminalDiagnosticPhase::Final => msg!("aspis-v6-terminal:final"),
    }
    sol_log_compute_units();
}

#[inline(never)]
fn log_relation_phase(phase: V6RelationDiagnosticPhase) {
    match phase {
        V6RelationDiagnosticPhase::Start => msg!("aspis-v6-integrated:relation-start"),
        V6RelationDiagnosticPhase::PreparedWeights => {
            msg!("aspis-v6-integrated:relation-prepared-weights")
        }
        V6RelationDiagnosticPhase::CircleSamples => {
            msg!("aspis-v6-integrated:relation-circle-samples")
        }
        V6RelationDiagnosticPhase::RelationFields => {
            msg!("aspis-v6-integrated:relation-fields")
        }
        V6RelationDiagnosticPhase::RoundZero => {
            msg!("aspis-v6-integrated:relation-round-zero")
        }
        V6RelationDiagnosticPhase::Final256 => msg!("aspis-v6-integrated:relation-final256"),
        V6RelationDiagnosticPhase::Queries => msg!("aspis-v6-integrated:relation-queries"),
        V6RelationDiagnosticPhase::QueryBatch => {
            msg!("aspis-v6-integrated:relation-query-batch")
        }
        V6RelationDiagnosticPhase::RoundOnePolynomial => {
            msg!("aspis-v6-integrated:relation-round-one-polynomial")
        }
        V6RelationDiagnosticPhase::RoundOneWeights => {
            msg!("aspis-v6-integrated:relation-round-one-weights")
        }
        V6RelationDiagnosticPhase::RoundOne => {
            msg!("aspis-v6-integrated:relation-round-one-values")
        }
        V6RelationDiagnosticPhase::RoundTwoPolynomial => {
            msg!("aspis-v6-integrated:relation-round-two-polynomial")
        }
        V6RelationDiagnosticPhase::RoundTwoWeights => {
            msg!("aspis-v6-integrated:relation-round-two-weights")
        }
        V6RelationDiagnosticPhase::RoundTwo => {
            msg!("aspis-v6-integrated:relation-round-two-values")
        }
        V6RelationDiagnosticPhase::RoundThreePolynomial => {
            msg!("aspis-v6-integrated:relation-round-three-polynomial")
        }
        V6RelationDiagnosticPhase::RoundThreeWeights => {
            msg!("aspis-v6-integrated:relation-round-three-weights")
        }
        V6RelationDiagnosticPhase::RoundThree => {
            msg!("aspis-v6-integrated:relation-round-three-values")
        }
        V6RelationDiagnosticPhase::Terminal => msg!("aspis-v6-integrated:relation-terminal"),
    }
    sol_log_compute_units();
}

#[inline(never)]
fn process_v6_integrated_probe(
    program_id: &Pubkey,
    proof_account: &AccountInfo,
    proof: &[u8],
    c1_frontier_nodes: usize,
    c2_frontier_nodes: usize,
    selector: u8,
) -> ProgramResult {
    msg!("aspis-v6-integrated:entry");
    sol_log_compute_units();
    let parsed =
        V6OneFoldWire::parse_deferred_canonicality(proof, c1_frontier_nodes, c2_frontier_nodes)
            .map_err(|_| ProgramError::InvalidAccountData)?;
    msg!("aspis-v6-integrated:parsed");
    sol_log_compute_units();

    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding: V6_PROBE_RELEASE_BINDING,
        statement_digest: V6_PROBE_STATEMENT_DIGEST,
        attempt_id: proof_account.key.to_bytes(),
    };
    let statement = diagnostic_statement();
    let mut terminal_value = QM31::ZERO;
    let verified = verify_v6_transcript_and_relation_prepared_with_diagnostic_trace(
        sbf_hashv_accept_probe_work,
        &parsed,
        &context,
        selector,
        atomic_state_only_copy_inactive_row_groups_v3(),
        atomic_state_only_copy_inactive_group_masks_v3(),
        true,
        |view| {
            msg!("aspis-v6-integrated:terminal-start");
            sol_log_compute_units();
            let Ok(value) = atomic_state_only_selected_masked_terminal_value_compiled_v3(
                &statement,
                &terminal_claims(view),
                &view.point,
                view.lambda,
                view.chi,
                view.batching.theta,
                &view.batching.zerocheck_point,
                view.batching.mu,
                view.eta,
            ) else {
                return false;
            };
            terminal_value = value;
            msg!("aspis-v6-integrated:terminal-end");
            sol_log_compute_units();
            true
        },
        |view| {
            msg!("aspis-v6-integrated:query-start");
            sol_log_compute_units();
            let combined = verify_and_gamma_combine_v6_binary_openings_prepared(
                sbf_hashv_accept_probe_work,
                &parsed,
                view.queries,
                view.gamma_powers,
            )?;
            msg!("aspis-v6-integrated:merkle-and-gamma");
            sol_log_compute_units();
            let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
            msg!("aspis-v6-integrated:coordinates");
            sol_log_compute_units();
            let folded = fold_v6_onefold_queries(&combined, &coordinates, view.alpha0);
            msg!("aspis-v6-integrated:onefold-query-values");
            sol_log_compute_units();
            Ok(V6AuthenticatedQueryBatch {
                values: folded,
                line_x: coordinates.line_x,
            })
        },
        log_relation_phase,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    msg!("aspis-v6-integrated:relation-tail");
    sol_log_compute_units();
    let folded_sum = qm31_bytes(verified.folded_query_sum);
    let terminal = qm31_bytes(terminal_value);
    let slices = [
        folded_sum.as_slice(),
        terminal.as_slice(),
        verified.transcript_state_after_queries.as_slice(),
    ];
    let sink = hashv(&slices);
    sol_log_data(&[b"aspis-v6-integrated-core-probe-v1", sink.as_ref()]);
    msg!("aspis-v6-integrated:sink");
    sol_log_compute_units();
    Ok(())
}

#[inline(never)]
fn process_v6_atomic_probe<'a>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    public: &crate::atomic_payment::AtomicPaymentPublicInputs,
    c1_frontier_nodes: usize,
    c2_frontier_nodes: usize,
    selector: u8,
) -> ProgramResult {
    crate::atomic_payment::verify_and_apply_atomic_payment_state(
        program_id,
        accounts,
        public,
        |proof_account, statement, statement_digest| {
            let account_data = proof_account.try_borrow_data()?;
            if !crate::lifecycle::proof_account_finalized(&account_data) {
                return Err(ProgramError::InvalidAccountData);
            }
            let (proof_start, proof_end) = crate::lifecycle::uploaded_proof_bounds(&account_data)?;
            let proof = &account_data[proof_start..proof_end];
            let parsed = V6OneFoldWire::parse_deferred_canonicality(
                proof,
                c1_frontier_nodes,
                c2_frontier_nodes,
            )
            .map_err(|_| ProgramError::InvalidAccountData)?;
            let context = V6TranscriptContext {
                program_id: program_id.to_bytes(),
                release_binding: V6_PROBE_RELEASE_BINDING,
                statement_digest: *statement_digest,
                attempt_id: proof_account.key.to_bytes(),
            };
            verify_v6_transcript_and_relation_prepared(
                sbf_hashv_accept_probe_work,
                &parsed,
                &context,
                selector,
                atomic_state_only_copy_inactive_row_groups_v3(),
                atomic_state_only_copy_inactive_group_masks_v3(),
                true,
                |view| {
                    atomic_state_only_selected_masked_terminal_value_compiled_v3(
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
                    .is_ok()
                },
                |view| {
                    let combined = verify_and_gamma_combine_v6_binary_openings_prepared(
                        sbf_hashv_accept_probe_work,
                        &parsed,
                        view.queries,
                        view.gamma_powers,
                    )?;
                    let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
                    Ok(V6AuthenticatedQueryBatch {
                        values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
                        line_x: coordinates.line_x,
                    })
                },
            )
            .map_err(|_| ProgramError::InvalidAccountData)?;
            Ok(())
        },
    )
}

#[inline(never)]
fn process_v6_atomic_probe_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() != V6_ATOMIC_CU_PROBE_WIRE_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if proof_account.owner != program_id || proof_account.is_writable {
        return Err(ProgramError::IncorrectProgramId);
    }
    let mut input = &instruction_data[1..];
    let c1_frontier_nodes = usize::from(read_u16(&mut input)?);
    let c2_frontier_nodes = usize::from(read_u16(&mut input)?);
    let selector = input
        .first()
        .copied()
        .ok_or(ProgramError::InvalidInstructionData)?;
    input = &input[1..];
    let public = crate::atomic_payment::AtomicPaymentPublicInputs {
        current_anchor: read_array(&mut input)?,
        nullifier: read_array(&mut input)?,
        output_commitment: read_array(&mut input)?,
        output_anchor: read_array(&mut input)?,
        asset_id: read_u32(&mut input)?,
        fee: read_u32(&mut input)?,
        deployment_domain: read_array(&mut input)?,
    };
    if !input.is_empty() {
        return Err(ProgramError::InvalidInstructionData);
    }
    process_v6_atomic_probe(
        program_id,
        accounts,
        &public,
        c1_frontier_nodes,
        c2_frontier_nodes,
        selector,
    )
}

pub fn process_v6_cu_probe_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let tag = instruction_data
        .first()
        .copied()
        .ok_or(ProgramError::InvalidInstructionData)?;
    if tag == V6_ATOMIC_CU_PROBE_TAG {
        return process_v6_atomic_probe_instruction(program_id, accounts, instruction_data);
    }
    let expected_wire_bytes = match tag {
        V6_CU_PROBE_TAG => V6_CU_PROBE_WIRE_BYTES,
        V6_FULL_CU_PROBE_TAG => V6_FULL_CU_PROBE_WIRE_BYTES,
        V6_TERMINAL_CU_PROBE_TAG => V6_TERMINAL_CU_PROBE_WIRE_BYTES,
        V6_INTEGRATED_CU_PROBE_TAG => V6_INTEGRATED_CU_PROBE_WIRE_BYTES,
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    if instruction_data.len() != expected_wire_bytes {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if proof_account.owner != program_id || proof_account.is_writable {
        return Err(ProgramError::IncorrectProgramId);
    }

    let mut input = &instruction_data[1..];
    let c1_frontier_nodes = usize::from(read_u16(&mut input)?);
    let c2_frontier_nodes = usize::from(read_u16(&mut input)?);
    let mut queries = [0u32; V6_QUERY_COUNT];
    let full_selector = if tag == V6_FULL_CU_PROBE_TAG
        || tag == V6_TERMINAL_CU_PROBE_TAG
        || tag == V6_INTEGRATED_CU_PROBE_TAG
    {
        let selector = input
            .first()
            .copied()
            .ok_or(ProgramError::InvalidInstructionData)?;
        input = &input[1..];
        Some(selector)
    } else {
        for query in &mut queries {
            *query = read_u32(&mut input)?;
        }
        None
    };
    if !input.is_empty() {
        return Err(ProgramError::InvalidInstructionData);
    }

    let account_data = proof_account.try_borrow_data()?;
    if !crate::lifecycle::proof_account_finalized(&account_data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = crate::lifecycle::uploaded_proof_bounds(&account_data)?;
    let proof = &account_data[proof_start..proof_end];

    if tag == V6_TERMINAL_CU_PROBE_TAG {
        let selector = full_selector.ok_or(ProgramError::InvalidInstructionData)?;
        msg!("aspis-v6-terminal:entry");
        sol_log_compute_units();
        let parsed =
            V6OneFoldWire::parse_deferred_canonicality(proof, c1_frontier_nodes, c2_frontier_nodes)
                .map_err(|_| ProgramError::InvalidAccountData)?;
        msg!("aspis-v6-terminal:parsed");
        sol_log_compute_units();
        let context = V6TranscriptContext {
            program_id: program_id.to_bytes(),
            release_binding: V6_PROBE_RELEASE_BINDING,
            statement_digest: V6_PROBE_STATEMENT_DIGEST,
            attempt_id: proof_account.key.to_bytes(),
        };
        let statement = diagnostic_statement();
        let result = verify_v6_transcript_and_relation_prepared(
            crate::verify::sbf_hashv,
            &parsed,
            &context,
            selector,
            atomic_state_only_copy_inactive_row_groups_v3(),
            atomic_state_only_copy_inactive_group_masks_v3(),
            false,
            |view| {
                msg!("aspis-v6-terminal:start");
                sol_log_compute_units();
                let value = atomic_state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace_v3(
                    &statement,
                    &terminal_claims(view),
                    &view.point,
                    view.lambda,
                    view.chi,
                    view.batching.theta,
                    &view.batching.zerocheck_point,
                    view.batching.mu,
                    view.eta,
                    log_terminal_phase,
                );
                let Ok(value) = value else {
                    return false;
                };
                let bytes = qm31_bytes(value);
                sol_log_data(&[b"aspis-v6-terminal-value-v1", bytes.as_slice()]);
                msg!("aspis-v6-terminal:output");
                sol_log_compute_units();
                false
            },
            |_| Err(aspis_core::v6_onefold::V6WireError::WrongLength),
        );
        return match result {
            Err(V6TranscriptError::TerminalRejected) => Ok(()),
            _ => Err(ProgramError::InvalidAccountData),
        };
    }

    if tag == V6_INTEGRATED_CU_PROBE_TAG {
        let selector = full_selector.ok_or(ProgramError::InvalidInstructionData)?;
        return process_v6_integrated_probe(
            program_id,
            proof_account,
            proof,
            c1_frontier_nodes,
            c2_frontier_nodes,
            selector,
        );
    }

    if tag == V6_FULL_CU_PROBE_TAG {
        let selector = full_selector.ok_or(ProgramError::InvalidInstructionData)?;

        msg!("aspis-v6-full:entry");
        sol_log_compute_units();
        let parsed =
            V6OneFoldWire::parse_deferred_canonicality(proof, c1_frontier_nodes, c2_frontier_nodes)
                .map_err(|_| ProgramError::InvalidAccountData)?;
        msg!("aspis-v6-full:parsed");
        sol_log_compute_units();

        let context = V6TranscriptContext {
            program_id: program_id.to_bytes(),
            release_binding: V6_PROBE_RELEASE_BINDING,
            statement_digest: V6_PROBE_STATEMENT_DIGEST,
            attempt_id: proof_account.key.to_bytes(),
        };
        let verified = verify_v6_transcript_and_relation_prepared(
            crate::verify::sbf_hashv,
            &parsed,
            &context,
            selector,
            atomic_state_only_copy_inactive_row_groups_v3(),
            atomic_state_only_copy_inactive_group_masks_v3(),
            false,
            |_| true,
            |view| {
                msg!("aspis-v6-full:transcript-prefix");
                sol_log_compute_units();
                let combined = verify_and_gamma_combine_v6_binary_openings_prepared(
                    crate::verify::sbf_hashv,
                    &parsed,
                    view.queries,
                    view.gamma_powers,
                )?;
                msg!("aspis-v6-full:merkle-and-gamma");
                sol_log_compute_units();
                let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
                msg!("aspis-v6-full:coordinates");
                sol_log_compute_units();
                let folded = fold_v6_onefold_queries(&combined, &coordinates, view.alpha0);
                msg!("aspis-v6-full:onefold-query-values");
                sol_log_compute_units();
                Ok(V6AuthenticatedQueryBatch {
                    values: folded,
                    line_x: coordinates.line_x,
                })
            },
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        msg!("aspis-v6-full:relation-tail");
        sol_log_compute_units();
        let folded_sum = qm31_bytes(verified.folded_query_sum);
        let slices = [
            folded_sum.as_slice(),
            verified.transcript_state_after_queries.as_slice(),
        ];
        let sink = hashv(&slices);
        sol_log_data(&[b"aspis-v6-full-readonly-probe-v1", sink.as_ref()]);
        msg!("aspis-v6-full:sink");
        sol_log_compute_units();
        return Ok(());
    }

    msg!("aspis-v6-cu:entry");
    sol_log_compute_units();
    let parsed =
        V6OneFoldWire::parse_deferred_canonicality(proof, c1_frontier_nodes, c2_frontier_nodes)
            .map_err(|_| ProgramError::InvalidAccountData)?;
    msg!("aspis-v6-cu:parsed");
    sol_log_compute_units();

    let frontier =
        binary_frontier_nodes(queries, 18).map_err(|_| ProgramError::InvalidInstructionData)?;
    if frontier != c1_frontier_nodes || frontier != c2_frontier_nodes {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!("aspis-v6-cu:frontier");
    sol_log_compute_units();

    let gamma = QM31 {
        c0: CM31::new(M31(17), M31(23)),
        c1: CM31::new(M31(31), M31(47)),
    };
    let alpha = QM31 {
        c0: CM31::new(M31(53), M31(59)),
        c1: CM31::new(M31(61), M31(67)),
    };
    let combined = verify_and_gamma_combine_v6_binary_openings(
        crate::verify::sbf_hashv,
        &parsed,
        queries,
        gamma,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    msg!("aspis-v6-cu:merkle-and-gamma");
    sol_log_compute_units();
    let expected = evaluate_packed_final256_at_queries(parsed.fixed_fields_packed, queries)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    msg!("aspis-v6-cu:final-evaluations");
    sol_log_compute_units();
    let coordinates =
        prepare_v6_onefold_coordinates(queries).map_err(|_| ProgramError::InvalidAccountData)?;
    msg!("aspis-v6-cu:coordinates");
    sol_log_compute_units();
    let folded = fold_v6_onefold_queries(&combined, &coordinates, alpha);
    if folded != expected {
        return Err(ProgramError::InvalidAccountData);
    }
    let outputs = folded.map(qm31_bytes);
    msg!("aspis-v6-cu:onefold-query-checks");
    sol_log_compute_units();

    let slices: [&[u8]; V6_QUERY_COUNT] = core::array::from_fn(|index| outputs[index].as_slice());
    let sink = hashv(&slices);
    sol_log_data(&[b"aspis-v6-final256-probe-v1", sink.as_ref()]);
    msg!("aspis-v6-cu:sink");
    sol_log_compute_units();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lifecycle::PROOF_ACCOUNT_HEADER_LEN;
    use crate::test_support::make_account;
    use aspis_core::merkle::node_hash;
    use aspis_core::state_only_private_merkle::private_leaf_hash;
    use aspis_core::v6_onefold::{
        V6_BODY_WITHOUT_FRONTIERS, V6_C1_TREE_TAG, V6_C2_TREE_TAG, V6_FIXED_PACKED_FIELD_BYTES,
        V6_FRONTIER_CAP_PER_TREE,
    };

    fn clustered_queries() -> [u32; V6_QUERY_COUNT] {
        core::array::from_fn(|index| index as u32)
    }

    fn wire(frontier: usize, queries: [u32; V6_QUERY_COUNT]) -> Vec<u8> {
        let mut wire = Vec::with_capacity(V6_CU_PROBE_WIRE_BYTES);
        wire.push(V6_CU_PROBE_TAG);
        wire.extend_from_slice(&(frontier as u16).to_le_bytes());
        wire.extend_from_slice(&(frontier as u16).to_le_bytes());
        for query in queries {
            wire.extend_from_slice(&query.to_le_bytes());
        }
        wire
    }

    fn minimal_binary_root(entries: &[(u32, [u8; 32])], frontier: &[[u8; 32]]) -> [u8; 32] {
        let mut stream = frontier.iter();
        let mut level = entries.to_vec();
        for _ in 0..18 {
            let mut next = Vec::with_capacity(level.len());
            let mut index = 0usize;
            while index < level.len() {
                let (position, digest) = level[index];
                let parent = if position & 1 == 0
                    && index + 1 < level.len()
                    && level[index + 1].0 == position + 1
                {
                    let combined =
                        node_hash(crate::verify::sbf_hashv, &digest, &level[index + 1].1);
                    index += 2;
                    combined
                } else {
                    let sibling = stream.next().unwrap();
                    index += 1;
                    if position & 1 == 0 {
                        node_hash(crate::verify::sbf_hashv, &digest, sibling)
                    } else {
                        node_hash(crate::verify::sbf_hashv, sibling, &digest)
                    }
                };
                next.push((position >> 1, parent));
            }
            level = next;
        }
        assert!(stream.next().is_none());
        level[0].1
    }

    fn valid_body(queries: [u32; V6_QUERY_COUNT], frontier: usize) -> Vec<u8> {
        let mut body = vec![0u8; V6_BODY_WITHOUT_FRONTIERS + 2 * frontier * 32];
        let parsed = V6OneFoldWire::parse(&body, frontier, frontier).unwrap();
        let mut order: [(u32, usize); V6_QUERY_COUNT] =
            core::array::from_fn(|ordinal| (queries[ordinal], ordinal));
        order.sort_unstable_by_key(|entry| entry.0);
        let c1_entries: Vec<_> = order
            .iter()
            .map(|(query, ordinal)| {
                let record = parsed.query(*ordinal).unwrap();
                (
                    *query,
                    private_leaf_hash(
                        crate::verify::sbf_hashv,
                        V6_C1_TREE_TAG,
                        record.c1_packed,
                        record.salt,
                    ),
                )
            })
            .collect();
        let c2_entries: Vec<_> = order
            .iter()
            .map(|(query, ordinal)| {
                let record = parsed.query(*ordinal).unwrap();
                (
                    *query,
                    private_leaf_hash(
                        crate::verify::sbf_hashv,
                        V6_C2_TREE_TAG,
                        record.c2_packed,
                        record.salt,
                    ),
                )
            })
            .collect();
        let zero_frontier = vec![[0u8; 32]; frontier];
        let c1_root = minimal_binary_root(&c1_entries, &zero_frontier);
        let c2_root = minimal_binary_root(&c2_entries, &zero_frontier);
        body[V6_FIXED_PACKED_FIELD_BYTES..V6_FIXED_PACKED_FIELD_BYTES + 32]
            .copy_from_slice(&c1_root);
        body[V6_FIXED_PACKED_FIELD_BYTES + 32..V6_FIXED_PACKED_FIELD_BYTES + 64]
            .copy_from_slice(&c2_root);
        body
    }

    #[test]
    fn exact_sealed_probe_accepts_and_mismatched_frontier_rejects() {
        let program_id = crate::id();
        let proof_key = Pubkey::new_unique();
        let queries = clustered_queries();
        let frontier = binary_frontier_nodes(queries, 18).unwrap();
        assert!(frontier <= V6_FRONTIER_CAP_PER_TREE);
        let body_len = V6_BODY_WITHOUT_FRONTIERS + 2 * frontier * 32;
        let body = valid_body(queries, frontier);
        assert_eq!(body.len(), body_len);
        let mut data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + body_len];
        data[0..4].copy_from_slice(b"ASPU");
        data[4..8].copy_from_slice(&(body_len as u32).to_le_bytes());
        data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(&body);
        let mut lamports = 1;
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut lamports,
            &mut data,
            false,
            false,
        );
        assert_eq!(
            process_v6_cu_probe_instruction(
                &program_id,
                &[proof.clone()],
                &wire(frontier, queries)
            ),
            Ok(())
        );
        assert_eq!(
            process_v6_cu_probe_instruction(&program_id, &[proof], &wire(frontier + 1, queries)),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn probe_feature_cannot_change_the_production_dispatch() {
        assert_eq!(
            crate::dispatch::process_spend_production_instruction(
                &crate::id(),
                &[],
                &[V6_CU_PROBE_TAG]
            ),
            Err(ProgramError::InvalidInstructionData)
        );
    }
}
