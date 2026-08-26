//! State-bound prepared settlement for Pool V1.
//!
//! Preparation consumes the same sealed canonical Pool/tree capability as the
//! direct append path and performs every Poseidon operation there.  The final
//! gate below is intentionally pure: it authenticates exact byte images with
//! SHA-256, checks the Pool-owned plan PDA, statement/receipt/nullifier/time
//! bindings, and returns borrowed precomputed images.  It contains no Merkle
//! append or Poseidon call.

extern crate alloc;

use alloc::{boxed::Box, vec};

use aspis_core::transcript::HashFn;
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_authorization_receipt_account_v1, decode_pool_v1_private_transfer_public_v1,
        decode_pool_v1_withdrawal_public_v1, decode_verifier_policy_v1,
        encode_historical_anchor_envelope_v1, historical_anchor_envelope_digest_v1,
        pool_v1_authorization_receipt_pda_inputs_for_binding_v1, root_history_location,
        validate_pool_v1_authorization_receipt_account_pda_inputs_v1,
        validate_pool_v1_authorization_receipt_account_request_v1,
        validate_pool_v1_authorization_receipt_for_settlement_v1,
        verifier_statement_payload_digest_v1, HistoricalAnchorEnvelopeV1,
        PoolV1AuthorizationReceiptAccountStatusV1, PoolV1AuthorizationReceiptPdaInputsV1,
        PoolV1AuthorizationReceiptV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
        PoolV1WithdrawalPublicV1, VerifierDispatchRequestV1,
        POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES, POOL_V1_AUTHORIZATION_RECEIPT_SEED,
        POOL_V1_PAYMENT_STATEMENT_BYTES, POOL_V1_ROOT_HISTORY_CAPACITY,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    },
    poseidon2::Digest,
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::{
    anchor::{
        authenticate_historical_anchor_after_prevalidated_state_v1, HistoricalAnchorAuthorizationV1,
    },
    error::PoolV1ProgramError,
    history::{
        append_roots_unchecked, pool_v1_root_page_address, validate_new_page_account,
        validate_root_page_bytes, write_new_page_unchecked, RootPageHeaderV1,
    },
    nullifier::{pool_v1_nullifier_marker_address, PlannedNullifierMarkerV1},
    prepared_settlement_format::{
        decode_prepared_settlement_plan_v1, encode_prepared_settlement_plan_v1,
        exact_image_digest_v1, pool_v1_prepared_settlement_plan_address,
        PreparedSettlementPlanFieldsV1, PreparedSettlementPlanImagesV1,
        PreparedSettlementPlanViewV1, PreparedSettlementRolloverShardAccountV1,
    },
    registry::{
        authenticate_verifier_selection_v1, AuthenticatedVerifierSelectionV1, VerifierSelectionV1,
    },
    state::{
        CanonicalPoolStateV1, POOL_V1_STATE_ACCOUNT_BYTES, POOL_V1_STATE_IDENTITY_OFFSET,
        POOL_V1_STATE_POLICY_OFFSET, POOL_V1_STATE_TREE_OFFSET,
    },
    transition::{
        prepare_authorized_append_images_v1, validate_current_history_after_prevalidated_anchor_v1,
        AuthorizedAppendReceiptV1, AuthorizedAppendV1,
    },
};

const STATE_SEQUENCE_OFFSET: usize = 40;
const STATE_PAGE_OFFSET: usize = 48;
const STATE_SLOT_OFFSET: usize = 56;
const TREE_SEQUENCE_RELATIVE_OFFSET: usize = 8;
const TREE_ROOT_RELATIVE_OFFSET: usize = 16;
const TREE_FRONTIER_RELATIVE_OFFSET: usize = 48;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CanonicalSettlementStatementV1 {
    PrivateTransfer(PoolV1PrivateTransferPublicV1),
    Withdrawal(PoolV1WithdrawalPublicV1),
}

/// Sealed, canonical statement action returned by the final apply gate.  A
/// custody processor can consume the authenticated withdrawal fields directly
/// and must not reparse an unchecked payload after this point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AuthenticatedPreparedSettlementActionV1 {
    statement: CanonicalSettlementStatementV1,
}

impl AuthenticatedPreparedSettlementActionV1 {
    pub(crate) fn transition_kind(self) -> PoolV1TransitionKind {
        self.statement.transition_kind()
    }

    pub(crate) fn withdrawal_amount_and_destination(self) -> Option<(u32, [u8; 32])> {
        match self.statement {
            CanonicalSettlementStatementV1::PrivateTransfer(_) => None,
            CanonicalSettlementStatementV1::Withdrawal(statement) => {
                Some((statement.amount, statement.destination_token_account))
            }
        }
    }
}

impl CanonicalSettlementStatementV1 {
    fn transition_kind(self) -> PoolV1TransitionKind {
        match self {
            Self::PrivateTransfer(_) => PoolV1TransitionKind::PrivateTransfer,
            Self::Withdrawal(_) => PoolV1TransitionKind::Withdrawal,
        }
    }

    fn pool(self) -> [u8; 32] {
        match self {
            Self::PrivateTransfer(statement) => statement.pool,
            Self::Withdrawal(statement) => statement.pool,
        }
    }

    fn deployment_domain(self) -> [u8; 32] {
        match self {
            Self::PrivateTransfer(statement) => statement.deployment_domain,
            Self::Withdrawal(statement) => statement.deployment_domain,
        }
    }

    fn anchor_sequence(self) -> u64 {
        match self {
            Self::PrivateTransfer(statement) => statement.anchor_sequence,
            Self::Withdrawal(statement) => statement.anchor_sequence,
        }
    }

    fn anchor_root(self) -> Digest {
        match self {
            Self::PrivateTransfer(statement) => statement.anchor_root,
            Self::Withdrawal(statement) => statement.anchor_root,
        }
    }

    fn nullifier(self) -> Digest {
        match self {
            Self::PrivateTransfer(statement) => statement.nullifier,
            Self::Withdrawal(statement) => statement.nullifier,
        }
    }

    fn asset_id(self) -> aspis_core::field::M31 {
        match self {
            Self::PrivateTransfer(statement) => statement.asset_id,
            Self::Withdrawal(statement) => statement.asset_id,
        }
    }

    fn ordered_commitments(self) -> (Digest, Option<Digest>) {
        match self {
            Self::PrivateTransfer(statement) => (
                statement.recipient_commitment,
                Some(statement.change_commitment),
            ),
            Self::Withdrawal(statement) => (statement.change_commitment, None),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AuthenticatedSettlementStatementV1 {
    statement: CanonicalSettlementStatementV1,
    statement_digest: [u8; 32],
    receipt: PoolV1AuthorizationReceiptV1,
    envelope: HistoricalAnchorEnvelopeV1,
    receipt_image_digest: [u8; 32],
}

/// Final-gate context supplied from the already selected transaction
/// accounts.  Keeping this byte-oriented makes the absence of Poseidon in the
/// apply phase auditable directly from this module.
pub(crate) struct PreparedSettlementApplyContextV1<'a> {
    pub program_id: &'a Pubkey,
    pub plan_address: &'a Pubkey,
    pub plan_owner: &'a Pubkey,
    pub plan_authority: &'a Pubkey,
    pub plan_image: &'a [u8],
    pub rollover_shard: Option<PreparedSettlementRolloverShardAccountV1<'a>>,
    pub pool_address: &'a Pubkey,
    pub source_pool_image: &'a [u8],
    pub current_page_address: &'a Pubkey,
    pub source_current_page_image: &'a [u8],
    pub next_page: Option<(&'a Pubkey, &'a [u8])>,
    pub statement_payload: &'a [u8],
    pub expected_transition_kind: PoolV1TransitionKind,
    pub expected_statement_digest: [u8; 32],
    pub expected_nullifier: Digest,
    pub authorization_receipt_address: &'a Pubkey,
    pub authorization_receipt_owner: &'a Pubkey,
    pub authorization_receipt_image: &'a [u8],
    pub authorization_receipt_is_signer: bool,
    pub authorization_receipt_is_writable: bool,
    pub authorization_receipt_executable: bool,
    /// Sealed evidence obtained from the Pool's exact current verifier-policy
    /// registry accounts at `settlement_slot`.
    pub verifier_selection: AuthenticatedVerifierSelectionV1,
    pub nullifier_marker_address: &'a Pubkey,
    pub nullifier_marker_plan: &'a PlannedNullifierMarkerV1,
    pub settlement_slot: u64,
    pub hash: HashFn,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PreparedSettlementApplyResultV1<'a> {
    pub action: AuthenticatedPreparedSettlementActionV1,
    pub receipt: AuthorizedAppendReceiptV1,
    pub next_pool_image: &'a [u8; POOL_V1_STATE_ACCOUNT_BYTES],
    pub next_current_page_image: &'a [u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    pub next_rollover_page_image: Option<&'a [u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>,
}

pub(crate) fn pool_v1_authorization_receipt_account_address(
    verifier_program: &Pubkey,
    inputs: &PoolV1AuthorizationReceiptPdaInputsV1,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_AUTHORIZATION_RECEIPT_SEED,
            &inputs.proof_account,
            &inputs.statement_digest,
            &inputs.binding_digest,
        ],
        verifier_program,
    )
}

fn decode_canonical_statement(
    transition_kind: PoolV1TransitionKind,
    payload: &[u8],
) -> Result<CanonicalSettlementStatementV1, ProgramError> {
    match transition_kind {
        PoolV1TransitionKind::PrivateTransfer => {
            Ok(CanonicalSettlementStatementV1::PrivateTransfer(
                decode_pool_v1_private_transfer_public_v1(payload)
                    .map_err(|_| ProgramError::InvalidInstructionData)?,
            ))
        }
        PoolV1TransitionKind::Withdrawal => Ok(CanonicalSettlementStatementV1::Withdrawal(
            decode_pool_v1_withdrawal_public_v1(payload)
                .map_err(|_| ProgramError::InvalidInstructionData)?,
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn authenticate_statement_and_receipt_v1(
    transition_kind: PoolV1TransitionKind,
    statement_payload: &[u8],
    receipt_address: &Pubkey,
    receipt_owner: &Pubkey,
    receipt_image: &[u8],
    settlement_slot: u64,
    hash: HashFn,
) -> Result<AuthenticatedSettlementStatementV1, ProgramError> {
    if statement_payload.len() != POOL_V1_PAYMENT_STATEMENT_BYTES
        || receipt_image.len() != POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let statement = decode_canonical_statement(transition_kind, statement_payload)?;
    let receipt_account = decode_pool_v1_authorization_receipt_account_v1(receipt_image, hash)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if receipt_account.status != PoolV1AuthorizationReceiptAccountStatusV1::Verified {
        return Err(ProgramError::InvalidAccountData);
    }
    let receipt = receipt_account
        .receipt
        .ok_or(ProgramError::InvalidAccountData)?;
    if receipt.binding.transition_kind != transition_kind
        || receipt.binding.pool != statement.pool()
        || receipt.binding.deployment_domain != statement.deployment_domain()
        || receipt.binding.anchor_sequence != statement.anchor_sequence()
        || receipt.binding.anchor_root != statement.anchor_root()
        || receipt.binding.nullifier != statement.nullifier()
        || receipt.binding.statement_payload_length as usize != statement_payload.len()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let statement_digest = verifier_statement_payload_digest_v1(
        receipt.binding.statement_version,
        &receipt.binding.profile_binding,
        &receipt.binding.release_binding,
        statement_payload,
        hash,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if statement_digest != receipt.binding.statement_digest {
        return Err(ProgramError::InvalidAccountData);
    }
    let request = VerifierDispatchRequestV1 {
        binding: receipt.binding,
        statement_payload,
    };
    validate_pool_v1_authorization_receipt_account_request_v1(&receipt_account, &request, hash)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let pda_inputs = pool_v1_authorization_receipt_pda_inputs_for_binding_v1(
        &receipt.binding,
        receipt_account.pda_bump,
        hash,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    validate_pool_v1_authorization_receipt_account_pda_inputs_v1(&receipt_account, &pda_inputs)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    validate_pool_v1_authorization_receipt_for_settlement_v1(
        &receipt,
        &receipt.binding,
        settlement_slot,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    let verifier_program = Pubkey::new_from_array(receipt.binding.verifier_program);
    let (expected_address, expected_bump) =
        pool_v1_authorization_receipt_account_address(&verifier_program, &pda_inputs);
    if *receipt_owner != verifier_program
        || *receipt_address != expected_address
        || receipt_account.pda_bump != expected_bump
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind,
        pool: statement.pool(),
        deployment_domain: statement.deployment_domain(),
        anchor_sequence: statement.anchor_sequence(),
        anchor_root: statement.anchor_root(),
        nullifier: statement.nullifier(),
        verifier_profile: receipt.binding.profile_binding,
        verifier_release: receipt.binding.release_binding,
    };
    if historical_anchor_envelope_digest_v1(&envelope, hash)
        .map_err(|_| ProgramError::InvalidAccountData)?
        != receipt.binding.envelope_digest
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(AuthenticatedSettlementStatementV1 {
        statement,
        statement_digest,
        receipt,
        envelope,
        receipt_image_digest: exact_image_digest_v1(receipt_image, hash),
    })
}

fn verifier_selection_from_receipt(
    authenticated: AuthenticatedSettlementStatementV1,
) -> VerifierSelectionV1 {
    VerifierSelectionV1 {
        verifier_program: authenticated.receipt.binding.verifier_program,
        profile_binding: authenticated.receipt.binding.profile_binding,
        release_binding: authenticated.receipt.binding.release_binding,
        statement_version: authenticated.receipt.binding.statement_version,
    }
}

fn authenticated_selection_matches_receipt(
    selected: AuthenticatedVerifierSelectionV1,
    authenticated: AuthenticatedSettlementStatementV1,
) -> bool {
    selected.matches(
        authenticated.statement.pool(),
        authenticated.receipt.binding.verifier_program,
        authenticated.receipt.binding.profile_binding,
        authenticated.receipt.binding.release_binding,
        authenticated.receipt.binding.statement_version,
    )
}

fn checked_history_distribution(
    source_sequence: u64,
    current_header: RootPageHeaderV1,
    count: u64,
) -> Result<(usize, usize), ProgramError> {
    let first_sequence = source_sequence
        .checked_add(1)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    let final_sequence = source_sequence
        .checked_add(count)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    let first_location = root_history_location(first_sequence);
    let last_location = root_history_location(final_sequence);
    if first_location.page_number < current_header.page_number
        || last_location.page_number > current_header.page_number + 1
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let current = if first_location.page_number == current_header.page_number {
        if last_location.page_number == current_header.page_number {
            count as usize
        } else {
            1
        }
    } else {
        0
    };
    let next = count as usize - current;
    if usize::from(current_header.filled) + current > POOL_V1_ROOT_HISTORY_CAPACITY {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok((current, next))
}

fn zeroed_page_box() -> Result<Box<[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>, ProgramError> {
    let raw: Box<[u8]> = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES].into_boxed_slice();
    raw.try_into().map_err(|_| ProgramError::InvalidAccountData)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn build_prepared_settlement_plan_v1(
    program_id: &Pubkey,
    pool_account: &AccountInfo<'_>,
    historical_anchor_page_account: &AccountInfo<'_>,
    current_page_account: &AccountInfo<'_>,
    supplied_next_page: Option<&AccountInfo<'_>>,
    state: &CanonicalPoolStateV1,
    request: AuthorizedAppendV1,
    statement_payload: &[u8],
    authorization_receipt_account: &AccountInfo<'_>,
    registry_accounts: &[AccountInfo<'_>],
    plan_authority: &Pubkey,
    preparation_slot: u64,
    not_before_slot: u64,
    expires_at_slot: u64,
    hash: HashFn,
) -> Result<PreparedSettlementPlanImagesV1, ProgramError> {
    state.require_same_writable_account(program_id, pool_account)?;
    if authorization_receipt_account.executable
        || authorization_receipt_account.is_signer
        || authorization_receipt_account.is_writable
        || authorization_receipt_account.key == pool_account.key
        || authorization_receipt_account.key == historical_anchor_page_account.key
        || authorization_receipt_account.key == current_page_account.key
        || supplied_next_page
            .map(|account| account.key == authorization_receipt_account.key)
            .unwrap_or(false)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let receipt_data = authorization_receipt_account.try_borrow_data()?;
    let authenticated = authenticate_statement_and_receipt_v1(
        request_transition_kind(request),
        statement_payload,
        authorization_receipt_account.key,
        authorization_receipt_account.owner,
        &receipt_data,
        preparation_slot,
        hash,
    )?;
    let selected = authenticate_verifier_selection_v1(
        pool_account.key,
        &state.verifier_policy,
        registry_accounts,
        verifier_selection_from_receipt(authenticated),
        preparation_slot,
    )?;
    if *plan_authority == Pubkey::default()
        || not_before_slot > expires_at_slot
        || preparation_slot > expires_at_slot
        || not_before_slot < authenticated.receipt.verified_slot
        || !authenticated_selection_matches_receipt(selected, authenticated)
        || authenticated.statement.pool() != pool_account.key.to_bytes()
        || authenticated.statement.pool() != state.identity.pool
        || authenticated.statement.deployment_domain() != state.identity.deployment_domain
        || authenticated.statement.asset_id() != state.identity.asset_id
        || authenticated.statement.anchor_sequence() > state.current_root_sequence()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let ordered_commitments = authenticated.statement.ordered_commitments();
    if request_commitments(request) != ordered_commitments {
        return Err(ProgramError::InvalidInstructionData);
    }
    let envelope_bytes = encode_historical_anchor_envelope_v1(&authenticated.envelope)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let anchor = authenticate_historical_anchor_after_prevalidated_state_v1(
        program_id,
        pool_account,
        historical_anchor_page_account,
        &envelope_bytes,
        HistoricalAnchorAuthorizationV1 {
            transition_kind: authenticated.statement.transition_kind(),
            verifier_profile: authenticated.receipt.binding.profile_binding,
            verifier_release: authenticated.receipt.binding.release_binding,
        },
        state,
    )?;
    let history = validate_current_history_after_prevalidated_anchor_v1(
        program_id,
        pool_account,
        current_page_account,
        state,
        anchor,
    )?;
    let current_header = history.require_matches(
        program_id,
        pool_account,
        current_page_account,
        state.as_state(),
    )?;

    let prepared = prepare_authorized_append_images_v1(state, request)?;
    let count = request.count();
    let (roots_in_current, roots_in_next) =
        checked_history_distribution(state.current_root_sequence(), current_header, count)?;
    let source_pool_data = pool_account.try_borrow_data()?;
    let source_pool_image: &[u8; POOL_V1_STATE_ACCOUNT_BYTES] = (&**source_pool_data)
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let source_current_data = current_page_account.try_borrow_data()?;
    let source_current_image: &[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES] =
        (&**source_current_data)
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?;
    let roots = append_roots(&prepared.receipt)?;
    let (next_page_address, source_next_digest, rollover_page_number, rollover_first_sequence) =
        if roots_in_next == 0 {
            if supplied_next_page.is_some() {
                return Err(PoolV1ProgramError::UnexpectedRootPage.into());
            }
            (None, None, 0, 0)
        } else {
            let next = supplied_next_page.ok_or(PoolV1ProgramError::UnexpectedRootPage)?;
            let page_number = current_header
                .page_number
                .checked_add(1)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            validate_new_page_account(program_id, pool_account.key, page_number, next)?;
            if next.key == pool_account.key || next.key == current_page_account.key {
                return Err(ProgramError::InvalidAccountData);
            }
            let source_next = next.try_borrow_data()?;
            let source_next_image: &[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES] =
                (&**source_next)
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?;
            let first_sequence = page_number
                .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            (
                Some(next.key.to_bytes()),
                Some(exact_image_digest_v1(source_next_image, hash)),
                page_number,
                first_sequence,
            )
        };
    let (_, pda_bump) = pool_v1_prepared_settlement_plan_address(
        program_id,
        pool_account.key,
        &authenticated.statement_digest,
        state.current_root_sequence(),
        plan_authority,
    );
    encode_prepared_settlement_plan_v1(
        PreparedSettlementPlanFieldsV1 {
            pda_bump,
            transition_kind: authenticated.statement.transition_kind(),
            program_id: program_id.to_bytes(),
            pool: pool_account.key.to_bytes(),
            plan_authority: plan_authority.to_bytes(),
            source_sequence: state.current_root_sequence(),
            source_root: state.tree.root,
            source_pool_image_digest: exact_image_digest_v1(source_pool_image, hash),
            current_page_address: current_page_account.key.to_bytes(),
            source_current_page_image_digest: exact_image_digest_v1(source_current_image, hash),
            next_page_address,
            source_next_page_image_digest: source_next_digest,
            statement_digest: authenticated.statement_digest,
            nullifier: authenticated.statement.nullifier(),
            authorization_receipt_address: authorization_receipt_account.key.to_bytes(),
            authorization_receipt_image_digest: authenticated.receipt_image_digest,
            not_before_slot,
            expires_at_slot,
            first_commitment: ordered_commitments.0,
            second_commitment: ordered_commitments.1,
            first_receipt: prepared.receipt.first,
            second_receipt: prepared.receipt.second,
            next_pool_image: &prepared.next_state_image,
        },
        |output| {
            output.copy_from_slice(source_current_image);
            if roots_in_current != 0 {
                append_roots_unchecked(output, current_header, &roots[..roots_in_current]);
            }
        },
        |output| {
            write_new_page_unchecked(
                output,
                pool_account.key,
                rollover_page_number,
                rollover_first_sequence,
                &roots[roots_in_current..],
            );
        },
        hash,
    )
    .map_err(Into::into)
}

fn request_transition_kind(request: AuthorizedAppendV1) -> PoolV1TransitionKind {
    match request {
        AuthorizedAppendV1::One(_) => PoolV1TransitionKind::Withdrawal,
        AuthorizedAppendV1::Two(_, _) => PoolV1TransitionKind::PrivateTransfer,
    }
}

fn request_commitments(request: AuthorizedAppendV1) -> (Digest, Option<Digest>) {
    match request {
        AuthorizedAppendV1::One(first) => (first, None),
        AuthorizedAppendV1::Two(first, second) => (first, Some(second)),
    }
}

fn append_roots(receipt: &AuthorizedAppendReceiptV1) -> Result<[Digest; 2], ProgramError> {
    let mut roots = [receipt.first.root; 2];
    if let Some(second) = receipt.second {
        roots[1] = second.root;
    }
    Ok(roots)
}

fn validate_receipt_progression(
    plan: PreparedSettlementPlanViewV1<'_>,
) -> Result<AuthorizedAppendReceiptV1, ProgramError> {
    let first_sequence = plan
        .source_sequence
        .checked_add(1)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    if plan.first_receipt.leaf_index != plan.source_sequence
        || plan.first_receipt.root_sequence != first_sequence
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let second = match (plan.transition_kind, plan.second_receipt) {
        (PoolV1TransitionKind::PrivateTransfer, Some(second))
            if second.leaf_index == first_sequence
                && second.root_sequence == first_sequence.checked_add(1).unwrap_or(u64::MAX) =>
        {
            Some(second)
        }
        (PoolV1TransitionKind::Withdrawal, None) => None,
        _ => return Err(ProgramError::InvalidAccountData),
    };
    Ok(AuthorizedAppendReceiptV1 {
        first: plan.first_receipt,
        second,
    })
}

fn source_state_and_result_image_match(
    plan: PreparedSettlementPlanViewV1<'_>,
    source: &[u8; POOL_V1_STATE_ACCOUNT_BYTES],
) -> Result<(), ProgramError> {
    let source_sequence = u64::from_le_bytes(
        source[STATE_SEQUENCE_OFFSET..STATE_PAGE_OFFSET]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    );
    let source_tree_sequence = u64::from_le_bytes(
        source[POOL_V1_STATE_TREE_OFFSET + TREE_SEQUENCE_RELATIVE_OFFSET
            ..POOL_V1_STATE_TREE_OFFSET + TREE_ROOT_RELATIVE_OFFSET]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    );
    if source_sequence != plan.source_sequence
        || source_tree_sequence != plan.source_sequence
        || source[POOL_V1_STATE_TREE_OFFSET + TREE_ROOT_RELATIVE_OFFSET
            ..POOL_V1_STATE_TREE_OFFSET + TREE_FRONTIER_RELATIVE_OFFSET]
            != encode_digest_canonical(&plan.source_root)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let count = match plan.transition_kind {
        PoolV1TransitionKind::PrivateTransfer => 2u64,
        PoolV1TransitionKind::Withdrawal => 1u64,
    };
    let final_sequence = plan
        .source_sequence
        .checked_add(count)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    let final_root = plan.second_receipt.unwrap_or(plan.first_receipt).root;
    let result = plan.next_pool_image;
    let location = root_history_location(final_sequence);
    if result[..40] != source[..40]
        || result[58..POOL_V1_STATE_TREE_OFFSET] != source[58..POOL_V1_STATE_TREE_OFFSET]
        || result
            [POOL_V1_STATE_TREE_OFFSET..POOL_V1_STATE_TREE_OFFSET + TREE_SEQUENCE_RELATIVE_OFFSET]
            != source[POOL_V1_STATE_TREE_OFFSET
                ..POOL_V1_STATE_TREE_OFFSET + TREE_SEQUENCE_RELATIVE_OFFSET]
        || result[STATE_SEQUENCE_OFFSET..STATE_PAGE_OFFSET] != final_sequence.to_le_bytes()
        || result[STATE_PAGE_OFFSET..STATE_SLOT_OFFSET] != location.page_number.to_le_bytes()
        || result[STATE_SLOT_OFFSET..58] != location.slot.to_le_bytes()
        || result[POOL_V1_STATE_TREE_OFFSET + TREE_SEQUENCE_RELATIVE_OFFSET
            ..POOL_V1_STATE_TREE_OFFSET + TREE_ROOT_RELATIVE_OFFSET]
            != final_sequence.to_le_bytes()
        || result[POOL_V1_STATE_TREE_OFFSET + TREE_ROOT_RELATIVE_OFFSET
            ..POOL_V1_STATE_TREE_OFFSET + TREE_FRONTIER_RELATIVE_OFFSET]
            != encode_digest_canonical(&final_root)
        || result[POOL_V1_STATE_IDENTITY_OFFSET + 8..POOL_V1_STATE_IDENTITY_OFFSET + 40]
            != plan.pool
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn history_result_images_match(
    program_id: &Pubkey,
    pool: &Pubkey,
    plan: PreparedSettlementPlanViewV1<'_>,
    source_current: &[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    source_next: Option<&[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>,
) -> Result<(), ProgramError> {
    let location = root_history_location(plan.source_sequence);
    let current_header = validate_root_page_bytes(source_current, pool, location.page_number)?;
    if current_header.filled != location.slot + 1
        || plan.current_page_address
            != pool_v1_root_page_address(program_id, pool, location.page_number)
                .0
                .to_bytes()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let count = match plan.transition_kind {
        PoolV1TransitionKind::PrivateTransfer => 2,
        PoolV1TransitionKind::Withdrawal => 1,
    };
    let (roots_in_current, roots_in_next) =
        checked_history_distribution(plan.source_sequence, current_header, count)?;
    let receipt = AuthorizedAppendReceiptV1 {
        first: plan.first_receipt,
        second: plan.second_receipt,
    };
    let roots = append_roots(&receipt)?;
    let mut expected_current = zeroed_page_box()?;
    expected_current.copy_from_slice(source_current);
    if roots_in_current != 0 {
        append_roots_unchecked(
            expected_current.as_mut(),
            current_header,
            &roots[..roots_in_current],
        );
    }
    if expected_current.as_ref() != plan.next_current_page_image {
        return Err(ProgramError::InvalidAccountData);
    }
    match (
        roots_in_next,
        plan.next_page_address,
        source_next,
        plan.next_rollover_page_image,
    ) {
        (0, None, None, None) => Ok(()),
        (nonzero, Some(address), Some(source), Some(result)) if nonzero != 0 => {
            let next_page_number = location
                .page_number
                .checked_add(1)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            if address
                != pool_v1_root_page_address(program_id, pool, next_page_number)
                    .0
                    .to_bytes()
                || source.iter().any(|byte| *byte != 0)
            {
                return Err(ProgramError::InvalidAccountData);
            }
            let mut expected_next = zeroed_page_box()?;
            let first_sequence = next_page_number
                .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            write_new_page_unchecked(
                expected_next.as_mut(),
                pool,
                next_page_number,
                first_sequence,
                &roots[roots_in_current..],
            );
            if expected_next.as_ref() != result {
                return Err(ProgramError::InvalidAccountData);
            }
            Ok(())
        }
        _ => Err(ProgramError::InvalidAccountData),
    }
}

fn nullifier_marker_matches(
    program_id: &Pubkey,
    marker_address: &Pubkey,
    marker_plan: &PlannedNullifierMarkerV1,
    authenticated: AuthenticatedSettlementStatementV1,
) -> Result<(), ProgramError> {
    let statement = authenticated.statement;
    let marker = marker_plan.marker();
    let canonical_nullifier = encode_digest_canonical(&statement.nullifier());
    let (expected_address, expected_bump) = pool_v1_nullifier_marker_address(
        program_id,
        &Pubkey::new_from_array(statement.pool()),
        &canonical_nullifier,
    )?;
    if *marker_address != expected_address
        || marker_plan.address_bump() != expected_bump
        || marker.transition_kind != statement.transition_kind()
        || marker.pool != statement.pool()
        || marker.deployment_domain != statement.deployment_domain()
        || marker.nullifier != statement.nullifier()
        || marker.retained_anchor_sequence != statement.anchor_sequence()
        || marker.retained_anchor_root != statement.anchor_root()
        || marker.verifier_profile != authenticated.receipt.binding.profile_binding
        || marker.verifier_release != authenticated.receipt.binding.release_binding
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

/// Authenticate and expose the exact prepared images for final atomic
/// persistence. This function performs SHA-256 and byte comparisons only.
#[inline(never)]
pub(crate) fn apply_prepared_settlement_plan_v1(
    context: PreparedSettlementApplyContextV1<'_>,
) -> Result<PreparedSettlementApplyResultV1<'_>, ProgramError> {
    if context.plan_owner != context.program_id
        || context.source_pool_image.len() != POOL_V1_STATE_ACCOUNT_BYTES
        || context.source_current_page_image.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
        || context.authorization_receipt_is_signer
        || context.authorization_receipt_is_writable
        || context.authorization_receipt_executable
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let plan = decode_prepared_settlement_plan_v1(
        context.plan_address,
        context.plan_image,
        context.rollover_shard,
        context.hash,
    )
    .map_err(ProgramError::from)?;
    let (expected_plan_address, expected_plan_bump) = pool_v1_prepared_settlement_plan_address(
        context.program_id,
        context.pool_address,
        &context.expected_statement_digest,
        plan.source_sequence,
        context.plan_authority,
    );
    if *context.plan_address != expected_plan_address
        || plan.pda_bump != expected_plan_bump
        || plan.program_id != context.program_id.to_bytes()
        || plan.pool != context.pool_address.to_bytes()
        || plan.plan_authority != context.plan_authority.to_bytes()
        || plan.transition_kind != context.expected_transition_kind
        || plan.statement_digest != context.expected_statement_digest
        || plan.nullifier != context.expected_nullifier
        || plan.current_page_address != context.current_page_address.to_bytes()
        || context.settlement_slot < plan.not_before_slot
        || context.settlement_slot > plan.expires_at_slot
        || exact_image_digest_v1(context.source_pool_image, context.hash)
            != plan.source_pool_image_digest
        || exact_image_digest_v1(context.source_current_page_image, context.hash)
            != plan.source_current_page_image_digest
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let source_pool: &[u8; POOL_V1_STATE_ACCOUNT_BYTES] = context
        .source_pool_image
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let source_current: &[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES] = context
        .source_current_page_image
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let source_policy = decode_verifier_policy_v1(
        &source_pool[POOL_V1_STATE_POLICY_OFFSET..POOL_V1_STATE_TREE_OFFSET],
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if !context.verifier_selection.matches_policy(&source_policy) {
        return Err(ProgramError::InvalidAccountData);
    }
    let source_next = match (plan.next_page_address, context.next_page) {
        (None, None) => None,
        (Some(expected_address), Some((address, image)))
            if expected_address == address.to_bytes()
                && image.len() == POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
                && Some(exact_image_digest_v1(image, context.hash))
                    == plan.source_next_page_image_digest =>
        {
            Some(
                image
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?,
            )
        }
        _ => return Err(ProgramError::InvalidAccountData),
    };
    let authenticated = authenticate_statement_and_receipt_v1(
        context.expected_transition_kind,
        context.statement_payload,
        context.authorization_receipt_address,
        context.authorization_receipt_owner,
        context.authorization_receipt_image,
        context.settlement_slot,
        context.hash,
    )?;
    if context.verifier_selection.authenticated_at_slot() != context.settlement_slot
        || !authenticated_selection_matches_receipt(context.verifier_selection, authenticated)
        || authenticated.statement_digest != context.expected_statement_digest
        || authenticated.statement.nullifier() != context.expected_nullifier
        || authenticated.statement.pool() != context.pool_address.to_bytes()
        || authenticated.receipt_image_digest != plan.authorization_receipt_image_digest
        || context.authorization_receipt_address.to_bytes() != plan.authorization_receipt_address
        || authenticated.statement.ordered_commitments()
            != (plan.first_commitment, plan.second_commitment)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    nullifier_marker_matches(
        context.program_id,
        context.nullifier_marker_address,
        context.nullifier_marker_plan,
        authenticated,
    )?;
    let receipt = validate_receipt_progression(plan)?;
    source_state_and_result_image_match(plan, source_pool)?;
    history_result_images_match(
        context.program_id,
        context.pool_address,
        plan,
        source_current,
        source_next,
    )?;
    Ok(PreparedSettlementApplyResultV1 {
        action: AuthenticatedPreparedSettlementActionV1 {
            statement: authenticated.statement,
        },
        receipt,
        next_pool_image: plan.next_pool_image,
        next_current_page_image: plan.next_current_page_image,
        next_rollover_page_image: plan.next_rollover_page_image,
    })
}

/// Exact close/refund authorization for a prepared-plan PDA.  A future public
/// close instruction may delegate to this pure gate, but cannot redirect the
/// refund: only the nonzero authority authenticated inside the plan may sign.
pub(crate) fn authorize_prepared_settlement_plan_close_v1(
    program_id: &Pubkey,
    plan_address: &Pubkey,
    plan_owner: &Pubkey,
    plan_image: &[u8],
    rollover_shard: Option<PreparedSettlementRolloverShardAccountV1<'_>>,
    refund_authority: &Pubkey,
    refund_authority_is_signer: bool,
    hash: HashFn,
) -> Result<(), ProgramError> {
    if plan_owner != program_id || !refund_authority_is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    let plan = decode_prepared_settlement_plan_v1(plan_address, plan_image, rollover_shard, hash)
        .map_err(ProgramError::from)?;
    let authority = Pubkey::new_from_array(plan.plan_authority);
    let pool = Pubkey::new_from_array(plan.pool);
    let expected = pool_v1_prepared_settlement_plan_address(
        program_id,
        &pool,
        &plan.statement_digest,
        plan.source_sequence,
        &authority,
    );
    if authority != *refund_authority
        || expected.0 != *plan_address
        || expected.1 != plan.pda_bump
        || plan.program_id != program_id.to_bytes()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use aspis_core::field::{M31, P};
    use aspis_statement::pool_v1::{
        decode_verifier_registry_entry_v1, decode_verifier_registry_v1,
        encode_pool_v1_private_transfer_public_v1, encode_pool_v1_withdrawal_public_v1,
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1,
        finalize_pool_v1_authorization_receipt_account_v1, historical_anchor_envelope_digest_v1,
        initialize_pool_v1_authorization_receipt_account_v1,
        pool_v1_authorization_receipt_pda_inputs_for_binding_v1,
        verifier_statement_payload_digest_v1, HistoricalAnchorEnvelopeV1, PoolV1NullifierMarkerV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1, RootHistoryPageV1,
        VerifierDispatchBindingV1, VerifierDispatchRequestV1, VerifierEntryStatusV1,
        VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_DOMAIN, POOL_V1_TREE_DEPTH,
        POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED,
    };
    use sha2::{Digest as ShaDigest, Sha256};
    use solana_program::{
        clock::Epoch, entrypoint::ProgramResult, instruction::Instruction, rent::Rent,
    };
    use solana_sdk_ids::{native_loader, system_program};
    use std::vec::Vec;

    use crate::{
        empty_roots::POOL_V1_EMPTY_ROOTS,
        instruction::{
            encode_private_transfer_instruction_v1, encode_withdrawal_instruction_v1,
            PrivateTransferStatementV1, WithdrawalStatementV1,
        },
        nullifier::plan_nullifier_marker_consumption_v1,
        prepared_settlement_format::{
            bind_prepared_settlement_rollover_for_test, decode_prepared_settlement_plan_v1,
            reauthenticate_prepared_settlement_plan_for_test,
            reauthenticate_prepared_settlement_rollover_for_test, PreparedSettlementPlanImagesV1,
            PreparedSettlementRolloverShardAccountV1,
            POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES,
            POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES, TEST_FIRST_COMMITMENT_OFFSET,
            TEST_FIRST_RECEIPT_ROOT_OFFSET, TEST_ROLLOVER_SHARD_CORE_ADDRESS_OFFSET,
            TEST_ROLLOVER_SHARD_IMAGE_OFFSET, TEST_SECOND_COMMITMENT_OFFSET,
            TEST_SOURCE_ROOT_OFFSET,
        },
        prepared_settlement_instruction::encode_prepare_settlement_instruction_v1,
        processor::{process_prepare_settlement_with_runtime_v1, PoolCpiRuntimeV1},
        registry::{pool_v1_verifier_entry_address, pool_v1_verifier_registry_address},
        state::{pool_v1_state_address, PoolInitializationV1, PoolStateV1},
        transition::apply_authorized_append_after_v1,
        LEGACY_SPL_TOKEN_PROGRAM_ID,
    };

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        let mut state = Sha256::new();
        for input in inputs {
            state.update(input);
        }
        state.finalize().into()
    }

    fn refresh_asra_wrapper_digest(image: &mut [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES]) {
        let digest = sha256(&[
            POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_DOMAIN,
            &image[..688],
        ]);
        image[688..].copy_from_slice(&digest);
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31((seed + 101 * index as u32) % P))
    }

    fn initialization() -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: [2u8; 32],
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
            verifier_policy: aspis_statement::pool_v1::VerifierPolicyV1 {
                flags: 0,
                registry_program: [6u8; 32],
                registry_authority: [7u8; 32],
                policy_binding: [8u8; 32],
            },
        }
    }

    const PREPARATION_SLOT: u64 = 105;
    const SETTLEMENT_SLOT: u64 = 150;

    struct NoPreparationCpi;

    impl PoolCpiRuntimeV1 for NoPreparationCpi {
        fn invoke<'info>(&mut self, _: &Instruction, _: &[AccountInfo<'info>]) -> ProgramResult {
            panic!("unexpected preparation CPI")
        }

        fn invoke_signed<'info>(
            &mut self,
            _: &Instruction,
            _: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            panic!("unexpected preparation CPI")
        }
    }

    fn registry_selection(binding: &VerifierDispatchBindingV1) -> VerifierSelectionV1 {
        VerifierSelectionV1 {
            verifier_program: binding.verifier_program,
            profile_binding: binding.profile_binding,
            release_binding: binding.release_binding,
            statement_version: binding.statement_version,
        }
    }

    fn registry_images(
        pool: &Pubkey,
        policy: &aspis_statement::pool_v1::VerifierPolicyV1,
        selection: VerifierSelectionV1,
        status: VerifierEntryStatusV1,
        retirement_slot: u64,
    ) -> (
        Pubkey,
        [u8; POOL_V1_VERIFIER_REGISTRY_BYTES],
        Pubkey,
        [u8; POOL_V1_VERIFIER_ENTRY_BYTES],
    ) {
        let registry_program = Pubkey::new_from_array(policy.registry_program);
        let registry_address = pool_v1_verifier_registry_address(&registry_program, pool).0;
        let entry_address = pool_v1_verifier_entry_address(
            &registry_program,
            pool,
            &selection.profile_binding,
            &selection.release_binding,
        )
        .0;
        let registry_image = encode_verifier_registry_v1(&VerifierRegistryV1 {
            flags: 0,
            pool: pool.to_bytes(),
            authority: policy.registry_authority,
            policy_binding: policy.policy_binding,
            generation: 3,
            minimum_activation_delay_slots: 1,
        })
        .unwrap();
        let entry_image = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            status,
            statement_version: selection.statement_version,
            pool: pool.to_bytes(),
            verifier_program: selection.verifier_program,
            profile_binding: selection.profile_binding,
            release_binding: selection.release_binding,
            activation_slot: 90,
            retirement_slot,
            policy_binding: policy.policy_binding,
        })
        .unwrap();
        (registry_address, registry_image, entry_address, entry_image)
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }

    fn state_and_history_at(pool: &Pubkey, leaf_count: u64) -> (PoolStateV1, Vec<u8>) {
        let mut state = PoolStateV1::genesis(pool, initialization()).unwrap();
        let page_number = root_history_location(leaf_count).page_number;
        let first_sequence = page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64;
        let mut history = RootHistoryPageV1::new(pool.to_bytes(), page_number).unwrap();
        if page_number == 0 {
            history
                .push(0, POOL_V1_EMPTY_ROOTS[POOL_V1_TREE_DEPTH])
                .unwrap();
        }
        for index in 0..leaf_count {
            let (tree, receipt) = state
                .tree
                .append_one_with_empty_roots(digest(index as u32 + 1), &POOL_V1_EMPTY_ROOTS)
                .unwrap();
            state.tree = tree;
            if receipt.root_sequence >= first_sequence {
                history.push(receipt.root_sequence, receipt.root).unwrap();
            }
        }
        (state, history.encode().unwrap().to_vec())
    }

    struct Fixture {
        program_id: Pubkey,
        pool: Pubkey,
        current_page: Pubkey,
        next_page: Pubkey,
        has_next_page: bool,
        source_pool: [u8; POOL_V1_STATE_ACCOUNT_BYTES],
        source_current_page: Vec<u8>,
        source_next_page: Vec<u8>,
        statement_payload: [u8; POOL_V1_PAYMENT_STATEMENT_BYTES],
        statement_digest: [u8; 32],
        transition_kind: PoolV1TransitionKind,
        nullifier: Digest,
        authorization_receipt_address: Pubkey,
        authorization_receipt_owner: Pubkey,
        pending_authorization_receipt_image: [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
        authorization_receipt_image: [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
        registry_program: Pubkey,
        registry_address: Pubkey,
        registry_image: [u8; POOL_V1_VERIFIER_REGISTRY_BYTES],
        entry_address: Pubkey,
        entry_image: [u8; POOL_V1_VERIFIER_ENTRY_BYTES],
        verifier_selection: AuthenticatedVerifierSelectionV1,
        authority: Pubkey,
        plan_address: Pubkey,
        plan_image: Box<[u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]>,
        rollover_shard_address: Option<Pubkey>,
        rollover_shard_image: Option<Box<[u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES]>>,
        marker_address: Pubkey,
        marker_plan: PlannedNullifierMarkerV1,
        direct_pool: [u8; POOL_V1_STATE_ACCOUNT_BYTES],
        direct_current_page: Vec<u8>,
        direct_next_page: Vec<u8>,
        direct_receipt: AuthorizedAppendReceiptV1,
    }

    fn build_fixture(
        program_id: Pubkey,
        verifier_program: Pubkey,
        authority: Pubkey,
        transition_kind: PoolV1TransitionKind,
        leaf_count: u64,
    ) -> Fixture {
        let pool = pool_v1_state_address(
            &program_id,
            &Pubkey::new_from_array(initialization().asset_mint),
        )
        .0;
        let (state, source_current_page) = state_and_history_at(&pool, leaf_count);
        let source_pool = state.encode().unwrap();
        let current_page_number = root_history_location(leaf_count).page_number;
        let current_page = pool_v1_root_page_address(&program_id, &pool, current_page_number).0;
        let next_page = pool_v1_root_page_address(&program_id, &pool, current_page_number + 1).0;
        let source_next_page = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let nullifier = digest(30_000);
        let recipient = digest(31_000);
        let change = digest(32_000);
        let (statement_payload, request) = match transition_kind {
            PoolV1TransitionKind::PrivateTransfer => (
                encode_pool_v1_private_transfer_public_v1(&PoolV1PrivateTransferPublicV1 {
                    pool: pool.to_bytes(),
                    deployment_domain: state.identity.deployment_domain,
                    anchor_sequence: leaf_count,
                    anchor_root: state.tree.root,
                    nullifier,
                    asset_id: state.identity.asset_id,
                    recipient_commitment: recipient,
                    change_commitment: change,
                })
                .unwrap(),
                AuthorizedAppendV1::Two(recipient, change),
            ),
            PoolV1TransitionKind::Withdrawal => (
                encode_pool_v1_withdrawal_public_v1(&PoolV1WithdrawalPublicV1 {
                    pool: pool.to_bytes(),
                    deployment_domain: state.identity.deployment_domain,
                    anchor_sequence: leaf_count,
                    anchor_root: state.tree.root,
                    nullifier,
                    asset_id: state.identity.asset_id,
                    amount: 17,
                    destination_token_account: [71u8; 32],
                    change_commitment: change,
                })
                .unwrap(),
                AuthorizedAppendV1::One(change),
            ),
        };
        let profile_binding = [41u8; 32];
        let release_binding = [42u8; 32];
        let statement_digest = verifier_statement_payload_digest_v1(
            1,
            &profile_binding,
            &release_binding,
            &statement_payload,
            sha256,
        )
        .unwrap();
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind,
            pool: pool.to_bytes(),
            deployment_domain: state.identity.deployment_domain,
            anchor_sequence: leaf_count,
            anchor_root: state.tree.root,
            nullifier,
            verifier_profile: profile_binding,
            verifier_release: release_binding,
        };
        let binding = VerifierDispatchBindingV1 {
            statement_version: 1,
            transition_kind,
            verifier_program: verifier_program.to_bytes(),
            profile_binding,
            release_binding,
            pool: pool.to_bytes(),
            deployment_domain: state.identity.deployment_domain,
            anchor_sequence: leaf_count,
            anchor_root: state.tree.root,
            nullifier,
            statement_digest,
            envelope_digest: historical_anchor_envelope_digest_v1(&envelope, sha256).unwrap(),
            proof_account: [44u8; 32],
            proof_body_digest: [45u8; 32],
            proof_body_length: 30_504,
            statement_payload_length: POOL_V1_PAYMENT_STATEMENT_BYTES as u32,
        };
        let registry_program = Pubkey::new_from_array(state.verifier_policy.registry_program);
        let selection = registry_selection(&binding);
        let (registry_address, registry_image, entry_address, entry_image) = registry_images(
            &pool,
            &state.verifier_policy,
            selection,
            VerifierEntryStatusV1::Active,
            POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        );
        let dispatch_request = VerifierDispatchRequestV1 {
            binding,
            statement_payload: &statement_payload,
        };
        let placeholder_inputs =
            pool_v1_authorization_receipt_pda_inputs_for_binding_v1(&binding, 0, sha256).unwrap();
        let (authorization_receipt_address, receipt_bump) =
            pool_v1_authorization_receipt_account_address(&verifier_program, &placeholder_inputs);
        let pending_receipt = initialize_pool_v1_authorization_receipt_account_v1(
            &dispatch_request,
            binding.proof_account,
            [46u8; 32],
            Some([46u8; 32]),
            [47u8; 32],
            receipt_bump,
            sha256,
        )
        .unwrap();
        let authorization_receipt_image = finalize_pool_v1_authorization_receipt_account_v1(
            &pending_receipt,
            &dispatch_request,
            &PoolV1AuthorizationReceiptV1 {
                pda_bump: receipt_bump,
                verified_slot: 100,
                binding,
            },
            sha256,
        )
        .unwrap();
        let count = request.count();
        let has_next_page =
            root_history_location(leaf_count + count).page_number != current_page_number;

        let mut source_pool_for_plan = source_pool;
        let mut source_current_for_plan = source_current_page.clone();
        let mut source_next_for_plan = source_next_page.clone();
        let mut pool_lamports = 1;
        let mut current_lamports = 1;
        let mut next_lamports = 1;
        let mut receipt_lamports = 1;
        let mut receipt_for_plan = authorization_receipt_image;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut registry_for_plan = registry_image;
        let mut entry_for_plan = entry_image;
        let (plan_images, settlement_selection) = {
            let pool_account = account(
                &pool,
                &program_id,
                &mut pool_lamports,
                &mut source_pool_for_plan,
                false,
                true,
            );
            let current_account = account(
                &current_page,
                &program_id,
                &mut current_lamports,
                &mut source_current_for_plan,
                false,
                true,
            );
            let state = CanonicalPoolStateV1::decode_account(&program_id, &pool_account).unwrap();
            let receipt_account = account(
                &authorization_receipt_address,
                &verifier_program,
                &mut receipt_lamports,
                &mut receipt_for_plan,
                false,
                false,
            );
            let registry_account = account(
                &registry_address,
                &registry_program,
                &mut registry_lamports,
                &mut registry_for_plan,
                false,
                false,
            );
            let entry_account = account(
                &entry_address,
                &registry_program,
                &mut entry_lamports,
                &mut entry_for_plan,
                false,
                false,
            );
            let registry_accounts = [registry_account, entry_account];
            let settlement_selection = authenticate_verifier_selection_v1(
                &pool,
                &state.verifier_policy,
                &registry_accounts,
                selection,
                SETTLEMENT_SLOT,
            )
            .unwrap();
            let plan_images = if has_next_page {
                let next_account = account(
                    &next_page,
                    &program_id,
                    &mut next_lamports,
                    &mut source_next_for_plan,
                    false,
                    true,
                );
                build_prepared_settlement_plan_v1(
                    &program_id,
                    &pool_account,
                    &current_account,
                    &current_account,
                    Some(&next_account),
                    &state,
                    request,
                    &statement_payload,
                    &receipt_account,
                    &registry_accounts,
                    &authority,
                    PREPARATION_SLOT,
                    110,
                    200,
                    sha256,
                )
                .unwrap()
            } else {
                build_prepared_settlement_plan_v1(
                    &program_id,
                    &pool_account,
                    &current_account,
                    &current_account,
                    None,
                    &state,
                    request,
                    &statement_payload,
                    &receipt_account,
                    &registry_accounts,
                    &authority,
                    PREPARATION_SLOT,
                    110,
                    200,
                    sha256,
                )
                .unwrap()
            };
            (plan_images, settlement_selection)
        };
        assert_eq!(source_pool_for_plan, source_pool);
        assert_eq!(source_current_for_plan, source_current_page);
        assert_eq!(source_next_for_plan, source_next_page);
        assert_eq!(registry_for_plan, registry_image);
        assert_eq!(entry_for_plan, entry_image);
        let expected_plan_address = pool_v1_prepared_settlement_plan_address(
            &program_id,
            &pool,
            &statement_digest,
            leaf_count,
            &authority,
        )
        .0;
        assert_eq!(plan_images.core_address, expected_plan_address);
        assert_eq!(plan_images.rollover_shard.is_some(), has_next_page);
        let plan_address = plan_images.core_address;
        let plan_image = plan_images.core_image;
        let (rollover_shard_address, rollover_shard_image) = match plan_images.rollover_shard {
            Some(shard) => (Some(shard.address), Some(shard.image)),
            None => (None, None),
        };

        let marker = PoolV1NullifierMarkerV1 {
            transition_kind,
            pool: pool.to_bytes(),
            deployment_domain: state.identity.deployment_domain,
            nullifier,
            retained_anchor_sequence: leaf_count,
            retained_anchor_root: state.tree.root,
            verifier_profile: profile_binding,
            verifier_release: release_binding,
        };
        let marker_address = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &encode_digest_canonical(&nullifier),
        )
        .unwrap()
        .0;
        let mut marker_lamports = 1;
        let mut marker_data =
            [0u8; aspis_statement::pool_v1::POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let marker_account = account(
            &marker_address,
            &program_id,
            &mut marker_lamports,
            &mut marker_data,
            false,
            true,
        );
        let marker_plan =
            plan_nullifier_marker_consumption_v1(&program_id, &marker_account, marker).unwrap();

        let mut direct_pool = source_pool;
        let mut direct_current_page = source_current_page.clone();
        let mut direct_next_page = source_next_page.clone();
        let mut direct_pool_lamports = 1;
        let mut direct_current_lamports = 1;
        let mut direct_next_lamports = 1;
        let first_page = root_history_location(leaf_count + 1).page_number;
        let mutate_current = first_page == current_page_number;
        let direct_receipt = {
            let pool_account = account(
                &pool,
                &program_id,
                &mut direct_pool_lamports,
                &mut direct_pool,
                false,
                true,
            );
            let current_account = account(
                &current_page,
                &program_id,
                &mut direct_current_lamports,
                &mut direct_current_page,
                false,
                mutate_current,
            );
            if has_next_page {
                let next_account = account(
                    &next_page,
                    &program_id,
                    &mut direct_next_lamports,
                    &mut direct_next_page,
                    false,
                    true,
                );
                apply_authorized_append_after_v1(
                    &program_id,
                    &[pool_account, current_account, next_account],
                    request,
                    || Ok(()),
                )
                .unwrap()
            } else {
                apply_authorized_append_after_v1(
                    &program_id,
                    &[pool_account, current_account],
                    request,
                    || Ok(()),
                )
                .unwrap()
            }
        };

        Fixture {
            program_id,
            pool,
            current_page,
            next_page,
            has_next_page,
            source_pool,
            source_current_page,
            source_next_page,
            statement_payload,
            statement_digest,
            transition_kind,
            nullifier,
            authorization_receipt_address,
            authorization_receipt_owner: verifier_program,
            pending_authorization_receipt_image: pending_receipt,
            authorization_receipt_image,
            registry_program,
            registry_address,
            registry_image,
            entry_address,
            entry_image,
            verifier_selection: settlement_selection,
            authority,
            plan_address,
            plan_image,
            rollover_shard_address,
            rollover_shard_image,
            marker_address,
            marker_plan,
            direct_pool,
            direct_current_page,
            direct_next_page,
            direct_receipt,
        }
    }

    fn standard_fixture(kind: PoolV1TransitionKind, leaf_count: u64) -> Fixture {
        build_fixture(
            Pubkey::new_from_array([31u8; 32]),
            Pubkey::new_from_array([32u8; 32]),
            Pubkey::new_from_array([33u8; 32]),
            kind,
            leaf_count,
        )
    }

    fn prepare_instruction_for_fixture(
        fixture: &Fixture,
    ) -> [u8; crate::prepared_settlement_instruction::POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES]
    {
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: fixture.transition_kind,
            pool: fixture.pool.to_bytes(),
            deployment_domain: initialization().deployment_domain,
            anchor_sequence: fixture.direct_receipt.first.leaf_index,
            anchor_root: PoolStateV1::decode(&fixture.source_pool, &fixture.pool)
                .unwrap()
                .tree
                .root,
            nullifier: fixture.nullifier,
            verifier_profile: [41u8; 32],
            verifier_release: [42u8; 32],
        };
        let spend = match fixture.transition_kind {
            PoolV1TransitionKind::PrivateTransfer => {
                let statement =
                    decode_pool_v1_private_transfer_public_v1(&fixture.statement_payload).unwrap();
                encode_private_transfer_instruction_v1(
                    &envelope,
                    &PrivateTransferStatementV1 {
                        pool: statement.pool,
                        deployment_domain: statement.deployment_domain,
                        anchor_sequence: statement.anchor_sequence,
                        anchor_root: statement.anchor_root,
                        nullifier: statement.nullifier,
                        asset_id: statement.asset_id,
                        recipient_commitment: statement.recipient_commitment,
                        change_commitment: statement.change_commitment,
                    },
                )
                .unwrap()
            }
            PoolV1TransitionKind::Withdrawal => {
                let statement =
                    decode_pool_v1_withdrawal_public_v1(&fixture.statement_payload).unwrap();
                encode_withdrawal_instruction_v1(
                    &envelope,
                    &WithdrawalStatementV1 {
                        pool: statement.pool,
                        deployment_domain: statement.deployment_domain,
                        anchor_sequence: statement.anchor_sequence,
                        anchor_root: statement.anchor_root,
                        nullifier: statement.nullifier,
                        asset_id: statement.asset_id,
                        amount: statement.amount,
                        destination_token_account: statement.destination_token_account,
                        change_commitment: statement.change_commitment,
                    },
                )
                .unwrap()
            }
        };
        encode_prepare_settlement_instruction_v1(fixture.transition_kind, 110, 200, &spend).unwrap()
    }

    fn fixture_request(fixture: &Fixture) -> AuthorizedAppendV1 {
        match fixture.transition_kind {
            PoolV1TransitionKind::PrivateTransfer => {
                let statement =
                    decode_pool_v1_private_transfer_public_v1(&fixture.statement_payload).unwrap();
                AuthorizedAppendV1::Two(statement.recipient_commitment, statement.change_commitment)
            }
            PoolV1TransitionKind::Withdrawal => {
                let statement =
                    decode_pool_v1_withdrawal_public_v1(&fixture.statement_payload).unwrap();
                AuthorizedAppendV1::One(statement.change_commitment)
            }
        }
    }

    fn rebuild_fixture_plan_with_registry(
        fixture: &Fixture,
        registry_image: &mut [u8; POOL_V1_VERIFIER_REGISTRY_BYTES],
        entry_image: &mut [u8; POOL_V1_VERIFIER_ENTRY_BYTES],
        preparation_slot: u64,
    ) -> Result<PreparedSettlementPlanImagesV1, ProgramError> {
        let mut pool_image = fixture.source_pool;
        let mut current_image = fixture.source_current_page.clone();
        let mut next_image = fixture.source_next_page.clone();
        let mut receipt_image = fixture.authorization_receipt_image;
        let mut pool_lamports = 1;
        let mut current_lamports = 1;
        let mut next_lamports = 1;
        let mut receipt_lamports = 1;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let pool_account = account(
            &fixture.pool,
            &fixture.program_id,
            &mut pool_lamports,
            &mut pool_image,
            false,
            true,
        );
        let current_account = account(
            &fixture.current_page,
            &fixture.program_id,
            &mut current_lamports,
            &mut current_image,
            false,
            true,
        );
        let receipt_account = account(
            &fixture.authorization_receipt_address,
            &fixture.authorization_receipt_owner,
            &mut receipt_lamports,
            &mut receipt_image,
            false,
            false,
        );
        let registry_account = account(
            &fixture.registry_address,
            &fixture.registry_program,
            &mut registry_lamports,
            registry_image,
            false,
            false,
        );
        let entry_account = account(
            &fixture.entry_address,
            &fixture.registry_program,
            &mut entry_lamports,
            entry_image,
            false,
            false,
        );
        let registry_accounts = [registry_account, entry_account];
        let state = CanonicalPoolStateV1::decode_account(&fixture.program_id, &pool_account)?;
        let request = fixture_request(fixture);
        if fixture.has_next_page {
            let next_account = account(
                &fixture.next_page,
                &fixture.program_id,
                &mut next_lamports,
                &mut next_image,
                false,
                true,
            );
            build_prepared_settlement_plan_v1(
                &fixture.program_id,
                &pool_account,
                &current_account,
                &current_account,
                Some(&next_account),
                &state,
                request,
                &fixture.statement_payload,
                &receipt_account,
                &registry_accounts,
                &fixture.authority,
                preparation_slot,
                110,
                200,
                sha256,
            )
        } else {
            build_prepared_settlement_plan_v1(
                &fixture.program_id,
                &pool_account,
                &current_account,
                &current_account,
                None,
                &state,
                request,
                &fixture.statement_payload,
                &receipt_account,
                &registry_accounts,
                &fixture.authority,
                preparation_slot,
                110,
                200,
                sha256,
            )
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_with<'a>(
        fixture: &'a Fixture,
        plan_image: &'a Box<[u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]>,
        source_pool: &'a [u8],
        source_current: &'a [u8],
        source_next: Option<&'a [u8]>,
        statement_payload: &'a [u8],
        expected_statement_digest: [u8; 32],
        receipt_image: &'a [u8],
        authority: &'a Pubkey,
        settlement_slot: u64,
        marker_plan: &'a PlannedNullifierMarkerV1,
    ) -> Result<PreparedSettlementApplyResultV1<'a>, ProgramError> {
        apply_with_selection(
            fixture,
            plan_image,
            source_pool,
            source_current,
            source_next,
            statement_payload,
            expected_statement_digest,
            receipt_image,
            authority,
            settlement_slot,
            marker_plan,
            fixture.verifier_selection,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_with_selection<'a>(
        fixture: &'a Fixture,
        plan_image: &'a Box<[u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]>,
        source_pool: &'a [u8],
        source_current: &'a [u8],
        source_next: Option<&'a [u8]>,
        statement_payload: &'a [u8],
        expected_statement_digest: [u8; 32],
        receipt_image: &'a [u8],
        authority: &'a Pubkey,
        settlement_slot: u64,
        marker_plan: &'a PlannedNullifierMarkerV1,
        verifier_selection: AuthenticatedVerifierSelectionV1,
    ) -> Result<PreparedSettlementApplyResultV1<'a>, ProgramError> {
        let next_page = source_next.map(|image| (&fixture.next_page, image));
        let rollover_shard = match (
            fixture.rollover_shard_address.as_ref(),
            fixture.rollover_shard_image.as_ref(),
        ) {
            (Some(address), Some(image)) => Some(PreparedSettlementRolloverShardAccountV1 {
                address,
                owner: &fixture.program_id,
                image: image.as_ref(),
            }),
            (None, None) => None,
            _ => return Err(ProgramError::InvalidAccountData),
        };
        apply_prepared_settlement_plan_v1(PreparedSettlementApplyContextV1 {
            program_id: &fixture.program_id,
            plan_address: &fixture.plan_address,
            plan_owner: &fixture.program_id,
            plan_authority: authority,
            plan_image: plan_image.as_ref(),
            rollover_shard,
            pool_address: &fixture.pool,
            source_pool_image: source_pool,
            current_page_address: &fixture.current_page,
            source_current_page_image: source_current,
            next_page,
            statement_payload,
            expected_transition_kind: fixture.transition_kind,
            expected_statement_digest,
            expected_nullifier: fixture.nullifier,
            authorization_receipt_address: &fixture.authorization_receipt_address,
            authorization_receipt_owner: &fixture.authorization_receipt_owner,
            authorization_receipt_image: receipt_image,
            authorization_receipt_is_signer: false,
            authorization_receipt_is_writable: false,
            authorization_receipt_executable: false,
            verifier_selection,
            nullifier_marker_address: &fixture.marker_address,
            nullifier_marker_plan: marker_plan,
            settlement_slot,
            hash: sha256,
        })
    }

    fn apply_fixture(
        fixture: &Fixture,
    ) -> Result<PreparedSettlementApplyResultV1<'_>, ProgramError> {
        apply_with(
            fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            fixture
                .has_next_page
                .then_some(fixture.source_next_page.as_slice()),
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
    }

    fn assert_parity(fixture: &Fixture) {
        let result = apply_fixture(fixture).unwrap();
        assert_eq!(result.action.transition_kind(), fixture.transition_kind);
        match fixture.transition_kind {
            PoolV1TransitionKind::PrivateTransfer => {
                assert_eq!(result.action.withdrawal_amount_and_destination(), None);
            }
            PoolV1TransitionKind::Withdrawal => {
                let statement =
                    decode_pool_v1_withdrawal_public_v1(&fixture.statement_payload).unwrap();
                assert_eq!(
                    result.action.withdrawal_amount_and_destination(),
                    Some((statement.amount, statement.destination_token_account))
                );
            }
        }
        assert_eq!(result.receipt, fixture.direct_receipt);
        assert_eq!(result.next_pool_image, &fixture.direct_pool);
        assert_eq!(
            result.next_current_page_image.as_slice(),
            fixture.direct_current_page
        );
        match (result.next_rollover_page_image, fixture.has_next_page) {
            (Some(image), true) => assert_eq!(image.as_slice(), fixture.direct_next_page),
            (None, false) => {}
            _ => panic!("wrong rollover image shape"),
        }
    }

    #[test]
    fn public_preparation_processor_persists_exact_core_and_rejects_privilege_aliases() {
        let fixture = standard_fixture(PoolV1TransitionKind::Withdrawal, 0);
        let instruction = prepare_instruction_for_fixture(&fixture);
        let expected_core = fixture.plan_image.clone();
        let rent = Rent::default();
        let required_core_lamports =
            rent.minimum_balance(POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES);
        let system_id = system_program::id();
        let native_loader_id = native_loader::id();
        let mut payer_lamports = 1;
        let mut payer_data = [];
        let mut pool_lamports = 1;
        let mut pool_data = fixture.source_pool;
        let mut page_lamports = 1;
        let mut page_data = fixture.source_current_page.clone();
        let mut receipt_lamports = 1;
        let mut receipt_data = fixture.authorization_receipt_image;
        let mut registry_lamports = 1;
        let mut registry_data = fixture.registry_image;
        let mut entry_lamports = 1;
        let mut entry_data = fixture.entry_image;
        let mut core_lamports = required_core_lamports.saturating_sub(1);
        let mut core_data: Box<[u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]> =
            vec![0u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]
                .into_boxed_slice()
                .try_into()
                .unwrap();
        let mut system_lamports = 1;
        let mut system_data = [];
        let accounts = vec![
            account(
                &fixture.authority,
                &system_id,
                &mut payer_lamports,
                &mut payer_data,
                true,
                true,
            ),
            account(
                &fixture.pool,
                &fixture.program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
            ),
            account(
                &fixture.current_page,
                &fixture.program_id,
                &mut page_lamports,
                &mut page_data,
                false,
                false,
            ),
            account(
                &fixture.authorization_receipt_address,
                &fixture.authorization_receipt_owner,
                &mut receipt_lamports,
                &mut receipt_data,
                false,
                false,
            ),
            account(
                &fixture.registry_address,
                &fixture.registry_program,
                &mut registry_lamports,
                &mut registry_data,
                false,
                false,
            ),
            account(
                &fixture.entry_address,
                &fixture.registry_program,
                &mut entry_lamports,
                &mut entry_data,
                false,
                false,
            ),
            account(
                &fixture.plan_address,
                &fixture.program_id,
                &mut core_lamports,
                core_data.as_mut(),
                false,
                true,
            ),
            AccountInfo::new(
                &system_id,
                false,
                false,
                &mut system_lamports,
                &mut system_data,
                &native_loader_id,
                true,
                Epoch::default(),
            ),
        ];
        assert_eq!(
            process_prepare_settlement_with_runtime_v1(
                &fixture.program_id,
                &accounts,
                &instruction,
                PREPARATION_SLOT,
                &rent,
                sha256,
                &mut NoPreparationCpi,
            ),
            Err(PoolV1ProgramError::InvalidFreshAccount.into())
        );
        assert!(accounts[6]
            .try_borrow_data()
            .unwrap()
            .iter()
            .all(|byte| *byte == 0));
        **accounts[6].try_borrow_mut_lamports().unwrap() = required_core_lamports;
        assert_eq!(
            process_prepare_settlement_with_runtime_v1(
                &fixture.program_id,
                &accounts,
                &instruction,
                PREPARATION_SLOT,
                &rent,
                sha256,
                &mut NoPreparationCpi,
            ),
            Ok(())
        );
        assert_eq!(
            accounts[6].try_borrow_data().unwrap().as_ref(),
            expected_core.as_ref()
        );

        let mut alias = accounts.clone();
        alias[4] = alias[3].clone();
        assert_eq!(
            process_prepare_settlement_with_runtime_v1(
                &fixture.program_id,
                &alias,
                &instruction,
                PREPARATION_SLOT,
                &rent,
                sha256,
                &mut NoPreparationCpi,
            ),
            Err(ProgramError::InvalidArgument)
        );
        let mut missing_signature = accounts.clone();
        missing_signature[0].is_signer = false;
        assert_eq!(
            process_prepare_settlement_with_runtime_v1(
                &fixture.program_id,
                &missing_signature,
                &instruction,
                PREPARATION_SLOT,
                &rent,
                sha256,
                &mut NoPreparationCpi,
            ),
            Err(PoolV1ProgramError::InvalidPayer.into())
        );
        let mut writable_receipt = accounts.clone();
        writable_receipt[3].is_writable = true;
        assert!(process_prepare_settlement_with_runtime_v1(
            &fixture.program_id,
            &writable_receipt,
            &instruction,
            PREPARATION_SLOT,
            &rent,
            sha256,
            &mut NoPreparationCpi,
        )
        .is_err());
    }

    #[test]
    fn public_preparation_processor_persists_exact_rollover_core_and_shard() {
        let fixture = standard_fixture(PoolV1TransitionKind::PrivateTransfer, 254);
        let instruction = prepare_instruction_for_fixture(&fixture);
        let expected_core = fixture.plan_image.clone();
        let expected_shard = fixture.rollover_shard_image.clone().unwrap();
        let shard_address = fixture.rollover_shard_address.unwrap();
        let rent = Rent::default();
        let required_page_lamports = rent.minimum_balance(POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES);
        let required_core_lamports =
            rent.minimum_balance(POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES);
        let required_shard_lamports =
            rent.minimum_balance(POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES);
        let system_id = system_program::id();
        let native_loader_id = native_loader::id();
        let mut payer_lamports = 1;
        let mut payer_data = [];
        let mut pool_lamports = 1;
        let mut pool_data = fixture.source_pool;
        let mut page_lamports = 1;
        let mut page_data = fixture.source_current_page.clone();
        let mut next_lamports = required_page_lamports.saturating_sub(1);
        let mut next_data = fixture.source_next_page.clone();
        let mut receipt_lamports = 1;
        let mut receipt_data = fixture.authorization_receipt_image;
        let mut registry_lamports = 1;
        let mut registry_data = fixture.registry_image;
        let mut entry_lamports = 1;
        let mut entry_data = fixture.entry_image;
        let mut core_lamports = required_core_lamports;
        let mut core_data: Box<[u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]> =
            vec![0u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]
                .into_boxed_slice()
                .try_into()
                .unwrap();
        let mut shard_lamports = required_shard_lamports.saturating_sub(1);
        let mut shard_data: Box<[u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES]> =
            vec![0u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES]
                .into_boxed_slice()
                .try_into()
                .unwrap();
        let mut system_lamports = 1;
        let mut system_data = [];
        let accounts = vec![
            account(
                &fixture.authority,
                &system_id,
                &mut payer_lamports,
                &mut payer_data,
                true,
                true,
            ),
            account(
                &fixture.pool,
                &fixture.program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
            ),
            account(
                &fixture.current_page,
                &fixture.program_id,
                &mut page_lamports,
                &mut page_data,
                false,
                false,
            ),
            account(
                &fixture.next_page,
                &fixture.program_id,
                &mut next_lamports,
                &mut next_data,
                false,
                true,
            ),
            account(
                &fixture.authorization_receipt_address,
                &fixture.authorization_receipt_owner,
                &mut receipt_lamports,
                &mut receipt_data,
                false,
                false,
            ),
            account(
                &fixture.registry_address,
                &fixture.registry_program,
                &mut registry_lamports,
                &mut registry_data,
                false,
                false,
            ),
            account(
                &fixture.entry_address,
                &fixture.registry_program,
                &mut entry_lamports,
                &mut entry_data,
                false,
                false,
            ),
            account(
                &fixture.plan_address,
                &fixture.program_id,
                &mut core_lamports,
                core_data.as_mut(),
                false,
                true,
            ),
            account(
                &shard_address,
                &fixture.program_id,
                &mut shard_lamports,
                shard_data.as_mut(),
                false,
                true,
            ),
            AccountInfo::new(
                &system_id,
                false,
                false,
                &mut system_lamports,
                &mut system_data,
                &native_loader_id,
                true,
                Epoch::default(),
            ),
        ];
        assert_eq!(
            process_prepare_settlement_with_runtime_v1(
                &fixture.program_id,
                &accounts,
                &instruction,
                PREPARATION_SLOT,
                &rent,
                sha256,
                &mut NoPreparationCpi,
            ),
            Err(PoolV1ProgramError::InvalidFreshAccount.into())
        );
        assert!(accounts[3]
            .try_borrow_data()
            .unwrap()
            .iter()
            .all(|byte| *byte == 0));
        **accounts[3].try_borrow_mut_lamports().unwrap() = required_page_lamports;
        assert_eq!(
            process_prepare_settlement_with_runtime_v1(
                &fixture.program_id,
                &accounts,
                &instruction,
                PREPARATION_SLOT,
                &rent,
                sha256,
                &mut NoPreparationCpi,
            ),
            Err(PoolV1ProgramError::InvalidFreshAccount.into())
        );
        assert!(accounts[7]
            .try_borrow_data()
            .unwrap()
            .iter()
            .all(|byte| *byte == 0));
        assert!(accounts[8]
            .try_borrow_data()
            .unwrap()
            .iter()
            .all(|byte| *byte == 0));
        **accounts[8].try_borrow_mut_lamports().unwrap() = required_shard_lamports;
        assert_eq!(
            process_prepare_settlement_with_runtime_v1(
                &fixture.program_id,
                &accounts,
                &instruction,
                PREPARATION_SLOT,
                &rent,
                sha256,
                &mut NoPreparationCpi,
            ),
            Ok(())
        );
        assert_eq!(
            accounts[7].try_borrow_data().unwrap().as_ref(),
            expected_core.as_ref()
        );
        assert_eq!(
            accounts[8].try_borrow_data().unwrap().as_ref(),
            expected_shard.as_ref()
        );
        assert!(accounts[3]
            .try_borrow_data()
            .unwrap()
            .iter()
            .all(|byte| *byte == 0));
    }

    #[test]
    fn withdrawal_and_private_transfer_are_byte_exact_with_the_direct_path() {
        assert_parity(&standard_fixture(PoolV1TransitionKind::Withdrawal, 0));
        assert_parity(&standard_fixture(PoolV1TransitionKind::PrivateTransfer, 0));
    }

    #[test]
    fn rollover_encoder_owned_output_images_fit_default_solana_heap() {
        assert_eq!(
            crate::prepared_settlement_format::PREPARED_SETTLEMENT_MAX_LIVE_OUTPUT_IMAGE_BYTES,
            POOL_V1_STATE_ACCOUNT_BYTES
                + POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES
                + POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES
        );
        assert!(
            crate::prepared_settlement_format::PREPARED_SETTLEMENT_MAX_LIVE_OUTPUT_IMAGE_BYTES
                < 32 * 1_024
        );
    }

    #[test]
    fn two_leaf_plan_preserves_both_chronological_roots_across_page_boundary() {
        let fixture = standard_fixture(PoolV1TransitionKind::PrivateTransfer, 254);
        assert!(fixture.has_next_page);
        assert_eq!(fixture.direct_receipt.first.root_sequence, 255);
        assert_eq!(fixture.direct_receipt.second.unwrap().root_sequence, 256);
        assert_parity(&fixture);
    }

    #[test]
    fn every_plan_byte_is_authenticated() {
        let fixture = standard_fixture(PoolV1TransitionKind::Withdrawal, 0);
        let mut changed = fixture.plan_image.clone();
        for offset in 0..changed.len() {
            changed[offset] ^= 1;
            assert!(
                decode_prepared_settlement_plan_v1(
                    &fixture.plan_address,
                    changed.as_ref(),
                    None,
                    sha256,
                )
                .is_err(),
                "core byte {offset} was not authenticated"
            );
            changed[offset] ^= 1;
        }

        let rollover = standard_fixture(PoolV1TransitionKind::PrivateTransfer, 254);
        let shard_address = rollover.rollover_shard_address.as_ref().unwrap();
        let mut changed_shard = rollover.rollover_shard_image.clone().unwrap();
        for offset in 0..changed_shard.len() {
            changed_shard[offset] ^= 1;
            let shard = PreparedSettlementRolloverShardAccountV1 {
                address: shard_address,
                owner: &rollover.program_id,
                image: changed_shard.as_ref(),
            };
            assert!(
                decode_prepared_settlement_plan_v1(
                    &rollover.plan_address,
                    rollover.plan_image.as_ref(),
                    Some(shard),
                    sha256,
                )
                .is_err(),
                "rollover-shard byte {offset} was not authenticated"
            );
            changed_shard[offset] ^= 1;
        }
    }

    #[test]
    fn rollover_shard_is_mutually_bound_and_semantically_checked() {
        let fixture = standard_fixture(PoolV1TransitionKind::PrivateTransfer, 254);
        let shard_address = fixture.rollover_shard_address.as_ref().unwrap();
        let shard_image = fixture.rollover_shard_image.as_ref().unwrap();

        assert!(decode_prepared_settlement_plan_v1(
            &fixture.plan_address,
            fixture.plan_image.as_ref(),
            None,
            sha256,
        )
        .is_err());
        let wrong_owner = Pubkey::new_unique();
        assert!(decode_prepared_settlement_plan_v1(
            &fixture.plan_address,
            fixture.plan_image.as_ref(),
            Some(PreparedSettlementRolloverShardAccountV1 {
                address: shard_address,
                owner: &wrong_owner,
                image: shard_image.as_ref(),
            }),
            sha256,
        )
        .is_err());

        let no_rollover = standard_fixture(PoolV1TransitionKind::Withdrawal, 0);
        assert!(decode_prepared_settlement_plan_v1(
            &no_rollover.plan_address,
            no_rollover.plan_image.as_ref(),
            Some(PreparedSettlementRolloverShardAccountV1 {
                address: shard_address,
                owner: &fixture.program_id,
                image: shard_image.as_ref(),
            }),
            sha256,
        )
        .is_err());

        let mut wrong_core = fixture.plan_image.clone();
        let mut wrong_core_shard = shard_image.clone();
        wrong_core_shard[TEST_ROLLOVER_SHARD_CORE_ADDRESS_OFFSET] ^= 1;
        reauthenticate_prepared_settlement_rollover_for_test(&mut wrong_core_shard, sha256);
        bind_prepared_settlement_rollover_for_test(&mut wrong_core, &wrong_core_shard, sha256);
        assert!(decode_prepared_settlement_plan_v1(
            &fixture.plan_address,
            wrong_core.as_ref(),
            Some(PreparedSettlementRolloverShardAccountV1 {
                address: shard_address,
                owner: &fixture.program_id,
                image: wrong_core_shard.as_ref(),
            }),
            sha256,
        )
        .is_err());

        let mut wrong_image_core = fixture.plan_image.clone();
        let mut wrong_image_shard = shard_image.clone();
        wrong_image_shard[TEST_ROLLOVER_SHARD_IMAGE_OFFSET + 101] ^= 1;
        reauthenticate_prepared_settlement_rollover_for_test(&mut wrong_image_shard, sha256);
        bind_prepared_settlement_rollover_for_test(
            &mut wrong_image_core,
            &wrong_image_shard,
            sha256,
        );
        let plan = decode_prepared_settlement_plan_v1(
            &fixture.plan_address,
            wrong_image_core.as_ref(),
            Some(PreparedSettlementRolloverShardAccountV1 {
                address: shard_address,
                owner: &fixture.program_id,
                image: wrong_image_shard.as_ref(),
            }),
            sha256,
        )
        .unwrap();
        let source_current: &[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES] =
            fixture.source_current_page.as_slice().try_into().unwrap();
        let source_next: &[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES] =
            fixture.source_next_page.as_slice().try_into().unwrap();
        assert!(history_result_images_match(
            &fixture.program_id,
            &fixture.pool,
            plan,
            source_current,
            Some(source_next),
        )
        .is_err());
    }

    #[test]
    fn stale_pool_pages_receipt_and_time_fail_closed() {
        let fixture = standard_fixture(PoolV1TransitionKind::PrivateTransfer, 254);
        let mut stale_pool = fixture.source_pool;
        stale_pool[777] ^= 1;
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &stale_pool,
            &fixture.source_current_page,
            Some(&fixture.source_next_page),
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());

        let mut stale_current = fixture.source_current_page.clone();
        stale_current[101] ^= 1;
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &stale_current,
            Some(&fixture.source_next_page),
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());

        let mut stale_next = fixture.source_next_page.clone();
        stale_next[9] = 1;
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            Some(&stale_next),
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());

        let mut wrong_receipt = fixture.authorization_receipt_image;
        wrong_receipt[200] ^= 1;
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            Some(&fixture.source_next_page),
            &fixture.statement_payload,
            fixture.statement_digest,
            &wrong_receipt,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            Some(&fixture.source_next_page),
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            109,
            &fixture.marker_plan,
        )
        .is_err());
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            Some(&fixture.source_next_page),
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            201,
            &fixture.marker_plan,
        )
        .is_err());
    }

    #[test]
    fn asra_pending_wrapper_binding_pda_and_nested_receipt_fail_closed() {
        let fixture = standard_fixture(PoolV1TransitionKind::Withdrawal, 0);

        assert!(authenticate_statement_and_receipt_v1(
            fixture.transition_kind,
            &fixture.statement_payload,
            &fixture.authorization_receipt_address,
            &fixture.authorization_receipt_owner,
            &fixture.pending_authorization_receipt_image,
            150,
            sha256,
        )
        .is_err());

        let mut wrong_wrapper_digest = fixture.authorization_receipt_image;
        wrong_wrapper_digest[719] ^= 1;
        assert!(authenticate_statement_and_receipt_v1(
            fixture.transition_kind,
            &fixture.statement_payload,
            &fixture.authorization_receipt_address,
            &fixture.authorization_receipt_owner,
            &wrong_wrapper_digest,
            150,
            sha256,
        )
        .is_err());

        let mut wrong_binding = fixture.authorization_receipt_image;
        wrong_binding[112] ^= 1;
        refresh_asra_wrapper_digest(&mut wrong_binding);
        assert!(authenticate_statement_and_receipt_v1(
            fixture.transition_kind,
            &fixture.statement_payload,
            &fixture.authorization_receipt_address,
            &fixture.authorization_receipt_owner,
            &wrong_binding,
            150,
            sha256,
        )
        .is_err());

        let mut altered_nested_receipt = fixture.authorization_receipt_image;
        altered_nested_receipt[256 + 200] ^= 1;
        refresh_asra_wrapper_digest(&mut altered_nested_receipt);
        assert!(authenticate_statement_and_receipt_v1(
            fixture.transition_kind,
            &fixture.statement_payload,
            &fixture.authorization_receipt_address,
            &fixture.authorization_receipt_owner,
            &altered_nested_receipt,
            150,
            sha256,
        )
        .is_err());

        let wrong_pda = Pubkey::new_from_array([99u8; 32]);
        assert!(authenticate_statement_and_receipt_v1(
            fixture.transition_kind,
            &fixture.statement_payload,
            &wrong_pda,
            &fixture.authorization_receipt_owner,
            &fixture.authorization_receipt_image,
            150,
            sha256,
        )
        .is_err());
    }

    #[test]
    fn preparation_rejects_self_consistent_receipt_for_non_pool_historical_root() {
        let fixture = standard_fixture(PoolV1TransitionKind::Withdrawal, 0);
        let wrapper = decode_pool_v1_authorization_receipt_account_v1(
            &fixture.authorization_receipt_image,
            sha256,
        )
        .unwrap();
        let mut binding = wrapper.receipt.unwrap().binding;
        let mut statement =
            decode_pool_v1_withdrawal_public_v1(&fixture.statement_payload).unwrap();
        statement.anchor_root = digest(88_000);
        let fake_payload = encode_pool_v1_withdrawal_public_v1(&statement).unwrap();
        binding.anchor_root = statement.anchor_root;
        binding.statement_digest = verifier_statement_payload_digest_v1(
            binding.statement_version,
            &binding.profile_binding,
            &binding.release_binding,
            &fake_payload,
            sha256,
        )
        .unwrap();
        let fake_envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: binding.transition_kind,
            pool: binding.pool,
            deployment_domain: binding.deployment_domain,
            anchor_sequence: binding.anchor_sequence,
            anchor_root: binding.anchor_root,
            nullifier: binding.nullifier,
            verifier_profile: binding.profile_binding,
            verifier_release: binding.release_binding,
        };
        binding.envelope_digest =
            historical_anchor_envelope_digest_v1(&fake_envelope, sha256).unwrap();
        let dispatch_request = VerifierDispatchRequestV1 {
            binding,
            statement_payload: &fake_payload,
        };
        let inputs =
            pool_v1_authorization_receipt_pda_inputs_for_binding_v1(&binding, 0, sha256).unwrap();
        let (receipt_address, receipt_bump) = pool_v1_authorization_receipt_account_address(
            &fixture.authorization_receipt_owner,
            &inputs,
        );
        let pending = initialize_pool_v1_authorization_receipt_account_v1(
            &dispatch_request,
            binding.proof_account,
            [46u8; 32],
            Some([46u8; 32]),
            [47u8; 32],
            receipt_bump,
            sha256,
        )
        .unwrap();
        let mut fake_receipt = finalize_pool_v1_authorization_receipt_account_v1(
            &pending,
            &dispatch_request,
            &PoolV1AuthorizationReceiptV1 {
                pda_bump: receipt_bump,
                verified_slot: 100,
                binding,
            },
            sha256,
        )
        .unwrap();

        let mut pool_data = fixture.source_pool;
        let mut page_data = fixture.source_current_page.clone();
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        let mut receipt_lamports = 1;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut registry_image = fixture.registry_image;
        let mut entry_image = fixture.entry_image;
        let pool_account = account(
            &fixture.pool,
            &fixture.program_id,
            &mut pool_lamports,
            &mut pool_data,
            false,
            true,
        );
        let page_account = account(
            &fixture.current_page,
            &fixture.program_id,
            &mut page_lamports,
            &mut page_data,
            false,
            true,
        );
        let receipt_account = account(
            &receipt_address,
            &fixture.authorization_receipt_owner,
            &mut receipt_lamports,
            &mut fake_receipt,
            false,
            false,
        );
        let registry_account = account(
            &fixture.registry_address,
            &fixture.registry_program,
            &mut registry_lamports,
            &mut registry_image,
            false,
            false,
        );
        let entry_account = account(
            &fixture.entry_address,
            &fixture.registry_program,
            &mut entry_lamports,
            &mut entry_image,
            false,
            false,
        );
        let registry_accounts = [registry_account, entry_account];
        let state =
            CanonicalPoolStateV1::decode_account(&fixture.program_id, &pool_account).unwrap();
        let result = build_prepared_settlement_plan_v1(
            &fixture.program_id,
            &pool_account,
            &page_account,
            &page_account,
            None,
            &state,
            AuthorizedAppendV1::One(statement.change_commitment),
            &fake_payload,
            &receipt_account,
            &registry_accounts,
            &fixture.authority,
            PREPARATION_SLOT,
            110,
            200,
            sha256,
        );
        assert_eq!(
            result,
            Err(PoolV1ProgramError::HistoricalAnchorRootMismatch.into())
        );
        assert_eq!(pool_data, fixture.source_pool);
        assert_eq!(page_data, fixture.source_current_page);
    }

    #[test]
    fn registry_selection_is_active_exact_and_reauthenticated_at_settlement() {
        let fixture = standard_fixture(PoolV1TransitionKind::Withdrawal, 0);
        let original_registry = decode_verifier_registry_v1(&fixture.registry_image).unwrap();
        let original_entry = decode_verifier_registry_entry_v1(&fixture.entry_image).unwrap();

        let mut paused_registry = encode_verifier_registry_v1(&VerifierRegistryV1 {
            flags: original_registry.flags | POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED,
            ..original_registry
        })
        .unwrap();
        let mut entry_image = fixture.entry_image;
        assert_eq!(
            rebuild_fixture_plan_with_registry(
                &fixture,
                &mut paused_registry,
                &mut entry_image,
                PREPARATION_SLOT,
            ),
            Err(PoolV1ProgramError::VerifierRegistryPaused.into())
        );

        let mut registry_image = fixture.registry_image;
        let mut inactive_entry = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Paused,
            ..original_entry
        })
        .unwrap();
        assert_eq!(
            rebuild_fixture_plan_with_registry(
                &fixture,
                &mut registry_image,
                &mut inactive_entry,
                PREPARATION_SLOT,
            ),
            Err(PoolV1ProgramError::VerifierEntryInactive.into())
        );

        let mut registry_image = fixture.registry_image;
        let mut wrong_program = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            verifier_program: [91u8; 32],
            ..original_entry
        })
        .unwrap();
        assert_eq!(
            rebuild_fixture_plan_with_registry(
                &fixture,
                &mut registry_image,
                &mut wrong_program,
                PREPARATION_SLOT,
            ),
            Err(PoolV1ProgramError::VerifierSelectionMismatch.into())
        );

        let mut registry_image = fixture.registry_image;
        let mut wrong_profile = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            profile_binding: [92u8; 32],
            ..original_entry
        })
        .unwrap();
        assert_eq!(
            rebuild_fixture_plan_with_registry(
                &fixture,
                &mut registry_image,
                &mut wrong_profile,
                PREPARATION_SLOT,
            ),
            Err(PoolV1ProgramError::VerifierSelectionMismatch.into())
        );

        // The plan was prepared while this exact selection was active. Model
        // governance retiring it before settlement: current reauthentication
        // rejects, and even an otherwise matching pre-retirement capability
        // cannot be reused at the later settlement slot.
        let mut registry_image = fixture.registry_image;
        let mut retired_entry = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            retirement_slot: SETTLEMENT_SLOT,
            ..original_entry
        })
        .unwrap();
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let registry_account = account(
            &fixture.registry_address,
            &fixture.registry_program,
            &mut registry_lamports,
            &mut registry_image,
            false,
            false,
        );
        let entry_account = account(
            &fixture.entry_address,
            &fixture.registry_program,
            &mut entry_lamports,
            &mut retired_entry,
            false,
            false,
        );
        let registry_accounts = [registry_account, entry_account];
        let wrapper = decode_pool_v1_authorization_receipt_account_v1(
            &fixture.authorization_receipt_image,
            sha256,
        )
        .unwrap();
        let selection = registry_selection(&wrapper.receipt.unwrap().binding);
        let stale_selection = authenticate_verifier_selection_v1(
            &fixture.pool,
            &initialization().verifier_policy,
            &registry_accounts,
            selection,
            SETTLEMENT_SLOT - 1,
        )
        .unwrap();
        assert_eq!(
            authenticate_verifier_selection_v1(
                &fixture.pool,
                &initialization().verifier_policy,
                &registry_accounts,
                selection,
                SETTLEMENT_SLOT,
            ),
            Err(PoolV1ProgramError::VerifierEntryRetired.into())
        );
        assert!(apply_with_selection(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            None,
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            SETTLEMENT_SLOT,
            &fixture.marker_plan,
            stale_selection,
        )
        .is_err());

        // A sealed capability for the same Pool/selection/slot but obtained
        // from an attacker-chosen policy and registry is not interchangeable
        // with the policy encoded in the hash-bound source Pool image.
        let attacker_policy = aspis_statement::pool_v1::VerifierPolicyV1 {
            flags: 0,
            registry_program: [93u8; 32],
            registry_authority: [94u8; 32],
            policy_binding: [95u8; 32],
        };
        let attacker_registry_program = Pubkey::new_from_array(attacker_policy.registry_program);
        let (
            attacker_registry_address,
            mut attacker_registry_image,
            attacker_entry_address,
            mut attacker_entry_image,
        ) = registry_images(
            &fixture.pool,
            &attacker_policy,
            selection,
            VerifierEntryStatusV1::Active,
            POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        );
        let mut attacker_registry_lamports = 1;
        let mut attacker_entry_lamports = 1;
        let attacker_registry_account = account(
            &attacker_registry_address,
            &attacker_registry_program,
            &mut attacker_registry_lamports,
            &mut attacker_registry_image,
            false,
            false,
        );
        let attacker_entry_account = account(
            &attacker_entry_address,
            &attacker_registry_program,
            &mut attacker_entry_lamports,
            &mut attacker_entry_image,
            false,
            false,
        );
        let attacker_selection = authenticate_verifier_selection_v1(
            &fixture.pool,
            &attacker_policy,
            &[attacker_registry_account, attacker_entry_account],
            selection,
            SETTLEMENT_SLOT,
        )
        .unwrap();
        assert!(apply_with_selection(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            None,
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            SETTLEMENT_SLOT,
            &fixture.marker_plan,
            attacker_selection,
        )
        .is_err());
    }

    #[test]
    fn reauthenticated_root_receipt_and_output_order_substitutions_reject() {
        let fixture = standard_fixture(PoolV1TransitionKind::PrivateTransfer, 0);

        let mut wrong_source_root = fixture.plan_image.clone();
        wrong_source_root[TEST_SOURCE_ROOT_OFFSET] ^= 1;
        reauthenticate_prepared_settlement_plan_for_test(&mut wrong_source_root, sha256);
        assert!(apply_with(
            &fixture,
            &wrong_source_root,
            &fixture.source_pool,
            &fixture.source_current_page,
            None,
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());

        let mut wrong_receipt_root = fixture.plan_image.clone();
        wrong_receipt_root[TEST_FIRST_RECEIPT_ROOT_OFFSET] ^= 1;
        reauthenticate_prepared_settlement_plan_for_test(&mut wrong_receipt_root, sha256);
        assert!(apply_with(
            &fixture,
            &wrong_receipt_root,
            &fixture.source_pool,
            &fixture.source_current_page,
            None,
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());

        let mut reversed = fixture.plan_image.clone();
        for offset in 0..32 {
            reversed.swap(
                TEST_FIRST_COMMITMENT_OFFSET + offset,
                TEST_SECOND_COMMITMENT_OFFSET + offset,
            );
        }
        reauthenticate_prepared_settlement_plan_for_test(&mut reversed, sha256);
        assert!(apply_with(
            &fixture,
            &reversed,
            &fixture.source_pool,
            &fixture.source_current_page,
            None,
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());
    }

    #[test]
    fn authority_sequence_parallel_plan_and_close_bindings_are_exact() {
        let program_id = Pubkey::new_from_array([31u8; 32]);
        let verifier_program = Pubkey::new_from_array([32u8; 32]);
        let first_authority = Pubkey::new_from_array([33u8; 32]);
        let second_authority = Pubkey::new_from_array([34u8; 32]);
        let first = build_fixture(
            program_id,
            verifier_program,
            first_authority,
            PoolV1TransitionKind::Withdrawal,
            0,
        );
        let parallel = build_fixture(
            program_id,
            verifier_program,
            second_authority,
            PoolV1TransitionKind::Withdrawal,
            0,
        );
        assert_eq!(first.statement_digest, parallel.statement_digest);
        assert_ne!(first.plan_address, parallel.plan_address);
        assert!(apply_fixture(&first).is_ok());
        assert!(apply_fixture(&parallel).is_ok());
        assert!(apply_with(
            &first,
            &first.plan_image,
            &first.source_pool,
            &first.source_current_page,
            None,
            &first.statement_payload,
            first.statement_digest,
            &first.authorization_receipt_image,
            &second_authority,
            150,
            &first.marker_plan,
        )
        .is_err());

        let same_statement_next_sequence = pool_v1_prepared_settlement_plan_address(
            &program_id,
            &first.pool,
            &first.statement_digest,
            1,
            &first_authority,
        )
        .0;
        assert_ne!(first.plan_address, same_statement_next_sequence);

        assert_eq!(
            authorize_prepared_settlement_plan_close_v1(
                &program_id,
                &first.plan_address,
                &program_id,
                first.plan_image.as_ref(),
                None,
                &first_authority,
                true,
                sha256,
            ),
            Ok(())
        );
        assert!(authorize_prepared_settlement_plan_close_v1(
            &program_id,
            &first.plan_address,
            &program_id,
            first.plan_image.as_ref(),
            None,
            &second_authority,
            true,
            sha256,
        )
        .is_err());
        assert!(authorize_prepared_settlement_plan_close_v1(
            &program_id,
            &first.plan_address,
            &program_id,
            first.plan_image.as_ref(),
            None,
            &first_authority,
            false,
            sha256,
        )
        .is_err());
    }

    #[test]
    fn substituted_statement_and_nullifier_marker_reject() {
        let fixture = standard_fixture(PoolV1TransitionKind::Withdrawal, 0);
        let mut statement = fixture.statement_payload;
        statement[200] ^= 1;
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            None,
            &statement,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &fixture.marker_plan,
        )
        .is_err());

        let mut wrong_marker = fixture.marker_plan.marker();
        wrong_marker.nullifier = digest(99_000);
        let wrong_marker_address = pool_v1_nullifier_marker_address(
            &fixture.program_id,
            &fixture.pool,
            &encode_digest_canonical(&wrong_marker.nullifier),
        )
        .unwrap()
        .0;
        let mut marker_lamports = 1;
        let mut marker_data =
            [0u8; aspis_statement::pool_v1::POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let marker_account = account(
            &wrong_marker_address,
            &fixture.program_id,
            &mut marker_lamports,
            &mut marker_data,
            false,
            true,
        );
        let marker = plan_nullifier_marker_consumption_v1(
            &fixture.program_id,
            &marker_account,
            wrong_marker,
        )
        .unwrap();
        assert!(apply_with(
            &fixture,
            &fixture.plan_image,
            &fixture.source_pool,
            &fixture.source_current_page,
            None,
            &fixture.statement_payload,
            fixture.statement_digest,
            &fixture.authorization_receipt_image,
            &fixture.authority,
            150,
            &marker,
        )
        .is_err());
    }
}
