//! Production-inactive terminal contract for the eight-lane pair forest.
//!
//! The byte formats and account-binding checks in this module are versioned
//! independently of the legacy single-tree Pool terminal. No verifier tag,
//! proof profile, dispatch entry, account mutation, or CPI path consumes them.

use aspis_core::field::{M31, P};

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest};

use super::{
    decode_pool_v1_pair_late_public_statement_v1, decode_pool_v1_pair_verified_afterstate_v1,
    decode_pool_v1_private_transfer_public_v1, decode_pool_v1_withdrawal_public_v1,
    encode_pool_v1_pair_late_public_statement_v1, encode_pool_v1_pair_verified_afterstate_v1,
    encode_pool_v1_private_transfer_public_v1, encode_pool_v1_withdrawal_public_v1,
    pool_v1_pair_forest_output_lane_v1, PoolV1PairForestAccountErrorV1,
    PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
    PoolV1PairLatePublicStatementErrorV1, PoolV1PairLatePublicStatementV1,
    PoolV1PairVerifiedAfterstateV1, PoolV1PairVerifierTransportErrorV1,
    PoolV1PaymentStatementFormatError, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
    PoolV1WithdrawalPublicV1, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
    POOL_V1_PAIR_FOREST_LANE_COUNT, POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES,
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_PAYMENT_STATEMENT_BYTES,
};

pub const POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC: [u8; 4] = *b"ASF8";
pub const POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC: [u8; 4] = *b"ASR8";
pub const POOL_V1_PAIR_FOREST_TERMINAL_VERSION: u8 = 1;
pub const POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES: usize =
    144 + POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES + POOL_V1_PAYMENT_STATEMENT_BYTES;
pub const POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES: usize =
    8 + 3 * 32 + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
/// Compact transaction/CPI request.  The full 1,880-byte ASF8 statement is
/// reconstructed by the verifier from this payment public input and the four
/// canonical read-only accounts `[proof, master, checkpoint, lane]`.
pub const POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC: [u8; 4] = *b"ASQ8";
pub const POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES: usize =
    8 + 3 * 32 + POOL_V1_PAYMENT_STATEMENT_BYTES;

const MASTER_OFFSET: usize = 8;
const CHECKPOINT_ACCOUNT_OFFSET: usize = 40;
const SELECTED_LANE_ACCOUNT_OFFSET: usize = 72;
const CHECKPOINT_SEQUENCE_OFFSET: usize = 104;
const HISTORICAL_ANCHOR_OFFSET: usize = 112;
const LATE_STATEMENT_OFFSET: usize = 144;
const PAYMENT_STATEMENT_OFFSET: usize =
    LATE_STATEMENT_OFFSET + POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES;

const RESULT_MASTER_OFFSET: usize = 8;
const RESULT_SELECTED_LANE_OFFSET: usize = 40;
const RESULT_NULLIFIER_OFFSET: usize = 72;
const RESULT_AFTERSTATE_OFFSET: usize = 104;

const REQUEST_PROFILE_OFFSET: usize = 8;
const REQUEST_RELEASE_OFFSET: usize = 40;
const REQUEST_POOL_PROGRAM_OFFSET: usize = 72;
const REQUEST_PAYMENT_OFFSET: usize = 104;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalRequestV1 {
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
    pub pool_program: [u8; 32],
    pub public: PoolV1PairForestTerminalPaymentV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestTerminalPaymentV1 {
    PrivateTransfer(PoolV1PrivateTransferPublicV1),
    Withdrawal(PoolV1WithdrawalPublicV1),
}

impl PoolV1PairForestTerminalPaymentV1 {
    pub fn transition_kind(&self) -> PoolV1TransitionKind {
        match self {
            Self::PrivateTransfer(_) => PoolV1TransitionKind::PrivateTransfer,
            Self::Withdrawal(_) => PoolV1TransitionKind::Withdrawal,
        }
    }

    pub fn nullifier(&self) -> &Digest {
        match self {
            Self::PrivateTransfer(public) => &public.nullifier,
            Self::Withdrawal(public) => &public.nullifier,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalCommonV1 {
    pub master_account: [u8; 32],
    pub checkpoint_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub output_lane: u8,
    pub checkpoint_sequence: u64,
    /// Historical global membership anchor reconstructed at trace block 56.
    pub historical_global_anchor: Digest,
    /// Exact selected-output-lane beforestate and candidate afterstate.
    pub lane_transition: PoolV1PairLatePublicStatementV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestTerminalStatementV1 {
    PrivateTransfer {
        common: PoolV1PairForestTerminalCommonV1,
        public: PoolV1PrivateTransferPublicV1,
    },
    Withdrawal {
        common: PoolV1PairForestTerminalCommonV1,
        public: PoolV1WithdrawalPublicV1,
    },
}

impl PoolV1PairForestTerminalStatementV1 {
    #[inline]
    pub fn common(&self) -> &PoolV1PairForestTerminalCommonV1 {
        match self {
            Self::PrivateTransfer { common, .. } | Self::Withdrawal { common, .. } => common,
        }
    }

    #[inline]
    pub fn transition_kind(&self) -> PoolV1TransitionKind {
        match self {
            Self::PrivateTransfer { .. } => PoolV1TransitionKind::PrivateTransfer,
            Self::Withdrawal { .. } => PoolV1TransitionKind::Withdrawal,
        }
    }

    #[inline]
    pub fn nullifier(&self) -> &Digest {
        match self {
            Self::PrivateTransfer { public, .. } => &public.nullifier,
            Self::Withdrawal { public, .. } => &public.nullifier,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalAccountsV1 {
    pub master_account: [u8; 32],
    pub checkpoint_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub master: PoolV1PairForestMasterV1,
    pub checkpoint: PoolV1PairForestCheckpointV1,
    pub selected_lane: PoolV1PairForestLaneStateV1,
    /// Runtime withdrawal destination account. Canonically zero for transfers.
    pub withdrawal_destination_token_account: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalResultV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub master_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub output_lane: u8,
    pub nullifier: Digest,
    pub verified_afterstate: PoolV1PairVerifiedAfterstateV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestTerminalFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongDigestEncoding,
    InvalidTransitionKind,
    InvalidOutputLane,
    NonZeroBinding,
    NonCanonicalDigest,
    OutputLaneMismatch,
    MasterBindingMismatch,
    DeploymentBindingMismatch,
    HistoricalAnchorMismatch,
    CheckpointBindingMismatch,
    SelectedLaneBindingMismatch,
    LiveSnapshotMismatch,
    CandidateAfterstateMismatch,
    ResultBindingMismatch,
    WithdrawalDestinationMismatch,
    Payment(PoolV1PaymentStatementFormatError),
    LaneTransition(PoolV1PairLatePublicStatementErrorV1),
    Afterstate(PoolV1PairVerifierTransportErrorV1),
    Account(PoolV1PairForestAccountErrorV1),
}

fn transition_kind(
    byte: u8,
) -> Result<PoolV1TransitionKind, PoolV1PairForestTerminalFormatErrorV1> {
    match byte {
        value if value == PoolV1TransitionKind::PrivateTransfer as u8 => {
            Ok(PoolV1TransitionKind::PrivateTransfer)
        }
        value if value == PoolV1TransitionKind::Withdrawal as u8 => {
            Ok(PoolV1TransitionKind::Withdrawal)
        }
        _ => Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind),
    }
}

fn statement_public_common(
    statement: &PoolV1PairForestTerminalStatementV1,
) -> ([u8; 32], [u8; 32], u64, Digest, Digest, M31) {
    match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            public.anchor_root,
            public.nullifier,
            public.asset_id,
        ),
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            public.anchor_root,
            public.nullifier,
            public.asset_id,
        ),
    }
}

pub fn validate_pool_v1_pair_forest_terminal_statement_v1(
    statement: &PoolV1PairForestTerminalStatementV1,
) -> Result<(), PoolV1PairForestTerminalFormatErrorV1> {
    let common = statement.common();
    if common.master_account == [0u8; 32]
        || common.checkpoint_account == [0u8; 32]
        || common.selected_lane_account == [0u8; 32]
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    if usize::from(common.output_lane) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(PoolV1PairForestTerminalFormatErrorV1::InvalidOutputLane);
    }
    match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            encode_pool_v1_private_transfer_public_v1(public)
                .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?;
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            encode_pool_v1_withdrawal_public_v1(public)
                .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?;
        }
    }
    let (pool, deployment, anchor_sequence, anchor, nullifier, _) =
        statement_public_common(statement);
    if pool != common.master_account {
        return Err(PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch);
    }
    if deployment != common.lane_transition.live_snapshot.deployment_domain {
        return Err(PoolV1PairForestTerminalFormatErrorV1::DeploymentBindingMismatch);
    }
    if common.lane_transition.live_snapshot.pool != common.master_account {
        return Err(PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch);
    }
    if anchor_sequence != common.checkpoint_sequence {
        return Err(PoolV1PairForestTerminalFormatErrorV1::CheckpointBindingMismatch);
    }
    if anchor != common.historical_global_anchor {
        return Err(PoolV1PairForestTerminalFormatErrorV1::HistoricalAnchorMismatch);
    }
    let expected_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(PoolV1PairForestTerminalFormatErrorV1::Account)?;
    if expected_lane != common.output_lane {
        return Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch);
    }
    let mut late_bytes = [0u8; POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES];
    encode_pool_v1_pair_late_public_statement_v1(&common.lane_transition, &mut late_bytes)
        .map_err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition)?;
    Ok(())
}

pub fn encode_pool_v1_pair_forest_terminal_statement_v1(
    statement: &PoolV1PairForestTerminalStatementV1,
) -> Result<[u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES], PoolV1PairForestTerminalFormatErrorV1>
{
    validate_pool_v1_pair_forest_terminal_statement_v1(statement)?;
    let common = statement.common();
    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    output[5] = statement.transition_kind() as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = common.output_lane;
    output[MASTER_OFFSET..CHECKPOINT_ACCOUNT_OFFSET].copy_from_slice(&common.master_account);
    output[CHECKPOINT_ACCOUNT_OFFSET..SELECTED_LANE_ACCOUNT_OFFSET]
        .copy_from_slice(&common.checkpoint_account);
    output[SELECTED_LANE_ACCOUNT_OFFSET..CHECKPOINT_SEQUENCE_OFFSET]
        .copy_from_slice(&common.selected_lane_account);
    output[CHECKPOINT_SEQUENCE_OFFSET..HISTORICAL_ANCHOR_OFFSET]
        .copy_from_slice(&common.checkpoint_sequence.to_le_bytes());
    output[HISTORICAL_ANCHOR_OFFSET..LATE_STATEMENT_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.historical_global_anchor));
    encode_pool_v1_pair_late_public_statement_v1(
        &common.lane_transition,
        &mut output[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET],
    )
    .map_err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition)?;
    let payment = match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            encode_pool_v1_private_transfer_public_v1(public)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            encode_pool_v1_withdrawal_public_v1(public)
        }
    }
    .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?;
    output[PAYMENT_STATEMENT_OFFSET..].copy_from_slice(&payment);
    Ok(output)
}

pub fn decode_pool_v1_pair_forest_terminal_statement_v1(
    bytes: &[u8],
) -> Result<PoolV1PairForestTerminalStatementV1, PoolV1PairForestTerminalFormatErrorV1> {
    if bytes.len() != POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_TERMINAL_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion);
    }
    let kind = transition_kind(bytes[5])?;
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding);
    }
    let historical_global_anchor = decode_digest_canonical(
        bytes[HISTORICAL_ANCHOR_OFFSET..LATE_STATEMENT_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
    )
    .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::NonCanonicalDigest)?;
    let common = PoolV1PairForestTerminalCommonV1 {
        master_account: bytes[MASTER_OFFSET..CHECKPOINT_ACCOUNT_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        checkpoint_account: bytes[CHECKPOINT_ACCOUNT_OFFSET..SELECTED_LANE_ACCOUNT_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        selected_lane_account: bytes[SELECTED_LANE_ACCOUNT_OFFSET..CHECKPOINT_SEQUENCE_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        output_lane: bytes[7],
        checkpoint_sequence: u64::from_le_bytes(
            bytes[CHECKPOINT_SEQUENCE_OFFSET..HISTORICAL_ANCHOR_OFFSET]
                .try_into()
                .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        ),
        historical_global_anchor,
        lane_transition: decode_pool_v1_pair_late_public_statement_v1(
            &bytes[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET],
        )
        .map_err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition)?,
    };
    let statement = match kind {
        PoolV1TransitionKind::PrivateTransfer => {
            PoolV1PairForestTerminalStatementV1::PrivateTransfer {
                common,
                public: decode_pool_v1_private_transfer_public_v1(
                    &bytes[PAYMENT_STATEMENT_OFFSET..],
                )
                .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?,
            }
        }
        PoolV1TransitionKind::Withdrawal => PoolV1PairForestTerminalStatementV1::Withdrawal {
            common,
            public: decode_pool_v1_withdrawal_public_v1(&bytes[PAYMENT_STATEMENT_OFFSET..])
                .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?,
        },
    };
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)?;
    Ok(statement)
}

pub fn encode_pool_v1_pair_forest_terminal_request_v1(
    request: &PoolV1PairForestTerminalRequestV1,
) -> Result<[u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES], PoolV1PairForestTerminalFormatErrorV1>
{
    if request.verifier_profile == [0u8; 32]
        || request.verifier_release == [0u8; 32]
        || request.pool_program == [0u8; 32]
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    let payment = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            encode_pool_v1_private_transfer_public_v1(&public)
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            encode_pool_v1_withdrawal_public_v1(&public)
        }
    }
    .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?;
    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    output[5] = request.public.transition_kind() as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[REQUEST_PROFILE_OFFSET..REQUEST_RELEASE_OFFSET]
        .copy_from_slice(&request.verifier_profile);
    output[REQUEST_RELEASE_OFFSET..REQUEST_POOL_PROGRAM_OFFSET]
        .copy_from_slice(&request.verifier_release);
    output[REQUEST_POOL_PROGRAM_OFFSET..REQUEST_PAYMENT_OFFSET]
        .copy_from_slice(&request.pool_program);
    output[REQUEST_PAYMENT_OFFSET..].copy_from_slice(&payment);
    Ok(output)
}

pub fn decode_pool_v1_pair_forest_terminal_request_v1(
    bytes: &[u8],
) -> Result<PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalFormatErrorV1> {
    if bytes.len() != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_TERMINAL_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion);
    }
    let kind = transition_kind(bytes[5])?;
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    let public = match kind {
        PoolV1TransitionKind::PrivateTransfer => {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(
                decode_pool_v1_private_transfer_public_v1(&bytes[REQUEST_PAYMENT_OFFSET..])
                    .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?,
            )
        }
        PoolV1TransitionKind::Withdrawal => PoolV1PairForestTerminalPaymentV1::Withdrawal(
            decode_pool_v1_withdrawal_public_v1(&bytes[REQUEST_PAYMENT_OFFSET..])
                .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?,
        ),
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: bytes[REQUEST_PROFILE_OFFSET..REQUEST_RELEASE_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        verifier_release: bytes[REQUEST_RELEASE_OFFSET..REQUEST_POOL_PROGRAM_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        pool_program: bytes[REQUEST_POOL_PROGRAM_OFFSET..REQUEST_PAYMENT_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        public,
    };
    if request.verifier_profile == [0u8; 32]
        || request.verifier_release == [0u8; 32]
        || request.pool_program == [0u8; 32]
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    Ok(request)
}

/// Construct the exact semantic ASF8 object independently on both sides of
/// the CPI boundary.  Equality of its canonical encoding is the binding that
/// prevents the compact request from weakening any full-statement field.
pub fn reconstruct_pool_v1_pair_forest_terminal_statement_v1(
    request: &PoolV1PairForestTerminalRequestV1,
    common: PoolV1PairForestTerminalCommonV1,
) -> Result<PoolV1PairForestTerminalStatementV1, PoolV1PairForestTerminalFormatErrorV1> {
    let statement = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public }
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            PoolV1PairForestTerminalStatementV1::Withdrawal { common, public }
        }
    };
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)?;
    Ok(statement)
}

fn validate_result(
    result: &PoolV1PairForestTerminalResultV1,
) -> Result<(), PoolV1PairForestTerminalFormatErrorV1> {
    if result.master_account == [0u8; 32] || result.selected_lane_account == [0u8; 32] {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    let expected = pool_v1_pair_forest_output_lane_v1(&result.nullifier)
        .map_err(PoolV1PairForestTerminalFormatErrorV1::Account)?;
    if result.output_lane != expected {
        return Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch);
    }
    encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)
        .map_err(PoolV1PairForestTerminalFormatErrorV1::Afterstate)?;
    Ok(())
}

/// Fail-closed binding check for the bytes returned to the Pool caller.
///
/// Standalone result decoding can establish canonical encoding, but account
/// identifiers are authenticated only relative to the accepted statement.
pub fn validate_pool_v1_pair_forest_terminal_result_against_statement_v1(
    statement: &PoolV1PairForestTerminalStatementV1,
    result: &PoolV1PairForestTerminalResultV1,
) -> Result<(), PoolV1PairForestTerminalFormatErrorV1> {
    validate_pool_v1_pair_forest_terminal_statement_v1(statement)?;
    validate_result(result)?;
    let common = statement.common();
    if result.transition_kind != statement.transition_kind()
        || result.master_account != common.master_account
        || result.selected_lane_account != common.selected_lane_account
        || result.output_lane != common.output_lane
        || result.nullifier != *statement.nullifier()
        || result.verified_afterstate != common.lane_transition.candidate_afterstate
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch);
    }
    Ok(())
}

pub fn encode_pool_v1_pair_forest_terminal_result_v1(
    result: &PoolV1PairForestTerminalResultV1,
) -> Result<[u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES], PoolV1PairForestTerminalFormatErrorV1>
{
    validate_result(result)?;
    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    output[5] = result.transition_kind as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = result.output_lane;
    output[RESULT_MASTER_OFFSET..RESULT_SELECTED_LANE_OFFSET]
        .copy_from_slice(&result.master_account);
    output[RESULT_SELECTED_LANE_OFFSET..RESULT_NULLIFIER_OFFSET]
        .copy_from_slice(&result.selected_lane_account);
    output[RESULT_NULLIFIER_OFFSET..RESULT_AFTERSTATE_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&result.nullifier));
    output[RESULT_AFTERSTATE_OFFSET..].copy_from_slice(
        &encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)
            .map_err(PoolV1PairForestTerminalFormatErrorV1::Afterstate)?,
    );
    Ok(output)
}

pub fn decode_pool_v1_pair_forest_terminal_result_v1(
    bytes: &[u8],
) -> Result<PoolV1PairForestTerminalResultV1, PoolV1PairForestTerminalFormatErrorV1> {
    if bytes.len() != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_TERMINAL_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion);
    }
    let transition_kind = transition_kind(bytes[5])?;
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding);
    }
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind,
        master_account: bytes[RESULT_MASTER_OFFSET..RESULT_SELECTED_LANE_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        selected_lane_account: bytes[RESULT_SELECTED_LANE_OFFSET..RESULT_NULLIFIER_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        output_lane: bytes[7],
        nullifier: decode_digest_canonical(
            bytes[RESULT_NULLIFIER_OFFSET..RESULT_AFTERSTATE_OFFSET]
                .try_into()
                .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        )
        .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::NonCanonicalDigest)?,
        verified_afterstate: decode_pool_v1_pair_verified_afterstate_v1(
            &bytes[RESULT_AFTERSTATE_OFFSET..],
        )
        .map_err(PoolV1PairForestTerminalFormatErrorV1::Afterstate)?,
    };
    validate_result(&result)?;
    Ok(result)
}

#[cfg(not(target_os = "solana"))]
mod host {
    use super::*;
    use crate::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1,
        pair_forest_constraint_residuals::{
            evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1,
            evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1,
            POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT,
            POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT,
        },
        pair_forest_trace::PoolV1PairForestMergedC1CompilationV1,
        pair_trace::PoolV1PairTraceVariantV1,
        pool_v1_empty_roots, pool_v1_tree_parent, POOL_V1_PAIR_TREE_DEPTH,
    };

    fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
        let ordinary = pool_v1_empty_roots();
        core::array::from_fn(|level| {
            if level < POOL_V1_PAIR_TREE_DEPTH {
                ordinary[level + 1]
            } else {
                pool_v1_tree_parent(
                    &ordinary[POOL_V1_PAIR_TREE_DEPTH],
                    &ordinary[POOL_V1_PAIR_TREE_DEPTH],
                )
            }
        })
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum PoolV1PairForestTerminalHostErrorV1 {
        Format(PoolV1PairForestTerminalFormatErrorV1),
        Residual,
        WrongResidualCount { expected: usize, actual: usize },
        WrongTraceVariant,
    }

    impl From<PoolV1PairForestTerminalFormatErrorV1> for PoolV1PairForestTerminalHostErrorV1 {
        fn from(error: PoolV1PairForestTerminalFormatErrorV1) -> Self {
            Self::Format(error)
        }
    }

    fn validate_accounts(
        statement: &PoolV1PairForestTerminalStatementV1,
        accounts: &PoolV1PairForestTerminalAccountsV1,
    ) -> Result<(), PoolV1PairForestTerminalHostErrorV1> {
        validate_pool_v1_pair_forest_terminal_statement_v1(statement)?;
        encode_pool_v1_pair_forest_master_v1(&accounts.master)
            .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Account(error))?;
        encode_pool_v1_pair_forest_checkpoint_v1(&accounts.checkpoint)
            .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Account(error))?;
        encode_pool_v1_pair_forest_lane_state_v1(&accounts.selected_lane, &pair_empty_roots())
            .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Account(error))?;
        let common = statement.common();
        let (_, deployment, _, _, _, asset_id) = statement_public_common(statement);
        if accounts.master_account != common.master_account
            || accounts.master.identity.pool != common.master_account
        {
            return Err(PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch.into());
        }
        if accounts.master.identity.deployment_domain != deployment
            || accounts.checkpoint.deployment_domain != deployment
        {
            return Err(PoolV1PairForestTerminalFormatErrorV1::DeploymentBindingMismatch.into());
        }
        if accounts.master.identity.asset_id != asset_id {
            return Err(PoolV1PairForestTerminalFormatErrorV1::Payment(
                PoolV1PaymentStatementFormatError::EnvelopeMismatch,
            )
            .into());
        }
        if accounts.checkpoint_account != common.checkpoint_account
            || accounts.checkpoint.master != common.master_account
            || accounts.checkpoint.checkpoint_sequence != common.checkpoint_sequence
            || accounts.checkpoint.global_root != common.historical_global_anchor
        {
            return Err(PoolV1PairForestTerminalFormatErrorV1::CheckpointBindingMismatch.into());
        }
        if accounts.selected_lane_account != common.selected_lane_account
            || accounts.selected_lane.master != common.master_account
            || accounts.selected_lane.lane_id != common.output_lane
            || accounts.master.initialized_lane_mask & (1u8 << common.output_lane) == 0
        {
            return Err(PoolV1PairForestTerminalFormatErrorV1::SelectedLaneBindingMismatch.into());
        }
        let expected_destination = match statement {
            PoolV1PairForestTerminalStatementV1::PrivateTransfer { .. } => [0u8; 32],
            PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
                public.destination_token_account
            }
        };
        if accounts.withdrawal_destination_token_account != expected_destination {
            return Err(
                PoolV1PairForestTerminalFormatErrorV1::WithdrawalDestinationMismatch.into(),
            );
        }
        let source = common.lane_transition.live_snapshot;
        if source.sequence != accounts.selected_lane.tree.next_leaf_index
            || source.next_pair_index != accounts.selected_lane.tree.next_leaf_index
            || source.current_root != accounts.selected_lane.tree.root
            || source.frontier != accounts.selected_lane.tree.frontier
        {
            return Err(PoolV1PairForestTerminalFormatErrorV1::LiveSnapshotMismatch.into());
        }
        Ok(())
    }

    pub fn verify_pool_v1_pair_forest_terminal_inactive_v1(
        statement: &PoolV1PairForestTerminalStatementV1,
        accounts: &PoolV1PairForestTerminalAccountsV1,
        compilation: &PoolV1PairForestMergedC1CompilationV1,
    ) -> Result<PoolV1PairForestTerminalResultV1, PoolV1PairForestTerminalHostErrorV1> {
        validate_accounts(statement, accounts)?;
        let common = statement.common();
        if compilation.public_statement != common.lane_transition
            || compilation.trace.afterstate != common.lane_transition.candidate_afterstate
        {
            return Err(PoolV1PairForestTerminalFormatErrorV1::CandidateAfterstateMismatch.into());
        }
        let (expected_count, residuals) = match statement {
            PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
                if compilation.trace.variant != PoolV1PairTraceVariantV1::PrivateTransfer {
                    return Err(PoolV1PairForestTerminalHostErrorV1::WrongTraceVariant);
                }
                (
                    POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT,
                    evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1(
                        public,
                        &compilation.public_statement,
                        &compilation.semantic_c1,
                    )
                    .map_err(|_| PoolV1PairForestTerminalHostErrorV1::Residual)?,
                )
            }
            PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
                if compilation.trace.variant != PoolV1PairTraceVariantV1::Withdrawal {
                    return Err(PoolV1PairForestTerminalHostErrorV1::WrongTraceVariant);
                }
                (
                    POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT,
                    evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1(
                        public,
                        &compilation.public_statement,
                        &compilation.semantic_c1,
                    )
                    .map_err(|_| PoolV1PairForestTerminalHostErrorV1::Residual)?,
                )
            }
        };
        let actual = residuals.residual_count();
        if actual != expected_count {
            return Err(PoolV1PairForestTerminalHostErrorV1::WrongResidualCount {
                expected: expected_count,
                actual,
            });
        }
        if !residuals.all_zero() {
            return Err(PoolV1PairForestTerminalHostErrorV1::Residual);
        }
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: statement.transition_kind(),
            master_account: common.master_account,
            selected_lane_account: common.selected_lane_account,
            output_lane: common.output_lane,
            nullifier: *statement.nullifier(),
            verified_afterstate: common.lane_transition.candidate_afterstate,
        };
        validate_pool_v1_pair_forest_terminal_result_against_statement_v1(statement, &result)?;
        Ok(result)
    }

    const _: () = assert!(POOL_V1_PAIR_FOREST_ALL_LANES_MASK == 0xff);
}

#[cfg(not(target_os = "solana"))]
pub use host::{
    verify_pool_v1_pair_forest_terminal_inactive_v1, PoolV1PairForestTerminalHostErrorV1,
};

const _: () = assert!(POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES == 1_880);
const _: () = assert!(POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES == 792);
const _: () = assert!(POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES == 320);
const _: () = assert!(P > 8);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        derive_owner_key,
        pool_v1::{
            pair_forest_trace::{
                compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
                compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
                PoolV1PairForestInputNoteWitnessV1, PoolV1PairForestPrivateTransferWitnessV1,
                PoolV1PairForestWithdrawalWitnessV1,
            },
            pair_trace::PoolV1PairInputNoteWitnessV1,
            pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent,
            IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1MembershipWitnessV1,
            PoolV1OutputNoteWitnessV1, PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1,
            PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1, VerifierPolicyV1,
            POOL_V1_PAIR_TREE_DEPTH,
        },
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
    }

    fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
        let zero = [M31::ZERO; 8];
        let mut roots = [zero; POOL_V1_PAIR_TREE_DEPTH + 1];
        roots[0] = pool_v1_tree_parent(&zero, &zero);
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
        }
        roots
    }

    fn snapshot_at(pool: [u8; 32], deployment: [u8; 32], index: u64) -> PoolV1PairLiveSnapshotV1 {
        let empty = pair_empty_roots();
        let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            empty[POOL_V1_PAIR_TREE_DEPTH],
            core::array::from_fn(|level| empty[level]),
            &empty,
        )
        .unwrap();
        for leaf in 0..index {
            tree = tree
                .append_one_with_empty_roots(digest(20_000 + 32 * leaf as u32), &empty)
                .unwrap()
                .0;
        }
        PoolV1PairLiveSnapshotV1 {
            pool,
            deployment_domain: deployment,
            sequence: index,
            next_pair_index: index,
            current_root: tree.root,
            frontier: tree.frontier,
        }
    }

    fn input_witness(value: u32) -> PoolV1PairForestInputNoteWitnessV1 {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset_id = M31(77);
        let commitment =
            pool_v1_note_commitment(&derive_owner_key(&nullifier_key), value, asset_id, &salt);
        PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt,
                value,
                pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(commitment, digest(900)).unwrap(),
                selected_second: false,
                membership: PoolV1MembershipWitnessV1 {
                    siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                    index: 0x5_4321,
                },
            },
            // Private input-lane path. It is never derived from output_lane.
            super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
            super_root_directions: [true, false, true],
        }
    }

    fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
        let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            let sibling = input.pair.membership.siblings[level];
            current = if ((input.pair.membership.index >> level) & 1) == 0 {
                pool_v1_tree_parent(&current, &sibling)
            } else {
                pool_v1_tree_parent(&sibling, &current)
            };
        }
        for level in 0..3 {
            current = if input.super_root_directions[level] {
                pool_v1_tree_parent(&input.super_root_siblings[level], &current)
            } else {
                pool_v1_tree_parent(&current, &input.super_root_siblings[level])
            };
        }
        current
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn context(anchor: Digest) -> PoolV1PaymentRelationContextV1<'static> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: [1; 32],
                deployment_domain: [2; 32],
                anchor_sequence: 42,
                anchor_root: anchor,
                asset_id: M31(77),
            },
            spent_nullifiers: &[],
        }
    }

    fn accounts(
        common: PoolV1PairForestTerminalCommonV1,
        withdrawal_destination_token_account: [u8; 32],
    ) -> PoolV1PairForestTerminalAccountsV1 {
        let source = common.lane_transition.live_snapshot;
        let mut checkpoint_sequences = [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT];
        checkpoint_sequences[usize::from(common.output_lane)] = source.sequence;
        PoolV1PairForestTerminalAccountsV1 {
            master_account: common.master_account,
            checkpoint_account: common.checkpoint_account,
            selected_lane_account: common.selected_lane_account,
            master: PoolV1PairForestMasterV1 {
                identity: PoolIdentityV1 {
                    pool: common.master_account,
                    asset_mint: [5; 32],
                    token_program: [6; 32],
                    asset_id: M31(77),
                    deployment_domain: source.deployment_domain,
                },
                verifier_policy: VerifierPolicyV1 {
                    flags: 1,
                    registry_program: [7; 32],
                    registry_authority: [0; 32],
                    policy_binding: [8; 32],
                },
                initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
                has_checkpoint: true,
                next_checkpoint_sequence: common.checkpoint_sequence + 1,
                last_checkpoint_lane_sequences: checkpoint_sequences,
            },
            checkpoint: PoolV1PairForestCheckpointV1 {
                master: common.master_account,
                deployment_domain: source.deployment_domain,
                checkpoint_sequence: common.checkpoint_sequence,
                global_root: common.historical_global_anchor,
                lane_sequences: checkpoint_sequences,
            },
            selected_lane: PoolV1PairForestLaneStateV1 {
                master: common.master_account,
                lane_id: common.output_lane,
                tree: IncrementalMerkleTreeV1 {
                    next_leaf_index: source.next_pair_index,
                    root: source.current_root,
                    frontier: source.frontier,
                },
            },
            withdrawal_destination_token_account,
        }
    }

    #[derive(Clone)]
    struct Fixture {
        statement: PoolV1PairForestTerminalStatementV1,
        accounts: PoolV1PairForestTerminalAccountsV1,
        compilation: super::super::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1,
    }

    fn transfer_fixture() -> Fixture {
        let input = input_witness(1_000);
        let recipient = output(300, 600);
        let change = output(500, 400);
        let anchor = global_anchor(&input);
        let witness = PoolV1PairForestPrivateTransferWitnessV1 {
            input,
            recipient,
            change,
        };
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt),
            asset_id: M31(77),
            recipient_commitment: pool_v1_note_commitment(
                &recipient.owner_key,
                recipient.value,
                M31(77),
                &recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &change.owner_key,
                change.value,
                M31(77),
                &change.salt,
            ),
        };
        let compilation = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
            &public,
            &witness,
            context(anchor),
            snapshot_at(public.pool, public.deployment_domain, 13),
        )
        .unwrap();
        let common = PoolV1PairForestTerminalCommonV1 {
            master_account: public.pool,
            checkpoint_account: [3; 32],
            selected_lane_account: [4; 32],
            output_lane: pool_v1_pair_forest_output_lane_v1(&public.nullifier).unwrap(),
            checkpoint_sequence: public.anchor_sequence,
            historical_global_anchor: public.anchor_root,
            lane_transition: compilation.public_statement,
        };
        Fixture {
            statement: PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public },
            accounts: accounts(common, [0; 32]),
            compilation,
        }
    }

    fn withdrawal_fixture() -> Fixture {
        let input = input_witness(1_000);
        let change = output(700, 750);
        let anchor = global_anchor(&input);
        let witness = PoolV1PairForestWithdrawalWitnessV1 { input, change };
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt),
            asset_id: M31(77),
            amount: 250,
            destination_token_account: [9; 32],
            change_commitment: pool_v1_note_commitment(
                &change.owner_key,
                change.value,
                M31(77),
                &change.salt,
            ),
        };
        let compilation = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
            &public,
            &witness,
            context(anchor),
            snapshot_at(public.pool, public.deployment_domain, 13),
        )
        .unwrap();
        let common = PoolV1PairForestTerminalCommonV1 {
            master_account: public.pool,
            checkpoint_account: [3; 32],
            selected_lane_account: [4; 32],
            output_lane: pool_v1_pair_forest_output_lane_v1(&public.nullifier).unwrap(),
            checkpoint_sequence: public.anchor_sequence,
            historical_global_anchor: public.anchor_root,
            lane_transition: compilation.public_statement,
        };
        Fixture {
            statement: PoolV1PairForestTerminalStatementV1::Withdrawal { common, public },
            accounts: accounts(common, public.destination_token_account),
            compilation,
        }
    }

    fn verify(
        fixture: &Fixture,
    ) -> Result<PoolV1PairForestTerminalResultV1, PoolV1PairForestTerminalHostErrorV1> {
        verify_pool_v1_pair_forest_terminal_inactive_v1(
            &fixture.statement,
            &fixture.accounts,
            &fixture.compilation,
        )
    }

    fn common_mut(
        statement: &mut PoolV1PairForestTerminalStatementV1,
    ) -> &mut PoolV1PairForestTerminalCommonV1 {
        match statement {
            PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, .. }
            | PoolV1PairForestTerminalStatementV1::Withdrawal { common, .. } => common,
        }
    }

    #[test]
    fn honest_transfer_and_withdrawal_round_trip_to_inactive_pool_results() {
        for fixture in [transfer_fixture(), withdrawal_fixture()] {
            let statement_bytes =
                encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap();
            assert_eq!(statement_bytes.len(), 1_880);
            assert_eq!(
                decode_pool_v1_pair_forest_terminal_statement_v1(&statement_bytes),
                Ok(fixture.statement)
            );
            let result = verify(&fixture).unwrap();
            assert_eq!(
                validate_pool_v1_pair_forest_terminal_result_against_statement_v1(
                    &fixture.statement,
                    &result,
                ),
                Ok(())
            );
            assert_eq!(
                result.verified_afterstate,
                fixture
                    .statement
                    .common()
                    .lane_transition
                    .candidate_afterstate
            );
            let result_bytes = encode_pool_v1_pair_forest_terminal_result_v1(&result).unwrap();
            assert_eq!(result_bytes.len(), 792);
            assert_eq!(
                decode_pool_v1_pair_forest_terminal_result_v1(&result_bytes),
                Ok(result)
            );
        }
    }

    #[test]
    fn compact_request_round_trip_reconstructs_byte_identical_asf8_and_rejects_mutations() {
        for fixture in [transfer_fixture(), withdrawal_fixture()] {
            let public = match fixture.statement {
                PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
                    PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)
                }
                PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
                    PoolV1PairForestTerminalPaymentV1::Withdrawal(public)
                }
            };
            let request = PoolV1PairForestTerminalRequestV1 {
                verifier_profile: [11; 32],
                verifier_release: [12; 32],
                pool_program: [13; 32],
                public,
            };
            let encoded = encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap();
            assert_eq!(encoded.len(), 320);
            assert_eq!(
                decode_pool_v1_pair_forest_terminal_request_v1(&encoded),
                Ok(request)
            );
            let verifier_reconstruction = reconstruct_pool_v1_pair_forest_terminal_statement_v1(
                &request,
                *fixture.statement.common(),
            )
            .unwrap();
            let pool_reconstruction = reconstruct_pool_v1_pair_forest_terminal_statement_v1(
                &decode_pool_v1_pair_forest_terminal_request_v1(&encoded).unwrap(),
                *fixture.statement.common(),
            )
            .unwrap();
            assert_eq!(
                encode_pool_v1_pair_forest_terminal_statement_v1(&verifier_reconstruction),
                encode_pool_v1_pair_forest_terminal_statement_v1(&pool_reconstruction)
            );
            assert_eq!(pool_reconstruction, fixture.statement);

            for index in [0usize, 4, 5, 6, 7] {
                let mut changed = encoded;
                changed[index] ^= 0x80;
                assert!(decode_pool_v1_pair_forest_terminal_request_v1(&changed).is_err());
            }
            for index in [8usize, 40, 72, 104, 319] {
                let mut changed = encoded;
                changed[index] ^= 1;
                assert_ne!(
                    decode_pool_v1_pair_forest_terminal_request_v1(&changed),
                    Ok(request)
                );
            }
            let mut noncanonical = encoded;
            noncanonical[REQUEST_PAYMENT_OFFSET + 112..REQUEST_PAYMENT_OFFSET + 116].fill(0xff);
            assert!(decode_pool_v1_pair_forest_terminal_request_v1(&noncanonical).is_err());
            let mut trailing = encoded.to_vec();
            trailing.push(0);
            assert!(decode_pool_v1_pair_forest_terminal_request_v1(&trailing).is_err());
        }
    }

    #[test]
    fn every_common_identity_anchor_and_lane_transition_field_fails_closed() {
        let honest = transfer_fixture();

        let mut changed = honest.clone();
        common_mut(&mut changed.statement).master_account[0] ^= 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        common_mut(&mut changed.statement).checkpoint_account[0] ^= 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        common_mut(&mut changed.statement).selected_lane_account[0] ^= 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        common_mut(&mut changed.statement).output_lane ^= 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        common_mut(&mut changed.statement).checkpoint_sequence += 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        let common = common_mut(&mut changed.statement);
        common.historical_global_anchor[0] = common.historical_global_anchor[0].add(M31::ONE);
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        common_mut(&mut changed.statement)
            .lane_transition
            .live_snapshot
            .sequence += 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        common_mut(&mut changed.statement)
            .lane_transition
            .live_snapshot
            .next_pair_index += 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        let common = common_mut(&mut changed.statement);
        common.lane_transition.live_snapshot.current_root[0] =
            common.lane_transition.live_snapshot.current_root[0].add(M31::ONE);
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        let common = common_mut(&mut changed.statement);
        common.lane_transition.live_snapshot.frontier[2][0] =
            common.lane_transition.live_snapshot.frontier[2][0].add(M31::ONE);
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        common_mut(&mut changed.statement)
            .lane_transition
            .candidate_afterstate
            .next_pair_index += 1;
        assert!(verify(&changed).is_err());

        let mut changed = honest.clone();
        let common = common_mut(&mut changed.statement);
        common.lane_transition.candidate_afterstate.next_root[0] =
            common.lane_transition.candidate_afterstate.next_root[0].add(M31::ONE);
        assert!(verify(&changed).is_err());

        let mut changed = honest;
        let common = common_mut(&mut changed.statement);
        common.lane_transition.candidate_afterstate.next_frontier[2][0] =
            common.lane_transition.candidate_afterstate.next_frontier[2][0].add(M31::ONE);
        assert!(verify(&changed).is_err());
    }

    #[test]
    fn every_authenticated_account_and_public_payment_binding_fails_closed() {
        let honest = transfer_fixture();
        let mut mutations: alloc::vec::Vec<Fixture> = alloc::vec::Vec::new();

        let mut changed = honest.clone();
        changed.accounts.master_account[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.checkpoint_account[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.selected_lane_account[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.withdrawal_destination_token_account[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.master.identity.pool[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.master.identity.deployment_domain[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.master.identity.asset_id = M31(78);
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.checkpoint.master[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.checkpoint.deployment_domain[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.checkpoint.checkpoint_sequence += 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.checkpoint.global_root[0] =
            changed.accounts.checkpoint.global_root[0].add(M31::ONE);
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.selected_lane.master[0] ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.selected_lane.lane_id ^= 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.selected_lane.tree.next_leaf_index += 1;
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.selected_lane.tree.root[0] =
            changed.accounts.selected_lane.tree.root[0].add(M31::ONE);
        mutations.push(changed);
        let mut changed = honest.clone();
        changed.accounts.selected_lane.tree.frontier[2][0] =
            changed.accounts.selected_lane.tree.frontier[2][0].add(M31::ONE);
        mutations.push(changed);

        for (index, changed) in mutations.iter().enumerate() {
            assert!(verify(changed).is_err(), "account mutation index={index}");
        }

        for mutate in 0..6 {
            let mut changed = honest.clone();
            let public = match &mut changed.statement {
                PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => public,
                PoolV1PairForestTerminalStatementV1::Withdrawal { .. } => {
                    assert!(false, "transfer fixture changed variant");
                    return;
                }
            };
            match mutate {
                0 => public.pool[0] ^= 1,
                1 => public.deployment_domain[0] ^= 1,
                2 => public.nullifier[0] = public.nullifier[0].add(M31::ONE),
                3 => public.asset_id = M31(78),
                4 => public.recipient_commitment[0] = public.recipient_commitment[0].add(M31::ONE),
                5 => public.change_commitment[0] = public.change_commitment[0].add(M31::ONE),
                _ => {}
            }
            assert!(verify(&changed).is_err(), "transfer public field={mutate}");
        }

        let withdrawal = withdrawal_fixture();
        for mutate in 0..3 {
            let mut changed = withdrawal.clone();
            let public = match &mut changed.statement {
                PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => public,
                PoolV1PairForestTerminalStatementV1::PrivateTransfer { .. } => {
                    assert!(false, "withdrawal fixture changed variant");
                    return;
                }
            };
            match mutate {
                0 => public.amount += 1,
                1 => public.destination_token_account[0] ^= 1,
                2 => public.change_commitment[0] = public.change_commitment[0].add(M31::ONE),
                _ => {}
            }
            assert!(
                verify(&changed).is_err(),
                "withdrawal public field={mutate}"
            );
        }
    }

    #[test]
    fn terminal_headers_and_result_bindings_are_versioned_and_fail_closed() {
        let fixture = transfer_fixture();
        let encoded = encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap();
        for offset in [0usize, 4, 5, 6, 7] {
            let mut changed = encoded;
            changed[offset] ^= 0x80;
            assert!(decode_pool_v1_pair_forest_terminal_statement_v1(&changed).is_err());
        }

        let result = verify(&fixture).unwrap();
        let encoded = encode_pool_v1_pair_forest_terminal_result_v1(&result).unwrap();
        for offset in [0usize, 4, 5, 6, 7, 104] {
            let mut changed = encoded;
            changed[offset] ^= 0x80;
            assert!(decode_pool_v1_pair_forest_terminal_result_v1(&changed).is_err());
        }
        let mut changed = encoded;
        changed[72] ^= 1;
        assert!(decode_pool_v1_pair_forest_terminal_result_v1(&changed).is_err());

        for mutate in 0..6 {
            let mut changed = result;
            match mutate {
                0 => changed.transition_kind = PoolV1TransitionKind::Withdrawal,
                1 => changed.master_account[0] ^= 1,
                2 => changed.selected_lane_account[0] ^= 1,
                3 => changed.output_lane ^= 1,
                4 => changed.nullifier[1] = changed.nullifier[1].add(M31::ONE),
                5 => changed.verified_afterstate.next_pair_index += 1,
                _ => {}
            }
            assert!(
                validate_pool_v1_pair_forest_terminal_result_against_statement_v1(
                    &fixture.statement,
                    &changed,
                )
                .is_err(),
                "result binding field={mutate}"
            );
        }
    }
}
