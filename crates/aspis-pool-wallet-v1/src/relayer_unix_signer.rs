//! Bounded Unix-domain transport for an external relayer signer.
//!
//! The request contains only the exact public Solana message and its already
//! authenticated simulation/startup bindings. The signer response echoes a
//! domain-separated request digest and returns one bounded signed transaction;
//! the execution coordinator subsequently verifies every signature and exact
//! message byte before journaling or submission.

#![cfg(unix)]

use std::{
    fs,
    io::{self, Read, Write},
    os::unix::{
        fs::{FileTypeExt as _, PermissionsExt as _},
        net::UnixStream,
    },
    path::{Path, PathBuf},
    time::Duration,
};

use sha2::{Digest as _, Sha256};
use subtle::ConstantTimeEq as _;

use crate::relayer_execution_port::{ExactRelayerSigningRequestV1, ExternalRelayerSignerV1};

const REQUEST_MAGIC_V1: [u8; 4] = *b"ASHS";
const RESPONSE_MAGIC_V1: [u8; 4] = *b"ASHR";
const VERSION_V1: u8 = 1;
const REQUEST_FIXED_BODY_BYTES_V1: usize = 280;
const RESPONSE_FIXED_BODY_BYTES_V1: usize = 44;
const CHECKSUM_BYTES_V1: usize = 32;
const MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1: usize = 4096;
const MAX_UNSIGNED_MESSAGE_BYTES_V1: usize = 4096;
const MAX_FRAME_BYTES_V1: usize =
    REQUEST_FIXED_BODY_BYTES_V1 + MAX_UNSIGNED_MESSAGE_BYTES_V1 + CHECKSUM_BYTES_V1;
const MAX_RESPONSE_BYTES_V1: usize =
    RESPONSE_FIXED_BODY_BYTES_V1 + MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1 + CHECKSUM_BYTES_V1;
const REQUEST_CHECKSUM_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:external-relayer-signer-request:sha256:v1";
const RESPONSE_CHECKSUM_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:external-relayer-signer-response:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnixRelayerSignerErrorV1 {
    InvalidSocketPath,
    UnsafeSocketPath,
    InsecureSocketPermissions,
    InvalidTimeout,
    InvalidSigningRequest,
    RequestTooLarge,
    ResponseTooLarge,
    InvalidResponse,
    WrongRequestDigest,
    ChecksumMismatch,
    Io(io::ErrorKind),
}

impl From<io::Error> for UnixRelayerSignerErrorV1 {
    fn from(error: io::Error) -> Self {
        Self::Io(error.kind())
    }
}

pub struct UnixSocketRelayerSignerV1 {
    socket_path: PathBuf,
    timeout: Duration,
}

impl UnixSocketRelayerSignerV1 {
    pub fn new(socket_path: &Path, timeout: Duration) -> Result<Self, UnixRelayerSignerErrorV1> {
        if timeout.is_zero() || timeout > Duration::from_secs(60) {
            return Err(UnixRelayerSignerErrorV1::InvalidTimeout);
        }
        validate_private_socket_v1(socket_path)?;
        Ok(Self {
            socket_path: socket_path.to_owned(),
            timeout,
        })
    }

    pub fn socket_path(&self) -> &Path {
        &self.socket_path
    }
}

impl ExternalRelayerSignerV1 for UnixSocketRelayerSignerV1 {
    type Error = UnixRelayerSignerErrorV1;

    fn sign_exact_relayer_message_v1(
        &mut self,
        request: ExactRelayerSigningRequestV1<'_>,
    ) -> Result<Vec<u8>, Self::Error> {
        let (frame, request_digest) = encode_signing_request_v1(&request)?;
        exchange_signer_frame_v1(&self.socket_path, self.timeout, &frame, request_digest)
    }
}

fn encode_signing_request_v1(
    request: &ExactRelayerSigningRequestV1<'_>,
) -> Result<(Vec<u8>, [u8; 32]), UnixRelayerSignerErrorV1> {
    let simulation = request.simulation();
    let message = request.exact_unsigned_message();
    let message_sha256: [u8; 32] = Sha256::digest(message).into();
    if request.request_id() == &[0u8; 32]
        || request.startup_receipt_digest() == &[0u8; 32]
        || request.fee_payer() == &[0u8; 32]
        || request.startup_receipt_digest() != simulation.startup_receipt_digest()
        || request.fee_payer() != simulation.fee_payer()
        || simulation.unsigned_message_sha256() != &message_sha256
        || simulation.simulated_at_slot() == 0
        || simulation.recent_blockhash() == &[0u8; 32]
        || simulation.last_valid_block_height() == 0
        || simulation.simulation_result_sha256() == &[0u8; 32]
        || simulation.simulation_accounts_sha256() == &[0u8; 32]
        || simulation.compute_unit_limit() == 0
        || simulation.compute_units_consumed() == 0
        || simulation.compute_units_consumed() > u64::from(simulation.compute_unit_limit())
        || simulation.estimated_fee_lamports() == 0
        || message.is_empty()
    {
        return Err(UnixRelayerSignerErrorV1::InvalidSigningRequest);
    }
    if message.len() > MAX_UNSIGNED_MESSAGE_BYTES_V1 {
        return Err(UnixRelayerSignerErrorV1::RequestTooLarge);
    }
    let message_length =
        u32::try_from(message.len()).map_err(|_| UnixRelayerSignerErrorV1::RequestTooLarge)?;
    let capacity = REQUEST_FIXED_BODY_BYTES_V1
        .checked_add(message.len())
        .and_then(|length| length.checked_add(CHECKSUM_BYTES_V1))
        .ok_or(UnixRelayerSignerErrorV1::RequestTooLarge)?;
    if capacity > MAX_FRAME_BYTES_V1 {
        return Err(UnixRelayerSignerErrorV1::RequestTooLarge);
    }

    let mut frame = Vec::with_capacity(capacity);
    frame.extend_from_slice(&REQUEST_MAGIC_V1);
    frame.push(VERSION_V1);
    frame.extend_from_slice(&[0u8; 3]);
    frame.extend_from_slice(request.request_id());
    frame.extend_from_slice(request.startup_receipt_digest());
    frame.extend_from_slice(request.fee_payer());
    frame.extend_from_slice(&simulation.simulated_at_slot().to_le_bytes());
    frame.extend_from_slice(simulation.recent_blockhash());
    frame.extend_from_slice(&simulation.last_valid_block_height().to_le_bytes());
    frame.extend_from_slice(simulation.unsigned_message_sha256());
    frame.extend_from_slice(simulation.simulation_result_sha256());
    frame.extend_from_slice(simulation.simulation_accounts_sha256());
    frame.extend_from_slice(&simulation.compute_unit_limit().to_le_bytes());
    frame.extend_from_slice(&simulation.compute_unit_price_micro_lamports().to_le_bytes());
    frame.extend_from_slice(&simulation.compute_units_consumed().to_le_bytes());
    frame.extend_from_slice(&simulation.estimated_fee_lamports().to_le_bytes());
    frame.extend_from_slice(&message_length.to_le_bytes());
    debug_assert_eq!(frame.len(), REQUEST_FIXED_BODY_BYTES_V1);
    frame.extend_from_slice(message);
    let request_digest = checksum_v1(REQUEST_CHECKSUM_DOMAIN_V1, &frame);
    frame.extend_from_slice(&request_digest);
    Ok((frame, request_digest))
}

fn exchange_signer_frame_v1(
    socket_path: &Path,
    timeout: Duration,
    request_frame: &[u8],
    request_digest: [u8; 32],
) -> Result<Vec<u8>, UnixRelayerSignerErrorV1> {
    if request_frame.is_empty() || request_frame.len() > MAX_FRAME_BYTES_V1 {
        return Err(UnixRelayerSignerErrorV1::RequestTooLarge);
    }
    validate_private_socket_v1(socket_path)?;
    let mut stream = UnixStream::connect(socket_path)?;
    stream.set_read_timeout(Some(timeout))?;
    stream.set_write_timeout(Some(timeout))?;
    let request_length = u32::try_from(request_frame.len())
        .map_err(|_| UnixRelayerSignerErrorV1::RequestTooLarge)?;
    stream.write_all(&request_length.to_le_bytes())?;
    stream.write_all(request_frame)?;
    stream.flush()?;

    let mut length_bytes = [0u8; 4];
    stream.read_exact(&mut length_bytes)?;
    let response_length = usize::try_from(u32::from_le_bytes(length_bytes))
        .map_err(|_| UnixRelayerSignerErrorV1::ResponseTooLarge)?;
    if response_length < RESPONSE_FIXED_BODY_BYTES_V1 + CHECKSUM_BYTES_V1
        || response_length > MAX_RESPONSE_BYTES_V1
    {
        return Err(UnixRelayerSignerErrorV1::ResponseTooLarge);
    }
    let mut response = vec![0u8; response_length];
    stream.read_exact(&mut response)?;
    decode_signer_response_v1(&response, request_digest)
}

fn decode_signer_response_v1(
    response: &[u8],
    request_digest: [u8; 32],
) -> Result<Vec<u8>, UnixRelayerSignerErrorV1> {
    if response.len() < RESPONSE_FIXED_BODY_BYTES_V1 + CHECKSUM_BYTES_V1
        || response.len() > MAX_RESPONSE_BYTES_V1
        || response[..4] != RESPONSE_MAGIC_V1
        || response[4] != VERSION_V1
        || response[5..8] != [0u8; 3]
    {
        return Err(UnixRelayerSignerErrorV1::InvalidResponse);
    }
    if response[8..40].ct_eq(&request_digest).unwrap_u8() != 1 {
        return Err(UnixRelayerSignerErrorV1::WrongRequestDigest);
    }
    let signed_wire_length = usize::try_from(u32::from_le_bytes(
        response[40..44]
            .try_into()
            .map_err(|_| UnixRelayerSignerErrorV1::InvalidResponse)?,
    ))
    .map_err(|_| UnixRelayerSignerErrorV1::ResponseTooLarge)?;
    if signed_wire_length == 0 || signed_wire_length > MAX_SIGNED_TRANSACTION_WIRE_BYTES_V1 {
        return Err(UnixRelayerSignerErrorV1::InvalidResponse);
    }
    let body_length = RESPONSE_FIXED_BODY_BYTES_V1
        .checked_add(signed_wire_length)
        .ok_or(UnixRelayerSignerErrorV1::ResponseTooLarge)?;
    if response.len() != body_length + CHECKSUM_BYTES_V1 {
        return Err(UnixRelayerSignerErrorV1::InvalidResponse);
    }
    let expected_checksum = checksum_v1(RESPONSE_CHECKSUM_DOMAIN_V1, &response[..body_length]);
    if response[body_length..]
        .ct_eq(&expected_checksum)
        .unwrap_u8()
        != 1
    {
        return Err(UnixRelayerSignerErrorV1::ChecksumMismatch);
    }
    Ok(response[RESPONSE_FIXED_BODY_BYTES_V1..body_length].to_vec())
}

fn validate_private_socket_v1(path: &Path) -> Result<(), UnixRelayerSignerErrorV1> {
    if !path.is_absolute() || path.file_name().is_none() {
        return Err(UnixRelayerSignerErrorV1::InvalidSocketPath);
    }
    let parent = path
        .parent()
        .ok_or(UnixRelayerSignerErrorV1::InvalidSocketPath)?;
    let parent_metadata = fs::symlink_metadata(parent)?;
    if parent_metadata.file_type().is_symlink() || !parent_metadata.is_dir() {
        return Err(UnixRelayerSignerErrorV1::UnsafeSocketPath);
    }
    if parent_metadata.permissions().mode() & 0o077 != 0 {
        return Err(UnixRelayerSignerErrorV1::InsecureSocketPermissions);
    }
    let metadata = fs::symlink_metadata(path)?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_socket() {
        return Err(UnixRelayerSignerErrorV1::UnsafeSocketPath);
    }
    if metadata.permissions().mode() & 0o077 != 0 {
        return Err(UnixRelayerSignerErrorV1::InsecureSocketPermissions);
    }
    Ok(())
}

fn checksum_v1(domain: &[u8], body: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update((body.len() as u64).to_le_bytes());
    hasher.update(body);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use std::{
        convert::Infallible,
        os::unix::{fs::PermissionsExt as _, net::UnixListener},
        sync::atomic::{AtomicU64, Ordering},
        thread,
    };

    use aspis_core::field::M31;
    use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address};
    use aspis_statement::{encode_digest_canonical, poseidon2::Digest};
    use solana_keypair::Keypair;
    use solana_message::VersionedMessage;
    use solana_program::pubkey::Pubkey;
    use solana_signer::Signer;
    use solana_transaction::versioned::VersionedTransaction;

    use super::*;
    use crate::{
        derive_viewing_keypair_v1,
        operator_execution::RelayerExecutionPortV1,
        operator_startup::{FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1},
        relayer::{prepare_permissionless_relayer_plan_v1, RelayerSnapshotV1},
        relayer_execution_journal::RelayerSimulationEvidenceV1,
        relayer_execution_port::{
            ExactHttpsRelayerExecutionPortV1, ExactRelayerExecutionRpcV1,
            RelayerExecutionRpcPolicyV1,
        },
        relayer_https_rpc::RelayerHttpsRpcErrorV1,
        relayer_rpc_json::{
            ExactRelayerSimulationRequestV1, ExactSendTransactionRequestV1,
            FinalizedAddressLookupTableBatchV1, FinalizedAddressLookupTablesRequestV1,
            FinalizedBlockHeightRequestV1, FinalizedFeeForMessageRequestV1,
            FinalizedFeeForMessageV1, FinalizedLatestBlockhashRequestV1,
            FinalizedLatestBlockhashV1, RelayerSignatureStatusRpcV1, SignatureStatusesRequestV1,
            SuccessfulRelayerSimulationRpcV1,
        },
        relayer_rpc_quorum::RelayerRpcAgreementV1,
        relayer_rpc_request_id::RelayerRpcRequestIdSourceV1,
        relayer_transaction::{
            assemble_exact_pre_simulation_relayer_transaction_v1,
            assemble_exact_unsigned_relayer_message_v1, validate_exact_relayer_transaction_v1,
            RelayerSignedTransactionArtifactV1,
        },
        rpc_adapter::DepositRpcBindingV1,
        rpc_json::FinalizedGetBlockRequestV1,
        rpc_json_quorum::{AgreedFinalizedBlockIngestV1, AgreedFinalizedRpcJsonPlanV1},
        scan_state::{
            DepositScanIdentityV1, FinalizedChainPointV1, LocalOwnerKeyStoreV1, ScanStateV1,
        },
        transaction_builder::build_deposit_instruction_v1,
        ViewingSecretKeyV1,
    };

    static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-external-signer-{}-{sequence}",
                std::process::id()
            ));
            fs::create_dir(&path).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
            Self(path)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn response_v1(request_digest: [u8; 32], wire: &[u8]) -> Vec<u8> {
        let mut response = Vec::new();
        response.extend_from_slice(&RESPONSE_MAGIC_V1);
        response.push(VERSION_V1);
        response.extend_from_slice(&[0u8; 3]);
        response.extend_from_slice(&request_digest);
        response.extend_from_slice(&(wire.len() as u32).to_le_bytes());
        response.extend_from_slice(wire);
        let checksum = checksum_v1(RESPONSE_CHECKSUM_DOMAIN_V1, &response);
        response.extend_from_slice(&checksum);
        response
    }

    struct SignerOnlyRpcV1([u8; 32]);

    impl ExactRelayerExecutionRpcV1 for SignerOnlyRpcV1 {
        fn startup_receipt_digest_v1(&self) -> &[u8; 32] {
            &self.0
        }

        fn finalized_latest_blockhash_v1(
            &self,
            _request: &FinalizedLatestBlockhashRequestV1,
        ) -> Result<RelayerRpcAgreementV1<FinalizedLatestBlockhashV1>, RelayerHttpsRpcErrorV1>
        {
            unreachable!("signing must not issue RPC")
        }

        fn finalized_lookup_tables_v1(
            &self,
            _request: &FinalizedAddressLookupTablesRequestV1,
        ) -> Result<RelayerRpcAgreementV1<FinalizedAddressLookupTableBatchV1>, RelayerHttpsRpcErrorV1>
        {
            unreachable!("signing must not issue RPC")
        }

        fn successful_simulation_v1(
            &self,
            _request: &ExactRelayerSimulationRequestV1,
        ) -> Result<RelayerRpcAgreementV1<SuccessfulRelayerSimulationRpcV1>, RelayerHttpsRpcErrorV1>
        {
            unreachable!("signing must not issue RPC")
        }

        fn finalized_fee_v1(
            &self,
            _request: &FinalizedFeeForMessageRequestV1,
        ) -> Result<RelayerRpcAgreementV1<FinalizedFeeForMessageV1>, RelayerHttpsRpcErrorV1>
        {
            unreachable!("signing must not issue RPC")
        }

        fn send_exact_transaction_v1(
            &self,
            _request: &ExactSendTransactionRequestV1,
        ) -> Result<RelayerRpcAgreementV1<[u8; 64]>, RelayerHttpsRpcErrorV1> {
            unreachable!("signing must not issue RPC")
        }

        fn signature_status_v1(
            &self,
            _request: &SignatureStatusesRequestV1,
        ) -> Result<RelayerRpcAgreementV1<RelayerSignatureStatusRpcV1>, RelayerHttpsRpcErrorV1>
        {
            unreachable!("signing must not issue RPC")
        }

        fn finalized_block_height_v1(
            &self,
            _request: &FinalizedBlockHeightRequestV1,
        ) -> Result<RelayerRpcAgreementV1<u64>, RelayerHttpsRpcErrorV1> {
            unreachable!("signing must not issue RPC")
        }

        fn agreed_finalized_block_plan_v1(
            &self,
            _state: &ScanStateV1,
            _binding: &DepositRpcBindingV1,
            _request: FinalizedGetBlockRequestV1,
        ) -> Result<AgreedFinalizedRpcJsonPlanV1, RelayerHttpsRpcErrorV1> {
            unreachable!("signing must not issue RPC")
        }

        fn ingest_agreed_finalized_block_v1<L: LocalOwnerKeyStoreV1>(
            &self,
            _state: &mut ScanStateV1,
            _binding: &DepositRpcBindingV1,
            _agreed: &AgreedFinalizedRpcJsonPlanV1,
            _root_request_id: u64,
            _viewing_secret: &ViewingSecretKeyV1,
            _local_keys: &L,
        ) -> Result<AgreedFinalizedBlockIngestV1, RelayerHttpsRpcErrorV1> {
            unreachable!("signing must not issue RPC")
        }
    }

    struct NeverRequestIdsV1;

    impl RelayerRpcRequestIdSourceV1 for NeverRequestIdsV1 {
        type Error = Infallible;

        fn take_next_request_id_v1(&mut self) -> Result<u64, Self::Error> {
            unreachable!("signing must not allocate an RPC request id")
        }
    }

    struct NoLocalKeysV1;

    impl LocalOwnerKeyStoreV1 for NoLocalKeysV1 {
        fn contains_owner_key_v1(&self, _owner_key: &[u8; 32]) -> bool {
            false
        }
    }

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    #[test]
    fn execution_port_unix_signer_frame_round_trips_exact_validated_wire() {
        const STARTUP_SLOT: u64 = 90;
        const SIMULATION_SLOT: u64 = 101;
        const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
        const COMPUTE_UNIT_PRICE: u64 = 7;
        const RECENT_BLOCKHASH: [u8; 32] = [0x39u8; 32];

        let fee_payer = Keypair::new();
        let source_authority = Keypair::new();
        let program_id = key(11);
        let mint = key(12);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let vault = aspis_pool::pool_v1_vault_token_account_address(&program_id, &pool).0;
        let instruction = build_deposit_instruction_v1(
            program_id,
            pool,
            mint,
            7,
            key(13),
            source_authority.pubkey(),
            None,
            &DepositRequestV1 {
                owner_key: digest(10),
                amount: 77,
                salt: digest(20),
                encrypted_note_payload: &[],
            },
        )
        .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(14),
            current_root_sequence: 7,
            observed_slot: STARTUP_SLOT,
            pool_state_sha256: [0x90u8; 32],
        };
        let plan =
            prepare_permissionless_relayer_plan_v1(snapshot, fee_payer.pubkey(), &instruction)
                .unwrap();
        let point = FinalizedChainPointV1::new(STARTUP_SLOT, [0x91u8; 32]).unwrap();
        let root = encode_digest_canonical(&digest(30));
        let startup = OperatorStartupReceiptV1::test_only_v1(
            [0x93u8; 32],
            [0x94u8; 32],
            FinalizedReleaseCheckpointV1 {
                point,
                pool_state_sha256: snapshot.pool_state_sha256,
                root_sequence: snapshot.current_root_sequence,
                root,
            },
        );
        let pre_simulation = assemble_exact_pre_simulation_relayer_transaction_v1(
            &plan,
            &startup,
            SIMULATION_SLOT,
            RECENT_BLOCKHASH,
            500,
            COMPUTE_UNIT_LIMIT,
            COMPUTE_UNIT_PRICE,
            &[],
        )
        .unwrap();
        let simulation = RelayerSimulationEvidenceV1 {
            simulated_at_slot: SIMULATION_SLOT,
            recent_blockhash: RECENT_BLOCKHASH,
            last_valid_block_height: 500,
            fee_payer: plan.fee_payer.to_bytes(),
            unsigned_message_sha256: *pre_simulation.exact_message().message_sha256(),
            simulation_result_sha256: [0xa1u8; 32],
            simulation_accounts_sha256: *pre_simulation
                .exact_message()
                .simulation_accounts_sha256(),
            startup_receipt_digest: *startup.receipt_digest(),
            compute_unit_limit: COMPUTE_UNIT_LIMIT,
            compute_unit_price_micro_lamports: COMPUTE_UNIT_PRICE,
            compute_units_consumed: 1_200_000,
            estimated_fee_lamports: 10_000,
        };
        let exact =
            assemble_exact_unsigned_relayer_message_v1(&plan, &startup, simulation, &[]).unwrap();

        let directory = TestDirectory::new();
        let socket_path = directory.0.join("port-signer.sock");
        let listener = UnixListener::bind(&socket_path).unwrap();
        fs::set_permissions(&socket_path, fs::Permissions::from_mode(0o600)).unwrap();
        let signer = UnixSocketRelayerSignerV1::new(&socket_path, Duration::from_secs(2)).unwrap();

        let expected_request_id = plan.request_id;
        let expected_startup = *startup.receipt_digest();
        let expected_fee_payer = plan.fee_payer.to_bytes();
        let expected_message = exact.serialized_message().to_vec();
        let expected_simulation_result = *simulation.simulation_result_sha256();
        let expected_accounts = *simulation.simulation_accounts_sha256();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut length = [0u8; 4];
            stream.read_exact(&mut length).unwrap();
            let mut frame = vec![0u8; u32::from_le_bytes(length) as usize];
            stream.read_exact(&mut frame).unwrap();

            assert_eq!(
                frame.len(),
                REQUEST_FIXED_BODY_BYTES_V1 + expected_message.len() + 32
            );
            assert_eq!(frame[..4], REQUEST_MAGIC_V1);
            assert_eq!(frame[4], VERSION_V1);
            assert_eq!(frame[5..8], [0u8; 3]);
            assert_eq!(frame[8..40], expected_request_id);
            assert_eq!(frame[40..72], expected_startup);
            assert_eq!(frame[72..104], expected_fee_payer);
            assert_eq!(frame[104..112], SIMULATION_SLOT.to_le_bytes());
            assert_eq!(frame[112..144], RECENT_BLOCKHASH);
            assert_eq!(frame[144..152], 500u64.to_le_bytes());
            assert_eq!(
                &frame[152..184],
                Sha256::digest(&expected_message).as_slice()
            );
            assert_eq!(frame[184..216], expected_simulation_result);
            assert_eq!(frame[216..248], expected_accounts);
            assert_eq!(frame[248..252], COMPUTE_UNIT_LIMIT.to_le_bytes());
            assert_eq!(frame[252..260], COMPUTE_UNIT_PRICE.to_le_bytes());
            assert_eq!(frame[260..268], 1_200_000u64.to_le_bytes());
            assert_eq!(frame[268..276], 10_000u64.to_le_bytes());
            assert_eq!(
                frame[276..280],
                u32::try_from(expected_message.len()).unwrap().to_le_bytes()
            );
            assert_eq!(frame[280..280 + expected_message.len()], expected_message);
            let body_length = frame.len() - CHECKSUM_BYTES_V1;
            let request_digest = checksum_v1(REQUEST_CHECKSUM_DOMAIN_V1, &frame[..body_length]);
            assert_eq!(frame[body_length..], request_digest);

            let message: VersionedMessage = bincode::deserialize(&expected_message).unwrap();
            let transaction =
                VersionedTransaction::try_new(message, &[&fee_payer, &source_authority]).unwrap();
            let signed_wire = bincode::serialize(&transaction).unwrap();
            let response = response_v1(request_digest, &signed_wire);
            stream
                .write_all(&(response.len() as u32).to_le_bytes())
                .unwrap();
            stream.write_all(&response).unwrap();
            signed_wire
        });

        let identity = DepositScanIdentityV1::new(
            pool.to_bytes(),
            [0x92u8; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap();
        let mut scan_state = ScanStateV1::new(identity, point, 7, root).unwrap();
        let binding = DepositRpcBindingV1::new(program_id.to_bytes()).unwrap();
        let viewing_secret = derive_viewing_keypair_v1(&[0x51u8; 32]).unwrap().0;
        let local_keys = NoLocalKeysV1;
        let mut port = ExactHttpsRelayerExecutionPortV1::test_only_with_rpc_v1(
            SignerOnlyRpcV1(*startup.receipt_digest()),
            NeverRequestIdsV1,
            signer,
            RelayerExecutionRpcPolicyV1::new(
                COMPUTE_UNIT_LIMIT,
                COMPUTE_UNIT_PRICE,
                20_000,
                Vec::new(),
            )
            .unwrap(),
            &mut scan_state,
            &binding,
            &viewing_secret,
            &local_keys,
        );
        let signed_wire = port
            .sign_exact_unsigned_message_v1(&plan, simulation, exact.serialized_message())
            .unwrap();
        let server_wire = server.join().unwrap();
        assert_eq!(signed_wire, server_wire);
        let validated = validate_exact_relayer_transaction_v1(
            &plan,
            &startup,
            simulation,
            &RelayerSignedTransactionArtifactV1 {
                signed_wire,
                lookup_tables: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(validated.inspected.fee_payer, expected_fee_payer);
        assert_eq!(validated.lookup_table_count, 0);
    }

    #[test]
    fn framed_private_socket_exchange_binds_request_digest() {
        let directory = TestDirectory::new();
        let socket_path = directory.0.join("signer.sock");
        let listener = UnixListener::bind(&socket_path).unwrap();
        fs::set_permissions(&socket_path, fs::Permissions::from_mode(0o600)).unwrap();
        let request_frame = vec![0x41; 128];
        let request_digest = [0x51; 32];
        let signed_wire = vec![0x61; 512];
        let expected_request = request_frame.clone();
        let expected_wire = signed_wire.clone();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut length = [0u8; 4];
            stream.read_exact(&mut length).unwrap();
            let mut request = vec![0u8; u32::from_le_bytes(length) as usize];
            stream.read_exact(&mut request).unwrap();
            assert_eq!(request, expected_request);
            let response = response_v1(request_digest, &expected_wire);
            stream
                .write_all(&(response.len() as u32).to_le_bytes())
                .unwrap();
            stream.write_all(&response).unwrap();
        });
        assert_eq!(
            exchange_signer_frame_v1(
                &socket_path,
                Duration::from_secs(1),
                &request_frame,
                request_digest,
            )
            .unwrap(),
            signed_wire
        );
        server.join().unwrap();
    }

    #[test]
    fn response_digest_checksum_and_socket_permissions_fail_closed() {
        let digest = [0x71; 32];
        let mut response = response_v1(digest, &[0x81; 64]);
        assert_eq!(
            decode_signer_response_v1(&response, [0x72; 32]),
            Err(UnixRelayerSignerErrorV1::WrongRequestDigest)
        );
        *response.last_mut().unwrap() ^= 1;
        assert_eq!(
            decode_signer_response_v1(&response, digest),
            Err(UnixRelayerSignerErrorV1::ChecksumMismatch)
        );

        let directory = TestDirectory::new();
        let socket_path = directory.0.join("signer.sock");
        let _listener = UnixListener::bind(&socket_path).unwrap();
        fs::set_permissions(&socket_path, fs::Permissions::from_mode(0o666)).unwrap();
        assert_eq!(
            UnixSocketRelayerSignerV1::new(&socket_path, Duration::from_secs(1)).err(),
            Some(UnixRelayerSignerErrorV1::InsecureSocketPermissions)
        );
    }
}
