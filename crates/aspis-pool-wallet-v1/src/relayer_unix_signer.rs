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
        os::unix::{fs::PermissionsExt as _, net::UnixListener},
        sync::atomic::{AtomicU64, Ordering},
        thread,
    };

    use super::*;

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
