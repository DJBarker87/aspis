//! Crash-safe monotonically increasing JSON-RPC request identifiers.
//!
//! Request ids are part of every exact two-provider evidence binding. An id is
//! therefore burned to durable storage before it is returned to the caller;
//! a crash may skip an id but can never cause an already-issued id to be
//! reused by this allocator.

use std::path::Path;

use sha2::{Digest as _, Sha256};

use crate::durable_state::{AtomicStateFileV1, DurableStateErrorV1};

const MAGIC_V1: [u8; 4] = *b"ASRI";
const VERSION_V1: u8 = 1;
const IMAGE_BYTES_V1: usize = 48;
const BODY_BYTES_V1: usize = 16;
const CHECKSUM_DOMAIN_V1: &[u8] = b"aspis:pool-v1:relayer-rpc-request-id:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerRpcRequestIdErrorV1 {
    Durable(DurableStateErrorV1),
    InvalidImage,
    Exhausted,
}

impl From<DurableStateErrorV1> for RelayerRpcRequestIdErrorV1 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

/// Source used by the production relayer port. Implementations must persist a
/// successful allocation before returning it and must never return zero.
pub trait RelayerRpcRequestIdSourceV1 {
    type Error;

    fn take_next_request_id_v1(&mut self) -> Result<u64, Self::Error>;
}

pub struct DurableRelayerRpcRequestIdSourceV1 {
    file: AtomicStateFileV1,
    next_request_id: u64,
}

impl DurableRelayerRpcRequestIdSourceV1 {
    /// Open one exclusively locked allocator. A missing image begins at
    /// `initial_request_id`; an existing image always wins over that argument.
    pub fn open_or_create_v1(
        path: &Path,
        initial_request_id: u64,
    ) -> Result<Self, RelayerRpcRequestIdErrorV1> {
        if initial_request_id == 0 {
            return Err(RelayerRpcRequestIdErrorV1::InvalidImage);
        }
        let file = AtomicStateFileV1::acquire(path)?;
        let next_request_id = match file.read_optional()? {
            Some(image) => decode_image_v1(&image)?,
            None => initial_request_id,
        };
        Ok(Self {
            file,
            next_request_id,
        })
    }

    pub fn next_unallocated_request_id_v1(&self) -> Option<u64> {
        (self.next_request_id != 0).then_some(self.next_request_id)
    }
}

impl RelayerRpcRequestIdSourceV1 for DurableRelayerRpcRequestIdSourceV1 {
    type Error = RelayerRpcRequestIdErrorV1;

    fn take_next_request_id_v1(&mut self) -> Result<u64, Self::Error> {
        let allocated = self.next_request_id;
        if allocated == 0 {
            return Err(RelayerRpcRequestIdErrorV1::Exhausted);
        }
        let next = allocated.checked_add(1).unwrap_or(0);
        let image = encode_image_v1(next);
        self.file.replace(&image)?;
        self.next_request_id = next;
        Ok(allocated)
    }
}

fn encode_image_v1(next_request_id: u64) -> [u8; IMAGE_BYTES_V1] {
    let mut image = [0u8; IMAGE_BYTES_V1];
    image[..4].copy_from_slice(&MAGIC_V1);
    image[4] = VERSION_V1;
    image[8..16].copy_from_slice(&next_request_id.to_le_bytes());
    let checksum = checksum_v1(&image[..BODY_BYTES_V1]);
    image[BODY_BYTES_V1..].copy_from_slice(&checksum);
    image
}

fn decode_image_v1(image: &[u8]) -> Result<u64, RelayerRpcRequestIdErrorV1> {
    if image.len() != IMAGE_BYTES_V1
        || image[..4] != MAGIC_V1
        || image[4] != VERSION_V1
        || image[5..8] != [0u8; 3]
        || image[BODY_BYTES_V1..] != checksum_v1(&image[..BODY_BYTES_V1])
    {
        return Err(RelayerRpcRequestIdErrorV1::InvalidImage);
    }
    Ok(u64::from_le_bytes(
        image[8..16]
            .try_into()
            .map_err(|_| RelayerRpcRequestIdErrorV1::InvalidImage)?,
    ))
}

fn checksum_v1(body: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(CHECKSUM_DOMAIN_V1);
    hasher.update((body.len() as u64).to_le_bytes());
    hasher.update(body);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;

    static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(std::path::PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-relayer-rpc-id-{}-{sequence}",
                std::process::id()
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn allocation_is_committed_before_restart_and_corruption_fails_closed() {
        let directory = TestDirectory::new();
        let path = directory.0.join("rpc-id.state");
        {
            let mut source =
                DurableRelayerRpcRequestIdSourceV1::open_or_create_v1(&path, 41).unwrap();
            assert_eq!(source.take_next_request_id_v1().unwrap(), 41);
            assert_eq!(source.take_next_request_id_v1().unwrap(), 42);
            assert_eq!(source.next_unallocated_request_id_v1(), Some(43));
        }
        {
            let mut source =
                DurableRelayerRpcRequestIdSourceV1::open_or_create_v1(&path, 1).unwrap();
            assert_eq!(source.take_next_request_id_v1().unwrap(), 43);
        }

        let mut bytes = fs::read(&path).unwrap();
        bytes[8] ^= 1;
        fs::write(&path, bytes).unwrap();
        assert!(matches!(
            DurableRelayerRpcRequestIdSourceV1::open_or_create_v1(&path, 1),
            Err(RelayerRpcRequestIdErrorV1::InvalidImage)
        ));
    }

    #[test]
    fn maximum_id_is_returned_once_then_allocator_is_exhausted() {
        let directory = TestDirectory::new();
        let path = directory.0.join("rpc-id.state");
        let mut source =
            DurableRelayerRpcRequestIdSourceV1::open_or_create_v1(&path, u64::MAX).unwrap();
        assert_eq!(source.take_next_request_id_v1().unwrap(), u64::MAX);
        assert_eq!(source.next_unallocated_request_id_v1(), None);
        assert_eq!(
            source.take_next_request_id_v1(),
            Err(RelayerRpcRequestIdErrorV1::Exhausted)
        );
    }
}
