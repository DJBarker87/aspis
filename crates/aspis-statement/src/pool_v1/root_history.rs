//! Pure Pool V1 historical-root page model.
//!
//! Root sequence zero is the empty-tree root.  Appending leaf `i` produces
//! root sequence `i + 1`.  Consequently a sequence has exactly one page and
//! slot, independent of transaction batching or verifier version.

use aspis_core::field::M31;

use crate::{
    decode_digest_canonical, encode_digest_canonical,
    poseidon2::{Digest, DIGEST_ELEMS},
};

pub const POOL_V1_ROOT_HISTORY_PAGE_MAGIC: [u8; 4] = *b"ASPR";
pub const POOL_V1_ROOT_HISTORY_PAGE_VERSION: u8 = 1;
pub const POOL_V1_ROOT_HISTORY_CAPACITY_LOG2: u8 = 8;
pub const POOL_V1_ROOT_HISTORY_CAPACITY: usize = 1 << POOL_V1_ROOT_HISTORY_CAPACITY_LOG2;
pub const POOL_V1_ROOT_HISTORY_PAGE_SEED: &[u8] = b"aspis-pool-root-page-v1";
pub const POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES: usize = 64;
pub const POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES: usize =
    POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + 32 * POOL_V1_ROOT_HISTORY_CAPACITY;

const PAGE_POOL_OFFSET: usize = 8;
const PAGE_NUMBER_OFFSET: usize = 40;
const PAGE_FIRST_SEQUENCE_OFFSET: usize = 48;
const PAGE_FILLED_OFFSET: usize = 56;
const PAGE_RESERVED_OFFSET: usize = 58;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1RootHistoryError {
    SequenceOverflow,
    PageNumberOverflow,
    WrongPage,
    OutOfOrder,
    PageFull,
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongCapacity,
    NonZeroReserved,
    InvalidFilled,
    InvalidFirstSequence,
    NonCanonicalDigest,
    NonCanonicalUnusedRoot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootHistoryLocationV1 {
    pub page_number: u64,
    pub slot: u16,
}

impl RootHistoryLocationV1 {
    pub fn first_sequence(self) -> Result<u64, PoolV1RootHistoryError> {
        self.page_number
            .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
            .ok_or(PoolV1RootHistoryError::PageNumberOverflow)
    }
}

pub fn root_history_location(sequence: u64) -> RootHistoryLocationV1 {
    RootHistoryLocationV1 {
        page_number: sequence / POOL_V1_ROOT_HISTORY_CAPACITY as u64,
        slot: (sequence % POOL_V1_ROOT_HISTORY_CAPACITY as u64) as u16,
    }
}

/// Pure description of the future root-page PDA seeds.
///
/// Program integration should derive the account with exactly
/// `[POOL_V1_ROOT_HISTORY_PAGE_SEED, pool, page_number_le]` and its own
/// program id.  Keeping this type Solana-independent lets the indexing and
/// byte layout be tested without importing runtime account machinery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootHistoryPageAddressV1 {
    pub pool: [u8; 32],
    pub page_number: u64,
}

/// Checked metadata borrowed from one canonical root-history account image.
///
/// Unlike [`RootHistoryPageV1`], this header is small enough for the SBF stack.
/// The in-place helpers below validate or mutate the caller-provided account
/// byte slice without copying its 8 KiB root payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootHistoryPageHeaderV1 {
    pub pool: [u8; 32],
    pub page_number: u64,
    pub first_sequence: u64,
    pub filled: u16,
}

fn validate_root_history_page_prefix_v1(
    bytes: &[u8],
) -> Result<RootHistoryPageHeaderV1, PoolV1RootHistoryError> {
    if bytes.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES {
        return Err(PoolV1RootHistoryError::WrongLength);
    }
    if bytes[..4] != POOL_V1_ROOT_HISTORY_PAGE_MAGIC {
        return Err(PoolV1RootHistoryError::WrongMagic);
    }
    if bytes[4] != POOL_V1_ROOT_HISTORY_PAGE_VERSION
        || bytes[6] != super::format::POOL_V1_DIGEST_ENCODING_VERSION
    {
        return Err(PoolV1RootHistoryError::WrongVersion);
    }
    if bytes[5] != POOL_V1_ROOT_HISTORY_CAPACITY_LOG2 {
        return Err(PoolV1RootHistoryError::WrongCapacity);
    }
    if bytes[7] != 0
        || bytes[PAGE_RESERVED_OFFSET..POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES] != [0u8; 6]
    {
        return Err(PoolV1RootHistoryError::NonZeroReserved);
    }
    let filled = u16::from_le_bytes(
        bytes[PAGE_FILLED_OFFSET..PAGE_RESERVED_OFFSET]
            .try_into()
            .unwrap(),
    );
    if usize::from(filled) > POOL_V1_ROOT_HISTORY_CAPACITY {
        return Err(PoolV1RootHistoryError::InvalidFilled);
    }
    Ok(RootHistoryPageHeaderV1 {
        pool: bytes[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET]
            .try_into()
            .unwrap(),
        page_number: u64::from_le_bytes(
            bytes[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
                .try_into()
                .unwrap(),
        ),
        first_sequence: u64::from_le_bytes(
            bytes[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
                .try_into()
                .unwrap(),
        ),
        filled,
    })
}

/// Validate one exact page directly in its account byte image.
///
/// Every digest is decoded one at a time, retaining the legacy decoder's
/// error priority: any non-canonical unused digest is rejected as
/// [`PoolV1RootHistoryError::NonCanonicalDigest`] before a canonical nonzero
/// unused digest is reported as
/// [`PoolV1RootHistoryError::NonCanonicalUnusedRoot`].
pub fn validate_root_history_page_bytes_v1(
    bytes: &[u8],
) -> Result<RootHistoryPageHeaderV1, PoolV1RootHistoryError> {
    let header = validate_root_history_page_prefix_v1(bytes)?;
    let mut nonzero_unused_root = false;
    for slot in 0..POOL_V1_ROOT_HISTORY_CAPACITY {
        let start = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + slot * 32;
        let root = decode_digest_canonical(bytes[start..start + 32].try_into().unwrap())
            .map_err(|_| PoolV1RootHistoryError::NonCanonicalDigest)?;
        if slot >= usize::from(header.filled) && root != [M31::ZERO; DIGEST_ELEMS] {
            nonzero_unused_root = true;
        }
    }
    let expected_first = header
        .page_number
        .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
        .ok_or(PoolV1RootHistoryError::PageNumberOverflow)?;
    if header.first_sequence != expected_first {
        return Err(PoolV1RootHistoryError::InvalidFirstSequence);
    }
    if nonzero_unused_root {
        return Err(PoolV1RootHistoryError::NonCanonicalUnusedRoot);
    }
    Ok(header)
}

/// Initialize one canonical page in caller-provided account storage.
///
/// The destination is validated before its first write.  No heap allocation,
/// unsafe cast, or full-page stack temporary is used.
pub fn initialize_root_history_page_bytes_v1(
    bytes: &mut [u8],
    pool: [u8; 32],
    page_number: u64,
    roots: &[Digest],
) -> Result<RootHistoryPageHeaderV1, PoolV1RootHistoryError> {
    if bytes.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES {
        return Err(PoolV1RootHistoryError::WrongLength);
    }
    if roots.len() > POOL_V1_ROOT_HISTORY_CAPACITY {
        return Err(PoolV1RootHistoryError::PageFull);
    }
    let first_sequence = page_number
        .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
        .ok_or(PoolV1RootHistoryError::PageNumberOverflow)?;
    let filled = roots.len() as u16;

    bytes.fill(0);
    bytes[..4].copy_from_slice(&POOL_V1_ROOT_HISTORY_PAGE_MAGIC);
    bytes[4] = POOL_V1_ROOT_HISTORY_PAGE_VERSION;
    bytes[5] = POOL_V1_ROOT_HISTORY_CAPACITY_LOG2;
    bytes[6] = super::format::POOL_V1_DIGEST_ENCODING_VERSION;
    bytes[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET].copy_from_slice(&pool);
    bytes[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
        .copy_from_slice(&page_number.to_le_bytes());
    bytes[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
        .copy_from_slice(&first_sequence.to_le_bytes());
    bytes[PAGE_FILLED_OFFSET..PAGE_RESERVED_OFFSET].copy_from_slice(&filled.to_le_bytes());
    for (slot, root) in roots.iter().enumerate() {
        let start = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + slot * 32;
        bytes[start..start + 32].copy_from_slice(&encode_digest_canonical(root));
    }
    Ok(RootHistoryPageHeaderV1 {
        pool,
        page_number,
        first_sequence,
        filled,
    })
}

/// Append one root directly to a previously validated page image.
///
/// All failure checks precede the two bounded writes, preserving the pure
/// model's fail-without-mutation behavior.
pub fn append_root_history_page_bytes_v1(
    bytes: &mut [u8],
    sequence: u64,
    root: Digest,
) -> Result<RootHistoryLocationV1, PoolV1RootHistoryError> {
    let header = validate_root_history_page_bytes_v1(bytes)?;
    if usize::from(header.filled) == POOL_V1_ROOT_HISTORY_CAPACITY {
        return Err(PoolV1RootHistoryError::PageFull);
    }
    let location = root_history_location(sequence);
    if location.page_number != header.page_number {
        return Err(PoolV1RootHistoryError::WrongPage);
    }
    let expected_sequence = header
        .first_sequence
        .checked_add(u64::from(header.filled))
        .ok_or(PoolV1RootHistoryError::SequenceOverflow)?;
    if sequence != expected_sequence {
        return Err(PoolV1RootHistoryError::OutOfOrder);
    }

    let start = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + usize::from(location.slot) * 32;
    bytes[start..start + 32].copy_from_slice(&encode_digest_canonical(&root));
    bytes[PAGE_FILLED_OFFSET..PAGE_RESERVED_OFFSET]
        .copy_from_slice(&(header.filled + 1).to_le_bytes());
    Ok(location)
}

/// Read one retained root from a canonical account image.
pub fn read_root_history_page_root_v1(
    bytes: &[u8],
    sequence: u64,
) -> Result<Digest, PoolV1RootHistoryError> {
    let header = validate_root_history_page_bytes_v1(bytes)?;
    let location = root_history_location(sequence);
    if location.page_number != header.page_number || location.slot >= header.filled {
        return Err(PoolV1RootHistoryError::WrongPage);
    }
    let start = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + usize::from(location.slot) * 32;
    decode_digest_canonical(bytes[start..start + 32].try_into().unwrap())
        .map_err(|_| PoolV1RootHistoryError::NonCanonicalDigest)
}

impl RootHistoryPageAddressV1 {
    pub fn for_sequence(pool: [u8; 32], sequence: u64) -> Self {
        Self {
            pool,
            page_number: root_history_location(sequence).page_number,
        }
    }

    pub fn page_number_seed(self) -> [u8; 8] {
        self.page_number.to_le_bytes()
    }
}

/// One append-only page of 256 exact roots.
///
/// Unfilled slots are canonical zero digests.  This makes the on-chain image
/// unique and prevents stale bytes from being interpreted as retained roots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootHistoryPageV1 {
    pub pool: [u8; 32],
    pub page_number: u64,
    pub first_sequence: u64,
    pub filled: u16,
    roots: [Digest; POOL_V1_ROOT_HISTORY_CAPACITY],
}

impl RootHistoryPageV1 {
    /// Construct the host/reference value model.
    ///
    /// Returning this 8 KiB value by value cannot fit the fixed SBF stack.
    /// On-chain callers use [`initialize_root_history_page_bytes_v1`] over
    /// checked account storage instead.
    #[cfg(not(target_os = "solana"))]
    pub fn new(pool: [u8; 32], page_number: u64) -> Result<Self, PoolV1RootHistoryError> {
        let first_sequence = page_number
            .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
            .ok_or(PoolV1RootHistoryError::PageNumberOverflow)?;
        Ok(Self {
            pool,
            page_number,
            first_sequence,
            filled: 0,
            roots: [[M31::ZERO; DIGEST_ELEMS]; POOL_V1_ROOT_HISTORY_CAPACITY],
        })
    }

    /// Page zero with the empty-tree root retained at sequence zero.
    #[cfg(not(target_os = "solana"))]
    pub fn genesis(pool: [u8; 32], empty_root: Digest) -> Self {
        let mut page = Self::new(pool, 0).expect("page zero cannot overflow");
        page.push(0, empty_root)
            .expect("the empty genesis page accepts sequence zero");
        page
    }

    pub fn is_full(&self) -> bool {
        usize::from(self.filled) == POOL_V1_ROOT_HISTORY_CAPACITY
    }

    pub fn next_sequence(&self) -> Result<u64, PoolV1RootHistoryError> {
        self.first_sequence
            .checked_add(u64::from(self.filled))
            .ok_or(PoolV1RootHistoryError::SequenceOverflow)
    }

    pub fn push(
        &mut self,
        sequence: u64,
        root: Digest,
    ) -> Result<RootHistoryLocationV1, PoolV1RootHistoryError> {
        self.validate_metadata()?;
        if self.is_full() {
            return Err(PoolV1RootHistoryError::PageFull);
        }
        let location = root_history_location(sequence);
        if location.page_number != self.page_number {
            return Err(PoolV1RootHistoryError::WrongPage);
        }
        if sequence != self.next_sequence()? {
            return Err(PoolV1RootHistoryError::OutOfOrder);
        }
        let slot = usize::from(location.slot);
        self.roots[slot] = root;
        self.filled += 1;
        Ok(location)
    }

    pub fn get(&self, sequence: u64) -> Option<&Digest> {
        let location = root_history_location(sequence);
        if location.page_number != self.page_number || location.slot >= self.filled {
            return None;
        }
        self.roots.get(usize::from(location.slot))
    }

    pub fn roots(&self) -> &[Digest] {
        &self.roots[..usize::from(self.filled)]
    }

    fn validate_metadata(&self) -> Result<(), PoolV1RootHistoryError> {
        if usize::from(self.filled) > POOL_V1_ROOT_HISTORY_CAPACITY {
            return Err(PoolV1RootHistoryError::InvalidFilled);
        }
        let expected_first = self
            .page_number
            .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
            .ok_or(PoolV1RootHistoryError::PageNumberOverflow)?;
        if self.first_sequence != expected_first {
            return Err(PoolV1RootHistoryError::InvalidFirstSequence);
        }
        Ok(())
    }

    /// Encode into caller-provided storage without a full-page stack return.
    pub fn encode_into(&self, output: &mut [u8]) -> Result<(), PoolV1RootHistoryError> {
        if output.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES {
            return Err(PoolV1RootHistoryError::WrongLength);
        }
        self.validate_metadata()?;
        if self.roots[usize::from(self.filled)..]
            .iter()
            .any(|root| *root != [M31::ZERO; DIGEST_ELEMS])
        {
            return Err(PoolV1RootHistoryError::NonCanonicalUnusedRoot);
        }
        output.fill(0);
        output[..4].copy_from_slice(&POOL_V1_ROOT_HISTORY_PAGE_MAGIC);
        output[4] = POOL_V1_ROOT_HISTORY_PAGE_VERSION;
        output[5] = POOL_V1_ROOT_HISTORY_CAPACITY_LOG2;
        output[6] = super::format::POOL_V1_DIGEST_ENCODING_VERSION;
        output[8..40].copy_from_slice(&self.pool);
        output[40..48].copy_from_slice(&self.page_number.to_le_bytes());
        output[48..56].copy_from_slice(&self.first_sequence.to_le_bytes());
        output[56..58].copy_from_slice(&self.filled.to_le_bytes());
        for (slot, root) in self.roots.iter().enumerate() {
            let start = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + slot * 32;
            output[start..start + 32].copy_from_slice(&encode_digest_canonical(root));
        }
        Ok(())
    }

    /// Host/reference convenience wrapper around [`Self::encode_into`].
    #[cfg(not(target_os = "solana"))]
    pub fn encode(
        &self,
    ) -> Result<[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES], PoolV1RootHistoryError> {
        let mut output = [0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        self.encode_into(&mut output)?;
        Ok(output)
    }

    /// Decode the host/reference value model.
    ///
    /// SBF callers validate and read the account-backed image through
    /// [`validate_root_history_page_bytes_v1`] and
    /// [`read_root_history_page_root_v1`], avoiding an 8 KiB return value.
    #[cfg(not(target_os = "solana"))]
    pub fn decode(bytes: &[u8]) -> Result<Self, PoolV1RootHistoryError> {
        let header = validate_root_history_page_bytes_v1(bytes)?;
        let mut roots = [[M31::ZERO; DIGEST_ELEMS]; POOL_V1_ROOT_HISTORY_CAPACITY];
        for (slot, root) in roots
            .iter_mut()
            .take(usize::from(header.filled))
            .enumerate()
        {
            let start = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + slot * 32;
            *root = decode_digest_canonical(bytes[start..start + 32].try_into().unwrap())
                .map_err(|_| PoolV1RootHistoryError::NonCanonicalDigest)?;
        }
        Ok(Self {
            pool: header.pool,
            page_number: header.page_number,
            first_sequence: header.first_sequence,
            filled: header.filled,
            roots,
        })
    }
}

#[cfg(test)]
mod tests {
    use aspis_core::field::P;

    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    #[test]
    fn sequence_mapping_is_total_and_hits_exact_boundaries() {
        assert_eq!(
            root_history_location(0),
            RootHistoryLocationV1 {
                page_number: 0,
                slot: 0
            }
        );
        assert_eq!(
            root_history_location(255),
            RootHistoryLocationV1 {
                page_number: 0,
                slot: 255
            }
        );
        assert_eq!(
            root_history_location(256),
            RootHistoryLocationV1 {
                page_number: 1,
                slot: 0
            }
        );
        assert_eq!(
            root_history_location(511),
            RootHistoryLocationV1 {
                page_number: 1,
                slot: 255
            }
        );
    }

    #[test]
    fn page_address_uses_pool_and_little_endian_page_number() {
        let address = RootHistoryPageAddressV1::for_sequence([9u8; 32], 0x0102);
        assert_eq!(address.pool, [9u8; 32]);
        assert_eq!(address.page_number, 1);
        assert_eq!(address.page_number_seed(), 1u64.to_le_bytes());
        assert_eq!(POOL_V1_ROOT_HISTORY_PAGE_SEED, b"aspis-pool-root-page-v1");
    }

    #[test]
    fn history_is_append_only_exact_sequence_and_failure_is_atomic() {
        let mut page = RootHistoryPageV1::genesis([3u8; 32], digest(10));
        assert_eq!(page.get(0), Some(&digest(10)));
        let before = page.clone();
        assert_eq!(
            page.push(2, digest(20)),
            Err(PoolV1RootHistoryError::OutOfOrder)
        );
        assert_eq!(page, before);
        assert_eq!(
            page.push(1, digest(20)),
            Ok(RootHistoryLocationV1 {
                page_number: 0,
                slot: 1
            })
        );
        assert_eq!(page.get(1), Some(&digest(20)));
    }

    #[test]
    fn full_page_and_wrong_page_fail_without_writes() {
        let mut page = RootHistoryPageV1::new([4u8; 32], 0).unwrap();
        for sequence in 0..POOL_V1_ROOT_HISTORY_CAPACITY as u64 {
            page.push(sequence, digest(sequence as u32 + 1)).unwrap();
        }
        let before = page.clone();
        assert_eq!(
            page.push(POOL_V1_ROOT_HISTORY_CAPACITY as u64, digest(999)),
            Err(PoolV1RootHistoryError::PageFull)
        );
        assert_eq!(page, before);

        let mut next = RootHistoryPageV1::new([4u8; 32], 1).unwrap();
        let before = next.clone();
        assert_eq!(
            next.push(255, digest(1000)),
            Err(PoolV1RootHistoryError::WrongPage)
        );
        assert_eq!(next, before);
    }

    #[test]
    fn account_image_roundtrips_and_rejects_noncanonical_bytes() {
        let mut page = RootHistoryPageV1::genesis([5u8; 32], digest(10));
        page.push(1, digest(20)).unwrap();
        let encoded = page.encode().unwrap();
        assert_eq!(encoded.len(), 8_256);
        assert_eq!(RootHistoryPageV1::decode(&encoded), Ok(page));

        let mut reserved = encoded;
        reserved[63] = 1;
        assert_eq!(
            RootHistoryPageV1::decode(&reserved),
            Err(PoolV1RootHistoryError::NonZeroReserved)
        );

        let mut noncanonical = encoded;
        noncanonical
            [POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES..POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + 4]
            .copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            RootHistoryPageV1::decode(&noncanonical),
            Err(PoolV1RootHistoryError::NonCanonicalDigest)
        );
    }

    #[test]
    fn in_place_helpers_match_reference_bytes_and_fail_without_writes() {
        let pool = [6u8; 32];
        let roots = [digest(10), digest(20)];
        let mut bytes = std::vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let header = initialize_root_history_page_bytes_v1(&mut bytes, pool, 0, &roots).unwrap();
        assert_eq!(
            header,
            RootHistoryPageHeaderV1 {
                pool,
                page_number: 0,
                first_sequence: 0,
                filled: 2,
            }
        );

        let mut reference = RootHistoryPageV1::genesis(pool, roots[0]);
        reference.push(1, roots[1]).unwrap();
        assert_eq!(bytes.as_slice(), &reference.encode().unwrap());
        assert_eq!(validate_root_history_page_bytes_v1(&bytes), Ok(header));
        assert_eq!(read_root_history_page_root_v1(&bytes, 1), Ok(roots[1]));

        let before = bytes.clone();
        assert_eq!(
            append_root_history_page_bytes_v1(&mut bytes, 3, digest(30)),
            Err(PoolV1RootHistoryError::OutOfOrder)
        );
        assert_eq!(bytes, before);
        assert_eq!(
            append_root_history_page_bytes_v1(&mut bytes, 2, digest(30)),
            Ok(RootHistoryLocationV1 {
                page_number: 0,
                slot: 2,
            })
        );
        reference.push(2, digest(30)).unwrap();
        assert_eq!(bytes.as_slice(), &reference.encode().unwrap());
    }

    #[test]
    fn in_place_validation_preserves_legacy_unused_error_priority() {
        let mut bytes = std::vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(&mut bytes, [7u8; 32], 0, &[digest(10)]).unwrap();

        let canonical_nonzero = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + 32;
        bytes[canonical_nonzero..canonical_nonzero + 32]
            .copy_from_slice(&encode_digest_canonical(&digest(20)));
        assert_eq!(
            validate_root_history_page_bytes_v1(&bytes),
            Err(PoolV1RootHistoryError::NonCanonicalUnusedRoot)
        );

        let later_noncanonical = POOL_V1_ROOT_HISTORY_PAGE_HEADER_BYTES + 64;
        bytes[later_noncanonical..later_noncanonical + 4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            validate_root_history_page_bytes_v1(&bytes),
            Err(PoolV1RootHistoryError::NonCanonicalDigest)
        );
    }
}
