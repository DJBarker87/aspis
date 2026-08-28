#![no_std]

pub const M31_MODULUS: u32 = 2_147_483_647;
pub const LANE_COUNT: usize = 8;
pub const TREE_DEPTH: usize = 20;
pub const TREE_CAPACITY: u64 = 1u64 << TREE_DEPTH;
pub const LANE_HEADER_BYTES: usize = 80;
pub const TREE_STATE_BYTES: usize = 688;
pub const LANE_ACCOUNT_BYTES: usize = LANE_HEADER_BYTES + TREE_STATE_BYTES;

pub const LANE_MAGIC: [u8; 4] = *b"ASL8";
pub const LANE_VERSION: u8 = 1;
pub const TREE_MAGIC: [u8; 4] = *b"ASPT";
pub const TREE_VERSION: u8 = 1;
pub const TREE_HASH_VERSION: u8 = 3;
pub const DIGEST_ENCODING_VERSION: u8 = 1;
pub const ACCOUNT_FORMAT_BINDING: [u8; 32] = [
    b'A', b'S', b'P', b'I', b'S', b'F', b'O', b'R', b'E', b'S', b'T', b'8', 1, 1, 1, 8, 1, 20, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Digest(pub [u32; 8]);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneState {
    pub master: [u8; 32],
    pub lane_id: u8,
    pub next_leaf_index: u64,
    pub root: Digest,
    pub frontier: [Digest; TREE_DEPTH],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneSourceError {
    WrongLength,
    WrongHeader,
    WrongBinding,
    WrongMaster,
    WrongLane,
    WrongTreeHeader,
    IndexOutOfRange,
    NonCanonicalDigest,
    InactiveFrontier,
    WrongGenesis,
    MissingProgramOwnedInvariant,
    InvalidWriterTransition,
}

fn read_u32_le(bytes: &[u8], start: usize) -> u32 {
    u32::from_le_bytes([
        bytes[start],
        bytes[start + 1],
        bytes[start + 2],
        bytes[start + 3],
    ])
}

fn read_u64_le(bytes: &[u8], start: usize) -> u64 {
    u64::from_le_bytes([
        bytes[start],
        bytes[start + 1],
        bytes[start + 2],
        bytes[start + 3],
        bytes[start + 4],
        bytes[start + 5],
        bytes[start + 6],
        bytes[start + 7],
    ])
}

fn decode_digest(bytes: &[u8], start: usize) -> Result<Digest, LaneSourceError> {
    let mut limbs = [0u32; 8];
    let mut index = 0usize;
    let mut canonical = true;
    while index < 8 {
        let limb = read_u32_le(bytes, start + 4 * index);
        if limb >= M31_MODULUS {
            canonical = false;
        }
        limbs[index] = limb;
        index += 1;
    }
    if canonical {
        Ok(Digest(limbs))
    } else {
        Err(LaneSourceError::NonCanonicalDigest)
    }
}

fn digest_is_canonical(digest: &Digest) -> bool {
    let mut index = 0usize;
    let mut canonical = true;
    while index < 8 {
        if digest.0[index] >= M31_MODULUS {
            canonical = false;
        }
        index += 1;
    }
    canonical
}

fn write_digest(output: &mut [u8; LANE_ACCOUNT_BYTES], start: usize, digest: &Digest) {
    let mut index = 0usize;
    while index < 8 {
        let limb = digest.0[index].to_le_bytes();
        let offset = start + 4 * index;
        output[offset] = limb[0];
        output[offset + 1] = limb[1];
        output[offset + 2] = limb[2];
        output[offset + 3] = limb[3];
        index += 1;
    }
}

fn bytes32_nonzero(bytes: &[u8; 32]) -> bool {
    let mut index = 0usize;
    let mut nonzero = false;
    while index < 32 {
        if bytes[index] != 0 {
            nonzero = true;
        }
        index += 1;
    }
    nonzero
}

fn binding_matches(bytes: &[u8]) -> bool {
    let mut index = 0usize;
    let mut is_match = true;
    while index < 32 {
        if bytes[8 + index] != ACCOUNT_FORMAT_BINDING[index] {
            is_match = false;
        }
        index += 1;
    }
    is_match
}

fn reserved_header_is_zero(bytes: &[u8]) -> bool {
    let mut index = 72usize;
    let mut zero = true;
    while index < LANE_HEADER_BYTES {
        if bytes[index] != 0 {
            zero = false;
        }
        index += 1;
    }
    zero
}

fn decode_frontier(bytes: &[u8], tree: usize) -> Result<[Digest; TREE_DEPTH], LaneSourceError> {
    let mut frontier = [Digest([0u32; 8]); TREE_DEPTH];
    let mut level = 0usize;
    let mut failure = None;
    while level < TREE_DEPTH {
        match decode_digest(bytes, tree + 48 + 32 * level) {
            Ok(node) => {
                frontier[level] = node;
            }
            Err(error) => failure = Some(error),
        }
        level += 1;
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(frontier),
    }
}

fn validate_frontier(
    frontier: &[Digest; TREE_DEPTH],
    next_leaf_index: u64,
    empty_roots: &[Digest; TREE_DEPTH + 1],
) -> Result<(), LaneSourceError> {
    let mut level = 0usize;
    let mut canonical = true;
    let mut inactive_valid = true;
    while level < TREE_DEPTH {
        if !digest_is_canonical(&frontier[level]) {
            canonical = false;
        }
        if ((next_leaf_index >> level) & 1) == 0 && frontier[level] != empty_roots[level] {
            inactive_valid = false;
        }
        level += 1;
    }
    if !canonical {
        Err(LaneSourceError::NonCanonicalDigest)
    } else if !inactive_valid {
        Err(LaneSourceError::InactiveFrontier)
    } else {
        Ok(())
    }
}

/// Exact pure projection of the hot decoder after Solana owner, writable,
/// signer and PDA checks. The sole omitted computation is the active
/// root/frontier Poseidon reconstruction; `program_owned_invariant` is the
/// explicit capability supplied by the inductive writer theorem.
pub fn hot_decode_projected(
    bytes: &[u8],
    expected_master: [u8; 32],
    expected_lane: u8,
    empty_roots: [Digest; TREE_DEPTH + 1],
    program_owned_invariant: bool,
) -> Result<LaneState, LaneSourceError> {
    if !program_owned_invariant {
        return Err(LaneSourceError::MissingProgramOwnedInvariant);
    }
    if bytes.len() != LANE_ACCOUNT_BYTES {
        return Err(LaneSourceError::WrongLength);
    }
    if bytes[0] != LANE_MAGIC[0]
        || bytes[1] != LANE_MAGIC[1]
        || bytes[2] != LANE_MAGIC[2]
        || bytes[3] != LANE_MAGIC[3]
        || bytes[4] != LANE_VERSION
        || usize::from(bytes[5]) >= LANE_COUNT
        || bytes[6] != LANE_COUNT as u8
        || bytes[7] != TREE_DEPTH as u8
    {
        return Err(LaneSourceError::WrongHeader);
    }
    if !binding_matches(bytes) {
        return Err(LaneSourceError::WrongBinding);
    }
    let mut master = [0u8; 32];
    let mut master_index = 0usize;
    while master_index < 32 {
        master[master_index] = bytes[40 + master_index];
        master_index += 1;
    }
    if !bytes32_nonzero(&master) || master != expected_master {
        return Err(LaneSourceError::WrongMaster);
    }
    if bytes[5] != expected_lane {
        return Err(LaneSourceError::WrongLane);
    }
    if !reserved_header_is_zero(bytes) {
        return Err(LaneSourceError::WrongHeader);
    }
    let tree = LANE_HEADER_BYTES;
    if bytes[tree] != TREE_MAGIC[0]
        || bytes[tree + 1] != TREE_MAGIC[1]
        || bytes[tree + 2] != TREE_MAGIC[2]
        || bytes[tree + 3] != TREE_MAGIC[3]
        || bytes[tree + 4] != TREE_VERSION
        || bytes[tree + 5] != TREE_DEPTH as u8
        || bytes[tree + 6] != TREE_HASH_VERSION
        || bytes[tree + 7] != DIGEST_ENCODING_VERSION
    {
        return Err(LaneSourceError::WrongTreeHeader);
    }
    let next_leaf_index = read_u64_le(bytes, tree + 8);
    if next_leaf_index > TREE_CAPACITY {
        return Err(LaneSourceError::IndexOutOfRange);
    }
    let root = decode_digest(bytes, tree + 16)?;
    if !digest_is_canonical(&root) {
        return Err(LaneSourceError::NonCanonicalDigest);
    }
    let frontier = decode_frontier(bytes, tree)?;
    validate_frontier(&frontier, next_leaf_index, &empty_roots)?;
    if next_leaf_index == 0 && root != empty_roots[TREE_DEPTH] {
        return Err(LaneSourceError::WrongGenesis);
    }
    Ok(LaneState {
        master,
        lane_id: expected_lane,
        next_leaf_index,
        root,
        frontier,
    })
}

/// Exact byte construction of the fast result encoder. It checks every
/// structural property retained by production and omits only the active
/// root/frontier recomputation represented by the named capability.
pub fn fast_encode_projected(
    lane: LaneState,
    empty_roots: [Digest; TREE_DEPTH + 1],
    program_owned_invariant: bool,
) -> Result<[u8; LANE_ACCOUNT_BYTES], LaneSourceError> {
    if !program_owned_invariant {
        return Err(LaneSourceError::MissingProgramOwnedInvariant);
    }
    if usize::from(lane.lane_id) >= LANE_COUNT {
        return Err(LaneSourceError::WrongLane);
    }
    if !bytes32_nonzero(&lane.master) {
        return Err(LaneSourceError::WrongMaster);
    }
    if lane.next_leaf_index > TREE_CAPACITY {
        return Err(LaneSourceError::IndexOutOfRange);
    }
    if !digest_is_canonical(&lane.root) {
        return Err(LaneSourceError::NonCanonicalDigest);
    }
    validate_frontier(&lane.frontier, lane.next_leaf_index, &empty_roots)?;
    if lane.next_leaf_index == 0 && lane.root != empty_roots[TREE_DEPTH] {
        return Err(LaneSourceError::WrongGenesis);
    }

    let mut output = [0u8; LANE_ACCOUNT_BYTES];
    output[0] = LANE_MAGIC[0];
    output[1] = LANE_MAGIC[1];
    output[2] = LANE_MAGIC[2];
    output[3] = LANE_MAGIC[3];
    output[4] = LANE_VERSION;
    output[5] = lane.lane_id;
    output[6] = LANE_COUNT as u8;
    output[7] = TREE_DEPTH as u8;
    let mut binding_index = 0usize;
    while binding_index < 32 {
        output[8 + binding_index] = ACCOUNT_FORMAT_BINDING[binding_index];
        output[40 + binding_index] = lane.master[binding_index];
        binding_index += 1;
    }
    let tree = LANE_HEADER_BYTES;
    output[tree] = TREE_MAGIC[0];
    output[tree + 1] = TREE_MAGIC[1];
    output[tree + 2] = TREE_MAGIC[2];
    output[tree + 3] = TREE_MAGIC[3];
    output[tree + 4] = TREE_VERSION;
    output[tree + 5] = TREE_DEPTH as u8;
    output[tree + 6] = TREE_HASH_VERSION;
    output[tree + 7] = DIGEST_ENCODING_VERSION;
    let index_bytes = lane.next_leaf_index.to_le_bytes();
    let mut byte_index = 0usize;
    while byte_index < 8 {
        output[tree + 8 + byte_index] = index_bytes[byte_index];
        byte_index += 1;
    }
    write_digest(&mut output, tree + 16, &lane.root);
    let mut level = 0usize;
    while level < TREE_DEPTH {
        write_digest(&mut output, tree + 48 + 32 * level, &lane.frontier[level]);
        level += 1;
    }
    Ok(output)
}

/// Source projection of the strict encoder. Its extra boolean is exactly the
/// root/frontier recomputation result which the fast path replaces with the
/// single inductive capability.
pub fn strict_encode_projected(
    lane: LaneState,
    empty_roots: [Digest; TREE_DEPTH + 1],
    strict_root_frontier_check: bool,
) -> Result<[u8; LANE_ACCOUNT_BYTES], LaneSourceError> {
    if !strict_root_frontier_check {
        return Err(LaneSourceError::MissingProgramOwnedInvariant);
    }
    fast_encode_projected(lane, empty_roots, true)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProductionLaneWrite {
    Initialize {
        master: [u8; 32],
        lane_id: u8,
    },
    CheckedDepositAppend {
        before: LaneState,
        after: LaneState,
        append_checked: bool,
    },
    AuthenticatedAsr8Settlement {
        before: LaneState,
        after: LaneState,
        asr8_authenticated: bool,
    },
}

fn genesis_frontier(empty_roots: &[Digest; TREE_DEPTH + 1]) -> [Digest; TREE_DEPTH] {
    [
        empty_roots[0],
        empty_roots[1],
        empty_roots[2],
        empty_roots[3],
        empty_roots[4],
        empty_roots[5],
        empty_roots[6],
        empty_roots[7],
        empty_roots[8],
        empty_roots[9],
        empty_roots[10],
        empty_roots[11],
        empty_roots[12],
        empty_roots[13],
        empty_roots[14],
        empty_roots[15],
        empty_roots[16],
        empty_roots[17],
        empty_roots[18],
        empty_roots[19],
    ]
}

/// Exhaustive source projection of the three production writes to a forest
/// lane PDA. Checkpoint is absent because it never mutates a lane.
pub fn apply_production_lane_write(
    write: ProductionLaneWrite,
    empty_roots: [Digest; TREE_DEPTH + 1],
) -> Result<LaneState, LaneSourceError> {
    match write {
        ProductionLaneWrite::Initialize { master, lane_id } => {
            if !bytes32_nonzero(&master) || usize::from(lane_id) >= LANE_COUNT {
                return Err(LaneSourceError::InvalidWriterTransition);
            }
            let frontier = genesis_frontier(&empty_roots);
            Ok(LaneState {
                master,
                lane_id,
                next_leaf_index: 0,
                root: empty_roots[TREE_DEPTH],
                frontier,
            })
        }
        ProductionLaneWrite::CheckedDepositAppend {
            before,
            after,
            append_checked,
        } => {
            if !append_checked
                || before.master != after.master
                || before.lane_id != after.lane_id
                || before.next_leaf_index.checked_add(1) != Some(after.next_leaf_index)
            {
                return Err(LaneSourceError::InvalidWriterTransition);
            }
            fast_encode_projected(after, empty_roots, true)?;
            Ok(after)
        }
        ProductionLaneWrite::AuthenticatedAsr8Settlement {
            before,
            after,
            asr8_authenticated,
        } => {
            if !asr8_authenticated
                || before.master != after.master
                || before.lane_id != after.lane_id
                || before.next_leaf_index.checked_add(1) != Some(after.next_leaf_index)
            {
                return Err(LaneSourceError::InvalidWriterTransition);
            }
            fast_encode_projected(after, empty_roots, true)?;
            Ok(after)
        }
    }
}
