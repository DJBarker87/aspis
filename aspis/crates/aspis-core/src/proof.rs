//! Fixed-layout proof envelope.
//!
//! ```text
//! header (16 bytes):
//!   0  u32  magic "ASP0"
//!   4  u8   version (3: Stage 1 two-phase envelope)
//!   5  u8   profile_id
//!   6  u8   log_rows
//!   7  u8   log_blowup
//!   8  u16  query_count (LE)
//!   10 u8   grinding_bits
//!   11 u8   fold_payload   (0 raw_fibers, 1 proof_carried_round_local)
//!   12 u8   merkle_mode    (0 single_paths, 1 binary minimal_subtree,
//!                           2 radix-4 minimal_subtree)
//!   13 u8   num_rounds
//!   14 u8   final_poly_log_len
//!   15 u8   flags (bit 0 = externally supplied (z, v) evaluation claim;
//!           bit 1 = second commitment phase C2. Claim-carrying proofs must
//!           also set C2. The main claim is a PUBLIC INPUT, never proof
//!           bytes.)
//! round 0 transcript record:
//!   root:       32 bytes
//!   if C2:      c2_root 32 bytes
//!   if C2+claim: c2_claimed_value 16 bytes QM31 LE
//!   ood_value:  16 bytes QM31 LE (the evaluation point is transcript-derived)
//!   sumcheck:   7 * 16 bytes QM31 LE (degree-6 relation polynomial)
//! later round transcript records, repeated for rounds 1..num_rounds:
//!   root || ood_value || sumcheck, with the same sizes as above
//! final_poly:   (1 << final_poly_log_len) * 16   (QM31 LE)
//! grinding_nonce: u64 LE
//! per layer r in 0..num_rounds:
//!   unique_count u16 LE   (must equal the verifier-recomputed unique fiber count)
//!   fibers: unique_count * fiber_bytes(r), ascending fiber-index order
//!           fiber_bytes(0) = 32 (4 CM31), fiber_bytes(r>0) = 64 (4 QM31)
//!   if C2 and r=0: unique_count * 64 helper-fiber bytes (4 QM31)
//!   carried (fold_payload = 1 only): unique_count * 32 (g1, g2 as QM31)
//!   merkle single_paths:    unique_count * depth_r * 32
//!          binary/radix-4 minimal_subtree:
//!                           u32 node_count LE + node_count * 32
//!   if C2 and r=0: a second Merkle proof in the selected mode, for C2
//! ```
//!
//! All sections are length-checked; trailing bytes reject.

pub const MAGIC: u32 = u32::from_le_bytes(*b"ASP0");
pub const VERSION: u8 = 3;
pub const HEADER_LEN: usize = 16;
pub const ROOT_LEN: usize = 32;
pub const OOD_VALUE_LEN: usize = 16;
pub const ROUND_COMMITMENT_LEN: usize = ROOT_LEN + OOD_VALUE_LEN + crate::sumcheck::SUMCHECK_BYTES;
pub const FLAG_EVALUATION_CLAIM: u8 = 1;
pub const FLAG_SECOND_PHASE: u8 = 2;
pub const ALLOWED_FLAGS: u8 = FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE;
pub const SECOND_PHASE_LAYER_TAG: u8 = 0x80;

#[derive(Clone, Copy, Debug)]
pub struct Header {
    pub profile_id: u8,
    pub log_rows: u32,
    pub log_blowup: u32,
    pub query_count: u16,
    pub grinding_bits: u8,
    pub fold_payload: u8,
    pub merkle_mode: u8,
    pub num_rounds: u32,
    pub final_poly_log_len: u32,
    pub flags: u8,
}

impl Header {
    pub fn parse(bytes: &[u8]) -> Option<Header> {
        if bytes.len() < HEADER_LEN {
            return None;
        }
        let magic = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        let flags = bytes[15];
        if magic != MAGIC
            || bytes[4] != VERSION
            || flags & !ALLOWED_FLAGS != 0
            || flags == FLAG_EVALUATION_CLAIM
        {
            return None;
        }
        Some(Header {
            profile_id: bytes[5],
            log_rows: bytes[6] as u32,
            log_blowup: bytes[7] as u32,
            query_count: u16::from_le_bytes(bytes[8..10].try_into().unwrap()),
            grinding_bits: bytes[10],
            fold_payload: bytes[11],
            merkle_mode: bytes[12],
            num_rounds: bytes[13] as u32,
            final_poly_log_len: bytes[14] as u32,
            flags,
        })
    }

    pub fn write(&self, out: &mut [u8]) {
        out[0..4].copy_from_slice(&MAGIC.to_le_bytes());
        out[4] = VERSION;
        out[5] = self.profile_id;
        out[6] = self.log_rows as u8;
        out[7] = self.log_blowup as u8;
        out[8..10].copy_from_slice(&self.query_count.to_le_bytes());
        out[10] = self.grinding_bits;
        out[11] = self.fold_payload;
        out[12] = self.merkle_mode;
        out[13] = self.num_rounds as u8;
        out[14] = self.final_poly_log_len as u8;
        out[15] = self.flags;
    }

    pub const fn has_claim(&self) -> bool {
        self.flags & FLAG_EVALUATION_CLAIM != 0
    }

    pub const fn has_second_phase(&self) -> bool {
        self.flags & FLAG_SECOND_PHASE != 0
    }
}

/// Bytes between the fixed header and final polynomial. C2 adds one root;
/// a claim-carrying C2 adds the helper's claimed evaluation as proof bytes.
pub const fn transcript_records_len(num_rounds: usize, flags: u8) -> usize {
    num_rounds * ROUND_COMMITMENT_LEN
        + if flags & FLAG_SECOND_PHASE != 0 {
            ROOT_LEN
        } else {
            0
        }
        + if flags & FLAG_EVALUATION_CLAIM != 0 {
            OOD_VALUE_LEN
        } else {
            0
        }
}

/// Bounds-checked forward cursor over the proof bytes.
pub struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(bytes: &'a [u8]) -> Cursor<'a> {
        Cursor { bytes, pos: 0 }
    }

    pub fn take(&mut self, len: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(len)?;
        if end > self.bytes.len() {
            return None;
        }
        let out = &self.bytes[self.pos..end];
        self.pos = end;
        Some(out)
    }

    pub fn take_u16(&mut self) -> Option<u16> {
        Some(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }

    pub fn take_u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }

    pub fn take_u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    pub fn take_hash(&mut self) -> Option<[u8; 32]> {
        Some(self.take(32)?.try_into().unwrap())
    }

    pub fn is_empty(&self) -> bool {
        self.pos == self.bytes.len()
    }

    pub fn position(&self) -> usize {
        self.pos
    }
}

pub const fn fiber_value_bytes(layer: u32) -> usize {
    if layer == 0 {
        4 * 8 // 4 CM31
    } else {
        4 * 16 // 4 QM31
    }
}
