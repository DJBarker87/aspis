//! Fixed-layout proof envelope.
//!
//! ```text
//! header (16 bytes):
//!   0  u32  magic "ASP0"
//!   4  u8   version (1)
//!   5  u8   profile_id
//!   6  u8   log_rows
//!   7  u8   log_blowup
//!   8  u16  query_count (LE)
//!   10 u8   grinding_bits
//!   11 u8   fold_payload   (0 raw_fibers, 1 proof_carried_round_local)
//!   12 u8   merkle_mode    (0 single_paths, 1 minimal_subtree)
//!   13 u8   num_rounds
//!   14 u8   final_poly_log_len
//!   15 u8   reserved (0)
//! roots:        num_rounds * 32
//! final_poly:   (1 << final_poly_log_len) * 16   (QM31 LE)
//! grinding_nonce: u64 LE
//! per layer r in 0..num_rounds:
//!   unique_count u16 LE   (must equal the verifier-recomputed unique fiber count)
//!   fibers: unique_count * fiber_bytes(r), ascending fiber-index order
//!           fiber_bytes(0) = 32 (4 CM31), fiber_bytes(r>0) = 64 (4 QM31)
//!   carried (fold_payload = 1 only): unique_count * 32 (g1, g2 as QM31)
//!   merkle single_paths:    unique_count * depth_r * 32
//!          minimal_subtree: u32 node_count LE + node_count * 32
//! ```
//!
//! All sections are length-checked; trailing bytes reject.

pub const MAGIC: u32 = u32::from_le_bytes(*b"ASP0");
pub const VERSION: u8 = 1;
pub const HEADER_LEN: usize = 16;

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
}

impl Header {
    pub fn parse(bytes: &[u8]) -> Option<Header> {
        if bytes.len() < HEADER_LEN {
            return None;
        }
        let magic = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        if magic != MAGIC || bytes[4] != VERSION || bytes[15] != 0 {
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
        out[15] = 0;
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
