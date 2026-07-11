//! Fixed-layout proof envelope.
//!
//! ```text
//! header (16 bytes):
//!   0  u32  magic "ASP0"
//!   4  u8   version (3: one OOD sample per round;
//!                    4: two sequential OOD samples per round)
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
//!           bytes; bit 2 = v4 exact-wide C1 PCS scaffold. The wide flag is
//!           valid only with v4+C2; bit 3 = diagnostic M31 circle C1 basis.
//!           The circle flag is valid only as the exact v4+C2+claim word
//!           `0x0b`, and production verification rejects it.)
//! round 0 transcript record:
//!   root:       32 bytes
//!   if C2:      c2_root 32 bytes. V3 commits one four-QM31 helper fiber;
//!               v4 commits two helper fibers as one eight-QM31/128-byte leaf.
//!   if C2+claim: v3 carries one 16-byte helper evaluation; v4 carries two
//!                sequential 16-byte helper evaluations, both before gamma.
//!   ood_value:  16 bytes QM31 LE (v3), or
//!   ood_value_1 || ood_value_2: 2 * 16 bytes QM31 LE (v4). Each evaluation
//!                 point is transcript-derived and each complete
//!                 `(beta, y, mu)` triple precedes the next.
//!   sumcheck:   7 * 16 bytes QM31 LE (degree-6 relation polynomial)
//! later round transcript records, repeated for rounds 1..num_rounds:
//!   root || ood_value(s) || sumcheck, with the same versioned sizes as above
//! final_poly:   (1 << final_poly_log_len) * 16   (QM31 LE)
//! grinding_nonce: u64 LE
//! per layer r in 0..num_rounds:
//!   unique_count u16 LE   (must equal the verifier-recomputed unique fiber count)
//!   fibers: unique_count * fiber_bytes(r), ascending fiber-index order
//!           fiber_bytes(0) = 32 (4 CM31), fiber_bytes(r>0) = 64 (4 QM31)
//!           v4 exact-wide C1 overrides fiber_bytes(0) with
//!           4 slots * 49 CM31 columns * 8 bytes = 1,568 bytes
//!   if C2 and r=0: v3: unique_count * 64 helper-fiber bytes (4 QM31)
//!                   v4: unique_count * 128 combined helper bytes (8 QM31)
//!   carried (fold_payload = 1 only): unique_count * 32 (g1, g2 as QM31)
//!   merkle single_paths:    unique_count * depth_r * 32
//!          binary/radix-4 minimal_subtree:
//!                           u32 node_count LE + node_count * 32
//!   if C2 and r=0: a second Merkle proof in the selected mode, for C2
//! ```
//!
//! All sections are length-checked; trailing bytes reject.

pub const MAGIC: u32 = u32::from_le_bytes(*b"ASP0");
/// Frozen one-OOD-sample envelope version.
pub const VERSION_V3: u8 = 3;
/// Two sequential OOD samples per fold round.
pub const VERSION_V4_S2: u8 = 4;
/// Short alias for the v4/s=2 envelope.
pub const VERSION_V4: u8 = VERSION_V4_S2;
/// Backward-compatible name for the frozen legacy version.
pub const VERSION: u8 = VERSION_V3;
pub const HEADER_LEN: usize = 16;
pub const ROOT_LEN: usize = 32;
pub const OOD_VALUE_LEN: usize = 16;
pub const SECOND_PHASE_CLAIM_LEN: usize = OOD_VALUE_LEN;
pub const SECOND_PHASE_LEAF_LEN_V3: usize = 4 * OOD_VALUE_LEN;
pub const SECOND_PHASE_LEAF_LEN_V4_S2: usize = 8 * OOD_VALUE_LEN;
/// Frozen v3 round record length.
pub const ROUND_COMMITMENT_LEN: usize = ROOT_LEN + OOD_VALUE_LEN + crate::sumcheck::SUMCHECK_BYTES;
/// V4 adds exactly one encoded QM31 OOD value to every round record.
pub const ROUND_COMMITMENT_LEN_V4: usize =
    ROOT_LEN + 2 * OOD_VALUE_LEN + crate::sumcheck::SUMCHECK_BYTES;
/// Explicit name for the v4/s=2 round record.
pub const ROUND_COMMITMENT_LEN_V4_S2: usize = ROUND_COMMITMENT_LEN_V4;
pub const FLAG_EVALUATION_CLAIM: u8 = 1;
pub const FLAG_SECOND_PHASE: u8 = 2;
/// V4 exact-wide PCS scaffold: 49 CM31 C1 columns are authenticated and
/// combined with the two QM31 C2 helpers at gamma powers 49 and 50.
pub const FLAG_EXACT_WIDE_C1: u8 = 4;
/// Diagnostic-only genuine-circle M31 C1 basis discriminator. Header parsing
/// recognizes this append-only bit so the dedicated diagnostic wire can be
/// framed, but canonical production verification rejects it before any
/// transcript, field, or Merkle work.
pub const FLAG_M31_CIRCLE_C1_DIAGNOSTIC: u8 = 8;
pub const ALLOWED_FLAGS: u8 =
    FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_EXACT_WIDE_C1 | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;
/// Domain separator reserved for the diagnostic transcript. Merely defining
/// it does not enable a transcript schedule or production verifier.
pub const M31_CIRCLE_BASIS_DISCRIMINATOR: &[u8; 22] = b"aspis:c1:m31-circle:v0";
pub const EXACT_WIDE_C1_COLUMNS: usize = 49;
pub const EXACT_WIDE_C1_FIBER_LEN: usize = EXACT_WIDE_C1_COLUMNS * 4 * 8;
pub const M31_CIRCLE_C1_COLUMNS: usize = 49;
pub const M31_CIRCLE_C1_FIBER_LEN: usize = M31_CIRCLE_C1_COLUMNS * 4 * 4;
pub const SECOND_PHASE_LAYER_TAG: u8 = 0x80;

#[derive(Clone, Copy, Debug)]
pub struct Header {
    pub version: u8,
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
        let version = bytes[4];
        let has_claim = flags & FLAG_EVALUATION_CLAIM != 0;
        let has_second_phase = flags & FLAG_SECOND_PHASE != 0;
        let has_exact_wide_c1 = flags & FLAG_EXACT_WIDE_C1 != 0;
        let has_m31_circle_c1 = flags & FLAG_M31_CIRCLE_C1_DIAGNOSTIC != 0;
        let required_m31_circle_flags =
            FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;
        if magic != MAGIC
            || (version != VERSION_V3 && version != VERSION_V4)
            || flags & !ALLOWED_FLAGS != 0
            || (has_claim && !has_second_phase)
            || (has_exact_wide_c1 && (version != VERSION_V4 || !has_second_phase))
            || (has_m31_circle_c1 && (version != VERSION_V4 || flags != required_m31_circle_flags))
        {
            return None;
        }
        Some(Header {
            version,
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
        out[4] = self.version;
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

    pub const fn has_exact_wide_c1(&self) -> bool {
        self.flags & FLAG_EXACT_WIDE_C1 != 0
    }

    pub const fn has_m31_circle_c1_diagnostic(&self) -> bool {
        self.flags & FLAG_M31_CIRCLE_C1_DIAGNOSTIC != 0
    }

    /// Version-aware C1 leaf width. Deeper layers always contain four QM31
    /// values after the layer-zero gamma combination.
    pub const fn first_phase_leaf_len(&self, layer: u32) -> usize {
        if layer == 0 && self.has_exact_wide_c1() {
            EXACT_WIDE_C1_FIBER_LEN
        } else if layer == 0 && self.has_m31_circle_c1_diagnostic() {
            M31_CIRCLE_C1_FIBER_LEN
        } else {
            fiber_value_bytes(layer)
        }
    }

    /// Number of sequential `(beta, y, mu)` relation samples in each round.
    pub const fn ood_samples_per_round(&self) -> usize {
        match self.version {
            VERSION_V3 => 1,
            VERSION_V4 => 2,
            _ => 0,
        }
    }

    pub const fn round_commitment_len(&self) -> usize {
        match self.version {
            VERSION_V3 => ROUND_COMMITMENT_LEN,
            VERSION_V4 => ROUND_COMMITMENT_LEN_V4,
            _ => 0,
        }
    }

    /// Number of helper columns committed in the single C2 tree.
    pub const fn second_phase_helper_count(&self) -> usize {
        if !self.has_second_phase() {
            return 0;
        }
        match self.version {
            VERSION_V3 => 1,
            VERSION_V4_S2 => 2,
            _ => 0,
        }
    }

    /// Width of one C2 leaf. V4 authenticates both helper halves with one
    /// root, rather than introducing an independently swappable tree.
    pub const fn second_phase_leaf_len(&self) -> usize {
        if !self.has_second_phase() {
            return 0;
        }
        match self.version {
            VERSION_V3 => SECOND_PHASE_LEAF_LEN_V3,
            VERSION_V4_S2 => SECOND_PHASE_LEAF_LEN_V4_S2,
            _ => 0,
        }
    }

    /// Number of helper evaluations carried before gamma when a main claim
    /// is present.
    pub const fn second_phase_claim_count(&self) -> usize {
        self.second_phase_helper_count()
    }

    pub const fn second_phase_claims_len(&self) -> usize {
        if self.has_claim() {
            self.second_phase_claim_count() * SECOND_PHASE_CLAIM_LEN
        } else {
            0
        }
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

/// Version-aware transcript-record length. The legacy two-argument helper
/// above intentionally remains pinned to v3 so existing offset code cannot
/// silently reinterpret old proofs.
pub const fn transcript_records_len_for_version(
    num_rounds: usize,
    flags: u8,
    version: u8,
) -> Option<usize> {
    let round_len = match version {
        VERSION_V3 => ROUND_COMMITMENT_LEN,
        VERSION_V4 => ROUND_COMMITMENT_LEN_V4,
        _ => return None,
    };
    Some(
        num_rounds * round_len
            + if flags & FLAG_SECOND_PHASE != 0 {
                ROOT_LEN
            } else {
                0
            }
            + if flags & FLAG_EVALUATION_CLAIM != 0 {
                match version {
                    VERSION_V3 => SECOND_PHASE_CLAIM_LEN,
                    VERSION_V4_S2 => 2 * SECOND_PHASE_CLAIM_LEN,
                    _ => 0,
                }
            } else {
                0
            },
    )
}

/// Absolute proof-byte offset of one encoded per-round OOD value.
///
/// `sample` is zero-based and is restricted by the header version. This is
/// useful to corruption tests and measurement harnesses without duplicating
/// the layer-zero C2 framing rules.
pub fn ood_value_offset(header: &Header, layer: usize, sample: usize) -> Option<usize> {
    if layer >= header.num_rounds as usize || sample >= header.ood_samples_per_round() {
        return None;
    }
    let phase_extra = if header.has_second_phase() {
        ROOT_LEN
    } else {
        0
    } + header.second_phase_claims_len();
    HEADER_LEN
        .checked_add(layer.checked_mul(header.round_commitment_len())?)?
        .checked_add(ROOT_LEN)?
        .checked_add(phase_extra)?
        .checked_add(sample.checked_mul(OOD_VALUE_LEN)?)
}

/// Absolute offset of a C2 helper evaluation carried before gamma.
pub fn second_phase_claim_offset(header: &Header, helper: usize) -> Option<usize> {
    if !header.has_second_phase()
        || !header.has_claim()
        || helper >= header.second_phase_claim_count()
    {
        return None;
    }
    HEADER_LEN
        .checked_add(2 * ROOT_LEN)?
        .checked_add(helper.checked_mul(SECOND_PHASE_CLAIM_LEN)?)
}

/// Absolute offset of the first authenticated C1 leaf in the layer-zero
/// opening section. This is version/flag aware and validates that the full C1
/// section fits before returning.
pub fn first_layer_first_phase_opening_offset(proof: &[u8]) -> Option<usize> {
    let header = Header::parse(proof)?;
    let transcript_len = transcript_records_len_for_version(
        header.num_rounds as usize,
        header.flags,
        header.version,
    )?;
    let final_poly_len = 1usize.checked_shl(header.final_poly_log_len)?;
    let opening_start = HEADER_LEN
        .checked_add(transcript_len)?
        .checked_add(final_poly_len.checked_mul(OOD_VALUE_LEN)?)?
        .checked_add(core::mem::size_of::<u64>())?;
    let count_end = opening_start.checked_add(core::mem::size_of::<u16>())?;
    let unique_count = usize::from(u16::from_le_bytes(
        proof.get(opening_start..count_end)?.try_into().ok()?,
    ));
    if unique_count == 0 {
        return None;
    }
    let c1_end =
        count_end.checked_add(unique_count.checked_mul(header.first_phase_leaf_len(0))?)?;
    if c1_end > proof.len() {
        return None;
    }
    Some(count_end)
}

/// Absolute offset of the first authenticated C2 leaf in the layer-zero
/// opening section. This parses the proof header and unique-count framing so
/// callers do not duplicate version-dependent transcript arithmetic.
pub fn first_layer_second_phase_opening_offset(proof: &[u8]) -> Option<usize> {
    let header = Header::parse(proof)?;
    if !header.has_second_phase() {
        return None;
    }
    let c1_start = first_layer_first_phase_opening_offset(proof)?;
    let count_start = c1_start.checked_sub(core::mem::size_of::<u16>())?;
    let unique_count = usize::from(u16::from_le_bytes(
        proof.get(count_start..c1_start)?.try_into().ok()?,
    ));
    let c2_start =
        c1_start.checked_add(unique_count.checked_mul(header.first_phase_leaf_len(0))?)?;
    let c2_end = c2_start.checked_add(unique_count.checked_mul(header.second_phase_leaf_len())?)?;
    if c2_end > proof.len() {
        return None;
    }
    Some(c2_start)
}

/// Absolute offset of helper `helper` inside the first authenticated C2 leaf.
/// Each helper half is one four-QM31/64-byte fiber; v3 admits index 0 and v4
/// admits indices 0 and 1.
pub fn first_layer_second_phase_helper_offset(proof: &[u8], helper: usize) -> Option<usize> {
    let header = Header::parse(proof)?;
    if helper >= header.second_phase_helper_count() {
        return None;
    }
    first_layer_second_phase_opening_offset(proof)?
        .checked_add(helper.checked_mul(SECOND_PHASE_LEAF_LEN_V3)?)
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

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    fn framed_opening(version: u8, flags: u8, unique_count: u16) -> (Vec<u8>, usize) {
        let header = Header {
            version,
            profile_id: 0,
            log_rows: 10,
            log_blowup: 2,
            query_count: 36,
            grinding_bits: 16,
            fold_payload: 0,
            merkle_mode: 2,
            num_rounds: 4,
            final_poly_log_len: 2,
            flags,
        };
        let transcript_len =
            transcript_records_len_for_version(4, flags, version).expect("supported version");
        let opening_start = HEADER_LEN + transcript_len + 4 * OOD_VALUE_LEN + 8;
        let c2_start =
            opening_start + 2 + usize::from(unique_count) * header.first_phase_leaf_len(0);
        let total_len =
            c2_start + usize::from(unique_count).max(1) * header.second_phase_leaf_len().max(1);
        let mut proof = vec![0u8; total_len];
        header.write(&mut proof[..HEADER_LEN]);
        proof[opening_start..opening_start + 2].copy_from_slice(&unique_count.to_le_bytes());
        (proof, c2_start)
    }

    #[test]
    fn second_phase_opening_offsets_are_version_aware_and_checked() {
        let (v3, v3_c2) = framed_opening(VERSION_V3, FLAG_SECOND_PHASE, 2);
        assert_eq!(first_layer_second_phase_opening_offset(&v3), Some(v3_c2));
        assert_eq!(first_layer_second_phase_helper_offset(&v3, 0), Some(v3_c2));
        assert_eq!(first_layer_second_phase_helper_offset(&v3, 1), None);

        let (v4, v4_c2) =
            framed_opening(VERSION_V4_S2, FLAG_SECOND_PHASE | FLAG_EVALUATION_CLAIM, 3);
        assert_eq!(first_layer_second_phase_opening_offset(&v4), Some(v4_c2));
        assert_eq!(first_layer_second_phase_helper_offset(&v4, 0), Some(v4_c2));
        assert_eq!(
            first_layer_second_phase_helper_offset(&v4, 1),
            Some(v4_c2 + SECOND_PHASE_LEAF_LEN_V3)
        );
        assert_eq!(first_layer_second_phase_helper_offset(&v4, 2), None);

        let (no_c2, _) = framed_opening(VERSION_V4_S2, 0, 1);
        assert_eq!(first_layer_second_phase_opening_offset(&no_c2), None);
        let (empty, _) = framed_opening(VERSION_V4_S2, FLAG_SECOND_PHASE, 0);
        assert_eq!(first_layer_second_phase_opening_offset(&empty), None);
        assert_eq!(first_layer_second_phase_opening_offset(&v4[..v4_c2]), None);
    }

    #[test]
    fn exact_wide_flag_is_v4_c2_only_and_moves_the_c2_offset() {
        let flags = FLAG_SECOND_PHASE | FLAG_EVALUATION_CLAIM | FLAG_EXACT_WIDE_C1;
        let (wide, wide_c2) = framed_opening(VERSION_V4_S2, flags, 3);
        let header = Header::parse(&wide).expect("valid exact-wide v4 header");
        assert!(header.has_exact_wide_c1());
        assert_eq!(header.first_phase_leaf_len(0), EXACT_WIDE_C1_FIBER_LEN);
        assert_eq!(header.first_phase_leaf_len(1), fiber_value_bytes(1));
        assert_eq!(
            first_layer_second_phase_opening_offset(&wide),
            Some(wide_c2)
        );

        let invalid_v3 = Header {
            version: VERSION_V3,
            ..header
        };
        let mut bytes = [0u8; HEADER_LEN];
        invalid_v3.write(&mut bytes);
        assert!(Header::parse(&bytes).is_none());

        let mut invalid_no_c2 = header;
        invalid_no_c2.flags = FLAG_EXACT_WIDE_C1;
        invalid_no_c2.write(&mut bytes);
        assert!(Header::parse(&bytes).is_none());
    }

    #[test]
    fn m31_circle_flag_has_one_noncolliding_v4_claim_frame() {
        let required_flags =
            FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;
        let header = Header {
            version: VERSION_V4_S2,
            profile_id: 6,
            log_rows: 10,
            log_blowup: 2,
            query_count: 36,
            grinding_bits: 16,
            fold_payload: 0,
            merkle_mode: 2,
            num_rounds: 4,
            final_poly_log_len: 2,
            flags: required_flags,
        };
        let mut bytes = [0u8; HEADER_LEN];
        header.write(&mut bytes);
        let parsed = Header::parse(&bytes).expect("valid diagnostic M31 circle header");
        assert!(parsed.has_m31_circle_c1_diagnostic());
        assert!(!parsed.has_exact_wide_c1());
        assert_eq!(parsed.first_phase_leaf_len(0), M31_CIRCLE_C1_FIBER_LEN);
        assert_eq!(parsed.first_phase_leaf_len(1), fiber_value_bytes(1));
        assert_eq!(M31_CIRCLE_BASIS_DISCRIMINATOR, b"aspis:c1:m31-circle:v0");

        for invalid in [
            Header {
                version: VERSION_V3,
                ..header
            },
            Header {
                flags: FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC,
                ..header
            },
            Header {
                flags: required_flags | FLAG_EXACT_WIDE_C1,
                ..header
            },
            Header {
                flags: required_flags | 0x10,
                ..header
            },
        ] {
            invalid.write(&mut bytes);
            assert!(Header::parse(&bytes).is_none());
        }
    }
}
