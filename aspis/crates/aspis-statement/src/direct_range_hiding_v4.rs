//! Host algebra probe for replacing the range LogUp with direct 10-bit
//! decompositions and zero-sum padding on the surviving copy helper.
//!
//! This module does not alter the frozen profile-13 registry. It is the
//! candidate relation which a new hiding profile must integrate and measure.

use alloc::{vec, vec::Vec};

use aspis_core::field::{CM31, M31, QM31};

use crate::{
    hiding_v4::expanded_hiding_padding_cells_v4,
    logup::{build_copy_logup_helper, compress_tagged_tuple, copy_logup_residual, CopyLogUpRow},
    poseidon2::POSEIDON2_WIDTH,
    trace_v4::{
        visit_copy_links, CopyLink, CopyLinkKind, CopyTuple, SpendTraceV4, TraceCell, TupleLimb,
        COPY_LINK_COUNT, INPUT_VALUE_RANGE_ROW, MULTIPLICITY_COLUMN, OUTPUT_VALUE_RANGE_ROW,
        TRACE_ROWS,
    },
};

pub const DIRECT_RANGE_BIT_ROW_START: usize = 864;
pub const DIRECT_RANGE_LIMB_COUNT: usize = 6;
pub const DIRECT_RANGE_BITS_PER_LIMB: usize = 10;
pub const DIRECT_RANGE_LIMBS_PER_ROW: usize = 3;
pub const DIRECT_RANGE_BIT_ROW_COUNT: usize = DIRECT_RANGE_LIMB_COUNT / DIRECT_RANGE_LIMBS_PER_ROW;
pub const DIRECT_RANGE_BITS_PER_ROW: usize =
    DIRECT_RANGE_LIMBS_PER_ROW * DIRECT_RANGE_BITS_PER_LIMB;
pub const DIRECT_RANGE_RECONSTRUCTION_COLUMN_START: usize = DIRECT_RANGE_BITS_PER_ROW;
pub const COPY_HELPER_PADDING_ROW_START: usize =
    DIRECT_RANGE_BIT_ROW_START + DIRECT_RANGE_BIT_ROW_COUNT;
pub const COPY_HELPER_PADDING_ROW_COUNT: usize = TRACE_ROWS - COPY_HELPER_PADDING_ROW_START;
pub const COPY_HELPER_MASK_VARIABLES: usize = COPY_HELPER_PADDING_ROW_COUNT - 1;
pub const PAYMENT_MASK_ORACLE_VALUES: usize = TRACE_ROWS;
pub const DIRECT_RANGE_COPY_LINK_COUNT: usize = 2;
pub const DIRECT_RANGE_TOTAL_COPY_LINK_COUNT: usize =
    COPY_LINK_COUNT + DIRECT_RANGE_COPY_LINK_COUNT;
pub const DIRECT_RANGE_C1_COLUMN_COUNT: usize = MULTIPLICITY_COLUMN + 1;
pub const DIRECT_RANGE_C1_MASK_CELL_COUNT: usize = 11_611;
pub const PINNED_DIRECT_RANGE_C1_MASK_LAYOUT_FINGERPRINT: u64 = 0x3a81_06eb_75a8_2cde;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirectRangeHidingHelpersV4 {
    pub copy_rows: Vec<CopyLogUpRow>,
    pub h1: Vec<QM31>,
    /// One full-domain QM31 oracle. Together with the relation-free C1
    /// padding it masks the payment sumcheck and occupies the removed range
    /// helper's second C2 slot.
    pub payment_mask: Vec<QM31>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirectRangeHidingError {
    Shape,
    Bitness { limb: u8, bit: u8 },
    Reconstruction { limb: u8 },
    SourceCopy { limb: u8 },
    PaddingLength { expected: usize, actual: usize },
    PaymentMaskLength { expected: usize, actual: usize },
    PaddingSum,
    CopyRelation { row: u16 },
    CopyTotal,
    C1PaddingSum { column: u8 },
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

fn source_limb(trace: &SpendTraceV4, limb: usize) -> M31 {
    let row = if limb < 3 {
        INPUT_VALUE_RANGE_ROW
    } else {
        OUTPUT_VALUE_RANGE_ROW
    };
    trace.c1[limb % 3][row]
}

/// Populate two rows with the ten bits of the already committed range limbs.
/// Column 10 mirrors each reconstructed limb and is the endpoint a selected
/// production copy link will bind to the old source cell.
pub fn apply_direct_range_witness_v4(
    trace: &mut SpendTraceV4,
) -> Result<(), DirectRangeHidingError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(DirectRangeHidingError::Shape);
    }
    for limb in 0..DIRECT_RANGE_LIMB_COUNT {
        let value = source_limb(trace, limb);
        let side = limb / DIRECT_RANGE_LIMBS_PER_ROW;
        let local_limb = limb % DIRECT_RANGE_LIMBS_PER_ROW;
        let row = DIRECT_RANGE_BIT_ROW_START + side;
        for bit in 0..DIRECT_RANGE_BITS_PER_LIMB {
            trace.c1[local_limb * DIRECT_RANGE_BITS_PER_LIMB + bit][row] =
                M31((value.0 >> bit) & 1);
        }
        trace.c1[DIRECT_RANGE_RECONSTRUCTION_COLUMN_START + local_limb][row] = value;
    }
    // The direct bit constraints replace the fixed-table multiplicity witness.
    // A later hiding sampler may use this now-free column as mask entropy.
    for value in &mut trace.c1[MULTIPLICITY_COLUMN] {
        *value = M31::ZERO;
    }
    Ok(())
}

/// Independent C1 mask cells for the direct-range candidate. Row 1023 is
/// omitted in every column because it is the dependent value which makes the
/// helper-padding interval sum to zero. The six bit rows in columns 0..10 are
/// also omitted. Column 48 is entirely reclaimed after removing multiplicity.
pub fn direct_range_c1_mask_cells_v4() -> Vec<TraceCell> {
    let mut cells = expanded_hiding_padding_cells_v4()
        .into_iter()
        .filter(|cell| {
            usize::from(cell.row) != TRACE_ROWS - 1
                && !((DIRECT_RANGE_BIT_ROW_START
                    ..DIRECT_RANGE_BIT_ROW_START + DIRECT_RANGE_BIT_ROW_COUNT)
                    .contains(&usize::from(cell.row))
                    && usize::from(cell.column)
                        < DIRECT_RANGE_RECONSTRUCTION_COLUMN_START + DIRECT_RANGE_LIMBS_PER_ROW)
        })
        .collect::<Vec<_>>();
    cells.extend((0..TRACE_ROWS - 1).map(|row| TraceCell {
        row: row as u16,
        column: MULTIPLICITY_COLUMN as u8,
    }));
    cells
}

pub fn direct_range_c1_mask_layout_fingerprint() -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for cell in direct_range_c1_mask_cells_v4() {
        for byte in cell.row.to_le_bytes().into_iter().chain([cell.column]) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    hash
}

pub fn apply_direct_range_c1_masks_v4(
    trace: &mut SpendTraceV4,
    masks: &[M31],
) -> Result<(), DirectRangeHidingError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(DirectRangeHidingError::Shape);
    }
    let cells = direct_range_c1_mask_cells_v4();
    if masks.len() != cells.len() {
        return Err(DirectRangeHidingError::PaddingLength {
            expected: cells.len(),
            actual: masks.len(),
        });
    }
    for (cell, value) in cells.into_iter().zip(masks.iter().copied()) {
        trace.c1[usize::from(cell.column)][usize::from(cell.row)] = value;
    }
    for column in 0..DIRECT_RANGE_C1_COLUMN_COUNT {
        let sum = trace.c1[column][COPY_HELPER_PADDING_ROW_START..TRACE_ROWS - 1]
            .iter()
            .copied()
            .fold(M31::ZERO, M31::add);
        trace.c1[column][TRACE_ROWS - 1] = M31::ZERO.sub(sum);
    }
    Ok(())
}

pub fn verify_direct_range_c1_mask_sums_v4(
    trace: &SpendTraceV4,
) -> Result<(), DirectRangeHidingError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(DirectRangeHidingError::Shape);
    }
    for column in 0..DIRECT_RANGE_C1_COLUMN_COUNT {
        let sum = trace.c1[column][COPY_HELPER_PADDING_ROW_START..]
            .iter()
            .copied()
            .fold(M31::ZERO, M31::add);
        if sum != M31::ZERO {
            return Err(DirectRangeHidingError::C1PaddingSum {
                column: column as u8,
            });
        }
    }
    Ok(())
}

fn range_tuple(cells: [TraceCell; 3]) -> CopyTuple {
    let mut limbs = [TupleLimb::Zero; POSEIDON2_WIDTH];
    for (limb, cell) in cells.into_iter().enumerate() {
        limbs[limb] = TupleLimb::Cell(cell);
    }
    CopyTuple { limbs }
}

pub fn direct_range_copy_links_v4() -> [CopyLink; DIRECT_RANGE_COPY_LINK_COUNT] {
    core::array::from_fn(|side| {
        let source_row = if side == 0 {
            INPUT_VALUE_RANGE_ROW
        } else {
            OUTPUT_VALUE_RANGE_ROW
        };
        let bit_row = DIRECT_RANGE_BIT_ROW_START + side;
        let id = COPY_LINK_COUNT + side;
        CopyLink {
            id: id as u16,
            tag: M31(id as u32 + 1),
            kind: CopyLinkKind::ValueReconstruction,
            producer_row: bit_row as u16,
            consumer_row: source_row as u16,
            producer: range_tuple(core::array::from_fn(|limb| TraceCell {
                row: bit_row as u16,
                column: (DIRECT_RANGE_RECONSTRUCTION_COLUMN_START + limb) as u8,
            })),
            consumer: range_tuple(core::array::from_fn(|limb| TraceCell {
                row: source_row as u16,
                column: limb as u8,
            })),
        }
    })
}

fn tuple_values(trace: &SpendTraceV4, tuple: CopyTuple) -> [M31; POSEIDON2_WIDTH] {
    tuple.limbs.map(|limb| match limb {
        TupleLimb::Cell(cell) => trace.c1[usize::from(cell.column)][usize::from(cell.row)],
        TupleLimb::Zero => M31::ZERO,
    })
}

fn insert_endpoint(
    values: &mut [QM31; 2],
    weights: &mut [M31; 2],
    value: QM31,
    row: usize,
) -> Result<(), DirectRangeHidingError> {
    let Some(slot) = weights.iter().position(|weight| *weight == M31::ZERO) else {
        return Err(DirectRangeHidingError::CopyRelation { row: row as u16 });
    };
    values[slot] = value;
    weights[slot] = M31::ONE;
    Ok(())
}

pub fn build_direct_range_hiding_helpers_v4(
    trace: &SpendTraceV4,
    lambda: QM31,
    chi: QM31,
    helper_masks: &[QM31],
    payment_mask: &[QM31],
) -> Result<DirectRangeHidingHelpersV4, DirectRangeHidingError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(DirectRangeHidingError::Shape);
    }
    if payment_mask.len() != PAYMENT_MASK_ORACLE_VALUES {
        return Err(DirectRangeHidingError::PaymentMaskLength {
            expected: PAYMENT_MASK_ORACLE_VALUES,
            actual: payment_mask.len(),
        });
    }
    let empty = CopyLogUpRow {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [M31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [M31::ZERO; 2],
    };
    let mut rows = vec![empty; TRACE_ROWS];
    let mut error = None;
    let mut add_link = |link: CopyLink| {
        if error.is_some() {
            return;
        }
        let producer_row = usize::from(link.producer_row);
        let consumer_row = usize::from(link.consumer_row);
        let producer = compress_tagged_tuple(link.tag, &tuple_values(trace, link.producer), lambda);
        let consumer = compress_tagged_tuple(link.tag, &tuple_values(trace, link.consumer), lambda);
        let producer_record = &mut rows[producer_row];
        if let Err(found) = insert_endpoint(
            &mut producer_record.producer_values,
            &mut producer_record.producer_weights,
            producer,
            producer_row,
        ) {
            error = Some(found);
            return;
        }
        let consumer_record = &mut rows[consumer_row];
        if let Err(found) = insert_endpoint(
            &mut consumer_record.consumer_values,
            &mut consumer_record.consumer_weights,
            consumer,
            consumer_row,
        ) {
            error = Some(found);
        }
    };
    visit_copy_links(&mut add_link);
    for link in direct_range_copy_links_v4() {
        add_link(link);
    }
    if let Some(error) = error {
        return Err(error);
    }
    let mut h1 =
        build_copy_logup_helper(&rows, chi).map_err(|_| DirectRangeHidingError::CopyTotal)?;
    apply_copy_helper_padding_v4(&mut h1, helper_masks)?;
    Ok(DirectRangeHidingHelpersV4 {
        copy_rows: rows,
        h1,
        payment_mask: payment_mask.to_vec(),
    })
}

/// Boolean-row residuals for the direct range probe:
/// `(beta-batched bitness, reconstruction, source-copy)`.
pub fn direct_range_row_residuals_v4(
    trace: &SpendTraceV4,
    row: usize,
    beta: QM31,
) -> Result<[QM31; 3], DirectRangeHidingError> {
    if row >= TRACE_ROWS || trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(DirectRangeHidingError::Shape);
    }
    if !(DIRECT_RANGE_BIT_ROW_START..DIRECT_RANGE_BIT_ROW_START + DIRECT_RANGE_BIT_ROW_COUNT)
        .contains(&row)
    {
        return Ok([QM31::ZERO; 3]);
    }
    let side = row - DIRECT_RANGE_BIT_ROW_START;
    let mut bitness = QM31::ZERO;
    let mut beta_power = QM31::ONE;
    let mut reconstruction_residual = QM31::ZERO;
    let mut source_residual = QM31::ZERO;
    for local_limb in 0..DIRECT_RANGE_LIMBS_PER_ROW {
        let limb = side * DIRECT_RANGE_LIMBS_PER_ROW + local_limb;
        let mut reconstruction = M31::ZERO;
        let mut two_power = M31::ONE;
        for bit in 0..DIRECT_RANGE_BITS_PER_LIMB {
            let column = local_limb * DIRECT_RANGE_BITS_PER_LIMB + bit;
            let value = trace.c1[column][row];
            bitness = bitness.add(beta_power.mul_m31(value.mul(value.sub(M31::ONE))));
            reconstruction = reconstruction.add(value.mul(two_power));
            beta_power = beta_power.mul(beta);
            two_power = two_power.double();
        }
        let committed = trace.c1[DIRECT_RANGE_RECONSTRUCTION_COLUMN_START + local_limb][row];
        reconstruction_residual =
            reconstruction_residual.add(beta_power.mul_m31(committed.sub(reconstruction)));
        beta_power = beta_power.mul(beta);
        source_residual =
            source_residual.add(beta_power.mul_m31(committed.sub(source_limb(trace, limb))));
        beta_power = beta_power.mul(beta);
    }
    Ok([bitness, reconstruction_residual, source_residual])
}

pub fn verify_direct_range_witness_v4(trace: &SpendTraceV4) -> Result<(), DirectRangeHidingError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(DirectRangeHidingError::Shape);
    }
    for limb in 0..DIRECT_RANGE_LIMB_COUNT {
        let side = limb / DIRECT_RANGE_LIMBS_PER_ROW;
        let local_limb = limb % DIRECT_RANGE_LIMBS_PER_ROW;
        let row = DIRECT_RANGE_BIT_ROW_START + side;
        let mut reconstruction = 0u32;
        for bit in 0..DIRECT_RANGE_BITS_PER_LIMB {
            let value = trace.c1[local_limb * DIRECT_RANGE_BITS_PER_LIMB + bit][row];
            if value != M31::ZERO && value != M31::ONE {
                return Err(DirectRangeHidingError::Bitness {
                    limb: limb as u8,
                    bit: bit as u8,
                });
            }
            reconstruction |= value.0 << bit;
        }
        let committed = trace.c1[DIRECT_RANGE_RECONSTRUCTION_COLUMN_START + local_limb][row];
        if committed != M31(reconstruction) {
            return Err(DirectRangeHidingError::Reconstruction { limb: limb as u8 });
        }
        if committed != source_limb(trace, limb) {
            return Err(DirectRangeHidingError::SourceCopy { limb: limb as u8 });
        }
    }
    Ok(())
}

/// Replace the helper's inactive suffix with 153 independent QM31 masks and
/// one dependent value so the padding sum is exactly zero.
pub fn apply_copy_helper_padding_v4(
    helper: &mut [QM31],
    masks: &[QM31],
) -> Result<(), DirectRangeHidingError> {
    if helper.len() != TRACE_ROWS {
        return Err(DirectRangeHidingError::Shape);
    }
    if masks.len() != COPY_HELPER_MASK_VARIABLES {
        return Err(DirectRangeHidingError::PaddingLength {
            expected: COPY_HELPER_MASK_VARIABLES,
            actual: masks.len(),
        });
    }
    let mut sum = QM31::ZERO;
    for (offset, mask) in masks.iter().copied().enumerate() {
        helper[COPY_HELPER_PADDING_ROW_START + offset] = mask;
        sum = sum.add(mask);
    }
    helper[TRACE_ROWS - 1] = QM31::ZERO.sub(sum);
    Ok(())
}

pub fn verify_padded_copy_helper_v4(
    rows: &[CopyLogUpRow],
    helper: &[QM31],
    chi: QM31,
) -> Result<(), DirectRangeHidingError> {
    if rows.len() != TRACE_ROWS || helper.len() != TRACE_ROWS {
        return Err(DirectRangeHidingError::Shape);
    }
    for row in 0..COPY_HELPER_PADDING_ROW_START {
        if copy_logup_residual(rows[row], helper[row], chi) != QM31::ZERO {
            return Err(DirectRangeHidingError::CopyRelation { row: row as u16 });
        }
    }
    let padding_sum = helper[COPY_HELPER_PADDING_ROW_START..]
        .iter()
        .copied()
        .fold(QM31::ZERO, QM31::add);
    if padding_sum != QM31::ZERO {
        return Err(DirectRangeHidingError::PaddingSum);
    }
    let total = helper.iter().copied().fold(QM31::ZERO, QM31::add);
    if total != QM31::ZERO {
        return Err(DirectRangeHidingError::CopyTotal);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        build_spend_trace_v4, derive_nullifier, derive_owner_key, merkle_root, note_commitment,
        output_commitment, Digest, MerklePath, SpendPublic, SpendWitness,
    };
    use aspis_core::field::P;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn spend_fixture() -> (SpendPublic, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let owner_key = derive_owner_key(&nullifier_key);
        let note = note_commitment(&owner_key, value, asset_id, &input_salt);
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
            index: 0x5_4321,
        };
        let public = SpendPublic {
            anchor: merkle_root(note, &merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee: 1,
        };
        let witness = SpendWitness {
            nullifier_key,
            input_salt,
            output_salt,
            output_owner_key,
            input_asset_id: asset_id,
            value,
            value_out,
            merkle_path,
        };
        (public, witness)
    }

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed), M31(seed + 1)),
            c1: CM31::new(M31(seed + 2), M31(seed + 3)),
        }
    }

    #[test]
    fn direct_bits_and_zero_sum_copy_padding_preserve_the_real_witness() {
        let (public, witness) = spend_fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        let lambda = q(101);
        let chi = q(211);
        apply_direct_range_witness_v4(&mut trace).unwrap();
        let c1_cells = direct_range_c1_mask_cells_v4();
        std::eprintln!("direct-range C1 mask cells: {}", c1_cells.len());
        std::eprintln!(
            "direct-range C1 mask fingerprint: {:#018x}",
            direct_range_c1_mask_layout_fingerprint()
        );
        assert_eq!(c1_cells.len(), DIRECT_RANGE_C1_MASK_CELL_COUNT);
        assert_eq!(
            direct_range_c1_mask_layout_fingerprint(),
            PINNED_DIRECT_RANGE_C1_MASK_LAYOUT_FINGERPRINT
        );
        let c1_masks = (0..c1_cells.len())
            .map(|index| M31(((index as u64 * 2_246_822_519 + 0x91a7) % u64::from(P)) as u32))
            .collect::<Vec<_>>();
        apply_direct_range_c1_masks_v4(&mut trace, &c1_masks).unwrap();
        verify_direct_range_c1_mask_sums_v4(&trace).unwrap();
        verify_direct_range_witness_v4(&trace).unwrap();
        for row in 0..TRACE_ROWS {
            assert!(direct_range_row_residuals_v4(&trace, row, q(307))
                .unwrap()
                .iter()
                .all(|value| *value == QM31::ZERO));
        }

        let masks = (0..COPY_HELPER_MASK_VARIABLES)
            .map(|index| q(((index as u64 * 1_103_515_245 + 12_345) % u64::from(P)) as u32))
            .collect::<Vec<_>>();
        let payment_mask = (0..PAYMENT_MASK_ORACLE_VALUES)
            .map(|index| q(10_000 + index as u32 * 7))
            .collect::<Vec<_>>();
        let helpers =
            build_direct_range_hiding_helpers_v4(&trace, lambda, chi, &masks, &payment_mask)
                .unwrap();
        assert_eq!(helpers.payment_mask, payment_mask);
        std::eprintln!(
            "direct range copy slots: r784 p={:?} c={:?}; r785 p={:?} c={:?}; r864 p={:?} c={:?}; r865 p={:?} c={:?}",
            helpers.copy_rows[INPUT_VALUE_RANGE_ROW].producer_weights,
            helpers.copy_rows[INPUT_VALUE_RANGE_ROW].consumer_weights,
            helpers.copy_rows[OUTPUT_VALUE_RANGE_ROW].producer_weights,
            helpers.copy_rows[OUTPUT_VALUE_RANGE_ROW].consumer_weights,
            helpers.copy_rows[DIRECT_RANGE_BIT_ROW_START].producer_weights,
            helpers.copy_rows[DIRECT_RANGE_BIT_ROW_START].consumer_weights,
            helpers.copy_rows[DIRECT_RANGE_BIT_ROW_START + 1].producer_weights,
            helpers.copy_rows[DIRECT_RANGE_BIT_ROW_START + 1].consumer_weights,
        );
        verify_padded_copy_helper_v4(&helpers.copy_rows, &helpers.h1, chi).unwrap();
        assert_eq!(
            direct_range_copy_links_v4()[0].producer_row,
            DIRECT_RANGE_BIT_ROW_START as u16
        );
    }

    #[test]
    fn direct_range_teeth_reject_bad_bit_reconstruction_and_source_copy() {
        let (public, witness) = spend_fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();

        let mut bad_bit = trace.clone();
        apply_direct_range_witness_v4(&mut bad_bit).unwrap();
        bad_bit.c1[0][DIRECT_RANGE_BIT_ROW_START] = M31(2);
        assert!(matches!(
            verify_direct_range_witness_v4(&bad_bit),
            Err(DirectRangeHidingError::Bitness { .. })
        ));

        let mut bad_reconstruction = trace.clone();
        apply_direct_range_witness_v4(&mut bad_reconstruction).unwrap();
        bad_reconstruction.c1[DIRECT_RANGE_RECONSTRUCTION_COLUMN_START]
            [DIRECT_RANGE_BIT_ROW_START] = M31(17);
        assert!(matches!(
            verify_direct_range_witness_v4(&bad_reconstruction),
            Err(DirectRangeHidingError::Reconstruction { .. })
                | Err(DirectRangeHidingError::SourceCopy { .. })
        ));

        let mut bad_source = trace;
        apply_direct_range_witness_v4(&mut bad_source).unwrap();
        bad_source.c1[0][INPUT_VALUE_RANGE_ROW] =
            bad_source.c1[0][INPUT_VALUE_RANGE_ROW].add(M31::ONE);
        assert!(matches!(
            verify_direct_range_witness_v4(&bad_source),
            Err(DirectRangeHidingError::SourceCopy { .. })
        ));
    }
}
