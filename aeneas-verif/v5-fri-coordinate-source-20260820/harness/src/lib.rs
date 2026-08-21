use aspis_core::circle_fri::{
    derive_query_fold_inverses_for_circle, CircleFriError, DerivedCircleQueryFoldInverses,
};
use aspis_core::field::M31;

/// Source-shaped entry point with the exact inverse backend used by the V5
/// verifier. Keeping the five input slices separate avoids hiding their layer
/// order behind a test fixture or a precomputed table.
pub fn derive_released_query_fold_inverses(
    domain_log_size: u32,
    layer0: &[u32],
    line1: &[u32],
    line2: &[u32],
    line3: &[u32],
) -> Result<DerivedCircleQueryFoldInverses, CircleFriError> {
    derive_query_fold_inverses_for_circle(
        domain_log_size,
        layer0,
        [line1, line2, line3],
        M31::inv,
    )
}
