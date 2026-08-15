#![no_std]

/// Extraction witness for the two slice expressions in
/// `AtomicSemanticSelectors::at_point`.
pub fn atomic_semantic_selector_coordinate_slices<T>(point: &[T; 10]) -> (&[T], &[T]) {
    (&point[..6], &point[6..])
}
