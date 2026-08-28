use aspis_core::v6_onefold::V6WireError;
use aspis_core::v7_fixed_canonical_audit::V7CanonicalOneFoldWire;

/// Extraction-only free-function root for the selected inherent parser.
/// No production source is copied or reimplemented here.
pub fn parse_v7_canonical_deferred(
    bytes: &[u8],
    frontier_nodes: usize,
) -> Result<V7CanonicalOneFoldWire<'_>, V6WireError> {
    V7CanonicalOneFoldWire::parse_deferred_query_canonicality(bytes, frontier_nodes)
}
