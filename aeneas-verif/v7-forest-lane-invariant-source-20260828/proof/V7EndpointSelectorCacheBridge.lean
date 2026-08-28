import V7ForestLaneInvariant.Funs

/-!
# Exact source bridge for the endpoint-selector cache

The cache is a performance-only refinement. A value can be reused only when
its stored row tag exactly equals the requested endpoint row. Every mismatch,
including a direct-map collision, takes the literal recomputation/replacement
arm. Generated link visitation remains producer first, consumer second.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Aeneas Aeneas.Std Result

namespace V7ForestLaneInvariantGenerated

/-- The sole semantic cache invariant for one requested row. It is established
    by initialization plus the miss/replacement arm and consumed only after an
    exact row-tag equality. -/
def ExactSelectorSlotForRequest
    (slot : EndpointSelectorCacheSlotProjection)
    (requestedRow : Std.U16)
    (literalSelectorValue : Std.U64) : Prop :=
  slot.row_tag = requestedRow -> slot.value_tag = literalSelectorValue

/-- Under the exact tag/value invariant the translated lookup always returns
    the unchanged literal selector, on both hits and misses, and its successor
    slot retains the invariant. -/
theorem translated_cache_lookup_returns_literal
    (slot : EndpointSelectorCacheSlotProjection)
    (requestedRow : Std.U16)
    (literalSelectorValue : Std.U64)
    (result : EndpointSelectorLookupProjection)
    (sound : ExactSelectorSlotForRequest slot requestedRow literalSelectorValue)
    (run : endpoint_selector_cache_lookup_projected slot requestedRow
      literalSelectorValue = .ok result) :
    result.returned_value_tag = literalSelectorValue ∧
      ExactSelectorSlotForRequest result.next_slot requestedRow
        literalSelectorValue := by
  unfold endpoint_selector_cache_lookup_projected at run
  by_cases htag : slot.row_tag = requestedRow
  · simp only [htag, if_true] at run
    cases run
    exact ⟨sound htag, fun _ => sound htag⟩
  · simp only [htag, if_false] at run
    cases run
    exact ⟨rfl, fun _ => rfl⟩

/-- A direct-map collision cannot be a hit. It returns the freshly supplied
    literal value and replaces the slot with the exact requested tag/value. -/
theorem translated_cache_collision_is_literal_miss
    (slot : EndpointSelectorCacheSlotProjection)
    (requestedRow : Std.U16)
    (literalSelectorValue : Std.U64)
    (result : EndpointSelectorLookupProjection)
    (collision : slot.row_tag ≠ requestedRow)
    (run : endpoint_selector_cache_lookup_projected slot requestedRow
      literalSelectorValue = .ok result) :
    result.exact_tag_hit = false ∧
      result.returned_value_tag = literalSelectorValue ∧
      result.next_slot.row_tag = requestedRow ∧
      result.next_slot.value_tag = literalSelectorValue := by
  unfold endpoint_selector_cache_lookup_projected at run
  simp only [collision, if_false] at run
  cases run
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Conversely, the translated hit bit can be true only after exact row-tag
    equality. No hash, truncated tag or slot index is treated as identity. -/
theorem translated_cache_hit_requires_exact_row_tag
    (slot : EndpointSelectorCacheSlotProjection)
    (requestedRow : Std.U16)
    (literalSelectorValue : Std.U64)
    (result : EndpointSelectorLookupProjection)
    (run : endpoint_selector_cache_lookup_projected slot requestedRow
      literalSelectorValue = .ok result)
    (hit : result.exact_tag_hit = true) :
    slot.row_tag = requestedRow := by
  unfold endpoint_selector_cache_lookup_projected at run
  by_cases htag : slot.row_tag = requestedRow
  · exact htag
  · simp only [htag, if_false] at run
    cases run
    contradiction

/-- The translated generated-link projection fixes endpoint order exactly:
    producer first, consumer second. Cache state never reorders or suppresses
    an endpoint. -/
theorem translated_endpoint_order_is_unchanged
    (link : EndpointOrderProjection) :
    endpoint_order_projected link =
      .ok (Array.make 2#usize [link.producer_row, link.consumer_row]) := by
  rfl

#print axioms translated_cache_lookup_returns_literal
#print axioms translated_cache_collision_is_literal_miss
#print axioms translated_cache_hit_requires_exact_row_tag
#print axioms translated_endpoint_order_is_unchanged

end V7ForestLaneInvariantGenerated
