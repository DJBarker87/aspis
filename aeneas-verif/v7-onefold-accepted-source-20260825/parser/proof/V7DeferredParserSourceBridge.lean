import V7DeferredParser.Funs

/-!
# V7 deferred-parser extraction bridge

The imported definitions are generated from an extraction-only free wrapper
around the byte-identical deployed inherent parser body.  The five Rust
core-library calls left external by Charon have transparent definitions in
`V7DeferredParser.FunsExternal`; this file adds no parser axiom.  Equivalence
of the free wrapper to the inherent method is definitional (`rfl`).
-/

set_option autoImplicit false

namespace AspisV7DeferredParserSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7DeferredParserGenerated

/-- The extraction-only entry and the translated deployed inherent parser are
the same computation. -/
theorem extracted_entry_is_exact_deferred_parser
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize) :
    v7_onefold.parse_v7_compact_onefold_wire_deferred bytes frontierNodes =
      v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
        bytes frontierNodes := by
  rfl

/-- Frontiers over the deployed cap of 203 nodes are rejected before byte
slicing. -/
theorem extracted_parser_rejects_oversized_frontier
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (oversized : frontierNodes > 203#usize) :
    v7_onefold.parse_v7_compact_onefold_wire_deferred bytes frontierNodes =
      ok (.Err v6_onefold.V6WireError.FrontierTooLarge) := by
  simp [v7_onefold.parse_v7_compact_onefold_wire_deferred,
    v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality,
    v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE, oversized]

/-- Any successful extraction entry is exactly a successful execution of the
translated deployed parser body. -/
theorem extracted_parser_success_is_deployed_parser_success
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (wire : v7_onefold.V7CompactOneFoldWire)
    (accepted :
      v7_onefold.parse_v7_compact_onefold_wire_deferred
          bytes frontierNodes = ok (.Ok wire)) :
    v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
        bytes frontierNodes = ok (.Ok wire) := by
  simpa [extracted_entry_is_exact_deferred_parser] using accepted

#print axioms extracted_entry_is_exact_deferred_parser
#print axioms extracted_parser_rejects_oversized_frontier
#print axioms extracted_parser_success_is_deployed_parser_success

end AspisV7DeferredParserSourceBridge
