import V7Tag73CurrentParser.Funs

/-!
# Current Tag-73 deferred-parser source bridge

The imported definitions were generated from the exact `f45c21b1` production
`v7_onefold.rs`, with only the archived extraction wrapper patch applied in an
isolated Charon workspace.  The wrapper calls the deployed inherent parser
directly, so its source correspondence is definitional rather than axiomatic.
-/

set_option autoImplicit false

namespace AspisV7Tag73CurrentParserSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7Tag73CurrentParserGenerated

theorem extracted_entry_is_exact_deferred_parser
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize) :
    v7_onefold.parse_v7_compact_onefold_wire_deferred bytes frontierNodes =
      v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
        bytes frontierNodes := by
  rfl

theorem extracted_parser_rejects_oversized_frontier
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (oversized : frontierNodes > 203#usize) :
    v7_onefold.parse_v7_compact_onefold_wire_deferred bytes frontierNodes =
      ok (.Err v6_onefold.V6WireError.FrontierTooLarge) := by
  simp [v7_onefold.parse_v7_compact_onefold_wire_deferred,
    v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality,
    v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE, oversized]

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

end AspisV7Tag73CurrentParserSourceBridge
