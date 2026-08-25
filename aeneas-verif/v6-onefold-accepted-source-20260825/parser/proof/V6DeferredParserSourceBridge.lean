import V6DeferredParser.Funs

/-!
# V6 production deferred-parser source bridge

The imported definitions are generated from the production
`parse_v6_onefold_wire_deferred` call graph. The six Rust core-library calls
left external by Charon have transparent definitions in
`V6DeferredParser.FunsExternal`; this file adds no parser axiom.
-/

namespace AspisV6DeferredParserSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V6DeferredParserGenerated

/-- The public extraction root and the translated structural parser are the
same computation, through the two inlined Rust wrappers. -/
theorem extracted_entry_is_exact_layout_parser
    (bytes : Slice Std.U8) (c1FrontierNodes c2FrontierNodes : Std.Usize) :
    v6_onefold.parse_v6_onefold_wire_deferred
        bytes c1FrontierNodes c2FrontierNodes =
      v6_onefold.V6OneFoldWire.parse_layout
        bytes c1FrontierNodes c2FrontierNodes := by
  rfl

/-- Oversized C1 frontiers are rejected before any byte slicing. -/
theorem extracted_parser_rejects_oversized_c1
    (bytes : Slice Std.U8) (c1FrontierNodes c2FrontierNodes : Std.Usize)
    (oversized : c1FrontierNodes > 209#usize) :
    v6_onefold.parse_v6_onefold_wire_deferred
        bytes c1FrontierNodes c2FrontierNodes =
      ok (.Err v6_onefold.V6WireError.FrontierTooLarge) := by
  simp [v6_onefold.parse_v6_onefold_wire_deferred,
    v6_onefold.V6OneFoldWire.parse_deferred_canonicality,
    v6_onefold.V6OneFoldWire.parse_layout,
    v6_onefold.V6_FRONTIER_CAP_PER_TREE, oversized]

/-- Oversized C2 frontiers are rejected whenever C1 passed the cap. -/
theorem extracted_parser_rejects_oversized_c2
    (bytes : Slice Std.U8) (c1FrontierNodes c2FrontierNodes : Std.Usize)
    (c1Within : ¬c1FrontierNodes > 209#usize)
    (oversized : c2FrontierNodes > 209#usize) :
    v6_onefold.parse_v6_onefold_wire_deferred
        bytes c1FrontierNodes c2FrontierNodes =
      ok (.Err v6_onefold.V6WireError.FrontierTooLarge) := by
  simp [v6_onefold.parse_v6_onefold_wire_deferred,
    v6_onefold.V6OneFoldWire.parse_deferred_canonicality,
    v6_onefold.V6OneFoldWire.parse_layout,
    v6_onefold.V6_FRONTIER_CAP_PER_TREE, c1Within, oversized]

/-- Any successful translated entry call is exactly a successful execution of
the structural parser body; no wrapper can turn an error into acceptance. -/
theorem extracted_parser_success_is_layout_success
    (bytes : Slice Std.U8) (c1FrontierNodes c2FrontierNodes : Std.Usize)
    (wire : v6_onefold.V6OneFoldWire)
    (accepted :
      v6_onefold.parse_v6_onefold_wire_deferred
          bytes c1FrontierNodes c2FrontierNodes = ok (.Ok wire)) :
    v6_onefold.V6OneFoldWire.parse_layout
        bytes c1FrontierNodes c2FrontierNodes = ok (.Ok wire) := by
  simpa [extracted_entry_is_exact_layout_parser] using accepted

#print axioms extracted_entry_is_exact_layout_parser
#print axioms extracted_parser_rejects_oversized_c1
#print axioms extracted_parser_rejects_oversized_c2
#print axioms extracted_parser_success_is_layout_success

end AspisV6DeferredParserSourceBridge
