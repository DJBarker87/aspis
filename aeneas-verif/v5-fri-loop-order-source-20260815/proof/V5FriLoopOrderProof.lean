import V5FriLoopOrder.Funs
import Mathlib

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5FriLoopOrderProof

open V5FriLoopOrderGenerated

abbrev FixedTrace18 := fri_checks.V5FriFixedTrace18
abbrev LayerZeroRead := fri_checks.V5FriLayerZeroReadTrace
abbrev LineRead := fri_checks.V5FriLineReadTrace
abbrev TerminalRead := fri_checks.V5FriTerminalReadTrace
abbrev LoopTrace := fri_checks.V5FriLoopReadTrace
abbrev Openings := private_openings.VerifiedV5PrivateOpenings

/-- The mathematical list view of the extraction-only fixed-capacity trace.
Only the prefix selected by the corresponding count is part of a run. -/
def fixedTrace18ToList {T : Type} (trace : FixedTrace18 T) : List T :=
  [trace.v0, trace.v1, trace.v2, trace.v3, trace.v4, trace.v5,
    trace.v6, trace.v7, trace.v8, trace.v9, trace.v10, trace.v11,
    trace.v12, trace.v13, trace.v14, trace.v15, trace.v16, trace.v17]

def fixedTrace18Prefix {T : Type} (trace : FixedTrace18 T)
    (count : Std.Usize) : List T :=
  (fixedTrace18ToList trace).take count.val

structure LayerZeroOrder where
  query : Nat
  ordinal : Nat
  parentIndex : Nat
  parentOrdinal : Nat
  slot : Nat
  deriving DecidableEq

structure LineOrder where
  layer : Nat
  index : Nat
  ordinal : Nat
  parentIndex : Nat
  parentOrdinal : Nat
  slot : Nat
  deriving DecidableEq

structure TerminalOrder where
  index : Nat
  ordinal : Nat
  deriving DecidableEq

def layerZeroOrderOfRead (read : LayerZeroRead) : LayerZeroOrder where
  query := read.query.val
  ordinal := read.ordinal.val
  parentIndex := read.parent_index.val
  parentOrdinal := read.parent_ordinal.val
  slot := read.parent_slot.val

def lineOrderOfRead (read : LineRead) : LineOrder where
  layer := read.layer.val
  index := read.index.val
  ordinal := read.ordinal.val
  parentIndex := read.parent_index.val
  parentOrdinal := read.parent_ordinal.val
  slot := read.slot.val

def terminalOrderOfRead (read : TerminalRead) : TerminalOrder where
  index := read.index.val
  ordinal := read.ordinal.val

def u32Values (values : List Std.U32) : List Nat :=
  values.map (fun value => value.val)

def line1Indices (openings : Openings) : List Std.U32 :=
  (openings.indices.later.val[0]!).val

def line2Indices (openings : Openings) : List Std.U32 :=
  (openings.indices.later.val[1]!).val

def line3Indices (openings : Openings) : List Std.U32 :=
  (openings.indices.later.val[2]!).val

def expectedLayerZeroOrder (openings : Openings) : List LayerZeroOrder :=
  openings.indices.layer0.val.mapIdx fun ordinal query =>
    { query := query.val
      ordinal := ordinal
      parentIndex := query.val / 4
      parentOrdinal := (u32Values (line1Indices openings)).idxOf
        (query.val / 4)
      slot := query.val % 4 }

def expectedLineOrder (layer : Nat) (source target : List Std.U32) :
    List LineOrder :=
  source.mapIdx fun ordinal index =>
    { layer := layer
      index := index.val
      ordinal := ordinal
      parentIndex := index.val / 4
      parentOrdinal := (u32Values target).idxOf (index.val / 4)
      slot := index.val % 4 }

def expectedTerminalOrder (source : List Std.U32) : List TerminalOrder :=
  source.mapIdx fun ordinal index =>
    { index := index.val, ordinal := ordinal }

/-- Public shape expected by the maintained theorem
`ExactRustV5FriSourceLoopTrace`.  This package records order metadata; the
existing extracted value accessor and monotone-lookup proof supply the byte
slices and exact parent ordinal under their sorted-list hypotheses. -/
def ExactRustV5FriSourceLoopTrace (openings : Openings) (trace : LoopTrace) :
    Prop :=
  trace.layer0_count.val ≤ 18 ∧
  trace.line1_count.val ≤ 18 ∧
  trace.line2_count.val ≤ 18 ∧
  trace.line3_count.val ≤ 18 ∧
  (fixedTrace18Prefix trace.layer0_to_line1 trace.layer0_count).map
      layerZeroOrderOfRead = expectedLayerZeroOrder openings ∧
  (fixedTrace18Prefix trace.line1_to_line2 trace.line1_count).map
      lineOrderOfRead = expectedLineOrder 1 (line1Indices openings)
        (line2Indices openings) ∧
  (fixedTrace18Prefix trace.line2_to_line3 trace.line2_count).map
      lineOrderOfRead = expectedLineOrder 2 (line2Indices openings)
        (line3Indices openings) ∧
  (fixedTrace18Prefix trace.line3_to_final trace.line3_count).map
      terminalOrderOfRead = expectedTerminalOrder (line3Indices openings)

/-- The one remaining universal generated-code obligation.  Keeping it as a
named proposition is deliberate: extraction and replay do not turn a desired
source correspondence into a theorem by declaration. -/
def ExactGeneratedV5FriSourceLoopTrace : Prop :=
  ∀ openings trace,
    fri_checks.trace_v5_fri_reads_after_preparation openings =
      ok (.Ok trace) →
    ExactRustV5FriSourceLoopTrace openings trace

/-- The generated fixed-capacity writer changes exactly the selected slot.
This is the mechanical fact needed by an induction over each recursive pass. -/
theorem write_v5_fri_trace_exact
    {T : Type} (trace : FixedTrace18 T) (ordinal : Std.Usize) (value : T)
    (hordinal : ordinal.val < 18) :
    ∃ output,
      fri_checks.write_v5_fri_trace trace ordinal value = ok output ∧
      fixedTrace18ToList output =
        (fixedTrace18ToList trace).set ordinal.val value := by
  unfold fri_checks.write_v5_fri_trace
  interval_cases h : ordinal.val <;>
    simp_all [fixedTrace18ToList, List.set]

@[simp] theorem fixedTrace18ToList_length {T : Type}
    (trace : FixedTrace18 T) :
    (fixedTrace18ToList trace).length = 18 := by
  simp [fixedTrace18ToList]

theorem fixedTrace18Prefix_length {T : Type} (trace : FixedTrace18 T)
    (count : Std.Usize) (hcount : count.val ≤ 18) :
    (fixedTrace18Prefix trace count).length = count.val := by
  simp [fixedTrace18Prefix, hcount]

#print axioms fixedTrace18ToList_length
#print axioms fixedTrace18Prefix_length

#print axioms write_v5_fri_trace_exact

end V5FriLoopOrderProof
