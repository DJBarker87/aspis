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

/-- Facts supplied by the released preparation path, but not encoded in the
Rust `VerifiedV5PrivateOpenings` structure itself.  The four length bounds are
the released 18-query limit.  The four read facts say that every successful
generated read uses the source position and exact monotone-parent position in
the corresponding mathematical list. -/
structure ReleasedFriTraceInput (openings : Openings) : Prop where
  layer0_count_le : openings.indices.layer0.val.length ≤ 18
  line1_count_le : (line1Indices openings).length ≤ 18
  line2_count_le : (line2Indices openings).length ≤ 18
  line3_count_le : (line3Indices openings).length ≤ 18
  layer0_read_parent_exact :
    ∀ ordinal carried read next,
      fri_checks.trace_v5_fri_layer_zero_read openings ordinal carried =
          ok (.Ok (read, next)) →
        (expectedLayerZeroOrder openings)[ordinal.val]? =
          some (layerZeroOrderOfRead read)
  line1_read_parent_exact :
    ∀ ordinal carried read next,
      fri_checks.trace_v5_fri_line_read openings 0#usize ordinal carried =
          ok (.Ok (read, next)) →
        (expectedLineOrder 1 (line1Indices openings)
          (line2Indices openings))[ordinal.val]? = some (lineOrderOfRead read)
  line2_read_parent_exact :
    ∀ ordinal carried read next,
      fri_checks.trace_v5_fri_line_read openings 1#usize ordinal carried =
          ok (.Ok (read, next)) →
        (expectedLineOrder 2 (line2Indices openings)
          (line3Indices openings))[ordinal.val]? = some (lineOrderOfRead read)
  terminal_read_exact :
    ∀ ordinal read,
      fri_checks.trace_v5_fri_terminal_read openings ordinal = ok (.Ok read) →
        (expectedTerminalOrder (line3Indices openings))[ordinal.val]? =
          some (terminalOrderOfRead read)

/-- Name for the remaining source-to-input obligation.  A later package must
show that the unchanged released parser/preparation path supplies all of the
facts above. -/
def ProductionPreparedFriTraceInputBridge
    (producedByReleasedPreparation : Openings → Prop) : Prop :=
  ∀ openings, producedByReleasedPreparation openings →
    ReleasedFriTraceInput openings

/-- Exact name for the other remaining source seam.  The unchanged production
helper is a `while` loop; this package extracts a recursive spelling from a
temporary copy. -/
def ProductionWhileLoopToTemporaryRecursionBridge
    (productionScan : Slice Std.U32 → Std.Usize → Std.U32 → Result Std.Usize) :
    Prop :=
  ∀ indices ordinal index,
    productionScan indices ordinal index =
      fri_checks.advance_monotone_ordinal indices ordinal index

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

/-- This is why the released length premise is necessary: a successful
diagnostic run records the source count even though its fixed trace has only
18 slots. -/
theorem layer0_count_above_18_cannot_be_exact
    (openings : Openings) (trace : LoopTrace)
    (hcount : trace.layer0_count.val = openings.indices.layer0.val.length)
    (htooMany : 18 < openings.indices.layer0.val.length) :
    ¬ ExactRustV5FriSourceLoopTrace openings trace := by
  intro hexact
  rcases hexact with ⟨hbound, _⟩
  rw [hcount] at hbound
  omega

def PrefixMatches {T A : Type} (project : T → A)
    (trace : FixedTrace18 T) (expected : List A) (count : Nat) : Prop :=
  ((fixedTrace18ToList trace).take count).map project = expected.take count

def repeatedTrace18 {T : Type} (value : T) : FixedTrace18 T where
  v0 := value
  v1 := value
  v2 := value
  v3 := value
  v4 := value
  v5 := value
  v6 := value
  v7 := value
  v8 := value
  v9 := value
  v10 := value
  v11 := value
  v12 := value
  v13 := value
  v14 := value
  v15 := value
  v16 := value
  v17 := value

@[simp] theorem repeated_v5_fri_trace_exact {T : Type}
    (copy : core.marker.Copy T) (value : T) :
    fri_checks.repeated_v5_fri_trace copy value = ok (repeatedTrace18 value) := by
  rfl

@[simp] theorem expectedLayerZeroOrder_length (openings : Openings) :
    (expectedLayerZeroOrder openings).length =
      openings.indices.layer0.val.length := by
  simp [expectedLayerZeroOrder]

@[simp] theorem expectedLineOrder_length (layer : Nat)
    (source target : List Std.U32) :
    (expectedLineOrder layer source target).length = source.length := by
  simp [expectedLineOrder]

@[simp] theorem expectedTerminalOrder_length (source : List Std.U32) :
    (expectedTerminalOrder source).length = source.length := by
  simp [expectedTerminalOrder]

private theorem wrapping_succ_exact_below_18
    (ordinal : Std.Usize) (hordinal : ordinal.val < 18) :
    (Std.Usize.wrapping_add ordinal 1#usize).val = ordinal.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  rw [UScalar.size_UScalarTyUsize]
  have hlarge : 18 < Usize.size := by
    rcases Usize.size_scalarTac_eq with ⟨hsize, _⟩
    rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
    omega
  have hone : (1#usize : Std.Usize).val = 1 := by rfl
  rw [hone]
  omega

private theorem array_index_run
    {T : Type} [Inhabited T] {size : Std.Usize}
    (values : Array T size) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Array.index_usize values index = ok values.val[index.val]! := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem hindex]
  simp only [List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hindex, Option.getD_some]

private theorem prefixMatches_write_succ
    {T A : Type} (project : T → A) (trace output : FixedTrace18 T)
    (expected : List A) (ordinal : Std.Usize) (value : T)
    (hordinal18 : ordinal.val < 18)
    (hordinalExpected : ordinal.val < expected.length)
    (hprefix : PrefixMatches project trace expected ordinal.val)
    (hvalue : expected[ordinal.val]? = some (project value))
    (hwrite : fri_checks.write_v5_fri_trace trace ordinal value = ok output) :
    PrefixMatches project output expected (ordinal.val + 1) := by
  obtain ⟨written, hwritten, hwrittenList⟩ :=
    write_v5_fri_trace_exact trace ordinal value hordinal18
  rw [hwrite] at hwritten
  cases hwritten
  unfold PrefixMatches at hprefix ⊢
  rw [hwrittenList]
  rw [List.take_succ_eq_append_getElem]
  · rw [List.take_succ_eq_append_getElem hordinalExpected]
    rw [List.take_set_of_le (Nat.le_refl ordinal.val)]
    rw [List.getElem_set_self]
    simp only [List.map_append, List.map_singleton]
    rw [hprefix]
    have hget : expected[ordinal.val] = project value := by
      rw [List.getElem?_eq_getElem hordinalExpected] at hvalue
      exact Option.some.inj hvalue
    rw [hget]
  · simpa [fixedTrace18ToList] using hordinal18

private theorem layerZeroPass_prefix
    (openings : Openings) (input : ReleasedFriTraceInput openings)
    (ordinal carried : Std.Usize) (trace output : FixedTrace18 LayerZeroRead)
    (finalCarried : Std.Usize)
    (hordinal : ordinal.val ≤ (expectedLayerZeroOrder openings).length)
    (hprefix : PrefixMatches layerZeroOrderOfRead trace
      (expectedLayerZeroOrder openings) ordinal.val)
    (hrun : fri_checks.trace_v5_fri_layer_zero_pass openings ordinal carried
      trace = ok (.Ok (output, finalCarried))) :
    PrefixMatches layerZeroOrderOfRead output
      (expectedLayerZeroOrder openings)
      (expectedLayerZeroOrder openings).length := by
  rw [fri_checks.trace_v5_fri_layer_zero_pass.eq_1] at hrun
  by_cases hactive : ordinal < alloc.vec.Vec.len openings.indices.layer0
  · rw [if_pos hactive] at hrun
    have hordinalExpected : ordinal.val <
        (expectedLayerZeroOrder openings).length := by
      simpa using hactive
    have hordinal18 : ordinal.val < 18 :=
      lt_of_lt_of_le hordinalExpected (by simpa using input.layer0_count_le)
    generalize hread :
        fri_checks.trace_v5_fri_layer_zero_read openings ordinal carried =
          readResult at hrun
    cases readResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok rustResult =>
      cases rustResult with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at hrun
      | Ok value =>
        rcases value with ⟨read, nextCarried⟩
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
        generalize hwrite :
            fri_checks.write_v5_fri_trace trace ordinal read = writeResult
          at hrun
        cases writeResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok nextTrace =>
          simp only [bind_tc_ok, Std.lift] at hrun
          let nextOrdinal := Std.Usize.wrapping_add ordinal 1#usize
          have hnextVal : nextOrdinal.val = ordinal.val + 1 :=
            wrapping_succ_exact_below_18 ordinal hordinal18
          have hreadExact := input.layer0_read_parent_exact
            ordinal carried read nextCarried hread
          have hnextPrefix : PrefixMatches layerZeroOrderOfRead nextTrace
              (expectedLayerZeroOrder openings) nextOrdinal.val := by
            rw [hnextVal]
            exact prefixMatches_write_succ layerZeroOrderOfRead trace nextTrace
              (expectedLayerZeroOrder openings) ordinal read hordinal18
              hordinalExpected hprefix hreadExact hwrite
          apply layerZeroPass_prefix openings input nextOrdinal nextCarried
            nextTrace output finalCarried
          · rw [hnextVal]
            omega
          · exact hnextPrefix
          · exact hrun
  · rw [if_neg hactive] at hrun
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq]
      at hrun
    rcases hrun with ⟨rfl, rfl⟩
    have hlength : ordinal.val =
        (expectedLayerZeroOrder openings).length := by
      have hnot : ¬ ordinal.val < openings.indices.layer0.val.length := by
        simpa using hactive
      rw [expectedLayerZeroOrder_length] at hordinal ⊢
      exact Nat.le_antisymm hordinal (Nat.le_of_not_gt hnot)
    simpa [hlength] using hprefix
termination_by (expectedLayerZeroOrder openings).length - ordinal.val
decreasing_by
  rw [hnextVal]
  omega

private theorem terminalPass_prefix
    (openings : Openings) (ordinal : Std.Usize)
    (indices : alloc.vec.Vec Std.U32) (expected : List TerminalOrder)
    (trace output : FixedTrace18 TerminalRead)
    (hindices : Array.index_usize openings.indices.later 2#usize = ok indices)
    (hexpectedLength : expected.length = indices.val.length)
    (hcount : expected.length ≤ 18)
    (hreadExact : ∀ readOrdinal read,
      fri_checks.trace_v5_fri_terminal_read openings readOrdinal =
          ok (.Ok read) →
        expected[readOrdinal.val]? = some (terminalOrderOfRead read))
    (hordinal : ordinal.val ≤ expected.length)
    (hprefix : PrefixMatches terminalOrderOfRead trace expected ordinal.val)
    (hrun : fri_checks.trace_v5_fri_terminal_pass openings ordinal trace =
      ok (.Ok output)) :
    PrefixMatches terminalOrderOfRead output expected expected.length := by
  rw [fri_checks.trace_v5_fri_terminal_pass.eq_1, hindices] at hrun
  simp only [bind_tc_ok] at hrun
  by_cases hactive : ordinal < alloc.vec.Vec.len indices
  · rw [if_pos hactive] at hrun
    have hordinalExpected : ordinal.val < expected.length := by
      rw [hexpectedLength]
      simpa using hactive
    have hordinal18 : ordinal.val < 18 :=
      lt_of_lt_of_le hordinalExpected hcount
    generalize hread :
        fri_checks.trace_v5_fri_terminal_read openings ordinal = readResult
      at hrun
    cases readResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok rustResult =>
      cases rustResult with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at hrun
      | Ok read =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
        generalize hwrite :
            fri_checks.write_v5_fri_trace trace ordinal read = writeResult
          at hrun
        cases writeResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok nextTrace =>
          simp only [bind_tc_ok, Std.lift] at hrun
          let nextOrdinal := Std.Usize.wrapping_add ordinal 1#usize
          have hnextVal : nextOrdinal.val = ordinal.val + 1 :=
            wrapping_succ_exact_below_18 ordinal hordinal18
          have hnextPrefix : PrefixMatches terminalOrderOfRead nextTrace
              expected nextOrdinal.val := by
            rw [hnextVal]
            exact prefixMatches_write_succ terminalOrderOfRead trace nextTrace
              expected ordinal read hordinal18 hordinalExpected hprefix
              (hreadExact ordinal read hread) hwrite
          apply terminalPass_prefix openings nextOrdinal indices expected
            nextTrace output hindices hexpectedLength hcount hreadExact
          · rw [hnextVal]
            omega
          · exact hnextPrefix
          · exact hrun
  · rw [if_neg hactive] at hrun
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hrun
    subst output
    have hnot : ¬ ordinal.val < indices.val.length := by
      simpa using hactive
    have hlength : ordinal.val = expected.length := by
      rw [hexpectedLength] at hordinal ⊢
      exact Nat.le_antisymm hordinal (Nat.le_of_not_gt hnot)
    simpa [hlength] using hprefix
termination_by expected.length - ordinal.val
decreasing_by
  rw [hnextVal]
  omega

private theorem linePass_prefix
    (openings : Openings) (layer ordinal carried : Std.Usize)
    (indices : alloc.vec.Vec Std.U32) (expected : List LineOrder)
    (trace output : FixedTrace18 LineRead) (finalCarried : Std.Usize)
    (hindices : Array.index_usize openings.indices.later layer = ok indices)
    (hexpectedLength : expected.length = indices.val.length)
    (hcount : expected.length ≤ 18)
    (hreadExact : ∀ readOrdinal readCarried read nextCarried,
      fri_checks.trace_v5_fri_line_read openings layer readOrdinal
          readCarried = ok (.Ok (read, nextCarried)) →
        expected[readOrdinal.val]? = some (lineOrderOfRead read))
    (hordinal : ordinal.val ≤ expected.length)
    (hprefix : PrefixMatches lineOrderOfRead trace expected ordinal.val)
    (hrun : fri_checks.trace_v5_fri_line_pass openings layer ordinal carried
      trace = ok (.Ok (output, finalCarried))) :
    PrefixMatches lineOrderOfRead output expected expected.length := by
  rw [fri_checks.trace_v5_fri_line_pass.eq_1, hindices] at hrun
  simp only [bind_tc_ok] at hrun
  by_cases hactive : ordinal < alloc.vec.Vec.len indices
  · rw [if_pos hactive] at hrun
    have hordinalExpected : ordinal.val < expected.length := by
      rw [hexpectedLength]
      simpa using hactive
    have hordinal18 : ordinal.val < 18 :=
      lt_of_lt_of_le hordinalExpected hcount
    generalize hread :
        fri_checks.trace_v5_fri_line_read openings layer ordinal carried =
          readResult at hrun
    cases readResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok rustResult =>
      cases rustResult with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at hrun
      | Ok value =>
        rcases value with ⟨read, nextCarried⟩
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
        generalize hwrite :
            fri_checks.write_v5_fri_trace trace ordinal read = writeResult
          at hrun
        cases writeResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok nextTrace =>
          simp only [bind_tc_ok, Std.lift] at hrun
          let nextOrdinal := Std.Usize.wrapping_add ordinal 1#usize
          have hnextVal : nextOrdinal.val = ordinal.val + 1 :=
            wrapping_succ_exact_below_18 ordinal hordinal18
          have hnextPrefix : PrefixMatches lineOrderOfRead nextTrace expected
              nextOrdinal.val := by
            rw [hnextVal]
            exact prefixMatches_write_succ lineOrderOfRead trace nextTrace
              expected ordinal read hordinal18 hordinalExpected hprefix
              (hreadExact ordinal carried read nextCarried hread) hwrite
          apply linePass_prefix openings layer nextOrdinal nextCarried indices
            expected nextTrace output finalCarried hindices hexpectedLength
            hcount hreadExact
          · rw [hnextVal]
            omega
          · exact hnextPrefix
          · exact hrun
  · rw [if_neg hactive] at hrun
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq]
      at hrun
    rcases hrun with ⟨rfl, rfl⟩
    have hnot : ¬ ordinal.val < indices.val.length := by
      simpa using hactive
    have hlength : ordinal.val = expected.length := by
      rw [hexpectedLength] at hordinal ⊢
      exact Nat.le_antisymm hordinal (Nat.le_of_not_gt hnot)
    simpa [hlength] using hprefix
termination_by expected.length - ordinal.val
decreasing_by
  rw [hnextVal]
  omega

/-- The corrected generated-code theorem.  It is universal over all released
inputs that carry the explicit 18-entry and exact-read facts above. -/
theorem ExactGeneratedV5FriSourceLoopTrace
    (openings : Openings) (input : ReleasedFriTraceInput openings)
    (trace : LoopTrace)
    (hrun : fri_checks.trace_v5_fri_reads_after_preparation openings =
      ok (.Ok trace)) :
    ExactRustV5FriSourceLoopTrace openings trace := by
  let layer0Initial : FixedTrace18 LayerZeroRead :=
    repeatedTrace18 fri_checks.EMPTY_LAYER_ZERO_READ
  let lineInitial : FixedTrace18 LineRead :=
    repeatedTrace18 fri_checks.EMPTY_LINE_READ
  let terminalInitial : FixedTrace18 TerminalRead :=
    repeatedTrace18 fri_checks.EMPTY_TERMINAL_READ
  let line1Vec : alloc.vec.Vec Std.U32 :=
    openings.indices.later.val[0]!
  let line2Vec : alloc.vec.Vec Std.U32 :=
    openings.indices.later.val[1]!
  let line3Vec : alloc.vec.Vec Std.U32 :=
    openings.indices.later.val[2]!
  have hindex0 : Array.index_usize openings.indices.later 0#usize =
      ok line1Vec := by
    apply array_index_run
    simp
  have hindex1 : Array.index_usize openings.indices.later 1#usize =
      ok line2Vec := by
    apply array_index_run
    simp
  have hindex2 : Array.index_usize openings.indices.later 2#usize =
      ok line3Vec := by
    apply array_index_run
    simp
  unfold fri_checks.trace_v5_fri_reads_after_preparation at hrun
  simp only [repeated_v5_fri_trace_exact, bind_tc_ok] at hrun
  generalize hpass0 : fri_checks.trace_v5_fri_layer_zero_pass openings
      0#usize 0#usize layer0Initial = pass0Result at hrun
  cases pass0Result with
  | fail error => simp at hrun
  | div => simp at hrun
  | ok rust0 =>
    cases rust0 with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at hrun
    | Ok value0 =>
      rcases value0 with ⟨layer0Out, layer0Carried⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
      generalize hpass1 : fri_checks.trace_v5_fri_line_pass openings
          0#usize 0#usize 0#usize lineInitial = pass1Result at hrun
      cases pass1Result with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok rust1 =>
        cases rust1 with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at hrun
        | Ok value1 =>
          rcases value1 with ⟨line1Out, line1Carried⟩
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
          generalize hpass2 : fri_checks.trace_v5_fri_line_pass openings
              1#usize 0#usize 0#usize lineInitial = pass2Result at hrun
          cases pass2Result with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok rust2 =>
            cases rust2 with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                at hrun
            | Ok value2 =>
              rcases value2 with ⟨line2Out, line2Carried⟩
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
                at hrun
              generalize hpass3 : fri_checks.trace_v5_fri_terminal_pass openings
                  0#usize terminalInitial = pass3Result at hrun
              cases pass3Result with
              | fail error => simp at hrun
              | div => simp at hrun
              | ok rust3 =>
                cases rust3 with
                | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                    at hrun
                | Ok terminalOut =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok] at hrun
                  rw [hindex0, hindex1, hindex2] at hrun
                  simp only [bind_tc_ok, Result.ok.injEq,
                    core.result.Result.Ok.injEq] at hrun
                  subst trace
                  have hlayer0 := layerZeroPass_prefix openings input 0#usize
                    0#usize layer0Initial layer0Out layer0Carried (by simp)
                    (by simp [PrefixMatches]) hpass0
                  unfold PrefixMatches at hlayer0
                  rw [List.take_length] at hlayer0
                  have hline1 := linePass_prefix openings 0#usize 0#usize
                    0#usize line1Vec
                    (expectedLineOrder 1 (line1Indices openings)
                      (line2Indices openings))
                    lineInitial line1Out line1Carried hindex0 (by
                      simp [line1Vec, line1Indices]) (by simpa using
                        input.line1_count_le) input.line1_read_parent_exact
                    (by simp) (by simp [PrefixMatches]) hpass1
                  unfold PrefixMatches at hline1
                  rw [List.take_length] at hline1
                  have hline2 := linePass_prefix openings 1#usize 0#usize
                    0#usize line2Vec
                    (expectedLineOrder 2 (line2Indices openings)
                      (line3Indices openings))
                    lineInitial line2Out line2Carried hindex1 (by
                      simp [line2Vec, line2Indices]) (by simpa using
                        input.line2_count_le) input.line2_read_parent_exact
                    (by simp) (by simp [PrefixMatches]) hpass2
                  unfold PrefixMatches at hline2
                  rw [List.take_length] at hline2
                  have hterminal := terminalPass_prefix openings 0#usize
                    line3Vec (expectedTerminalOrder (line3Indices openings))
                    terminalInitial terminalOut hindex2 (by
                      simp [line3Vec, line3Indices]) (by simpa using
                        input.line3_count_le) input.terminal_read_exact
                    (by simp) (by simp [PrefixMatches]) hpass3
                  unfold PrefixMatches at hterminal
                  rw [List.take_length] at hterminal
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simpa using input.layer0_count_le
                  · simpa [line1Vec, line1Indices] using input.line1_count_le
                  · simpa [line2Vec, line2Indices] using input.line2_count_le
                  · simpa [line3Vec, line3Indices] using input.line3_count_le
                  · simpa [fixedTrace18Prefix] using hlayer0
                  · simpa [fixedTrace18Prefix, line1Vec,
                      line1Indices] using hline1
                  · simpa [fixedTrace18Prefix, line2Vec,
                      line2Indices] using hline2
                  · simpa [fixedTrace18Prefix, line3Vec,
                      line3Indices] using hterminal

#print axioms fixedTrace18ToList_length
#print axioms fixedTrace18Prefix_length

#print axioms write_v5_fri_trace_exact
#print axioms layer0_count_above_18_cannot_be_exact
#print axioms ExactGeneratedV5FriSourceLoopTrace

end V5FriLoopOrderProof
