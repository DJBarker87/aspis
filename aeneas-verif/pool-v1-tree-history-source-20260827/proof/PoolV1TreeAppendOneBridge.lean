import PoolV1TreeAppendOne.Funs
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 production one-append source bridge

The focused Charon/Aeneas translation is transparent through validation,
binary carry, root reconstruction, receipt construction, and the public
`append_one_with_empty_roots` wrapper.  This first bridge records the exact
three-way semantics of one translated carry-loop step.  The only semantic
premise is the explicitly named Poseidon tree-parent callback boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1TreeAppendOneSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeAppendOneGenerated

abbrev Digest := Array Std.U32 8#usize
abbrev GeneratedValidatedTree :=
  aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1

def ParentCallbackExact (parent : Digest → Digest → Digest) : Prop :=
  ∀ left right,
    aspis_statement.pool_v1.format.pool_v1_tree_parent left right =
      .ok (parent left right)

theorem carry_bit_one_iff_shifted_quotient_odd
    (leafIndex shifted : Std.U64) (level : Std.Usize)
    (hlevel : level.val < 20)
    (hshift : leafIndex >>> level = .ok shifted) :
    shifted &&& 1#u64 = 1#u64 ↔
      (leafIndex.val >>> level.val) % 2 = 1 := by
  have hspec := Std.U64.ShiftRight_spec leafIndex level (by omega)
  rw [hshift] at hspec
  have hshiftVal : shifted.val = leafIndex.val >>> level.val := hspec.1
  have hand : (shifted &&& 1#u64).val = shifted.val % 2 := by
    rw [UScalar.val_and]
    norm_num [Nat.and_one_is_mod]
  constructor
  · intro hbit
    have hval := congrArg UScalar.val hbit
    rw [hand] at hval
    norm_num at hval
    rwa [hshiftVal] at hval
  · intro hodd
    apply UScalar.eq_of_val_eq
    rw [hand, hshiftVal, hodd]
    norm_num

theorem append_loop_body_stops_at_depth
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (frontier : Array Digest 20#usize)
    (carry : Digest)
    (level : Std.Usize)
    (hlevel : 20 ≤ level.val) :
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
        self leafIndex frontier carry level =
      .ok (.done (frontier, carry, level)) := by
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
  simp only [aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH, bind_tc_ok]
  simp [UScalar.lt_equiv, hlevel]

theorem append_loop_body_stops_at_zero_bit
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (frontier : Array Digest 20#usize)
    (carry : Digest)
    (level : Std.Usize)
    (shifted : Std.U64)
    (hlevel : level.val < 20)
    (hshift : leafIndex >>> level = .ok shifted)
    (hbit : shifted &&& 1#u64 = 0#u64) :
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
        self leafIndex frontier carry level =
      .ok (.done (frontier, carry, level)) := by
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
  simp only [aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH, bind_tc_ok]
  simp [UScalar.lt_equiv, hlevel, hshift, hbit, lift]

theorem append_loop_body_stops_at_nonone_bit
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (frontier : Array Digest 20#usize)
    (carry : Digest)
    (level : Std.Usize)
    (shifted : Std.U64)
    (hlevel : level.val < 20)
    (hshift : leafIndex >>> level = .ok shifted)
    (hbit : shifted &&& 1#u64 ≠ 1#u64) :
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
        self leafIndex frontier carry level =
      .ok (.done (frontier, carry, level)) := by
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
  simp only [aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH, bind_tc_ok]
  simp [UScalar.lt_equiv, hlevel, hshift, hbit, lift]

theorem append_loop_body_carries_at_one_bit
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (frontier : Array Digest 20#usize)
    (carry : Digest)
    (level : Std.Usize)
    (shifted : Std.U64)
    (hlevel : level.val < 20)
    (hshift : leafIndex >>> level = .ok shifted)
    (hbit : shifted &&& 1#u64 = 1#u64) :
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
        self leafIndex frontier carry level
      ⦃ flow => ∃ left emptyAtLevel nextFrontier nextLevel,
          flow = .cont (nextFrontier, parent left carry, nextLevel) ∧
          left = frontier.val.get ⟨level.val, by
            simpa [frontier.property] using hlevel⟩ ∧
          emptyAtLevel = self.empty.val.get ⟨level.val, by
            simpa [self.empty.property] using (show level.val < 21 by omega)⟩ ∧
          nextFrontier = frontier.set level emptyAtLevel ∧
          nextLevel.val = level.val + 1 ⦄ := by
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
  simp only [aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH, bind_tc_ok]
  simp only [UScalar.lt_equiv, hshift, hbit, bind_tc_ok]
  simp [hlevel, lift]
  apply WP.spec_bind
  · exact Array.index_usize_spec frontier level (by simpa [frontier.property])
  intro left hleft
  rw [parentExact left carry]
  simp only [bind_tc_ok]
  apply WP.spec_bind
  · exact Array.index_usize_spec self.empty level (by
      simpa [self.empty.property] using (show level.val < 21 by omega))
  intro emptyAtLevel hempty
  apply WP.spec_bind
  · exact Array.update_spec frontier level emptyAtLevel (by
      simpa [frontier.property])
  intro nextFrontier hfrontier
  apply WP.spec_bind
  · apply Usize.add_spec
    scalar_tac
  intro nextLevel hnext
  simp only [WP.spec_ok]
  refine ⟨nextLevel, ?_, ?_⟩
  · rw [hleft, hfrontier, hempty]
  · simpa using hnext

abbrev CarryState := Array Digest 20#usize × Digest × Std.Usize

def CarryTerminal (leafIndex : Std.U64) (state : CarryState) : Prop :=
  20 ≤ state.2.2.val ∨
    ∃ shifted : Std.U64,
      state.2.2.val < 20 ∧
      leafIndex >>> state.2.2 = .ok shifted ∧
      shifted &&& 1#u64 ≠ 1#u64

def CarryStep (parent : Digest → Digest → Digest)
    (self : GeneratedValidatedTree) (leafIndex : Std.U64)
    (before after : CarryState) : Prop :=
  ∃ (hlevel : before.2.2.val < 20) (shifted : Std.U64),
    leafIndex >>> before.2.2 = .ok shifted ∧
    shifted &&& 1#u64 = 1#u64 ∧
    ∃ left : Digest,
      left = before.1.val.get ⟨before.2.2.val, by
        simpa [before.1.property] using hlevel⟩ ∧
      ∃ emptyAtLevel : Digest,
        emptyAtLevel = self.empty.val.get ⟨before.2.2.val, by
          simpa [self.empty.property] using
            (show before.2.2.val < 21 by omega)⟩ ∧
        ∃ nextLevel : Std.Usize,
          nextLevel.val = before.2.2.val + 1 ∧
          after =
            (before.1.set before.2.2 emptyAtLevel,
              parent left before.2.1, nextLevel)

inductive CarryPrefix (parent : Digest → Digest → Digest)
    (self : GeneratedValidatedTree) (leafIndex : Std.U64) :
    CarryState → CarryState → Prop where
  | refl (state : CarryState) : CarryPrefix parent self leafIndex state state
  | snoc {start middle finish : CarryState} :
      CarryPrefix parent self leafIndex start middle →
      CarryStep parent self leafIndex middle finish →
      CarryPrefix parent self leafIndex start finish

inductive CarryTrace (parent : Digest → Digest → Digest)
    (self : GeneratedValidatedTree) (leafIndex : Std.U64) :
    CarryState → CarryState → Prop where
  | terminal {state : CarryState} :
      CarryTerminal leafIndex state →
      CarryTrace parent self leafIndex state state
  | step {before next final : CarryState} :
      CarryStep parent self leafIndex before next →
      CarryTrace parent self leafIndex next final →
      CarryTrace parent self leafIndex before final

theorem CarryPrefix.prependTrace
    {parent : Digest → Digest → Digest}
    {self : GeneratedValidatedTree} {leafIndex : Std.U64}
    {start middle final : CarryState}
    (path : CarryPrefix parent self leafIndex start middle)
    (trace : CarryTrace parent self leafIndex middle final) :
    CarryTrace parent self leafIndex start final := by
  induction path with
  | refl => exact trace
  | snoc path oneStep inductionHypothesis =>
      exact inductionHypothesis (CarryTrace.step oneStep trace)

private theorem append_loop_body_trace_spec
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (state : CarryState) :
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop.body
        self leafIndex state.1 state.2.1 state.2.2
      ⦃ flow => match flow with
        | .done final => final = state ∧ CarryTerminal leafIndex state
        | .cont next =>
            CarryStep parent self leafIndex state next ∧
              20 - next.2.2.val < 20 - state.2.2.val ⦄ := by
  rcases state with ⟨frontier, carry, level⟩
  simp only
  by_cases hlevel : level.val < 20
  · have shiftSpec := Std.U64.ShiftRight_spec leafIndex level (by omega)
    obtain ⟨shifted, hshift, _⟩ := WP.spec_imp_exists shiftSpec
    by_cases hbit : shifted &&& 1#u64 = 1#u64
    · apply WP.spec_mono
        (append_loop_body_carries_at_one_bit parent parentExact self leafIndex
          frontier carry level shifted hlevel hshift hbit)
      intro flow hflow
      rcases hflow with
        ⟨left, emptyAtLevel, nextFrontier, nextLevel, rfl, hleft, hempty,
          hfrontier, hnext⟩
      constructor
      · refine ⟨hlevel, shifted, hshift, hbit, left, hleft,
          emptyAtLevel, hempty, nextLevel, hnext, ?_⟩
        rw [hfrontier]
      · change 20 - nextLevel.val < 20 - level.val
        omega
    · rw [append_loop_body_stops_at_nonone_bit self leafIndex frontier carry
        level shifted hlevel hshift hbit]
      simp only [WP.spec_ok]
      exact ⟨True.intro, Or.inr ⟨shifted, hlevel, hshift, hbit⟩⟩
  · rw [append_loop_body_stops_at_depth self leafIndex frontier carry level
      (by omega)]
    simp only [WP.spec_ok]
    refine ⟨True.intro, Or.inl ?_⟩
    change 20 ≤ level.val
    omega

theorem append_loop_has_exact_source_trace
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (initial : CarryState) :
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
        self leafIndex initial.1 initial.2.1 initial.2.2
      ⦃ final =>
        CarryPrefix parent self leafIndex initial final ∧
          CarryTerminal leafIndex final ⦄ := by
  rcases initial with ⟨initialFrontier, initialCarry, initialLevel⟩
  let initialState : CarryState :=
    (initialFrontier, initialCarry, initialLevel)
  change
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
        self leafIndex initialFrontier initialCarry initialLevel
      ⦃ final =>
        CarryPrefix parent self leafIndex initialState final ∧
          CarryTerminal leafIndex final ⦄
  unfold
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
  apply loop.spec_decr_nat
    (measure := fun state : CarryState => 20 - state.2.2.val)
    (inv := fun state => CarryPrefix parent self leafIndex initialState state)
    (post := fun final =>
      CarryPrefix parent self leafIndex initialState final ∧
        CarryTerminal leafIndex final)
  · intro state path
    rcases state with ⟨frontier, carry, level⟩
    simp only at path ⊢
    apply WP.spec_mono
      (append_loop_body_trace_spec parent parentExact self leafIndex
        (frontier, carry, level))
    intro flow hflow
    cases flow with
    | done final =>
        rcases hflow with ⟨rfl, terminal⟩
        exact ⟨path, terminal⟩
    | cont next =>
        exact ⟨CarryPrefix.snoc path hflow.1, hflow.2⟩
  · simpa [initialState] using
      (CarryPrefix.refl initialState :
        CarryPrefix parent self leafIndex initialState initialState)

theorem append_loop_has_recursive_source_trace
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (initial : CarryState) :
    aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
        self leafIndex initial.1 initial.2.1 initial.2.2
      ⦃ final => CarryTrace parent self leafIndex initial final ⦄ := by
  apply WP.spec_mono
    (append_loop_has_exact_source_trace parent parentExact self leafIndex initial)
  intro final result
  exact result.1.prependTrace (CarryTrace.terminal result.2)

#print axioms append_loop_body_stops_at_depth
#print axioms carry_bit_one_iff_shifted_quotient_odd
#print axioms append_loop_body_stops_at_zero_bit
#print axioms append_loop_body_stops_at_nonone_bit
#print axioms append_loop_body_carries_at_one_bit
#print axioms append_loop_has_exact_source_trace
#print axioms append_loop_has_recursive_source_trace

end PoolV1TreeAppendOneSourceBridge
