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

#print axioms append_loop_body_stops_at_depth
#print axioms append_loop_body_stops_at_zero_bit
#print axioms append_loop_body_carries_at_one_bit

end PoolV1TreeAppendOneSourceBridge
