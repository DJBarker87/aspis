import V7ForestLaneInvariant.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ForestLaneInvariantGenerated

/-- Exact accepted-source relation for fresh lane-PDA initialization. -/
structure GenesisWriteRelation
    (master : Array Std.U8 32#usize)
    (lane_id : Std.U8)
    (out : LaneState)
    (empty_roots : Array Digest 21#usize) : Prop where
  master_nonzero : bytes32_nonzero master = ok true
  lane_in_range :
    ∃ lane_usize : Std.Usize,
      core.convert.num.FromUsizeU8.from lane_id = lane_usize ∧
      lane_usize < LANE_COUNT
  frontier_image : ∃ frontier,
    genesis_frontier empty_roots = ok frontier ∧
    out.frontier = frontier
  root_image : ∃ root,
    Array.index_usize empty_roots TREE_DEPTH = ok root ∧
    out.root = root
  master_exact : out.master = master
  lane_exact : out.lane_id = lane_id
  index_zero : out.next_leaf_index = 0#u64

/-- Exact accepted-source relation for a checked deposit lane mutation. -/
structure CheckedDepositWriteRelation
    (before after out : LaneState)
    (append_checked : Bool)
    (empty_roots : Array Digest 21#usize) : Prop where
  output_eq : out = after
  append_was_checked : append_checked = true
  master_preserved : before.master = after.master
  lane_preserved : before.lane_id = after.lane_id
  index_advanced :
    U64.checked_add before.next_leaf_index 1#u64 =
      some after.next_leaf_index
  fast_image_exists :
    ∃ bytes : Array Std.U8 768#usize,
      fast_encode_projected after empty_roots true = ok (.Ok bytes)

/-- Exact accepted-source relation for authenticated ASR8 settlement. -/
structure AuthenticatedSettlementWriteRelation
    (before after out : LaneState)
    (asr8_authenticated : Bool)
    (empty_roots : Array Digest 21#usize) : Prop where
  output_eq : out = after
  result_was_authenticated : asr8_authenticated = true
  master_preserved : before.master = after.master
  lane_preserved : before.lane_id = after.lane_id
  index_advanced :
    U64.checked_add before.next_leaf_index 1#u64 =
      some after.next_leaf_index
  fast_image_exists :
    ∃ bytes : Array Std.U8 768#usize,
      fast_encode_projected after empty_roots true = ok (.Ok bytes)

theorem partial_eq_u8_array_ne_false_implies_eq
    (left right : Array Std.U8 32#usize)
    (hrun :
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          left right = ok false) :
    left = right := by
  have hiff : left.to_slice = right.to_slice ↔ left = right := by
    constructor
    · intro h
      apply List.Vector.eq
      exact (Slice.eq_iff left.to_slice right.to_slice).mp h
    · intro h
      subst right
      rfl
  have hspec :
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          left right ⦃ b => b ↔ left ≠ right ⦄ := by
    unfold core.array.equality.PartialEqArray.ne
    apply WP.spec_bind
    · have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec
          core.cmp.PartialEqU8 left.to_slice right.to_slice (by
            intro x y
            simp [liftFun2, WP.spec_ok])
      simpa [core.array.equality.PartialEqArray.eq,
        core.slice.cmp.PartialEqSlice.eq, Array.to_slice] using hs
    · intro eqb heqb
      simp only [WP.spec_ok]
      cases eqb with
      | false =>
          have hsne : ¬ left.to_slice = right.to_slice := by
            intro hs
            have : false = true := heqb.mpr hs
            simp at this
          have habne : left ≠ right := fun hab => hsne (hiff.mpr hab)
          simpa using habne
      | true =>
          have hseq : left.to_slice = right.to_slice := heqb.mp (by rfl)
          have hab : left = right := hiff.mp hseq
          simp [hab]
  rw [hrun] at hspec
  simpa using hspec

theorem option_u64_ne_false_implies_eq
    (left right : Option Std.U64)
    (hrun :
      core.cmp.PartialEq.ne.trait_default
          (core.option.Option.Insts.CoreCmpPartialEqOption
            core.cmp.PartialEqU64)
          left right = ok false) :
    left = right := by
  cases left <;> cases right <;>
    simp [core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      liftFun2] at hrun ⊢
  exact hrun

theorem initialization_success_has_exact_source_relation
    (master : Array Std.U8 32#usize)
    (lane_id : Std.U8)
    (out : LaneState)
    (empty_roots : Array Digest 21#usize)
    (hrun :
      apply_production_lane_write (.Initialize master lane_id) empty_roots =
        ok (.Ok out)) :
    GenesisWriteRelation master lane_id out empty_roots := by
  unfold apply_production_lane_write at hrun
  generalize hnonzero : bytes32_nonzero master = nonzeroResult at hrun
  cases nonzeroResult with
  | fail error => simp [hnonzero, Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [hnonzero, Bind.bind, Aeneas.Std.bind] at hrun
  | ok nonzero =>
      cases nonzero with
      | false => simp [hnonzero, Bind.bind, Aeneas.Std.bind] at hrun
      | true =>
          let lane_usize := core.convert.num.FromUsizeU8.from lane_id
          have hcast : lane_usize.val = lane_id.val := by
            change (UScalar.cast .Usize lane_id).val = lane_id.val
            exact U8.cast_Usize_val_eq lane_id
          by_cases hrange : lane_usize < LANE_COUNT
          · simp [hnonzero, lane_usize, hrange, lift, Bind.bind,
              Aeneas.Std.bind] at hrun
            have hcondition : ¬ LANE_COUNT.val ≤ lane_id.val := by
              have hrangeNat : lane_usize.val < LANE_COUNT.val := hrange
              omega
            simp [hcondition] at hrun
            generalize hfrontier :
              genesis_frontier empty_roots = frontierResult at hrun
            cases frontierResult with
            | fail error => simp [hfrontier, Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [hfrontier, Bind.bind, Aeneas.Std.bind] at hrun
            | ok frontier =>
                generalize hroot :
                  Array.index_usize empty_roots TREE_DEPTH = rootResult at hrun
                cases rootResult with
                | fail error => simp [hroot, Bind.bind, Aeneas.Std.bind] at hrun
                | div => simp [hroot, Bind.bind, Aeneas.Std.bind] at hrun
                | ok root =>
                    simp [hroot, Bind.bind, Aeneas.Std.bind] at hrun
                    have hout : out = {
                        master := master
                        lane_id := lane_id
                        next_leaf_index := 0#u64
                        root := root
                        frontier := frontier
                      } := by simpa using hrun.symm
                    subst out
                    exact {
                      master_nonzero := hnonzero
                      lane_in_range := ⟨lane_usize, rfl, hrange⟩
                      frontier_image := ⟨frontier, hfrontier, rfl⟩
                      root_image := ⟨root, hroot, rfl⟩
                      master_exact := rfl
                      lane_exact := rfl
                      index_zero := rfl
                    }
          · simp [hnonzero, lane_usize, hrange, lift, Bind.bind,
              Aeneas.Std.bind] at hrun
            have hcondition : LANE_COUNT.val ≤ lane_id.val := by
              have hrangeNat : ¬ lane_usize.val < LANE_COUNT.val := hrange
              omega
            simp [hcondition] at hrun

theorem checked_deposit_success_has_exact_source_relation
    (before after out : LaneState)
    (append_checked : Bool)
    (empty_roots : Array Digest 21#usize)
    (hrun :
      apply_production_lane_write
          (.CheckedDepositAppend before after append_checked) empty_roots =
        ok (.Ok out)) :
    CheckedDepositWriteRelation before after out append_checked empty_roots := by
  unfold apply_production_lane_write at hrun
  cases append_checked with
  | false => simp at hrun
  | true =>
      simp only [if_pos rfl] at hrun
      generalize hmaster :
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          before.master after.master = masterResult at hrun
      cases masterResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok masterDiff =>
          cases masterDiff with
          | true => simp at hrun
          | false =>
              have hmasterEq :=
                partial_eq_u8_array_ne_false_implies_eq _ _ hmaster
              by_cases hlaneEq : before.lane_id = after.lane_id
              · generalize hadd :
                  U64.checked_add before.next_leaf_index 1#u64 = nextOption
                  at hrun
                simp [hmaster, hlaneEq, lift, Bind.bind, Aeneas.Std.bind] at hrun
                generalize hoption :
                  core.cmp.PartialEq.ne.trait_default
                    (core.option.Option.Insts.CoreCmpPartialEqOption
                      core.cmp.PartialEqU64)
                    nextOption (some after.next_leaf_index) = optionResult
                    at hrun
                cases optionResult with
                | fail error => simp [hoption, Bind.bind, Aeneas.Std.bind] at hrun
                | div => simp [hoption, Bind.bind, Aeneas.Std.bind] at hrun
                | ok optionDiff =>
                    cases optionDiff with
                    | true => simp [hoption, Bind.bind, Aeneas.Std.bind] at hrun
                    | false =>
                        have haddEq := option_u64_ne_false_implies_eq _ _ hoption
                        generalize hfast :
                          fast_encode_projected after empty_roots true =
                            fastResult at hrun
                        cases fastResult with
                        | fail error => simp [hoption, hfast, Bind.bind, Aeneas.Std.bind,
                            core.result.Result.Insts.CoreOpsTry.branch] at hrun
                        | div => simp [hoption, hfast, Bind.bind, Aeneas.Std.bind,
                            core.result.Result.Insts.CoreOpsTry.branch] at hrun
                        | ok inner =>
                            cases inner with
                            | Err sourceError =>
                                unfold core.result.Result.Insts.CoreOpsTry.branch at hrun
                                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  Bind.bind, Aeneas.Std.bind] at hrun
                            | Ok bytes =>
                                unfold core.result.Result.Insts.CoreOpsTry.branch at hrun
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                                have hout : out = after := by simpa using hrun.symm
                                exact {
                                  output_eq := hout
                                  append_was_checked := rfl
                                  master_preserved := hmasterEq
                                  lane_preserved := hlaneEq
                                  index_advanced := hadd.trans haddEq
                                  fast_image_exists := ⟨bytes, hfast⟩
                                }
              · simp [hlaneEq] at hrun

theorem authenticated_settlement_success_has_exact_source_relation
    (before after out : LaneState)
    (asr8_authenticated : Bool)
    (empty_roots : Array Digest 21#usize)
    (hrun :
      apply_production_lane_write
          (.AuthenticatedAsr8Settlement before after asr8_authenticated)
          empty_roots = ok (.Ok out)) :
    AuthenticatedSettlementWriteRelation before after out
      asr8_authenticated empty_roots := by
  unfold apply_production_lane_write at hrun
  cases asr8_authenticated with
  | false => simp at hrun
  | true =>
      simp only [if_pos rfl] at hrun
      generalize hmaster :
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          before.master after.master = masterResult at hrun
      cases masterResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok masterDiff =>
          cases masterDiff with
          | true => simp at hrun
          | false =>
              have hmasterEq :=
                partial_eq_u8_array_ne_false_implies_eq _ _ hmaster
              by_cases hlaneEq : before.lane_id = after.lane_id
              · generalize hadd :
                  U64.checked_add before.next_leaf_index 1#u64 = nextOption
                  at hrun
                simp [hmaster, hlaneEq, lift, Bind.bind, Aeneas.Std.bind] at hrun
                generalize hoption :
                  core.cmp.PartialEq.ne.trait_default
                    (core.option.Option.Insts.CoreCmpPartialEqOption
                      core.cmp.PartialEqU64)
                    nextOption (some after.next_leaf_index) = optionResult
                    at hrun
                cases optionResult with
                | fail error => simp [hoption, Bind.bind, Aeneas.Std.bind] at hrun
                | div => simp [hoption, Bind.bind, Aeneas.Std.bind] at hrun
                | ok optionDiff =>
                    cases optionDiff with
                    | true => simp [hoption, Bind.bind, Aeneas.Std.bind] at hrun
                    | false =>
                        have haddEq := option_u64_ne_false_implies_eq _ _ hoption
                        generalize hfast :
                          fast_encode_projected after empty_roots true =
                            fastResult at hrun
                        cases fastResult with
                        | fail error => simp [hoption, hfast, Bind.bind, Aeneas.Std.bind,
                            core.result.Result.Insts.CoreOpsTry.branch] at hrun
                        | div => simp [hoption, hfast, Bind.bind, Aeneas.Std.bind,
                            core.result.Result.Insts.CoreOpsTry.branch] at hrun
                        | ok inner =>
                            cases inner with
                            | Err sourceError =>
                                unfold core.result.Result.Insts.CoreOpsTry.branch at hrun
                                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  Bind.bind, Aeneas.Std.bind] at hrun
                            | Ok bytes =>
                                unfold core.result.Result.Insts.CoreOpsTry.branch at hrun
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                                have hout : out = after := by simpa using hrun.symm
                                exact {
                                  output_eq := hout
                                  result_was_authenticated := rfl
                                  master_preserved := hmasterEq
                                  lane_preserved := hlaneEq
                                  index_advanced := hadd.trans haddEq
                                  fast_image_exists := ⟨bytes, hfast⟩
                                }
              · simp [hlaneEq] at hrun

/-- The sole mathematical/cryptographic premise of the fast path. It states
    that exact fresh initialization establishes active root↔frontier
    consistency and that the two checked production mutations preserve it. -/
structure ProgramOwnedLaneInvariantCapability : Type where
  Holds : LaneState → Prop
  initialize_preserves :
    ∀ master lane out empty_roots,
      GenesisWriteRelation master lane out empty_roots → Holds out
  checked_deposit_preserves :
    ∀ before after out checked empty_roots,
      Holds before →
      CheckedDepositWriteRelation before after out checked empty_roots →
      Holds out
  authenticated_settlement_preserves :
    ∀ before after out authenticated empty_roots,
      Holds before →
      AuthenticatedSettlementWriteRelation before after out authenticated
        empty_roots →
      Holds out

/-- Fast-path activation is limited to newly initialized PDAs or a checked
    one-time migration. Merely being Pool-owned is deliberately insufficient. -/
inductive LaneInvariantActivationBoundary : Type where
  | newlyInitializedPda
  | checkedOneTimeMigration

structure ActivatedProgramOwnedLane
    (capability : ProgramOwnedLaneInvariantCapability)
    (lane : LaneState) : Type where
  boundary : LaneInvariantActivationBoundary
  invariant_holds : capability.Holds lane

/-- A migration is not authorized merely by Pool ownership.  If an existing
    lane is ever activated, release engineering must provide a one-shot
    certificate that the strict root/frontier check was performed, the target
    is the canonical lane PDA, and the activation cannot be replayed.  The
    current production source has no migration instruction, so fresh
    initialization is the only source-established activation route. -/
structure CheckedOneTimeMigrationCertificate
    (capability : ProgramOwnedLaneInvariantCapability)
    (lane : LaneState) : Type where
  strict_root_frontier_check_establishes_invariant : capability.Holds lane
  canonical_target_lane_pda_checked : Prop
  migration_authority_consumed_once : Prop

def activate_checked_one_time_migration
    (capability : ProgramOwnedLaneInvariantCapability)
    (lane : LaneState)
    (certificate : CheckedOneTimeMigrationCertificate capability lane) :
    ActivatedProgramOwnedLane capability lane :=
  ⟨.checkedOneTimeMigration,
    certificate.strict_root_frontier_check_establishes_invariant⟩

def ProductionWriteInputInvariant
    (capability : ProgramOwnedLaneInvariantCapability)
    (write : ProductionLaneWrite) : Prop :=
  match write with
  | .Initialize _ _ => True
  | .CheckedDepositAppend before _ _ => capability.Holds before
  | .AuthenticatedAsr8Settlement before _ _ => capability.Holds before

/-- Activation evidence consumed by each translated production writer.
    Initialization has no predecessor and can create only a fresh-PDA
    activation.  Both mutation writers must consume the already-activated
    predecessor, whose original activation boundary is preserved. -/
def ProductionWriteActivationInput
    (capability : ProgramOwnedLaneInvariantCapability)
    (write : ProductionLaneWrite) : Type :=
  match write with
  | .Initialize _ _ => Unit
  | .CheckedDepositAppend before _ _ => ActivatedProgramOwnedLane capability before
  | .AuthenticatedAsr8Settlement before _ _ => ActivatedProgramOwnedLane capability before

/-- Strongest translated writer theorem: because `ProductionLaneWrite` has
    exactly the three production constructors, every successful write is
    fresh initialization, checked deposit append, or authenticated exact-ASR8
    settlement, and each preserves the single named invariant capability. -/
theorem translated_production_lane_write_preserves_program_owned_invariant
    (capability : ProgramOwnedLaneInvariantCapability)
    (write : ProductionLaneWrite)
    (empty_roots : Array Digest 21#usize)
    (out : LaneState)
    (hinput : ProductionWriteInputInvariant capability write)
    (hrun : apply_production_lane_write write empty_roots = ok (.Ok out)) :
    capability.Holds out := by
  cases write with
  | Initialize master lane =>
      exact capability.initialize_preserves _ _ _ _
        (initialization_success_has_exact_source_relation _ _ _ _ hrun)
  | CheckedDepositAppend before after checked =>
      exact capability.checked_deposit_preserves _ _ _ _ _ hinput
        (checked_deposit_success_has_exact_source_relation _ _ _ _ _ hrun)
  | AuthenticatedAsr8Settlement before after authenticated =>
      exact capability.authenticated_settlement_preserves _ _ _ _ _ hinput
        (authenticated_settlement_success_has_exact_source_relation
          _ _ _ _ _ hrun)

def translated_write_renews_activation
    (capability : ProgramOwnedLaneInvariantCapability)
    (write : ProductionLaneWrite)
    (empty_roots : Array Digest 21#usize)
    (out : LaneState)
    (activation : ProductionWriteActivationInput capability write)
    (hrun : apply_production_lane_write write empty_roots = ok (.Ok out)) :
    ActivatedProgramOwnedLane capability out := by
  cases write with
  | Initialize master lane =>
      exact ⟨.newlyInitializedPda,
        capability.initialize_preserves _ _ _ _
          (initialization_success_has_exact_source_relation _ _ _ _ hrun)⟩
  | CheckedDepositAppend before after checked =>
      exact ⟨activation.boundary,
        capability.checked_deposit_preserves _ _ _ _ _
          activation.invariant_holds
          (checked_deposit_success_has_exact_source_relation
            _ _ _ _ _ hrun)⟩
  | AuthenticatedAsr8Settlement before after authenticated =>
      exact ⟨activation.boundary,
        capability.authenticated_settlement_preserves _ _ _ _ _
          activation.invariant_holds
          (authenticated_settlement_success_has_exact_source_relation
            _ _ _ _ _ hrun)⟩

#print axioms partial_eq_u8_array_ne_false_implies_eq
#print axioms option_u64_ne_false_implies_eq
#print axioms initialization_success_has_exact_source_relation
#print axioms checked_deposit_success_has_exact_source_relation
#print axioms authenticated_settlement_success_has_exact_source_relation
#print axioms translated_production_lane_write_preserves_program_owned_invariant
#print axioms activate_checked_one_time_migration
#print axioms translated_write_renews_activation

end V7ForestLaneInvariantGenerated
