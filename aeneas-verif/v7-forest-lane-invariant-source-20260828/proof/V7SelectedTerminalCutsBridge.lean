import V7ForestLaneInvariant.Funs

/-!
# Source and algebra bridges for the selected terminal CU cuts

This file keeps three optimizations separate:

* direct reuse of already decoded canonical ASR8 bytes;
* exact binary Copy-weight skip/add; and
* moving one common selector outside the fixed four-term digest pack.

The translated source projection pins control flow and input schedules.  The
generic commutative-ring lemmas prove the arithmetic rewrites; neither step
changes a transcript, constraint, endpoint, result field, or byte codec.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ForestLaneInvariantGenerated

/-- The direct and reconstructed-statement result binders consume the exact
    same authenticated/canonical prerequisites and material equalities. -/
theorem translated_direct_result_binding_eq_reconstructed
    (prerequisites : DirectResultPrerequisites)
    (bindings : DirectResultBindings) :
    direct_result_binding_projected prerequisites bindings =
      reconstructed_statement_result_binding_projected prerequisites bindings := by
  rfl

/-- The complete gate retained by direct canonical ASR8 reuse.  The direct cut
    cannot turn raw return bytes into authority: all four upstream facts and
    all six material result equalities must already hold. -/
def ExactDirectResultCut
    (prerequisites : DirectResultPrerequisites)
    (bindings : DirectResultBindings) : Prop :=
  prerequisites.request_master_checkpoint_lane_authenticated = true ∧
  prerequisites.exact_asr8_decoded_canonical = true ∧
  prerequisites.next_lane_encoder_accepted = true ∧
  prerequisites.returned_program_is_selected_verifier = true ∧
  bindings.transition_kind_exact = true ∧
  bindings.master_account_exact = true ∧
  bindings.selected_lane_account_exact = true ∧
  bindings.output_lane_exact = true ∧
  bindings.nullifier_exact = true ∧
  bindings.next_pair_index_exact = true

theorem translated_direct_result_success_has_exact_gate
    (prerequisites : DirectResultPrerequisites)
    (bindings : DirectResultBindings)
    (run : direct_result_binding_projected prerequisites bindings =
      .ok (.Ok ())) :
    ExactDirectResultCut prerequisites bindings := by
  unfold direct_result_binding_projected at run
  have h1 : prerequisites.request_master_checkpoint_lane_authenticated = true := by
    cases h : prerequisites.request_master_checkpoint_lane_authenticated
    · simp [h] at run
    · rfl
  simp only [h1, if_true] at run
  have h2 : prerequisites.exact_asr8_decoded_canonical = true := by
    cases h : prerequisites.exact_asr8_decoded_canonical
    · simp [h] at run
    · rfl
  simp only [h2, if_true] at run
  have h3 : prerequisites.next_lane_encoder_accepted = true := by
    cases h : prerequisites.next_lane_encoder_accepted
    · simp [h] at run
    · rfl
  simp only [h3, if_true] at run
  have h4 : prerequisites.returned_program_is_selected_verifier = true := by
    cases h : prerequisites.returned_program_is_selected_verifier
    · simp [h] at run
    · rfl
  simp only [h4, if_true] at run
  have h5 : bindings.transition_kind_exact = true := by
    cases h : bindings.transition_kind_exact
    · simp [h] at run
    · rfl
  simp only [h5, if_true] at run
  have h6 : bindings.master_account_exact = true := by
    cases h : bindings.master_account_exact
    · simp [h] at run
    · rfl
  simp only [h6, if_true] at run
  have h7 : bindings.selected_lane_account_exact = true := by
    cases h : bindings.selected_lane_account_exact
    · simp [h] at run
    · rfl
  simp only [h7, if_true] at run
  have h8 : bindings.output_lane_exact = true := by
    cases h : bindings.output_lane_exact
    · simp [h] at run
    · rfl
  simp only [h8, if_true] at run
  have h9 : bindings.nullifier_exact = true := by
    cases h : bindings.nullifier_exact
    · simp [h] at run
    · rfl
  simp only [h9, if_true] at run
  have h10 : bindings.next_pair_index_exact = true := by
    cases h : bindings.next_pair_index_exact
    · simp [h] at run
    · rfl
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- Both digest implementations receive the identical selector and four
    residuals. Only the placement of a multiplication differs. -/
theorem translated_digest_factoring_preserves_exact_schedule
    (schedule : DigestBindingScheduleProjection) :
    literal_digest_schedule_projected schedule =
      factored_digest_schedule_projected schedule := by
  rfl

theorem translated_binary_zero_selects_keep :
    binary_weight_action_projected 0#u8 =
      .ok (.Ok BinaryWeightActionProjection.Keep) := by
  rfl

theorem translated_binary_one_selects_add :
    binary_weight_action_projected 1#u8 =
      .ok (.Ok BinaryWeightActionProjection.AddSelector) := by
  rfl

theorem translated_binary_action_success_is_exact
    (weight : Std.U8) (action : BinaryWeightActionProjection)
    (run : binary_weight_action_projected weight = .ok (.Ok action)) :
    (weight = 0#u8 ∧ action = BinaryWeightActionProjection.Keep) ∨
      (weight = 1#u8 ∧ action = BinaryWeightActionProjection.AddSelector) := by
  unfold binary_weight_action_projected at run
  split at run
  · simp at run
    exact Or.inl ⟨rfl, run.symm⟩
  · simp at run
    exact Or.inr ⟨rfl, run.symm⟩
  · simp at run

/-- The selected source pipeline is fail closed: whenever a translated
    generated link weight is accepted by the translated skip/add consumer, the
    weight and action are exactly the zero/keep or one/add cases. -/
theorem translated_link_then_action_success_is_exact
    (weight_kind weight_level : Std.U8)
    (append_index : Std.U64)
    (variant : CopyVariantProjection)
    (weight : Std.U8)
    (action : BinaryWeightActionProjection)
    (_linkRun : binary_link_weight_projected weight_kind weight_level
      append_index variant = .ok (.Ok weight))
    (actionRun : binary_weight_action_projected weight = .ok (.Ok action)) :
    (weight = 0#u8 ∧ action = BinaryWeightActionProjection.Keep) ∨
      (weight = 1#u8 ∧ action = BinaryWeightActionProjection.AddSelector) :=
  translated_binary_action_success_is_exact weight action actionRun

/-! ## Arithmetic equalities, independent of the deployed field encoding -/

variable {K : Type*} [CommRing K]

/-- The symbolic fixed pack used by one four-residual group. The concrete
    `qm31_pack_base4` source implements this same linear combination at its
    fixed tower element. -/
def symbolicPack4 (u x0 x1 x2 x3 : K) : K :=
  x0 + u * x1 + u ^ 2 * x2 + u ^ 3 * x3

/-- Exact algebra behind the packed-digest selector cut. -/
theorem selector_mul_symbolicPack4
    (selector u x0 x1 x2 x3 : K) :
    symbolicPack4 u (selector * x0) (selector * x1)
        (selector * x2) (selector * x3) =
      selector * symbolicPack4 u x0 x1 x2 x3 := by
  simp only [symbolicPack4]
  ring

def literalBinaryWeight (sum selector : K) (weight : Bool) : K :=
  sum + selector * if weight then 1 else 0

def specializedBinaryWeight (sum selector : K) (weight : Bool) : K :=
  if weight then sum + selector else sum

/-- Exact algebra behind `selector * {0,1}` becoming skip/add. -/
theorem specialized_binary_weight_eq_literal
    (sum selector : K) (weight : Bool) :
    specializedBinaryWeight sum selector weight =
      literalBinaryWeight sum selector weight := by
  cases weight <;> simp [specializedBinaryWeight, literalBinaryWeight]

#print axioms translated_direct_result_binding_eq_reconstructed
#print axioms translated_direct_result_success_has_exact_gate
#print axioms translated_digest_factoring_preserves_exact_schedule
#print axioms translated_binary_action_success_is_exact
#print axioms translated_link_then_action_success_is_exact
#print axioms selector_mul_symbolicPack4
#print axioms specialized_binary_weight_eq_literal

end V7ForestLaneInvariantGenerated
