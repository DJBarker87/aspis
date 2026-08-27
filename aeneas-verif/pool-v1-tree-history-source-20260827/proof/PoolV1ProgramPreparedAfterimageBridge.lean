import PoolV1ProgramPreparedImagesFocused.Funs

/-!
# Pool V1 program prepared-afterimage source bridge

This file reasons directly from the freshly translated production method
`PreparedAuthorizedAppendV1::validate_inherited_state_and_cursor`.  It closes
the non-cryptographic afterimage checks: inherited pool identity, inherited
verifier policy, exact cursor motion, and exact one/two receipt shape.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1ProgramPreparedAfterimageBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1ProgramPreparedImagesFocusedGenerated

abbrev Digest := Array aspis_core.field.M31 8#usize
abbrev Prepared := transition.PreparedAuthorizedAppendV1
abbrev PoolState := state.PoolStateV1
abbrev Receipt := aspis_statement.pool_v1.incremental_merkle.AppendOneV1

private theorem list_allM_zipped_eq_true_implies_eq
    {T : Type} [DecidableEq T] :
    ∀ (left right : List T), left.length = right.length →
      List.allM (fun pair : T × T =>
        Result.ok (decide (pair.1 = pair.2))) (List.zip left right) =
          Result.ok true →
      left = right := by
  intro left
  induction left with
  | nil =>
      intro right lengths run
      cases right <;> simp_all
  | cons head tail ih =>
      intro right lengths run
      cases right with
      | nil => simp at lengths
      | cons other rest =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
          by_cases heads : head = other
          · subst other
            simp at run
            exact congrArg (List.cons head) (ih rest lengths run)
          · simp [heads, pure] at run

theorem digest_partial_eq_true_implies_eq (left right : Digest)
    (run :
      core.array.equality.PartialEqArray.eq
          aspis_core.field.M31.Insts.CoreCmpPartialEqM31 left right =
        .ok true) :
    left = right := by
  unfold core.array.equality.PartialEqArray.eq at run
  simp only [Array.length, ↓reduceIte] at run
  apply Subtype.ext
  apply list_allM_zipped_eq_true_implies_eq left.val right.val
  · simp
  · simpa [
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
      core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default] using run

theorem identity_partial_eq_false_implies_eq
    (left right : aspis_statement.pool_v1.format.PoolIdentityV1)
    (run :
      core.cmp.PartialEq.ne.trait_default
          aspis_statement.pool_v1.format.PoolIdentityV1.Insts.CoreCmpPartialEqPoolIdentityV1
          left right = .ok false) :
    left = right := by
  classical
  simpa [
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    aspis_statement.pool_v1.format.PoolIdentityV1.Insts.CoreCmpPartialEqPoolIdentityV1,
    aspis_statement.pool_v1.format.PoolIdentityV1.Insts.CoreCmpPartialEqPoolIdentityV1.eq]
    using run

theorem policy_partial_eq_false_implies_eq
    (left right : aspis_statement.pool_v1.format.VerifierPolicyV1)
    (run :
      core.cmp.PartialEq.ne.trait_default
          aspis_statement.pool_v1.format.VerifierPolicyV1.Insts.CoreCmpPartialEqVerifierPolicyV1
          left right = .ok false) :
    left = right := by
  classical
  simpa [
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    aspis_statement.pool_v1.format.VerifierPolicyV1.Insts.CoreCmpPartialEqVerifierPolicyV1,
    aspis_statement.pool_v1.format.VerifierPolicyV1.Insts.CoreCmpPartialEqVerifierPolicyV1.eq]
    using run

noncomputable def identityNeB
    (left right : aspis_statement.pool_v1.format.PoolIdentityV1) : Bool := by
  classical
  exact if left = right then false else true

noncomputable def policyNeB
    (left right : aspis_statement.pool_v1.format.VerifierPolicyV1) : Bool := by
  classical
  exact if left = right then false else true

@[simp] theorem identityNeB_eq_true
    (left right : aspis_statement.pool_v1.format.PoolIdentityV1) :
    identityNeB left right = true ↔ left ≠ right := by
  classical
  simp [identityNeB]

@[simp] theorem policyNeB_eq_true
    (left right : aspis_statement.pool_v1.format.VerifierPolicyV1) :
    policyNeB left right = true ↔ left ≠ right := by
  classical
  simp [policyNeB]

@[simp] theorem identity_ne_callback
    (left right : aspis_statement.pool_v1.format.PoolIdentityV1) :
    core.cmp.PartialEq.ne.trait_default
        aspis_statement.pool_v1.format.PoolIdentityV1.Insts.CoreCmpPartialEqPoolIdentityV1
        left right = .ok (identityNeB left right) := by
  classical
  simp [identityNeB,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    aspis_statement.pool_v1.format.PoolIdentityV1.Insts.CoreCmpPartialEqPoolIdentityV1,
    aspis_statement.pool_v1.format.PoolIdentityV1.Insts.CoreCmpPartialEqPoolIdentityV1.eq]

@[simp] theorem policy_ne_callback
    (left right : aspis_statement.pool_v1.format.VerifierPolicyV1) :
    core.cmp.PartialEq.ne.trait_default
        aspis_statement.pool_v1.format.VerifierPolicyV1.Insts.CoreCmpPartialEqVerifierPolicyV1
        left right = .ok (policyNeB left right) := by
  classical
  simp [policyNeB,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    aspis_statement.pool_v1.format.VerifierPolicyV1.Insts.CoreCmpPartialEqVerifierPolicyV1,
    aspis_statement.pool_v1.format.VerifierPolicyV1.Insts.CoreCmpPartialEqVerifierPolicyV1.eq]

def ExactPreparedAfterimage
    (prepared : Prepared) (source : PoolState)
    (request : transition.AuthorizedAppendV1) : Prop :=
  prepared.next_state.identity = source.identity ∧
  prepared.next_state.verifier_policy = source.verifier_policy ∧
  ∃ firstSequence finalSequence : Std.U64,
    U64.checked_add source.tree.next_leaf_index 1#u64 = some firstSequence ∧
    prepared.next_state.tree.next_leaf_index = finalSequence ∧
    prepared.receipt.first.leaf_index = source.tree.next_leaf_index ∧
    prepared.receipt.first.root_sequence = firstSequence ∧
    match request with
    | .One _ =>
        U64.checked_add source.tree.next_leaf_index 1#u64 = some finalSequence ∧
        prepared.receipt.second = none ∧
        prepared.receipt.first.root = prepared.next_state.tree.root
    | .Two _ _ =>
        U64.checked_add source.tree.next_leaf_index 2#u64 = some finalSequence ∧
        ∃ second : Receipt,
          prepared.receipt.second = some second ∧
          second.leaf_index = firstSequence ∧
          second.root_sequence = finalSequence ∧
          second.root = prepared.next_state.tree.root

theorem production_validate_success_implies_exact_afterimage
    (prepared : Prepared) (source : PoolState)
    (request : transition.AuthorizedAppendV1)
    (run :
      transition.PreparedAuthorizedAppendV1.validate_inherited_state_and_cursor
          prepared source request = .ok (.Ok ())) :
    ExactPreparedAfterimage prepared source request := by
  unfold transition.PreparedAuthorizedAppendV1.validate_inherited_state_and_cursor at run
  cases firstAdd : U64.checked_add source.tree.next_leaf_index 1#u64 with
  | none =>
      simp [state.PoolStateV1.current_root_sequence, firstAdd,
        lift, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at run
  | some firstSequence =>
      cases request with
      | One leaf =>
          cases finalAdd : U64.checked_add source.tree.next_leaf_index 1#u64 with
          | none => simp [firstAdd] at finalAdd
          | some finalSequence =>
              have finalEq : finalSequence = firstSequence := by
                rw [firstAdd] at finalAdd
                cases finalAdd
                rfl
              subst finalSequence
              simp only [
                state.PoolStateV1.current_root_sequence,
                firstAdd, lift, core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                transition.AuthorizedAppendV1.count,
                bind_tc_ok] at run
              by_cases firstLeaf :
                  prepared.receipt.first.leaf_index = source.tree.next_leaf_index
              · by_cases firstSequenceEq :
                    prepared.receipt.first.root_sequence = firstSequence
                · cases secondEq : prepared.receipt.second with
                  | none =>
                      cases rootResult :
                          core.array.equality.PartialEqArray.eq
                            aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                            prepared.receipt.first.root
                            prepared.next_state.tree.root with
                      | fail error => simp [firstLeaf, firstSequenceEq, secondEq,
                          rootResult] at run
                      | div => simp [firstLeaf, firstSequenceEq, secondEq,
                          rootResult] at run
                      | ok rootMatches =>
                          cases rootMatches with
                          | false => simp [firstLeaf, firstSequenceEq, secondEq,
                              rootResult] at run
                          | true =>
                              have rootEq := digest_partial_eq_true_implies_eq _ _ rootResult
                              by_cases identityEq :
                                  prepared.next_state.identity = source.identity
                              · by_cases policyEq :
                                    prepared.next_state.verifier_policy =
                                      source.verifier_policy
                                · by_cases cursorValEq :
                                      prepared.next_state.tree.next_leaf_index.val =
                                        firstSequence.val
                                  · have cursorEq :
                                        prepared.next_state.tree.next_leaf_index =
                                          firstSequence :=
                                      UScalar.eq_of_val_eq cursorValEq
                                    exact ⟨identityEq, policyEq, firstSequence,
                                      firstSequence, firstAdd, cursorEq, firstLeaf,
                                      firstSequenceEq, firstAdd, secondEq, rootEq⟩
                                  · simp [firstLeaf, firstSequenceEq, secondEq,
                                      rootResult, identityNeB, policyNeB,
                                      identityEq, policyEq, cursorValEq] at run
                                · simp [firstLeaf, firstSequenceEq, secondEq,
                                    rootResult, identityNeB, policyNeB,
                                    identityEq, policyEq] at run
                              · simp [firstLeaf, firstSequenceEq, secondEq,
                                  rootResult, identityNeB, identityEq] at run
                  | some second =>
                      simp [firstLeaf, firstSequenceEq, secondEq] at run
                · simp [firstLeaf, firstSequenceEq] at run
              · simp [firstLeaf] at run
      | Two first secondLeaf =>
          cases finalAdd : U64.checked_add source.tree.next_leaf_index 2#u64 with
          | none =>
              simp [state.PoolStateV1.current_root_sequence, firstAdd,
                transition.AuthorizedAppendV1.count, finalAdd, lift,
                core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                at run
          | some finalSequence =>
              simp only [
                state.PoolStateV1.current_root_sequence,
                firstAdd, lift, core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                transition.AuthorizedAppendV1.count,
                finalAdd, bind_tc_ok] at run
              by_cases firstLeaf :
                  prepared.receipt.first.leaf_index = source.tree.next_leaf_index
              · by_cases firstSequenceEq :
                    prepared.receipt.first.root_sequence = firstSequence
                · cases secondEq : prepared.receipt.second with
                  | none => simp [firstLeaf, firstSequenceEq, secondEq] at run
                  | some second =>
                      by_cases secondLeafEq : second.leaf_index = firstSequence
                      · by_cases secondSequenceEq :
                            second.root_sequence = finalSequence
                        · cases rootResult :
                              core.array.equality.PartialEqArray.eq
                                aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                                second.root prepared.next_state.tree.root with
                          | fail error => simp [firstLeaf, firstSequenceEq,
                              secondEq, secondLeafEq, secondSequenceEq,
                              rootResult] at run
                          | div => simp [firstLeaf, firstSequenceEq, secondEq,
                              secondLeafEq, secondSequenceEq, rootResult] at run
                          | ok rootMatches =>
                              cases rootMatches with
                              | false => simp [firstLeaf, firstSequenceEq,
                                  secondEq, secondLeafEq, secondSequenceEq,
                                  rootResult] at run
                              | true =>
                                  have rootEq :=
                                    digest_partial_eq_true_implies_eq _ _ rootResult
                                  by_cases identityEq :
                                      prepared.next_state.identity = source.identity
                                  · by_cases policyEq :
                                        prepared.next_state.verifier_policy =
                                          source.verifier_policy
                                    · by_cases cursorValEq :
                                          prepared.next_state.tree.next_leaf_index.val =
                                            finalSequence.val
                                      · have cursorEq :
                                            prepared.next_state.tree.next_leaf_index =
                                              finalSequence :=
                                          UScalar.eq_of_val_eq cursorValEq
                                        exact ⟨identityEq, policyEq, firstSequence,
                                          finalSequence, firstAdd, cursorEq, firstLeaf,
                                          firstSequenceEq, finalAdd, second, secondEq,
                                          secondLeafEq, secondSequenceEq, rootEq⟩
                                      · simp [firstLeaf, firstSequenceEq, secondEq,
                                          secondLeafEq, secondSequenceEq, rootResult,
                                          identityNeB, policyNeB, identityEq, policyEq,
                                          cursorValEq] at run
                                    · simp [firstLeaf, firstSequenceEq, secondEq,
                                        secondLeafEq, secondSequenceEq, rootResult,
                                        identityNeB, policyNeB, identityEq, policyEq]
                                        at run
                                  · simp [firstLeaf, firstSequenceEq, secondEq,
                                      secondLeafEq, secondSequenceEq, rootResult,
                                      identityNeB, identityEq] at run
                        · simp [firstLeaf, firstSequenceEq, secondEq,
                            secondLeafEq, secondSequenceEq] at run
                      · simp [firstLeaf, firstSequenceEq, secondEq,
                          secondLeafEq] at run
                · simp [firstLeaf, firstSequenceEq] at run
              · simp [firstLeaf] at run

#print axioms digest_partial_eq_true_implies_eq
#print axioms identity_partial_eq_false_implies_eq
#print axioms policy_partial_eq_false_implies_eq
#print axioms production_validate_success_implies_exact_afterimage

end PoolV1ProgramPreparedAfterimageBridge
