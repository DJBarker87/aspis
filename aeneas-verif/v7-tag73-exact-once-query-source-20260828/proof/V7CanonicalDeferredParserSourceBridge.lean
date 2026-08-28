import V7CanonicalDeferredParser.Funs

/-!
# Source bridge for the selected deferred canonical parser

The imported body is generated from the extraction-only free-function root,
which immediately calls the production inherent method.  All constants and
Rust-library result combinators used below have transparent definitions in
`FunsExternal`; this proof adds no parser axiom.
-/

set_option autoImplicit false

namespace AspisV7CanonicalDeferredParserSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CanonicalDeferredParserGenerated

private theorem usize_result_mul_exact (left right result : Std.Usize)
    (bound : left.val * right.val ≤ Std.Usize.max)
    (value : result.val = left.val * right.val) :
    (left * right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.mul_spec (x := left) (y := right) bound)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem usize_result_add_exact (left right result : Std.Usize)
    (bound : left.val + right.val ≤ Std.Usize.max)
    (value : result.val = left.val + right.val) :
    (left + right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.add_spec (x := left) (y := right) bound)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem usize_checked_add_eq_some
    (left right : Std.Usize)
    (bound : left.val + right.val ≤ Std.Usize.max) :
    ∃ sum : Std.Usize,
      Std.Usize.checked_add left right = some sum ∧
        sum.val = left.val + right.val := by
  have powerBound : left.val + right.val <
      2 ^ UScalarTy.Usize.numBits := by
    scalar_tac
  have systemBound : left.val + right.val <
      2 ^ System.Platform.numBits := by
    simpa using powerBound
  let sum : Std.Usize := Std.Usize.ofNatCore
    (left.val + right.val) powerBound
  refine ⟨sum, ?_, by simp [sum]⟩
  unfold Std.Usize.checked_add core.num.checked_add_UScalar
  change Option.ofResult (UScalar.add left right) = some sum
  simp [Option.ofResult, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    Result.ofOption, sum, systemBound]
  apply UScalar.eq_of_val_eq
  simp

private theorem usize_checked_mul_eq_some
    (left right : Std.Usize)
    (bound : left.val * right.val ≤ Std.Usize.max) :
    ∃ product : Std.Usize,
      Std.Usize.checked_mul left right = some product ∧
        product.val = left.val * right.val := by
  have powerBound : left.val * right.val <
      2 ^ UScalarTy.Usize.numBits := by
    scalar_tac
  have systemBound : left.val * right.val <
      2 ^ System.Platform.numBits := by
    simpa using powerBound
  let product : Std.Usize := Std.Usize.ofNatCore
    (left.val * right.val) powerBound
  refine ⟨product, ?_, by simp [product]⟩
  unfold Std.Usize.checked_mul core.num.checked_mul_UScalar
  simp [Option.ofResult, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    Result.ofOption, product, systemBound]
  apply UScalar.eq_of_val_eq
  simp

theorem extracted_wrapper_is_production_parser
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize) :
    parse_v7_canonical_deferred bytes frontierNodes =
      aspis_core.v7_fixed_canonical_audit.V7CanonicalOneFoldWire.parse_deferred_query_canonicality
        bytes frontierNodes := by
  rfl

private theorem extracted_fixed_bytes_run :
    aspis_core.v7_fixed_canonical_audit.V7_CANONICAL_FIXED_BYTES =
      ok 10256#usize := by
  have run : (16#usize * 641#usize : Result Std.Usize) =
      ok 10256#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  simp [aspis_core.v7_fixed_canonical_audit.V7_CANONICAL_FIXED_BYTES,
    aspis_core.v6_onefold.V6_FIXED_QM31_VALUES, run]

private theorem extracted_body_bytes_run :
    aspis_core.v7_fixed_canonical_audit.V7_CANONICAL_BODY_WITHOUT_FRONTIERS =
      ok 20268#usize := by
  have mul_2_26 : (2#usize * 26#usize : Result Std.Usize) =
      ok 52#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_10256_52 : (10256#usize + 52#usize : Result Std.Usize) =
      ok 10308#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_10308_24 : (10308#usize + 24#usize : Result Std.Usize) =
      ok 10332#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_10332_9936 : (10332#usize + 9936#usize : Result Std.Usize) =
      ok 20268#usize := by
    apply usize_result_add_exact <;> scalar_tac
  simp [aspis_core.v7_fixed_canonical_audit.V7_CANONICAL_BODY_WITHOUT_FRONTIERS,
    extracted_fixed_bytes_run,
    aspis_core.v6_onefold.V6_WORK_NONCE_BYTES,
    aspis_core.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES,
    aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES,
    mul_2_26, add_10256_52, add_10308_24, add_10332_9936]

theorem extracted_canonical_body_without_frontiers_is_20268 :
    aspis_core.v7_fixed_canonical_audit.V7_CANONICAL_BODY_WITHOUT_FRONTIERS =
      ok 20268#usize := by
  exact extracted_body_bytes_run

theorem extracted_parser_rejects_oversized_frontier
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (oversized : 209 < frontierNodes.val) :
    parse_v7_canonical_deferred bytes frontierNodes =
      ok (.Err aspis_core.v6_onefold.V6WireError.FrontierTooLarge) := by
  simp [parse_v7_canonical_deferred,
    aspis_core.v7_fixed_canonical_audit.V7CanonicalOneFoldWire.parse_deferred_query_canonicality,
    aspis_core.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE, oversized]

/-- At zero frontier nodes, every truncation and every trailing byte is the
same source `WrongLength` branch: only exactly 20,268 bytes can pass layout. -/
theorem extracted_parser_rejects_any_nonexact_zero_frontier_length
    (bytes : Slice Std.U8) (wrongLength : Slice.len bytes ≠ 20268#usize) :
    parse_v7_canonical_deferred bytes 0#usize =
      ok (.Err aspis_core.v6_onefold.V6WireError.WrongLength) := by
  have wrongLengthVal : bytes.val.length ≠ 20268 := by
    intro exactLength
    apply wrongLength
    apply UScalar.eq_of_val_eq
    simpa using exactLength
  obtain ⟨zeroFrontier, zeroFrontierRun, zeroFrontierValue⟩ :=
    usize_checked_mul_eq_some 0#usize 26#usize (by scalar_tac)
  have zeroFrontierExact : zeroFrontier = 0#usize := by
    apply UScalar.eq_of_val_eq
    norm_num at zeroFrontierValue ⊢
    exact zeroFrontierValue
  subst zeroFrontier
  have doubleZeroRun : (2#usize * 0#usize : Result Std.Usize) =
      ok 0#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  obtain ⟨total, totalRun, totalValue⟩ :=
    usize_checked_add_eq_some 20268#usize 0#usize (by scalar_tac)
  have totalExact : total = 20268#usize := by
    apply UScalar.eq_of_val_eq
    norm_num at totalValue ⊢
    exact totalValue
  subst total
  simp [parse_v7_canonical_deferred,
    aspis_core.v7_fixed_canonical_audit.V7CanonicalOneFoldWire.parse_deferred_query_canonicality,
    extracted_body_bytes_run,
    aspis_core.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE,
    aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES,
    core.option.Option.ok_or, lift, zeroFrontierRun, doubleZeroRun, totalRun,
    core.result.Result.Insts.CoreOpsTry.branch,
    wrongLengthVal]

#print axioms extracted_wrapper_is_production_parser
#print axioms extracted_canonical_body_without_frontiers_is_20268
#print axioms extracted_parser_rejects_oversized_frontier
#print axioms extracted_parser_rejects_any_nonexact_zero_frontier_length

end AspisV7CanonicalDeferredParserSourceBridge
