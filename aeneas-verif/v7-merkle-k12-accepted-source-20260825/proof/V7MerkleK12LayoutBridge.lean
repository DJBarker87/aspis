import V7MerkleK12SourceBridge
import V7DeferredParserSourceBridge
import AspisFormal.Pool.V7MerkleParserRoundtrip

open Aeneas Aeneas.Std Result

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Production V7 Merkle hash-input layout bridge

This file connects the lists passed by the Aeneas translation of the
production Rust hash helpers to the frozen Tag-73 `TypedPreimage` grammar.
SHA-256 itself remains the explicit `GeneratedHash` callback interface from
`V7MerkleK12SourceBridge`.

The production wire parser is supplied by the independently pinned transparent
`V7DeferredParser` extraction.  The `V7CompactOneFoldWire.query` accessor and
the caller's little-endian query-position decoder are not roots of either
imported extraction, so their source correspondence is stated as a remaining
boundary rather than reconstructed by hand.

Every Merkle object in scope here--roots, frontier nodes, packed values, and
salts--is a raw byte slice or fixed byte array.  No theorem in this file applies
an integer reinterpretation or endianness convention to those bytes.  The
translated Merkle verifier receives public positions already typed as `u32`;
provenance for the caller's construction of those values requires the caller
extraction rather than an assumed decoder.
-/

namespace AspisV7MerkleK12LayoutBridge


abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
abbrev GeneratedHash := AspisV7MerkleK12SourceBridge.GeneratedHash

def sliceFixed {n : Nat} (bytes : Slice Std.U8) : Fin n → Byte :=
  AspisPool.V7MerkleQueryExtractor.fixedOfListD (AspisV7MerkleK12SourceBridge.generatedSliceBytes bytes)

def saltFixed (bytes : Array Std.U8 32#usize) : AspisPool.V7MerkleQueryGrammar.Salt32 :=
  AspisPool.V7MerkleQueryExtractor.fixedOfListD (AspisV7MerkleK12SourceBridge.generatedArrayBytes bytes)

def digestFixed (bytes : Array Std.U8 26#usize) : AspisPool.V7MerkleQueryGrammar.Digest208 :=
  AspisPool.V7MerkleQueryExtractor.fixedOfListD (AspisV7MerkleK12SourceBridge.generatedArrayBytes bytes)

theorem generatedArrayBytes_length {n : Std.Usize}
    (bytes : Array Std.U8 n) :
    (AspisV7MerkleK12SourceBridge.generatedArrayBytes bytes).length = n.val := by
  have lengthExact := bytes.property
  change bytes.val.length = n.val at lengthExact
  simp [AspisV7MerkleK12SourceBridge.generatedArrayBytes, lengthExact]

theorem fixedBytes_sliceFixed {n : Nat} (bytes : Slice Std.U8)
    (lengthExact : (AspisV7MerkleK12SourceBridge.generatedSliceBytes bytes).length = n) :
    AspisPool.V7MerkleQueryGrammar.fixedBytes (sliceFixed (n := n) bytes) =
      AspisV7MerkleK12SourceBridge.generatedSliceBytes bytes := by
  exact AspisPool.V7MerkleQueryExtractor.fixedBytes_fixedOfListD_of_length _ lengthExact

@[simp] theorem fixedBytes_saltFixed (bytes : Array Std.U8 32#usize) :
    AspisPool.V7MerkleQueryGrammar.fixedBytes (saltFixed bytes) = AspisV7MerkleK12SourceBridge.generatedArrayBytes bytes := by
  exact AspisPool.V7MerkleQueryExtractor.fixedBytes_fixedOfListD_of_length _
    (by simpa using generatedArrayBytes_length bytes)

@[simp] theorem fixedBytes_digestFixed (bytes : Array Std.U8 26#usize) :
    AspisPool.V7MerkleQueryGrammar.fixedBytes (digestFixed bytes) = AspisV7MerkleK12SourceBridge.generatedArrayBytes bytes := by
  exact AspisPool.V7MerkleQueryExtractor.fixedBytes_fixedOfListD_of_length _
    (by simpa using generatedArrayBytes_length bytes)

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

private theorem usize_result_div_exact (left right result : Std.Usize)
    (nonzero : right.val ≠ 0)
    (value : result.val = left.val / right.val) :
    (left / right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.div_spec left (y := right) nonzero)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

/-! ## Extracted production wire parser layout

The independent deferred-parser extraction is transparent down through every
checked length computation, `split_at`, fixed-array conversion, and `Result`
branch.  These are the literal byte offsets used by the deployed parser:

* fixed packed fields: `[0, 9936)`;
* C1 root: `[9936, 9962)`;
* C2 root: `[9962, 9988)`;
* work nonces: `[9988, 10012)`;
* sixteen query records: `[10012, 19948)`;
* C1 frontier: the next `26 * frontierNodes` bytes;
* C2 frontier: the final `26 * frontierNodes` bytes.
-/

def deferredParserExactLayout
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (wire : V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire) : Prop :=
  frontierNodes.val ≤ 203 ∧
    bytes.val.length = 19948 + 52 * frontierNodes.val ∧
    wire.fixed_fields_packed.val = bytes.val.take 9936 ∧
    wire.c1_root.val = (bytes.val.drop 9936).take 26 ∧
    wire.c2_root.val = (bytes.val.drop 9962).take 26 ∧
    wire.work_nonces.val = (bytes.val.drop 9988).take 24 ∧
    wire.query_section.val = (bytes.val.drop 10012).take 9936 ∧
    wire.c1_frontier.val =
      (bytes.val.drop 19948).take (26 * frontierNodes.val) ∧
    wire.c2_frontier.val =
      bytes.val.drop (19948 + 26 * frontierNodes.val)

private theorem deferred_production_limit_exact :
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_PRODUCTION_LIMIT_BYTES =
      .ok 30720#usize := by
  have run : (30#usize * 1024#usize : Result Std.Usize) = .ok 30720#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  simpa [V7DeferredParserGenerated.v7_onefold.V7_COMPACT_PRODUCTION_LIMIT_BYTES,
    run]

private theorem deferred_work_nonce_bytes_exact :
    V7DeferredParserGenerated.v6_onefold.V6_WORK_NONCE_BYTES =
      .ok 24#usize := by
  have run : (3#usize * 8#usize : Result Std.Usize) = .ok 24#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  simpa [V7DeferredParserGenerated.v6_onefold.V6_WORK_NONCE_BYTES, run]

private theorem deferred_fixed_packed_field_bytes_exact :
    V7DeferredParserGenerated.v6_onefold.V6_FIXED_PACKED_FIELD_BYTES =
      .ok 9936#usize := by
  have mul_4_6 : (4#usize * 6#usize : Result Std.Usize) = .ok 24#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_26_3 : (26#usize + 3#usize : Result Std.Usize) = .ok 29#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_3_29 : (3#usize * 29#usize : Result Std.Usize) = .ok 87#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_10_27 : (10#usize * 27#usize : Result Std.Usize) = .ok 270#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_0_1 : (0#usize + 1#usize : Result Std.Usize) = .ok 1#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_1_270 : (1#usize + 270#usize : Result Std.Usize) = .ok 271#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_271_87 : (271#usize + 87#usize : Result Std.Usize) = .ok 358#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_358_1 : (358#usize + 1#usize : Result Std.Usize) = .ok 359#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_359_2 : (359#usize + 2#usize : Result Std.Usize) = .ok 361#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_361_24 : (361#usize + 24#usize : Result Std.Usize) = .ok 385#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_385_256 : (385#usize + 256#usize : Result Std.Usize) = .ok 641#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_4_641 : (4#usize * 641#usize : Result Std.Usize) = .ok 2564#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_2564_31 : (2564#usize * 31#usize : Result Std.Usize) = .ok 79484#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_79484_7 : (79484#usize + 7#usize : Result Std.Usize) = .ok 79491#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_79491_8 : (79491#usize / 8#usize : Result Std.Usize) = .ok 9936#usize := by
    apply usize_result_div_exact <;> scalar_tac
  simp [V7DeferredParserGenerated.v6_onefold.V6_FIXED_PACKED_FIELD_BYTES,
    V7DeferredParserGenerated.v6_onefold.V6_FIXED_M31_LIMBS,
    V7DeferredParserGenerated.v6_onefold.V6_FIXED_QM31_VALUES,
    V7DeferredParserGenerated.v6_onefold.V6_FINAL_QM31_VALUES,
    V7DeferredParserGenerated.v6_onefold.V6_FINAL_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_RELATION_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_OOD_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_INACTIVE_CLAIM_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_POINT_CLAIMS_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_SEMANTIC_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_INITIAL_CLAIM_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_RELATION_ROUNDS,
    V7DeferredParserGenerated.v6_onefold.V6_RELATION_SENT_VALUES,
    V7DeferredParserGenerated.v6_onefold.V6_POINT_CLAIM_ROWS,
    V7DeferredParserGenerated.v6_onefold.V6_TOTAL_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.V6_C1_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.V6_C2_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.V6_SEMANTIC_ROUNDS,
    V7DeferredParserGenerated.v6_onefold.V6_SEMANTIC_SENT_VALUES,
    V7DeferredParserGenerated.v6_onefold.packed_bytes,
    mul_4_6, add_26_3, mul_3_29, mul_10_27, add_0_1, add_1_270,
    add_271_87, add_358_1, add_359_2, add_361_24, add_385_256,
    mul_4_641, mul_2564_31, add_79484_7, div_79491_8]

private theorem deferred_query_section_bytes_exact :
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES =
      .ok 9936#usize := by
  have mul_4_26 : (4#usize * 26#usize : Result Std.Usize) = .ok 104#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_104_31 : (104#usize * 31#usize : Result Std.Usize) = .ok 3224#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_3224_7 : (3224#usize + 7#usize : Result Std.Usize) = .ok 3231#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_3231_8 : (3231#usize / 8#usize : Result Std.Usize) = .ok 403#usize := by
    apply usize_result_div_exact <;> scalar_tac
  have mul_4_4 : (4#usize * 4#usize : Result Std.Usize) = .ok 16#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_16_3 : (16#usize * 3#usize : Result Std.Usize) = .ok 48#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_48_31 : (48#usize * 31#usize : Result Std.Usize) = .ok 1488#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_1488_7 : (1488#usize + 7#usize : Result Std.Usize) = .ok 1495#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_1495_8 : (1495#usize / 8#usize : Result Std.Usize) = .ok 186#usize := by
    apply usize_result_div_exact <;> scalar_tac
  have add_403_186 : (403#usize + 186#usize : Result Std.Usize) = .ok 589#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_589_32 : (589#usize + 32#usize : Result Std.Usize) = .ok 621#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_16_621 : (16#usize * 621#usize : Result Std.Usize) = .ok 9936#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  simp [V7DeferredParserGenerated.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_QUERY_BYTES,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_C1_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_C2_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_PRIVATE_SALT_BYTES,
    V7DeferredParserGenerated.v6_onefold.V6_QUERY_COUNT,
    V7DeferredParserGenerated.v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.V6_C1_LIMBS_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.V6_C2_LIMBS_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.V6_C1_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.V6_C2_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.packed_bytes,
    mul_4_26, mul_104_31, add_3224_7, div_3231_8,
    mul_4_4, mul_16_3, mul_48_31, add_1488_7, div_1495_8,
    add_403_186, add_589_32, mul_16_621]

private theorem deferred_body_without_frontiers_exact :
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_BODY_WITHOUT_FRONTIERS =
      .ok 19948#usize := by
  have mul_4_6 : (4#usize * 6#usize : Result Std.Usize) = .ok 24#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_26_3 : (26#usize + 3#usize : Result Std.Usize) = .ok 29#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_3_29 : (3#usize * 29#usize : Result Std.Usize) = .ok 87#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_10_27 : (10#usize * 27#usize : Result Std.Usize) = .ok 270#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_0_1 : (0#usize + 1#usize : Result Std.Usize) = .ok 1#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_1_270 : (1#usize + 270#usize : Result Std.Usize) = .ok 271#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_271_87 : (271#usize + 87#usize : Result Std.Usize) = .ok 358#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_358_1 : (358#usize + 1#usize : Result Std.Usize) = .ok 359#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_359_2 : (359#usize + 2#usize : Result Std.Usize) = .ok 361#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_361_24 : (361#usize + 24#usize : Result Std.Usize) = .ok 385#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_385_256 : (385#usize + 256#usize : Result Std.Usize) = .ok 641#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_4_641 : (4#usize * 641#usize : Result Std.Usize) = .ok 2564#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_2564_31 : (2564#usize * 31#usize : Result Std.Usize) = .ok 79484#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_79484_7 : (79484#usize + 7#usize : Result Std.Usize) = .ok 79491#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_79491_8 : (79491#usize / 8#usize : Result Std.Usize) = .ok 9936#usize := by
    apply usize_result_div_exact <;> scalar_tac
  have mul_2_26 : (2#usize * 26#usize : Result Std.Usize) = .ok 52#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_9936_52 : (9936#usize + 52#usize : Result Std.Usize) = .ok 9988#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_3_8 : (3#usize * 8#usize : Result Std.Usize) = .ok 24#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_9988_24 : (9988#usize + 24#usize : Result Std.Usize) = .ok 10012#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_4_26 : (4#usize * 26#usize : Result Std.Usize) = .ok 104#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_104_31 : (104#usize * 31#usize : Result Std.Usize) = .ok 3224#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_3224_7 : (3224#usize + 7#usize : Result Std.Usize) = .ok 3231#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_3231_8 : (3231#usize / 8#usize : Result Std.Usize) = .ok 403#usize := by
    apply usize_result_div_exact <;> scalar_tac
  have mul_4_4 : (4#usize * 4#usize : Result Std.Usize) = .ok 16#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_16_3 : (16#usize * 3#usize : Result Std.Usize) = .ok 48#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_48_31 : (48#usize * 31#usize : Result Std.Usize) = .ok 1488#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_1488_7 : (1488#usize + 7#usize : Result Std.Usize) = .ok 1495#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_1495_8 : (1495#usize / 8#usize : Result Std.Usize) = .ok 186#usize := by
    apply usize_result_div_exact <;> scalar_tac
  have add_403_186 : (403#usize + 186#usize : Result Std.Usize) = .ok 589#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_589_32 : (589#usize + 32#usize : Result Std.Usize) = .ok 621#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have mul_16_621 : (16#usize * 621#usize : Result Std.Usize) = .ok 9936#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_10012_9936 : (10012#usize + 9936#usize : Result Std.Usize) = .ok 19948#usize := by
    apply usize_result_add_exact <;> scalar_tac
  simp [V7DeferredParserGenerated.v7_onefold.V7_COMPACT_BODY_WITHOUT_FRONTIERS,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_ROOT_BYTES,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_QUERY_BYTES,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_C1_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_C2_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_DIGEST_BYTES,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_PRIVATE_SALT_BYTES,
    V7DeferredParserGenerated.v6_onefold.V6_FIXED_PACKED_FIELD_BYTES,
    V7DeferredParserGenerated.v6_onefold.V6_FIXED_M31_LIMBS,
    V7DeferredParserGenerated.v6_onefold.V6_FIXED_QM31_VALUES,
    V7DeferredParserGenerated.v6_onefold.V6_FINAL_QM31_VALUES,
    V7DeferredParserGenerated.v6_onefold.V6_FINAL_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_RELATION_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_OOD_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_INACTIVE_CLAIM_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_POINT_CLAIMS_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_SEMANTIC_QM31_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_INITIAL_CLAIM_OFFSET,
    V7DeferredParserGenerated.v6_onefold.V6_RELATION_ROUNDS,
    V7DeferredParserGenerated.v6_onefold.V6_RELATION_SENT_VALUES,
    V7DeferredParserGenerated.v6_onefold.V6_POINT_CLAIM_ROWS,
    V7DeferredParserGenerated.v6_onefold.V6_TOTAL_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.V6_C1_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.V6_C2_COLUMNS,
    V7DeferredParserGenerated.v6_onefold.V6_SEMANTIC_ROUNDS,
    V7DeferredParserGenerated.v6_onefold.V6_SEMANTIC_SENT_VALUES,
    V7DeferredParserGenerated.v6_onefold.V6_WORK_NONCE_BYTES,
    V7DeferredParserGenerated.v6_onefold.V6_QUERY_COUNT,
    V7DeferredParserGenerated.v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.V6_C1_LIMBS_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.V6_C2_LIMBS_PER_QUERY,
    V7DeferredParserGenerated.v6_onefold.packed_bytes,
    mul_4_6, add_26_3, mul_3_29, mul_10_27, add_0_1, add_1_270,
    add_271_87, add_358_1, add_359_2, add_361_24, add_385_256,
    mul_4_641, mul_2564_31, add_79484_7, div_79491_8,
    mul_2_26, add_9936_52, mul_3_8, add_9988_24,
    mul_4_26, mul_104_31, add_3224_7, div_3231_8,
    mul_4_4, mul_16_3, mul_48_31, add_1488_7, div_1495_8,
    add_403_186, add_589_32, mul_16_621, add_10012_9936]

/-- Successful translated production parsing fixes the complete body length
and every returned slice.  In particular equality of the complete input
length rules out silently ignored trailing bytes. -/
theorem deferred_parser_success_has_exact_layout
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (wire : V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire)
    (accepted :
      V7DeferredParserGenerated.v7_onefold.parse_v7_compact_onefold_wire_deferred
          bytes frontierNodes = .ok (.Ok wire)) :
    deferredParserExactLayout bytes frontierNodes wire := by
  have frontierCap : frontierNodes.val ≤ 203 := by
    by_contra capFails
    have oversized : frontierNodes > 203#usize := by
      change 203 < frontierNodes.val
      omega
    have impossible := accepted
    simp [V7DeferredParserGenerated.v7_onefold.parse_v7_compact_onefold_wire_deferred,
      V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality,
      V7DeferredParserGenerated.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE,
      oversized] at impossible
  have frontierNotOversized : ¬ frontierNodes > 203#usize := by
    change ¬ 203 < frontierNodes.val
    omega
  have frontierValueNotOversized : ¬ 203 < frontierNodes.val := by
    omega
  have frontierProductBound : frontierNodes.val * 26 ≤ Std.Usize.max := by
    calc
      frontierNodes.val * 26 ≤ 203 * 26 :=
        Nat.mul_le_mul_right 26 frontierCap
      _ ≤ 4294967295 := by norm_num
      _ ≤ Std.Usize.max := Usize.cMax_bound_concrete.1
  obtain ⟨frontierBytes, frontierBytesRun, frontierBytesValue⟩ :=
    usize_checked_mul_eq_some frontierNodes 26#usize frontierProductBound
  have frontierBytesValue' :
      frontierBytes.val = frontierNodes.val * 26 := by
    norm_num at frontierBytesValue ⊢
    exact frontierBytesValue
  have doubledBound : 2 * frontierBytes.val ≤ Std.Usize.max := by
    calc
      2 * frontierBytes.val = 2 * (frontierNodes.val * 26) := by
        rw [frontierBytesValue']
      _ ≤ 2 * (203 * 26) := by omega
      _ ≤ 4294967295 := by norm_num
      _ ≤ Std.Usize.max := Usize.cMax_bound_concrete.1
  obtain ⟨doubledFrontierBytes, doubledFrontierRun,
      doubledFrontierValue, _⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.mul_bv_spec (x := 2#usize) (y := frontierBytes)
        (by
          rw [UScalar.max_USize_eq]
          norm_num
          exact doubledBound))
  have doubledFrontierValue' :
      doubledFrontierBytes.val = 2 * frontierBytes.val := by
    norm_num at doubledFrontierValue ⊢
    exact doubledFrontierValue
  have totalBound : 19948 + doubledFrontierBytes.val ≤ Std.Usize.max := by
    calc
      19948 + doubledFrontierBytes.val =
          19948 + 2 * (frontierNodes.val * 26) := by
        rw [doubledFrontierValue', frontierBytesValue']
      _ ≤ 19948 + 2 * (203 * 26) := by omega
      _ ≤ 4294967295 := by norm_num
      _ ≤ Std.Usize.max := Usize.cMax_bound_concrete.1
  obtain ⟨totalBytes, totalBytesRun, totalBytesValue⟩ :=
    usize_checked_add_eq_some 19948#usize doubledFrontierBytes totalBound
  have bytesLengthUsize : Slice.len bytes = totalBytes := by
    by_contra wrongLength
    have wrongValue : bytes.val.length ≠ totalBytes.val := by
      intro valuesEqual
      apply wrongLength
      apply UScalar.eq_of_val_eq
      simpa using valuesEqual
    have impossible := accepted
    unfold V7DeferredParserGenerated.v7_onefold.parse_v7_compact_onefold_wire_deferred at impossible
    unfold V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality at impossible
    simp [V7DeferredParserGenerated.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE,
      V7DeferredParserGenerated.v7_onefold.V7_COMPACT_DIGEST_BYTES,
      deferred_body_without_frontiers_exact,
      frontierBytesRun, doubledFrontierRun, totalBytesRun,
      frontierNotOversized, frontierValueNotOversized, wrongValue,
      core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      Bind.bind, Aeneas.Std.bind, lift] at impossible
  have bytesLengthToTotal : bytes.val.length = totalBytes.val := by
    have lengthValues := congrArg UScalar.val bytesLengthUsize
    simpa using lengthValues
  have totalBytesValue' :
      totalBytes.val = 19948 + doubledFrontierBytes.val := by
    norm_num at totalBytesValue ⊢
    exact totalBytesValue
  have bytesLengthExact :
      bytes.val.length = 19948 + 52 * frontierNodes.val := by
    calc
      bytes.val.length = totalBytes.val := bytesLengthToTotal
      _ = 19948 + doubledFrontierBytes.val := totalBytesValue'
      _ = 19948 + 2 * frontierBytes.val := by rw [doubledFrontierValue']
      _ = 19948 + 2 * (frontierNodes.val * 26) := by
        rw [frontierBytesValue']
      _ = 19948 + 52 * frontierNodes.val := by omega
  have fixedPrefixFitsExact :
      9936 ≤ 19948 + 2 * (frontierNodes.val * 26) := by
    omega
  have c1RootFits : 26 ≤ bytes.val.length - 9936 := by
    rw [bytesLengthExact]
    omega
  have c2RootFits : 26 ≤ bytes.val.length - 9962 := by
    rw [bytesLengthExact]
    omega
  have nonceFits : 24 ≤ bytes.val.length - 9988 := by
    rw [bytesLengthExact]
    omega
  have queryFits : 9936 ≤ bytes.val.length - 10012 := by
    rw [bytesLengthExact]
    omega
  have frontierFits :
      frontierNodes.val * 26 ≤ bytes.val.length - 19948 := by
    rw [bytesLengthExact]
    omega
  have c1RootFitsExact :
      26 ≤ 19948 + 2 * (frontierNodes.val * 26) - 9936 := by
    omega
  have c2RootFitsExact :
      26 ≤ 19948 + 2 * (frontierNodes.val * 26) - 9962 := by
    omega
  have nonceFitsExact :
      24 ≤ 19948 + 2 * (frontierNodes.val * 26) - 9988 := by
    omega
  have queryFitsExact :
      9936 ≤ 19948 + 2 * (frontierNodes.val * 26) - 10012 := by
    omega
  have frontierFitsExact :
      frontierNodes.val * 26 ≤
        19948 + 2 * (frontierNodes.val * 26) - 19948 := by
    omega
  have bytesWithinProductionLimit : ¬ Slice.len bytes > 30720#usize := by
    change ¬ 30720 < bytes.val.length
    rw [bytesLengthExact]
    omega
  have bytesWithinProductionLimitValue : ¬ 30720 < bytes.val.length := by
    rw [bytesLengthExact]
    omega
  have productionLimitFitsUsize : 30720 ≤ Std.Usize.max := by
    calc
      30720 ≤ 4294967295 := by norm_num
      _ ≤ Std.Usize.max := Usize.cMax_bound_concrete.1
  have totalWithinProductionLimit :
      19948 + 52 * frontierNodes.val ≤ 30720 := by
    omega
  have totalExactWithinUsize :
      19948 + 52 * frontierNodes.val ≤ Std.Usize.max := by
    exact le_trans totalWithinProductionLimit productionLimitFitsUsize
  have frontierOffsetWithinUsize :
      19948 + 26 * frontierNodes.val ≤ Std.Usize.max := by
    omega
  unfold V7DeferredParserGenerated.v7_onefold.parse_v7_compact_onefold_wire_deferred at accepted
  unfold V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality at accepted
  simp [V7DeferredParserGenerated.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE,
    V7DeferredParserGenerated.v7_onefold.V7_COMPACT_DIGEST_BYTES,
    deferred_production_limit_exact,
    deferred_body_without_frontiers_exact,
    deferred_query_section_bytes_exact,
    deferred_fixed_packed_field_bytes_exact,
    deferred_work_nonce_bytes_exact,
    frontierBytesRun, doubledFrontierRun, totalBytesRun,
    frontierNotOversized, frontierValueNotOversized,
    bytesLengthUsize, bytesLengthToTotal,
    bytesWithinProductionLimit, bytesWithinProductionLimitValue,
    if_pos fixedPrefixFitsExact,
    c1RootFits, c2RootFits, nonceFits, queryFits, frontierFits,
    c1RootFitsExact, c2RootFitsExact, nonceFitsExact,
    queryFitsExact, frontierFitsExact,
    core.option.Option.ok_or,
    core.option.Option.unwrap_or_default,
    core.option.OptionShared0T.copied,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.result.Result.map_err,
    core.slice.Slice.last,
    core.slice.Slice.split_at,
    core.array.TryFromSharedArraySlice.try_from,
    Bind.bind, Aeneas.Std.bind, lift] at accepted
  all_goals
    repeat' first
      | split at accepted
  all_goals
    simp_all [deferredParserExactLayout, bytesLengthExact,
      c1RootFits, c2RootFits, nonceFits, queryFits, frontierFits,
      c1RootFitsExact, c2RootFitsExact, nonceFitsExact,
      queryFitsExact, frontierFitsExact,
      List.length_drop, List.length_take,
      core.option.Option.ok_or,
      core.option.Option.unwrap_or_default,
      core.option.OptionShared0T.copied,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.result.Result.map_err,
      core.slice.Slice.last,
      core.slice.Slice.split_at,
      core.array.TryFromSharedArraySlice.try_from,
      Bind.bind, Aeneas.Std.bind, lift]
  case h_1 =>
    rename_i splitResult splitPair bitvectorEq splitPairEq
    cases splitPairEq
    have c1FitCase : 26 ≤ bytes.val.length - 9936 := by
      rw [bytesLengthExact]
      omega
    have c2FitCase : 26 ≤ bytes.val.length - 9962 := by
      rw [bytesLengthExact]
      omega
    have nonceFitCase : 24 ≤ bytes.val.length - 9988 := by
      rw [bytesLengthExact]
      omega
    have c1RootListLength :
        ((bytes.val.drop 9936).take 26).length = 26 := by
      simp [List.length_take, List.length_drop, c1FitCase]
    have c2RootListLength :
        ((bytes.val.drop 9962).take 26).length = 26 := by
      simp [List.length_take, List.length_drop, c2FitCase]
    have nonceListLength :
        ((bytes.val.drop 9988).take 24).length = 24 := by
      simp [List.length_take, List.length_drop, nonceFitCase]
    have c1RootSliceLength :
        ∀ property : ((bytes.val.drop 9936).take 26).length ≤ Std.Usize.max,
          Slice.len (⟨(bytes.val.drop 9936).take 26, property⟩ : Slice Std.U8) =
            26#usize := by
      intro property
      apply UScalar.eq_of_val_eq
      simpa using c1RootListLength
    have c2RootSliceLength :
        ∀ property : ((bytes.val.drop 9962).take 26).length ≤ Std.Usize.max,
          Slice.len (⟨(bytes.val.drop 9962).take 26, property⟩ : Slice Std.U8) =
            26#usize := by
      intro property
      apply UScalar.eq_of_val_eq
      simpa using c2RootListLength
    have nonceSliceLength :
        ∀ property : ((bytes.val.drop 9988).take 24).length ≤ Std.Usize.max,
          Slice.len (⟨(bytes.val.drop 9988).take 24, property⟩ : Slice Std.U8) =
            24#usize := by
      intro property
      apply UScalar.eq_of_val_eq
      simpa using nonceListLength
    repeat' first
      | split at accepted
    all_goals
      simp_all [deferredParserExactLayout, bytesLengthExact,
        frontierFits,
        c1RootFitsExact, c2RootFitsExact, nonceFitsExact,
        queryFitsExact,
        c1RootSliceLength, c2RootSliceLength, nonceSliceLength,
        List.length_drop, List.length_take,
        core.option.Option.ok_or,
        core.option.Option.unwrap_or_default,
        core.option.OptionShared0T.copied,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.result.Result.map_err,
        core.slice.Slice.last,
        core.slice.Slice.split_at,
        core.array.TryFromSharedArraySlice.try_from,
        Bind.bind, Aeneas.Std.bind, lift]
    all_goals
      repeat' first
        | split at accepted
    all_goals
      simp_all [deferredParserExactLayout, bytesLengthExact,
        List.length_drop, List.length_take,
        core.option.Option.ok_or,
        core.option.Option.unwrap_or_default,
        core.option.OptionShared0T.copied,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.result.Result.map_err,
        core.slice.Slice.last,
        core.slice.Slice.split_at,
        core.array.TryFromSharedArraySlice.try_from,
        Bind.bind, Aeneas.Std.bind, lift]
    subst wire
    simp [Nat.mul_comm]

/-- The Merkle-facing parser fields are byte-for-byte sublists of the input.
This is the explicit endianness boundary: roots and frontiers undergo no
integer decoding in the translated parser. -/
theorem deferred_parser_merkle_material_is_raw_bytes
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (wire : V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire)
    (accepted :
      V7DeferredParserGenerated.v7_onefold.parse_v7_compact_onefold_wire_deferred
          bytes frontierNodes = .ok (.Ok wire)) :
    wire.c1_root.val = (bytes.val.drop 9936).take 26 ∧
      wire.c2_root.val = (bytes.val.drop 9962).take 26 ∧
      wire.c1_frontier.val =
        (bytes.val.drop 19948).take (26 * frontierNodes.val) ∧
      wire.c2_frontier.val =
        bytes.val.drop (19948 + 26 * frontierNodes.val) := by
  rcases deferred_parser_success_has_exact_layout
      bytes frontierNodes wire accepted with
    ⟨_, _, _, c1Root, c2Root, _, _, c1Frontier, c2Frontier⟩
  exact ⟨c1Root, c2Root, c1Frontier, c2Frontier⟩

/-- A byte string of any short, long, or trailing-extended length cannot be
returned successfully by the translated parser. -/
theorem deferred_parser_rejects_wrong_or_trailing_length
    (bytes : Slice Std.U8) (frontierNodes : Std.Usize)
    (wrongLength : bytes.val.length ≠ 19948 + 52 * frontierNodes.val) :
    ∀ wire : V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire,
      V7DeferredParserGenerated.v7_onefold.parse_v7_compact_onefold_wire_deferred
          bytes frontierNodes ≠ .ok (.Ok wire) := by
  intro wire accepted
  exact wrongLength
    (deferred_parser_success_has_exact_layout
      bytes frontierNodes wire accepted).2.1

/-! ## Literal source hash inputs -/

def c1SourceInput (value : Slice Std.U8)
    (salt : Array Std.U8 32#usize) : List Byte :=
  [⟨0x10, by norm_num⟩, ⟨0x71, by norm_num⟩] ++
    AspisV7MerkleK12SourceBridge.generatedSliceBytes value ++ AspisV7MerkleK12SourceBridge.generatedArrayBytes salt

def c2SourceInput (value : Slice Std.U8)
    (salt : Array Std.U8 32#usize) : List Byte :=
  [⟨0x10, by norm_num⟩, ⟨0xf1, by norm_num⟩] ++
    AspisV7MerkleK12SourceBridge.generatedSliceBytes value ++ AspisV7MerkleK12SourceBridge.generatedArrayBytes salt

def nodeSourceInput (left right : Array Std.U8 26#usize) : List Byte :=
  [⟨0x11, by norm_num⟩] ++ AspisV7MerkleK12SourceBridge.generatedArrayBytes left ++
    AspisV7MerkleK12SourceBridge.generatedArrayBytes right

theorem c1_source_input_eq_frozen_serialize
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 403) :
    c1SourceInput value salt =
      AspisPool.V7MerkleQueryGrammar.serialize
        (.c1Leaf (sliceFixed (n := 403) value) (saltFixed salt)) := by
  simp [c1SourceInput, AspisPool.V7MerkleQueryGrammar.serialize,
    fixedBytes_sliceFixed value valueLength]

theorem c2_source_input_eq_frozen_serialize
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 186) :
    c2SourceInput value salt =
      AspisPool.V7MerkleQueryGrammar.serialize
        (.c2Leaf (sliceFixed (n := 186) value) (saltFixed salt)) := by
  simp [c2SourceInput, AspisPool.V7MerkleQueryGrammar.serialize,
    fixedBytes_sliceFixed value valueLength]

theorem node_source_input_eq_frozen_serialize
    (left right : Array Std.U8 26#usize) :
    nodeSourceInput left right =
      AspisPool.V7MerkleQueryGrammar.serialize (.node (digestFixed left) (digestFixed right)) := by
  simp [nodeSourceInput, AspisPool.V7MerkleQueryGrammar.serialize]

/-! ## Exact lengths and offsets

These equations expose the offsets directly.  In particular, the C1 salt
starts at byte 405, the C2 salt starts at byte 188, and the node's right child
starts at byte 27.  All quantities are byte strings, so there is no integer
endianness convention hidden inside these three SHA inputs.
-/

theorem c1_source_input_exact_layout
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 403) :
    (c1SourceInput value salt).length = 437 ∧
      (c1SourceInput value salt).take 2 = [0x10, 0x71] ∧
      ((c1SourceInput value salt).drop 2).take 403 =
        AspisV7MerkleK12SourceBridge.generatedSliceBytes value ∧
      (c1SourceInput value salt).drop 405 =
        AspisV7MerkleK12SourceBridge.generatedArrayBytes salt := by
  have saltLength :
      (AspisV7MerkleK12SourceBridge.generatedArrayBytes salt).length = 32 := by
    simpa using generatedArrayBytes_length salt
  simp [c1SourceInput, valueLength, saltLength]

theorem c2_source_input_exact_layout
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 186) :
    (c2SourceInput value salt).length = 220 ∧
      (c2SourceInput value salt).take 2 = [0x10, 0xf1] ∧
      ((c2SourceInput value salt).drop 2).take 186 =
        AspisV7MerkleK12SourceBridge.generatedSliceBytes value ∧
      (c2SourceInput value salt).drop 188 =
        AspisV7MerkleK12SourceBridge.generatedArrayBytes salt := by
  have saltLength :
      (AspisV7MerkleK12SourceBridge.generatedArrayBytes salt).length = 32 := by
    simpa using generatedArrayBytes_length salt
  simp [c2SourceInput, valueLength, saltLength]

theorem node_source_input_exact_layout
    (left right : Array Std.U8 26#usize) :
    (nodeSourceInput left right).length = 53 ∧
      (nodeSourceInput left right).take 1 = [0x11] ∧
      ((nodeSourceInput left right).drop 1).take 26 =
        AspisV7MerkleK12SourceBridge.generatedArrayBytes left ∧
      (nodeSourceInput left right).drop 27 =
        AspisV7MerkleK12SourceBridge.generatedArrayBytes right := by
  have leftLength :
      (AspisV7MerkleK12SourceBridge.generatedArrayBytes left).length = 26 := by
    simpa using generatedArrayBytes_length left
  have rightLength :
      (AspisV7MerkleK12SourceBridge.generatedArrayBytes right).length = 26 := by
    simpa using generatedArrayBytes_length right
  simp [nodeSourceInput, leftLength, rightLength]

/-! ## Extracted hashing functions use precisely those serializations -/

theorem truncate_sha256_v7_is_first_26_bytes
    (digest : Array Std.U8 32#usize) (output : Array Std.U8 26#usize)
    (run : V7MerkleK12Generated.v7_merkle208.truncate_sha256_v7 digest = .ok output) :
    AspisV7MerkleK12SourceBridge.generatedArrayBytes output =
      (AspisV7MerkleK12SourceBridge.generatedArrayBytes digest).take 26 :=
  AspisV7MerkleK12SourceBridge.truncate_sha256_v7_exact digest output run

theorem private_leaf_hash_v7_c1_matches_frozen_serialize
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (output : Array Std.U8 26#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 403)
    (run : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
      hash 0x71#u8 value salt = .ok output) :
    AspisV7MerkleK12SourceBridge.generatedArrayBytes output =
      (sha256 (AspisPool.V7MerkleQueryGrammar.serialize
        (.c1Leaf (sliceFixed (n := 403) value) (saltFixed salt)))).take 26 := by
  rw [← c1_source_input_eq_frozen_serialize value salt valueLength]
  simpa [c1SourceInput, AspisV7MerkleK12SourceBridge.generatedU8ToByte] using
    AspisV7MerkleK12SourceBridge.private_leaf_hash_v7_exact sha256 hash hashSemantics
      0x71#u8 value salt output run

theorem private_leaf_hash_v7_c2_matches_frozen_serialize
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (output : Array Std.U8 26#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 186)
    (run : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
      hash 0xf1#u8 value salt = .ok output) :
    AspisV7MerkleK12SourceBridge.generatedArrayBytes output =
      (sha256 (AspisPool.V7MerkleQueryGrammar.serialize
        (.c2Leaf (sliceFixed (n := 186) value) (saltFixed salt)))).take 26 := by
  rw [← c2_source_input_eq_frozen_serialize value salt valueLength]
  simpa [c2SourceInput, AspisV7MerkleK12SourceBridge.generatedU8ToByte] using
    AspisV7MerkleK12SourceBridge.private_leaf_hash_v7_exact sha256 hash hashSemantics
      0xf1#u8 value salt output run

theorem node_hash_v7_matches_frozen_serialize
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (left right output : Array Std.U8 26#usize)
    (run : V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash left right = .ok output) :
    AspisV7MerkleK12SourceBridge.generatedArrayBytes output =
      (sha256 (AspisPool.V7MerkleQueryGrammar.serialize
        (.node (digestFixed left) (digestFixed right)))).take 26 := by
  rw [← node_source_input_eq_frozen_serialize]
  simpa [nodeSourceInput] using
    AspisV7MerkleK12SourceBridge.node_hash_v7_exact sha256 hash hashSemantics left right output run

/-! ## Frozen parser correspondence and fail-closed grammar -/

theorem c1_source_input_parses_exactly
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 403) :
    AspisPool.V7MerkleQueryExtractor.parseTypedPreimage (c1SourceInput value salt) =
      some (.c1Leaf (sliceFixed (n := 403) value) (saltFixed salt)) := by
  rw [c1_source_input_eq_frozen_serialize value salt valueLength]
  exact AspisPool.V7MerkleParserRoundtrip.parse_serialize_typed_preimage _

theorem c2_source_input_parses_exactly
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 186) :
    AspisPool.V7MerkleQueryExtractor.parseTypedPreimage (c2SourceInput value salt) =
      some (.c2Leaf (sliceFixed (n := 186) value) (saltFixed salt)) := by
  rw [c2_source_input_eq_frozen_serialize value salt valueLength]
  exact AspisPool.V7MerkleParserRoundtrip.parse_serialize_typed_preimage _

theorem node_source_input_parses_exactly
    (left right : Array Std.U8 26#usize) :
    AspisPool.V7MerkleQueryExtractor.parseTypedPreimage (nodeSourceInput left right) =
      some (.node (digestFixed left) (digestFixed right)) := by
  rw [node_source_input_eq_frozen_serialize]
  exact AspisPool.V7MerkleParserRoundtrip.parse_serialize_typed_preimage _

/-- Successful parsing is equivalent to exact byte equality with one of the
three frozen serializations.  Therefore a wrong length, wrong tag, wrong
offset, or trailing byte is rejected rather than silently discarded. -/
theorem frozen_parser_success_iff_exact_serialization
    (input : AspisPool.V7MerkleQueryGrammar.RawHashInput) (typed : AspisPool.V7MerkleQueryGrammar.TypedPreimage) :
    AspisPool.V7MerkleQueryExtractor.parseTypedPreimage input = some typed ↔
      AspisPool.V7MerkleQueryGrammar.serialize typed = input :=
  AspisPool.V7MerkleParserRoundtrip.parse_typed_preimage_eq_some_iff input typed

theorem frozen_parser_rejects_untyped_input
    (input : AspisPool.V7MerkleQueryGrammar.RawHashInput) :
    AspisPool.V7MerkleQueryExtractor.parseTypedPreimage input = none ↔
      ∀ typed : AspisPool.V7MerkleQueryGrammar.TypedPreimage, AspisPool.V7MerkleQueryGrammar.serialize typed ≠ input := by
  constructor
  · intro rejected typed serialized
    have parsed := AspisPool.V7MerkleParserRoundtrip.parse_serialize_typed_preimage typed
    rw [serialized, rejected] at parsed
    simp at parsed
  · intro noSerialization
    cases parsed : AspisPool.V7MerkleQueryExtractor.parseTypedPreimage input with
    | none => rfl
    | some typed =>
        exact False.elim (noSerialization typed
          (AspisPool.V7MerkleParserRoundtrip.serialize_parse_typed_preimage input typed parsed))

theorem frozen_parser_rejects_trailing_bytes
    (typed : AspisPool.V7MerkleQueryGrammar.TypedPreimage) (trailing : List Byte)
    (hasTrailing : trailing ≠ []) :
    AspisPool.V7MerkleQueryExtractor.parseTypedPreimage (AspisPool.V7MerkleQueryGrammar.serialize typed ++ trailing) = none := by
  rw [frozen_parser_rejects_untyped_input]
  intro other equalWithTrailing
  have lengthsEqual := congrArg List.length equalWithTrailing
  have trailingPositive : 0 < trailing.length := by
    cases trailing with
    | nil => contradiction
    | cons head tail => simp
  cases typed <;> cases other <;>
    simp [AspisPool.V7MerkleQueryGrammar.serialize] at equalWithTrailing
  all_goals
    simp [AspisPool.V7MerkleQueryGrammar.serialize] at lengthsEqual
    omega

/-! ## The two leaves use one disclosed salt

This is a byte-level sharing theorem: both exact source inputs below are built
from the same generated 32-byte array and both frozen typed leaves contain the
same `Salt32` value.  It introduces no equality premise between independent
salts.
-/

theorem paired_leaf_source_inputs_share_exact_salt
    (c1Value c2Value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (c1Length : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c1Value).length = 403)
    (c2Length : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c2Value).length = 186) :
    ∃ sharedSalt : AspisPool.V7MerkleQueryGrammar.Salt32,
      c1SourceInput c1Value salt = AspisPool.V7MerkleQueryGrammar.serialize
        (.c1Leaf (sliceFixed (n := 403) c1Value) sharedSalt) ∧
      c2SourceInput c2Value salt = AspisPool.V7MerkleQueryGrammar.serialize
        (.c2Leaf (sliceFixed (n := 186) c2Value) sharedSalt) := by
  exact ⟨saltFixed salt,
    c1_source_input_eq_frozen_serialize c1Value salt c1Length,
    c2_source_input_eq_frozen_serialize c2Value salt c2Length⟩

#print axioms truncate_sha256_v7_is_first_26_bytes
#print axioms deferred_parser_success_has_exact_layout
#print axioms deferred_parser_merkle_material_is_raw_bytes
#print axioms deferred_parser_rejects_wrong_or_trailing_length
#print axioms private_leaf_hash_v7_c1_matches_frozen_serialize
#print axioms private_leaf_hash_v7_c2_matches_frozen_serialize
#print axioms node_hash_v7_matches_frozen_serialize
#print axioms frozen_parser_success_iff_exact_serialization
#print axioms frozen_parser_rejects_untyped_input
#print axioms frozen_parser_rejects_trailing_bytes
#print axioms paired_leaf_source_inputs_share_exact_salt

end AspisV7MerkleK12LayoutBridge
