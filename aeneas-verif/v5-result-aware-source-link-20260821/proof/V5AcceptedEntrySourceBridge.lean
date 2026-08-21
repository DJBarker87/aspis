import V5AcceptedEntryGenerated.Entry
import V5TranscriptFullDriverJoin

/-!
# Accepted production entry to transcript-model bridge

This file starts from the unchanged generated parser and composite verifier
body.  It projects the parser's successful result into the exact transcript
input used by the maintained model and into the separately generated relation
and tail helper types.  The constructions below are byte-preserving; they add
no cryptographic assumption.
-/

namespace AspisV5AcceptedEntrySourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection

abbrev EntryParsed :=
  V5AcceptedEntryGenerated.v5_cu_probe.ParsedProbeData

def byteOfGenerated (value : Std.U8) :
    AspisFormal.V5ExactRuntimeWireRepair.Byte :=
  AspisV5PrefixNonceEncodingProof.generatedToByte value

def generatedOfByte
    (value : AspisFormal.V5ExactRuntimeWireRepair.Byte) : Std.U8 :=
  AspisV5PrefixByteEncodingProof.byteToGenerated value

@[simp] theorem generatedOfByte_byteOfGenerated (value : Std.U8) :
    generatedOfByte (byteOfGenerated value) = value := by
  apply UScalar.eq_of_val_eq
  simp [generatedOfByte, byteOfGenerated,
    AspisV5PrefixByteEncodingProof.byteToGenerated,
    AspisV5PrefixNonceEncodingProof.generatedToByte]

@[simp] theorem relationGeneratedOfByte_byteOfGenerated (value : Std.U8) :
    AspisV5TranscriptRelationFinalJoin.byteToGenerated
        (byteOfGenerated value) = value := by
  apply UScalar.eq_of_val_eq
  simp [AspisV5TranscriptRelationFinalJoin.byteToGenerated,
    byteOfGenerated, AspisV5PrefixNonceEncodingProof.generatedToByte]

def fixedOfArray {width : Std.Usize} (value : Array Std.U8 width) :
    FixedBytes width.val :=
  fun index => byteOfGenerated value.val[index.val]!

theorem fixedToGenerated_fixedOfArray {width : Std.Usize}
    (value : Array Std.U8 width) :
    AspisV5TranscriptRelationFinalJoin.fixedToGenerated
        (fixedOfArray value) = value.val := by
  apply List.ext_get
  · simp [AspisV5TranscriptRelationFinalJoin.fixedToGenerated, bytes,
      value.property]
  · intro index hleft hright
    simp only [AspisV5TranscriptRelationFinalJoin.fixedToGenerated, bytes,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, Function.comp_apply,
      fixedOfArray]
    rw [List.getElem!_eq_getElem?_getD, getElem?_pos value.val index hright]
    exact relationGeneratedOfByte_byteOfGenerated value.val[index]

def fixedAt (values : List Std.U8) (start width : Nat) :
    FixedBytes width :=
  fun index => byteOfGenerated values[start + index.val]!

theorem fixedToGenerated_fixedAt (values : List Std.U8)
    (start width : Nat) (hbound : start + width ≤ values.length) :
    AspisV5TranscriptRelationFinalJoin.fixedToGenerated
        (fixedAt values start width) =
      values.slice start (start + width) := by
  apply List.ext_get
  · simp [AspisV5TranscriptRelationFinalJoin.fixedToGenerated, bytes,
      List.slice_length]
    omega
  · intro index hleft hright
    have hwidth : index < width := by
      simpa [AspisV5TranscriptRelationFinalJoin.fixedToGenerated, bytes]
        using hleft
    have hindex : start + index < values.length := by
      omega
    simp only [AspisV5TranscriptRelationFinalJoin.fixedToGenerated, bytes,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn,
      fixedAt, Function.comp_apply]
    rw [List.getElem!_eq_getElem?_getD,
      getElem?_pos values (start + index) hindex]
    rw [List.getElem_slice start (start + width) index values
      ⟨by omega, by omega⟩]
    exact relationGeneratedOfByte_byteOfGenerated values[start + index]

theorem tailBytesOfU8_fixedOfArray {width : Std.Usize}
    (value : Array Std.U8 width) :
    AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8 value.val =
      bytes (fixedOfArray value) := by
  apply List.ext_get
  · simp [AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8, bytes,
      value.property]
  · intro index hleft hright
    have hindex : index < value.val.length := by
      simpa [AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8] using hleft
    simp only [AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8, bytes,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, fixedOfArray]
    rw [List.getElem!_eq_getElem?_getD,
      getElem?_pos value.val index hindex]
    simp only [Option.getD_some]
    apply Fin.ext
    simp [AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8,
      byteOfGenerated, AspisV5PrefixNonceEncodingProof.generatedToByte]

@[simp] theorem tailByteOfU8_eq_byteOfGenerated (value : Std.U8) :
    AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8 value =
      byteOfGenerated value := by
  apply Fin.ext
  simp [AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8,
    byteOfGenerated, AspisV5PrefixNonceEncodingProof.generatedToByte]

theorem tailBytesOfU8_fixedAt (values : List Std.U8)
    (start width : Nat) (hbound : start + width ≤ values.length) :
    AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8
        (values.slice start (start + width)) =
      bytes (fixedAt values start width) := by
  apply List.ext_get
  · simp [AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8, bytes,
      List.slice_length]
    omega
  · intro index hleft hright
    have hwidth : index < width := by
      simpa [AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8]
        using hright
    have hindex : start + index < values.length := by omega
    simp only [AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8, bytes,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, fixedAt]
    rw [List.getElem_slice start (start + width) index values
      ⟨by omega, by omega⟩]
    rw [List.getElem!_eq_getElem?_getD,
      getElem?_pos values (start + index) hindex]
    simp

theorem fixedToGenerated_fixedAt32_exact32At
    (values : List Std.U8) (start : Nat) :
    AspisV5TranscriptRelationFinalJoin.fixedToGenerated
        (fixedAt values start 32) =
      (V5TranscriptRelationGenerated.exact32At values start).val := by
  apply List.ext_get
  · simp [AspisV5TranscriptRelationFinalJoin.fixedToGenerated, bytes,
      V5TranscriptRelationGenerated.exact32At]
  · intro index hleft hright
    simp only [AspisV5TranscriptRelationFinalJoin.fixedToGenerated, bytes,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, fixedAt,
      V5TranscriptRelationGenerated.exact32At, Array.make,
      V5TranscriptRelationGenerated.exactByteAt]
    rw [List.getElem!_eq_getElem?_getD]
    exact relationGeneratedOfByte_byteOfGenerated
      (values[start + index]?.getD 0#u8)

def nonceOfGenerated (value : Std.U64) : Nonce64 :=
  ⟨value.val, by simpa using value.lt_succ_max⟩

@[simp] theorem nonceOfGenerated_val (value : Std.U64) :
    (nonceOfGenerated value).val = value.val := rfl

def toRelationParsed (parsed : EntryParsed) :
    AspisV5TranscriptFullDriverJoin.RelationParsed where
  gamma := []
  production_c1 := parsed.production_c1
  candidate_c1 := parsed.candidate_c1
  c2 := parsed.c2
  relation_scales := parsed.relation_scales
  relation_points := parsed.relation_points
  relation_claims := parsed.relation_claims
  relation_alphas := parsed.relation_alphas
  relation_final := parsed.relation_final
  v5_fold_nonces := parsed.v5_fold_nonces
  v5_batch_nonce := parsed.v5_batch_nonce
  v5_wire_prefix := parsed.v5_wire_prefix
  v5_atomic_terminal_context := parsed.v5_atomic_terminal_context
  v5_private_roots := {
    c1 := parsed.v5_private_roots.c1
    c2 := parsed.v5_private_roots.c2
    later := parsed.v5_private_roots.later
  }
  v5_final_coefficients := parsed.v5_final_coefficients
  v5_relation_stress := parsed.v5_relation_stress
  v5_final_nonce := parsed.v5_final_nonce
  v5_query_selector := parsed.v5_query_selector
  v5_private_proof := parsed.v5_private_proof

def toTailParsed (parsed : EntryParsed) :
    AspisV5TranscriptFullDriverJoin.TailParsed where
  gamma := 0#usize
  production_c1 := parsed.production_c1
  candidate_c1 := parsed.candidate_c1
  c2 := parsed.c2
  relation_scales := parsed.relation_scales
  relation_points := parsed.relation_points
  relation_claims := parsed.relation_claims
  relation_alphas := parsed.relation_alphas
  relation_final := parsed.relation_final
  v5_fold_nonces := parsed.v5_fold_nonces
  v5_batch_nonce := parsed.v5_batch_nonce
  v5_wire_prefix := parsed.v5_wire_prefix
  v5_atomic_terminal_context := parsed.v5_atomic_terminal_context
  v5_private_roots := ()
  v5_final_coefficients := parsed.v5_final_coefficients
  v5_relation_stress := parsed.v5_relation_stress
  v5_final_nonce := parsed.v5_final_nonce
  v5_query_selector := parsed.v5_query_selector
  v5_private_proof := parsed.v5_private_proof

def entryTranscriptInput (parsed : EntryParsed)
    (statementDigest : Array Std.U8 32#usize) : V5TranscriptInputs where
  statementDigest := fixedOfArray statementDigest
  circleRoot := fun
    | ⟨0, _⟩ => fixedAt parsed.v5_private_roots.c1.val 0 32
    | ⟨later + 1, _⟩ =>
        fixedAt parsed.v5_private_roots.later.val[later]!.val 0 32
  c2Root := fixedAt parsed.v5_private_roots.c2.val 0 32
  publicSalt := fun saltIndex =>
    fixedAt parsed.v5_wire_prefix.val (5863 + saltIndex.val * 32) 32
  initialClaim := fixedAt parsed.v5_wire_prefix.val 87 16
  semanticSumcheck := fun round =>
    fixedAt parsed.v5_wire_prefix.val (103 + round.val * 448) 448
  relationPoints := fixedAt parsed.relation_points.val 0 480
  statementEvaluations := fixedAt parsed.relation_claims.val 0 1216
  terminalClaims := fixedAt parsed.v5_wire_prefix.val 5799 48
  batchNonce := nonceOfGenerated parsed.v5_batch_nonce
  inactiveClaim := fixedAt parsed.v5_wire_prefix.val 5847 16
  oodValue := fun round sample =>
    fixedAt parsed.v5_relation_stress.val
      (160 + 16 * (2 * round.val + sample.val)) 16
  relationSumcheck := fun round =>
    fixedAt parsed.v5_relation_stress.val (416 + 112 * round.val) 112
  foldNonce := fun round =>
    nonceOfGenerated parsed.v5_fold_nonces.val[round.val]!
  finalPolynomial := fixedAt parsed.v5_final_coefficients.val 0 64
  finalNonce := nonceOfGenerated parsed.v5_final_nonce
  selector := byteOfGenerated parsed.v5_query_selector

theorem entry_tail_final_bytes (parsed : EntryParsed)
    (statementDigest : Array Std.U8 32#usize)
    (hlength : parsed.v5_final_coefficients.val.length = 64) :
    AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8
        (toTailParsed parsed).v5_final_coefficients.val =
      bytes (entryTranscriptInput parsed statementDigest).finalPolynomial := by
  simp only [toTailParsed, entryTranscriptInput]
  have hslice := tailBytesOfU8_fixedAt
    parsed.v5_final_coefficients.val 0 64 (by omega)
  have htake : parsed.v5_final_coefficients.val.slice 0 64 =
      parsed.v5_final_coefficients.val := by
    simp only [List.slice, List.drop_zero]
    exact (List.take_eq_self_iff _).2 (by omega)
  simpa [htake] using hslice

theorem entry_tail_nonce (parsed : EntryParsed)
    (statementDigest : Array Std.U8 32#usize) :
    AspisV5TranscriptTailUnchangedFinalJoin.nonceOfU64
        (toTailParsed parsed).v5_final_nonce =
      (entryTranscriptInput parsed statementDigest).finalNonce := by
  apply Fin.ext
  simp [AspisV5TranscriptTailUnchangedFinalJoin.nonceOfU64,
    toTailParsed, entryTranscriptInput, nonceOfGenerated,
    Nat.mod_eq_of_lt parsed.v5_final_nonce.lt_succ_max]

theorem entry_tail_selector (parsed : EntryParsed)
    (statementDigest : Array Std.U8 32#usize) :
    AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8
        parsed.v5_query_selector =
      (entryTranscriptInput parsed statementDigest).selector := by
  exact tailByteOfU8_eq_byteOfGenerated parsed.v5_query_selector

theorem entry_relation_projection (parsed : EntryParsed)
    (statementDigest : Array Std.U8 32#usize) :
    AspisV5TranscriptRelationFinalJoin.ExactRelationParsedProjection
      (entryTranscriptInput parsed statementDigest)
      (toRelationParsed parsed) := by
  constructor
  · intro round sample
    unfold AspisV5TranscriptRelationSourceProof.stressWindow
    simp only [toRelationParsed, entryTranscriptInput]
    rw [fixedToGenerated_fixedAt]
    · rfl
    · have hlength : parsed.v5_relation_stress.val.length = 928 := by
        simpa using parsed.v5_relation_stress.property
      omega
  · intro round
    unfold AspisV5TranscriptRelationSourceProof.stressWindow
    simp only [toRelationParsed, entryTranscriptInput]
    rw [fixedToGenerated_fixedAt]
    · rfl
    · have hlength : parsed.v5_relation_stress.val.length = 928 := by
        simpa using parsed.v5_relation_stress.property
      omega
  · intro round
    simp [toRelationParsed, entryTranscriptInput, nonceOfGenerated]
  · intro round
    fin_cases round
    · simp only [toRelationParsed, entryTranscriptInput, Fin.val_zero,
        Nat.zero_add, Fin.isValue, ↓reduceIte, Fin.val_one, Nat.add_sub_cancel]
      symm
      rw [fixedToGenerated_fixedAt]
      · simp only [List.slice, List.drop_zero]
        exact (List.take_eq_self_iff _).2 (by
          simpa using parsed.v5_private_roots.later.val[0]!.property.le)
      · simpa using parsed.v5_private_roots.later.val[0]!.property
    · simp only [toRelationParsed, entryTranscriptInput, Fin.val_one,
        Nat.one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      symm
      rw [fixedToGenerated_fixedAt]
      · simp only [List.slice, List.drop_zero]
        exact (List.take_eq_self_iff _).2 (by
          simpa using parsed.v5_private_roots.later.val[1]!.property.le)
      · simpa using parsed.v5_private_roots.later.val[1]!.property
    · simp only [toRelationParsed, entryTranscriptInput, Fin.reduceFinMk,
        OfNat.ofNat, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub]
      symm
      rw [fixedToGenerated_fixedAt]
      · simp only [List.slice, List.drop_zero]
        exact (List.take_eq_self_iff _).2 (by
          simpa using parsed.v5_private_roots.later.val[2]!.property.le)
      · simpa using parsed.v5_private_roots.later.val[2]!.property
  · intro round
    fin_cases round <;>
      simp [toRelationParsed, entryTranscriptInput,
        AspisV5TranscriptRelationSourceProof.publicSaltBytes,
        fixedToGenerated_fixedAt32_exact32At]

theorem bind_eq_ok_iff {alpha beta : Type}
    (action : Result alpha) (next : alpha → Result beta) (value : beta) :
    Bind.bind action next = .ok value ↔
      ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action <;> simp [Bind.bind, Aeneas.Std.bind]

theorem branch_eq_ok_of_continue {valueType errorType : Type}
    (result : core.result.Result valueType errorType) (value : valueType)
    (success :
      core.result.Result.Insts.CoreOpsTry.branch result =
        .ok (.Continue value)) :
    result = .Ok value := by
  cases result with
  | Ok actual =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using success
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at success

theorem range_index_success_length
    (data : Slice Std.U8) (start finish : Std.Usize) (out : Slice Std.U8)
    (success :
      core.slice.index.SliceIndexRangeUsizeSlice.index
          { start, «end» := finish } data = .ok out) :
    out.val.length = finish.val - start.val := by
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at success
  split at success
  · rename_i hbounds
    simp only [Result.ok.injEq] at success
    subst out
    have hspec :=
      core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
        { start, «end» := finish } data hbounds.1 hbounds.2
    simp only [core.slice.index.SliceIndexRangeUsizeSlice.index,
      hbounds.1, hbounds.2, and_self, ↓reduceIte,
      Aeneas.Std.WP.spec_ok] at hspec
    exact hspec.2
  · simp at success

theorem final_coefficients_offset_gap
    (finalOffset stressOffset : Std.Usize)
    (hfinal :
      V5AcceptedEntryGenerated.v5_cu_probe.V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET =
        .ok finalOffset)
    (hstress :
      V5AcceptedEntryGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_STRESS_OFFSET =
        .ok stressOffset) :
    stressOffset.val = finalOffset.val + 64 := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_STRESS_OFFSET at hstress
  rw [hfinal] at hstress
  simp only [bind_tc_ok] at hstress
  unfold V5AcceptedEntryGenerated.v5_cu_probe.V5_CU_PROBE_FINAL_COEFFICIENTS_BYTES at hstress
  unfold V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES at hstress
  have hmul : (4#usize * 16#usize : Result Std.Usize) =
      .ok 64#usize := by
    change UScalar.mul 4#usize 16#usize = .ok 64#usize
    norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
    cases System.Platform.numBits_eq <;> simp_all
  rw [hmul] at hstress
  simp only [bind_tc_ok] at hstress
  change UScalar.add finalOffset 64#usize = .ok stressOffset at hstress
  unfold UScalar.add UScalar.tryMk UScalar.tryMkOpt at hstress
  split at hstress
  · simp only [Result.ofOption, Result.ok.injEq] at hstress
    subst stressOffset
    rfl
  · simp [Result.ofOption] at hstress

theorem accepted_parse_with_layout_final_coefficients_length
    (data : Slice Std.U8) (privateProofOffset : Std.Usize)
    (parsed : EntryParsed)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.parse_probe_data_with_layout
          data none privateProofOffset =
        .ok (.Ok parsed)) :
    parsed.v5_final_coefficients.val.length = 64 := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.parse_probe_data_with_layout at success
  simp only at success
  split at success
  · simp at success
  · rw [bind_eq_ok_iff] at success
    obtain ⟨magic, _, success⟩ := success
    cases magic with
    | false => simp at success
    | true =>
      simp only [if_true] at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨workWire, _, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨productionC1, _, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaEnd, _, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaBytes, _, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaOption, _, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨gammaResult, _, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨flow, _, success⟩ := success
      cases flow with
      | Break residual =>
        cases residual with
        | Ok impossible => nomatch impossible
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at success
      | Continue gamma =>
        simp only at success
        rw [bind_eq_ok_iff] at success
        obtain ⟨relationFinalOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨prefixOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨relationFinal, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨candidateOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨c2Offset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨candidateC1, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨scaleOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨c2, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨pointOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨scales, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨claimOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨points, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨alphaOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨claims, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨alphas, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨wirePrefix, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨terminalOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨privateRootsOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨terminalContext, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨privateRoots, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨finalOffset, hfinalOffset, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨stressOffset, hstressOffset, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨finalCoefficients, hfinalCoefficients, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨finalNonceOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨stressBytes, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨stressArrayResult, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨stressArray, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨privateProof, _, success⟩ := success
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at success
        subst parsed
        have hlength := range_index_success_length data finalOffset
          stressOffset finalCoefficients hfinalCoefficients
        have hgap := final_coefficients_offset_gap finalOffset stressOffset
          hfinalOffset hstressOffset
        change finalCoefficients.val.length = 64
        omega

theorem accepted_parse_final_coefficients_length
    (data : Slice Std.U8) (parsed : EntryParsed)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.parse_probe_data data =
        .ok (.Ok parsed)) :
    parsed.v5_final_coefficients.val.length = 64 := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.parse_probe_data at success
  simp only at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨maxProofBytes, _, success⟩ := success
  split at success
  · simp at success
  · rw [bind_eq_ok_iff] at success
    obtain ⟨privateProofOffset, _, success⟩ := success
    exact accepted_parse_with_layout_final_coefficients_length
      data privateProofOffset parsed success

/-- Everything the complete transcript join needs from the unchanged parser.
The only premise is that the generated production parser returned this value. -/
structure AcceptedParserTranscriptProjection
    (parsed : EntryParsed) (statementDigest : Array Std.U8 32#usize) : Prop where
  relation :
    AspisV5TranscriptRelationFinalJoin.ExactRelationParsedProjection
      (entryTranscriptInput parsed statementDigest) (toRelationParsed parsed)
  finalPolynomial :
    AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8
        (toTailParsed parsed).v5_final_coefficients.val =
      bytes (entryTranscriptInput parsed statementDigest).finalPolynomial
  finalNonce :
    AspisV5TranscriptTailUnchangedFinalJoin.nonceOfU64
        (toTailParsed parsed).v5_final_nonce =
      (entryTranscriptInput parsed statementDigest).finalNonce
  selector :
    AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8
        parsed.v5_query_selector =
      (entryTranscriptInput parsed statementDigest).selector

theorem accepted_parse_builds_transcript_projection
    (data : Slice Std.U8) (parsed : EntryParsed)
    (statementDigest : Array Std.U8 32#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.parse_probe_data data =
        .ok (.Ok parsed)) :
    AcceptedParserTranscriptProjection parsed statementDigest := by
  have hlength := accepted_parse_final_coefficients_length data parsed success
  exact {
    relation := entry_relation_projection parsed statementDigest
    finalPolynomial := entry_tail_final_bytes parsed statementDigest hlength
    finalNonce := entry_tail_nonce parsed statementDigest
    selector := entry_tail_selector parsed statementDigest
  }

abbrev EntryQM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev EntryTranscript :=
  V5AcceptedEntryGenerated.aspis_core.transcript.Transcript
abbrev EntryStatement :=
  V5AcceptedEntryGenerated.aspis_statement.atomic_statement.AtomicPaymentStatementV4
abbrev EntryVerifiedPrefix :=
  V5AcceptedEntryGenerated.v5_cu_probe.VerifiedRealV5Wire
abbrev EntryVerifiedTerminal :=
  V5AcceptedEntryGenerated.v5_atomic_terminal.VerifiedV5AtomicTerminal
abbrev EntryPreparedClaims :=
  V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims

/-- The proposition-only facts carried by one exact successful call and value
flow of the unchanged composite verifier.  The data are parameters so this
record remains in `Prop` and can be obtained by inverting a successful result. -/
structure AcceptedCompositeCallFacts
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (verifiedPrefix : EntryVerifiedPrefix)
    (prefixTranscript : EntryTranscript)
    (verifiedTerminal : EntryVerifiedTerminal)
    (relationTranscript : EntryTranscript)
    (finalPolynomial : Array EntryQM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (alphas : Array EntryQM31 4#usize)
    (friSum : EntryQM31)
    (preparedClaims : EntryPreparedClaims)
    (relationSum phaseSum : EntryQM31) : Prop where
  prefixSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
        parsed liveStatement statementDigest
        V5AcceptedEntryGenerated.verify.sbf_hashv =
      .ok (.Ok (verifiedPrefix, prefixTranscript))
  terminalSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_atomic_terminal_with_prefix
        parsed liveStatement verifiedPrefix =
      .ok (.Ok verifiedTerminal)
  relationSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds
        prefixTranscript parsed = .ok (.Ok relationTranscript)
  querySuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript
        relationTranscript parsed verifiedPrefix.round_challenges =
      .ok (.Ok (finalPolynomial, queries))
  alphaSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas parsed =
      .ok (.Ok alphas)
  friSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_fri_phase
        parsed queries finalPolynomial alphas verifiedPrefix.gamma =
      .ok (.Ok (friSum, preparedClaims))
  relationCheckSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_relation_phase
        parsed finalPolynomial alphas verifiedPrefix.kappa
        verifiedPrefix.inactive_claim verifiedPrefix.round_challenges
        preparedClaims = .ok (.Ok relationSum)
  phaseSumSuccess :
    V5AcceptedEntryGenerated.aspis_core.field.QM31.add friSum relationSum =
      .ok phaseSum
  acceptedSumSuccess :
    V5AcceptedEntryGenerated.aspis_core.field.QM31.add
        phaseSum verifiedTerminal.masked = .ok acceptedValue

/-- The exact successful call and value flow of the unchanged composite
verifier.  In particular the same four decoded alphas are passed to both the
FRI checks and the relation checks, and the same final polynomial and queries
returned by the transcript tail are passed to the FRI checks. -/
def AcceptedCompositeCallChain
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31) : Prop :=
  ∃ verifiedPrefix prefixTranscript verifiedTerminal relationTranscript
      finalPolynomial queries alphas friSum preparedClaims relationSum phaseSum,
    AcceptedCompositeCallFacts accountData parsed liveStatement statementDigest
      acceptedValue verifiedPrefix prefixTranscript verifiedTerminal
      relationTranscript finalPolynomial queries alphas friSum preparedClaims
      relationSum phaseSum

/-- A successful result from the generated production composite verifier
determines every successful helper call and the exact values passed between
those calls.  This is an inversion of the extracted Rust body, not an
additional implementation/model premise. -/
theorem accepted_composite_builds_call_chain
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    AcceptedCompositeCallChain accountData parsed liveStatement
      statementDigest acceptedValue := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨prefixResult, prefixSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨prefixFlow, prefixBranchSuccess, success⟩ := success
  cases prefixFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at success
  | Continue prefixPair =>
      rcases prefixPair with ⟨verifiedPrefix, prefixTranscript⟩
      have hprefixResult := branch_eq_ok_of_continue
        prefixResult (verifiedPrefix, prefixTranscript) prefixBranchSuccess
      rw [hprefixResult] at prefixSuccess
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨terminalResult, terminalSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨terminalFlow, terminalBranchSuccess, success⟩ := success
      cases terminalFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at success
      | Continue verifiedTerminal =>
          have hterminalResult := branch_eq_ok_of_continue
            terminalResult verifiedTerminal terminalBranchSuccess
          rw [hterminalResult] at terminalSuccess
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨relationResult, relationSuccess, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨relationFlow, relationBranchSuccess, success⟩ := success
          cases relationFlow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame, core.convert.FromSame.from] at success
          | Continue relationTranscript =>
              have hrelationResult := branch_eq_ok_of_continue
                relationResult relationTranscript relationBranchSuccess
              rw [hrelationResult] at relationSuccess
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨queryResult, querySuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨queryFlow, queryBranchSuccess, success⟩ := success
              cases queryFlow with
              | Break residual =>
                  cases residual with
                  | Ok impossible => nomatch impossible
                  | Err error =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame, core.convert.FromSame.from] at success
              | Continue queryPair =>
                  rcases queryPair with ⟨finalPolynomial, queries⟩
                  have hqueryResult := branch_eq_ok_of_continue
                    queryResult (finalPolynomial, queries) queryBranchSuccess
                  rw [hqueryResult] at querySuccess
                  simp only at success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨alphaResult, alphaSuccess, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨alphaFlow, alphaBranchSuccess, success⟩ := success
                  cases alphaFlow with
                  | Break residual =>
                      cases residual with
                      | Ok impossible => nomatch impossible
                      | Err error =>
                          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame, core.convert.FromSame.from] at success
                  | Continue alphas =>
                      have halphaResult := branch_eq_ok_of_continue
                        alphaResult alphas alphaBranchSuccess
                      rw [halphaResult] at alphaSuccess
                      simp only at success
                      rw [bind_eq_ok_iff] at success
                      obtain ⟨friResult, friSuccess, success⟩ := success
                      rw [bind_eq_ok_iff] at success
                      obtain ⟨friFlow, friBranchSuccess, success⟩ := success
                      cases friFlow with
                      | Break residual =>
                          cases residual with
                          | Ok impossible => nomatch impossible
                          | Err error =>
                              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                core.convert.FromSame, core.convert.FromSame.from] at success
                      | Continue friPair =>
                          rcases friPair with ⟨friSum, preparedClaims⟩
                          have hfriResult := branch_eq_ok_of_continue
                            friResult (friSum, preparedClaims) friBranchSuccess
                          rw [hfriResult] at friSuccess
                          simp only at success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨relationCheckResult, relationCheckSuccess, success⟩ := success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨relationCheckFlow, relationCheckBranchSuccess, success⟩ := success
                          cases relationCheckFlow with
                          | Break residual =>
                              cases residual with
                              | Ok impossible => nomatch impossible
                              | Err error =>
                                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame, core.convert.FromSame.from] at success
                          | Continue relationSum =>
                              have hrelationCheckResult := branch_eq_ok_of_continue
                                relationCheckResult relationSum relationCheckBranchSuccess
                              rw [hrelationCheckResult] at relationCheckSuccess
                              simp only at success
                              rw [bind_eq_ok_iff] at success
                              obtain ⟨_, _, success⟩ := success
                              rw [bind_eq_ok_iff] at success
                              obtain ⟨phaseSum, phaseSumSuccess, success⟩ := success
                              rw [bind_eq_ok_iff] at success
                              obtain ⟨finalValue, acceptedSumSuccess, success⟩ := success
                              simp only [Result.ok.injEq,
                                core.result.Result.Ok.injEq] at success
                              subst finalValue
                              refine ⟨verifiedPrefix, prefixTranscript,
                                verifiedTerminal, relationTranscript,
                                finalPolynomial, queries, alphas, friSum,
                                preparedClaims, relationSum, phaseSum, ?_⟩
                              exact {
                                prefixSuccess := prefixSuccess
                                terminalSuccess := terminalSuccess
                                relationSuccess := relationSuccess
                                querySuccess := querySuccess
                                alphaSuccess := alphaSuccess
                                friSuccess := friSuccess
                                relationCheckSuccess := relationCheckSuccess
                                phaseSumSuccess := phaseSumSuccess
                                acceptedSumSuccess := acceptedSumSuccess
                              }

#print axioms entry_relation_projection
#print axioms accepted_parse_final_coefficients_length
#print axioms accepted_parse_builds_transcript_projection
#print axioms accepted_composite_builds_call_chain

end AspisV5AcceptedEntrySourceBridge
