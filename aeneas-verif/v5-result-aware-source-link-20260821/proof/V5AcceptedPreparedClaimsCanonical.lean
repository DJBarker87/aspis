import V5AcceptedFriModelInputBinding
import V5PreparedPointClaimsProof

/-!
# Canonical prepared claims from the accepted source call

The accepted verifier now contains a concrete definition of
`prepare_v5_pcs_claims`.  This file proves that every one of the four point
claims returned by a successful call has a canonical four-limb field
representation.  The proof follows the translated decoder, gamma-power and
five-block accumulation calls; it does not add a property of an opaque
callback.
-/

namespace AspisV5AcceptedPreparedClaimsCanonical

open Aeneas Aeneas.Std Result
open AspisV5AcceptedFriModelInputBinding
open AspisV5PreparedPointClaimsSourceProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev EntryQM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev KernelQM31 :=
  V5RelationPreparedClaimsGenerated.aspis_core.field.QM31

def EntryCanonicalQM31 (value : EntryQM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c0.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c0.b.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c1.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c1.b.val

def EntryCanonicalArray {count : Std.Usize}
    (values : Array EntryQM31 count) : Prop :=
  ∀ index : Fin count.val, EntryCanonicalQM31 values.val[index.val]!

@[simp] theorem toPreparedKernel_canonical_iff (value : EntryQM31) :
    KernelCanonicalQM31
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
          value) ↔
      EntryCanonicalQM31 value := by
  simp [KernelCanonicalQM31, KernelCanonicalCM31, EntryCanonicalQM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelCM31]

@[simp] theorem fromPreparedKernel_canonical_iff (value : KernelQM31) :
    EntryCanonicalQM31
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
          value) ↔
      KernelCanonicalQM31 value := by
  simp [KernelCanonicalQM31, KernelCanonicalCM31, EntryCanonicalQM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelCM31]

theorem decoder_success_entry_canonical
    (bytes : Slice Std.U8) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes bytes =
        .ok (some value)) :
    EntryCanonicalQM31 value := by
  have canonical := entry_from_le_bytes_success_canonical bytes value success
  simp only [
    AspisV5FriArithmeticSemantics.canonicalQM31,
    AspisV5FriArithmeticSemantics.canonicalCM31,
    AspisV5FriConsumerValueSemantics.toExactQM31,
    AspisV5FriConsumerValueSemantics.toExactCM31,
    AspisV5AcceptedFriModelInputBinding.entryToConsumerQM31,
    AspisV5AcceptedFriModelInputBinding.entryToConsumerCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisV5FriArithmeticSemantics.canonicalM31] at canonical
  exact ⟨canonical.1.1, canonical.1.2, canonical.2.1, canonical.2.2⟩

@[simp] theorem mapped_fromKernel_entry {count : Std.Usize}
    (values : Array KernelQM31 count) (index : Fin count.val) :
    (V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
        values).val[index.val]! =
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
        values.val[index.val]! := by
  simp [V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray,
    index.isLt]

@[simp] theorem mapped_toKernel_entry {count : Std.Usize}
    (values : Array EntryQM31 count) (index : Fin count.val) :
    (V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
        values).val[index.val]! =
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
        values.val[index.val]! := by
  simp [V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray,
    index.isLt]

theorem preparedKernelGammaPowers_success_canonical
    (gamma : EntryQM31) (powers : Array EntryQM31 19#usize)
    (gammaCanonical : EntryCanonicalQM31 gamma)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers
          gamma = .ok powers) :
    EntryCanonicalArray powers := by
  let kernelGamma :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 gamma
  have kernelGammaCanonical : KernelCanonicalQM31 kernelGamma := by
    exact (toPreparedKernel_canonical_iff gamma).2 gammaCanonical
  obtain ⟨kernelPowers, kernelRun, kernelPost⟩ :=
    extracted_gamma_powers_eq_source_weights kernelGamma kernelGammaCanonical
  have wrapperRun :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers
          gamma =
        .ok (V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
          kernelPowers) := by
    simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers,
      V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult, kernelGamma,
      kernelRun]
  rw [wrapperRun] at success
  cases success
  intro index
  rw [mapped_fromKernel_entry]
  exact (fromPreparedKernel_canonical_iff
    kernelPowers.val[index.val]!).2 (kernelPost index).1

theorem entry_qm31_add_eq_preparedKernel
    (left right : EntryQM31) :
    V5AcceptedEntryGenerated.aspis_core.field.QM31.add left right =
      V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
        (V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.add
          (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
            left)
          (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
            right)) := by
  simp [V5AcceptedEntryGenerated.aspis_core.field.QM31.add,
    Aeneas.Std.lift, bind_tc_ok,
    V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult,
    V5AcceptedEntryGenerated.aspis_core.field.toLinkedQM31,
    V5AcceptedEntryGenerated.aspis_core.field.toLinkedCM31,
    V5AcceptedEntryGenerated.aspis_core.field.fromLinkedQM31,
    V5AcceptedEntryGenerated.aspis_core.field.fromLinkedCM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelCM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelCM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.add,
    V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.add,
    V5RelationLinkedGenerated.aspis_core.field.CM31.add,
    V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add,
    V5RelationLinkedGenerated.aspis_core.field.M31.add,
    V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add,
    V5RelationLinkedGenerated.aspis_core.field.P,
    V5RelationPreparedClaimsGenerated.aspis_core.field.P]
  by_cases h0 : 2147483647 ≤
      (left.c0.a.val + right.c0.a.val) % Std.U32.size <;>
    by_cases h1 : 2147483647 ≤
      (left.c0.b.val + right.c0.b.val) % Std.U32.size <;>
    by_cases h2 : 2147483647 ≤
      (left.c1.a.val + right.c1.a.val) % Std.U32.size <;>
    by_cases h3 : 2147483647 ≤
      (left.c1.b.val + right.c1.b.val) % Std.U32.size <;>
    simp [h0, h1, h2, h3, bind_tc_ok]

theorem entry_qm31_add_success_canonical
    (left right output : EntryQM31)
    (leftCanonical : EntryCanonicalQM31 left)
    (rightCanonical : EntryCanonicalQM31 right)
    (success :
      V5AcceptedEntryGenerated.aspis_core.field.QM31.add left right =
        .ok output) :
    EntryCanonicalQM31 output := by
  let kernelLeft :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 left
  let kernelRight :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 right
  have kernelLeftCanonical : KernelCanonicalQM31 kernelLeft :=
    (toPreparedKernel_canonical_iff left).2 leftCanonical
  have kernelRightCanonical : KernelCanonicalQM31 kernelRight :=
    (toPreparedKernel_canonical_iff right).2 rightCanonical
  obtain ⟨kernelOutput, kernelRun, kernelOutputCanonical, _⟩ :=
    extracted_kernel_qm31_add_corresponds kernelLeft kernelRight
      kernelLeftCanonical kernelRightCanonical
  have kernelAddRun :
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.add
          kernelLeft kernelRight = .ok kernelOutput := by
    simpa [V5RelationPreparedClaimsGenerated.extracted_qm31_add] using
      kernelRun
  rw [entry_qm31_add_eq_preparedKernel, kernelAddRun] at success
  simp only [V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult,
    Result.ok.injEq] at success
  subst output
  exact (fromPreparedKernel_canonical_iff kernelOutput).2
    kernelOutputCanonical

theorem entry_qm31_add_exists_canonical
    (left right : EntryQM31)
    (leftCanonical : EntryCanonicalQM31 left)
    (rightCanonical : EntryCanonicalQM31 right) :
    ∃ output,
      V5AcceptedEntryGenerated.aspis_core.field.QM31.add left right =
          .ok output ∧
        EntryCanonicalQM31 output := by
  let kernelLeft :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 left
  let kernelRight :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 right
  have kernelLeftCanonical : KernelCanonicalQM31 kernelLeft :=
    (toPreparedKernel_canonical_iff left).2 leftCanonical
  have kernelRightCanonical : KernelCanonicalQM31 kernelRight :=
    (toPreparedKernel_canonical_iff right).2 rightCanonical
  obtain ⟨kernelOutput, kernelRun, kernelOutputCanonical, _⟩ :=
    extracted_kernel_qm31_add_corresponds kernelLeft kernelRight
      kernelLeftCanonical kernelRightCanonical
  have kernelAddRun :
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.add
          kernelLeft kernelRight = .ok kernelOutput := by
    simpa [V5RelationPreparedClaimsGenerated.extracted_qm31_add] using
      kernelRun
  refine ⟨
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
      kernelOutput, ?_,
    (fromPreparedKernel_canonical_iff kernelOutput).2 kernelOutputCanonical⟩
  rw [entry_qm31_add_eq_preparedKernel, kernelAddRun]
  rfl

theorem entryCanonicalArray_toKernel
    (values : Array EntryQM31 19#usize)
    (canonical : EntryCanonicalArray values) :
    KernelCanonicalQM31Array19
      (V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
      values) := by
  intro index
  unfold kernelArrayEntry
  rw [mapped_toKernel_entry values index]
  exact (toPreparedKernel_canonical_iff values.val[index.val]!).2
    (canonical index)

theorem preparedKernelClaimDotBlock_success_canonical
    (powers values : Array EntryQM31 19#usize)
    (start count : Std.Usize) (output : EntryQM31)
    (countBound : count.val ≤ 4)
    (spanBound : start.val + count.val ≤ 19)
    (powersCanonical : EntryCanonicalArray powers)
    (valuesCanonical : EntryCanonicalArray values)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock
          powers values start count = .ok output) :
    EntryCanonicalQM31 output := by
  let kernelPowers :=
    V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
      powers
  let kernelValues :=
    V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
      values
  have kernelPowersCanonical : KernelCanonicalQM31Array19 kernelPowers :=
    entryCanonicalArray_toKernel powers powersCanonical
  have kernelValuesCanonical : KernelCanonicalQM31Array19 kernelValues :=
    entryCanonicalArray_toKernel values valuesCanonical
  obtain ⟨kernelOutput, kernelRun, kernelOutputCanonical, _⟩ :=
    extracted_claim_dot_block_corresponds kernelPowers kernelValues start count
      countBound spanBound kernelPowersCanonical kernelValuesCanonical
  have wrapperRun :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock
          powers values start count =
        .ok (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
          kernelOutput) := by
    simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock,
      V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult,
      kernelPowers, kernelValues, kernelRun]
  rw [wrapperRun] at success
  cases success
  exact (fromPreparedKernel_canonical_iff kernelOutput).2
    kernelOutputCanonical

theorem preparedKernelClaimDotBlock_exists_canonical
    (powers values : Array EntryQM31 19#usize)
    (start count : Std.Usize)
    (countBound : count.val ≤ 4)
    (spanBound : start.val + count.val ≤ 19)
    (powersCanonical : EntryCanonicalArray powers)
    (valuesCanonical : EntryCanonicalArray values) :
    ∃ output,
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock
          powers values start count = .ok output ∧
        EntryCanonicalQM31 output := by
  let kernelPowers :=
    V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
      powers
  let kernelValues :=
    V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
      values
  have kernelPowersCanonical : KernelCanonicalQM31Array19 kernelPowers :=
    entryCanonicalArray_toKernel powers powersCanonical
  have kernelValuesCanonical : KernelCanonicalQM31Array19 kernelValues :=
    entryCanonicalArray_toKernel values valuesCanonical
  obtain ⟨kernelOutput, kernelRun, kernelOutputCanonical, _⟩ :=
    extracted_claim_dot_block_corresponds kernelPowers kernelValues start count
      countBound spanBound kernelPowersCanonical kernelValuesCanonical
  refine ⟨
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
      kernelOutput, ?_,
    (fromPreparedKernel_canonical_iff kernelOutput).2 kernelOutputCanonical⟩
  simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock,
    V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult,
    kernelPowers, kernelValues, kernelRun]

theorem sumPreparedClaimBlocks_success_canonical
    (powers values : Array EntryQM31 19#usize) (output : EntryQM31)
    (powersCanonical : EntryCanonicalArray powers)
    (valuesCanonical : EntryCanonicalArray values)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks
          powers values = .ok output) :
    EntryCanonicalQM31 output := by
  obtain ⟨block0, block0Run, block0Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      0#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block1, block1Run, block1Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      4#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block2, block2Run, block2Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      8#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block3, block3Run, block3Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      12#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block4, block4Run, block4Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      16#usize 3#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨sum01, sum01Run, sum01Canonical⟩ :=
    entry_qm31_add_exists_canonical block0 block1 block0Canonical block1Canonical
  obtain ⟨sum012, sum012Run, sum012Canonical⟩ :=
    entry_qm31_add_exists_canonical sum01 block2 sum01Canonical block2Canonical
  obtain ⟨sum0123, sum0123Run, sum0123Canonical⟩ :=
    entry_qm31_add_exists_canonical sum012 block3 sum012Canonical block3Canonical
  obtain ⟨expected, expectedRun, expectedCanonical⟩ :=
    entry_qm31_add_exists_canonical sum0123 block4 sum0123Canonical
      block4Canonical
  have wholeRun :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks
          powers values = .ok expected := by
    simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks,
      block0Run, block1Run, block2Run, block3Run, block4Run,
      sum01Run, sum012Run, sum0123Run, expectedRun]
  rw [wholeRun] at success
  cases success
  exact expectedCanonical

theorem array_update_success_eq
    {T : Type} {count : Std.Usize} (values : Array T count)
    (index : Std.Usize) (value : T) (output : Array T count)
    (bound : index.val < count.val)
    (success : Array.update values index value = .ok output) :
    output = values.set index value := by
  obtain ⟨witness, witnessRun, witnessEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.update_spec values index value (by
        simpa [Array.length_eq] using bound))
  have witnessOutput : witness = output :=
    Result.ok.inj (witnessRun.symm.trans success)
  simpa [witnessOutput] using witnessEq

theorem entryCanonicalArray_set
    {count : Std.Usize} (values : Array EntryQM31 count)
    (index : Std.Usize) (value : EntryQM31)
    (bound : index.val < count.val)
    (valuesCanonical : EntryCanonicalArray values)
    (valueCanonical : EntryCanonicalQM31 value) :
    EntryCanonicalArray (values.set index value) := by
  intro outputIndex
  simp only [Array.set_val_eq]
  by_cases same : index.val = outputIndex.val
  · rw [← same]
    have listBound : index.val < values.val.length := by
      rw [values.property]
      exact bound
    have setSelf :
        (values.val.set index.val value)[index.val]! = value := by
      apply List.set_getElem!_eq
      exact ⟨listBound, rfl⟩
    rw [setSelf]
    exact valueCanonical
  · rw [List.set_getElem!_ne values.val index.val outputIndex.val value
      (Or.inl same)]
    exact valuesCanonical outputIndex

theorem array_update_preserves_entryCanonical
    {count : Std.Usize} (values output : Array EntryQM31 count)
    (index : Std.Usize) (value : EntryQM31)
    (bound : index.val < count.val)
    (valuesCanonical : EntryCanonicalArray values)
    (valueCanonical : EntryCanonicalQM31 value)
    (success : Array.update values index value = .ok output) :
    EntryCanonicalArray output := by
  rw [array_update_success_eq values index value output bound success]
  exact entryCanonicalArray_set values index value bound valuesCanonical
    valueCanonical

theorem decodeClaimValuesAux_success_canonical
    (remaining : Nat) :
    ∀ (point column : Std.Usize) (bytes : Slice Std.U8)
      (values output : Array EntryQM31 19#usize),
      column.val + remaining ≤ 19 →
      EntryCanonicalArray values →
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux
          remaining point column bytes values = .ok (.Ok output) →
      EntryCanonicalArray output := by
  induction remaining with
  | zero =>
      intro point column bytes values output _ valuesCanonical success
      simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux]
        at success
      subst output
      exact valuesCanonical
  | succ remaining inductionHypothesis =>
      intro point column bytes values output spanBound valuesCanonical success
      have columnBound : column.val < 19 := by omega
      unfold
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux
        at success
      generalize pointBaseEquation : point * 19#usize = pointBaseResult
        at success
      cases pointBaseResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
      | div => simp [Bind.bind, Aeneas.Std.bind] at success
      | ok pointBase =>
          simp only [bind_tc_ok] at success
          generalize indexEquation : pointBase + column = indexResult at success
          cases indexResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
          | div => simp [Bind.bind, Aeneas.Std.bind] at success
          | ok index =>
              simp only [bind_tc_ok] at success
              generalize offsetEquation : index * 16#usize = offsetResult
                at success
              cases offsetResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
              | div => simp [Bind.bind, Aeneas.Std.bind] at success
              | ok offset =>
                  simp only [bind_tc_ok] at success
                  generalize stopEquation : offset + 16#usize = stopResult
                    at success
                  cases stopResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
                  | div => simp [Bind.bind, Aeneas.Std.bind] at success
                  | ok stop =>
                      simp only [bind_tc_ok] at success
                      generalize encodedEquation :
                        core.slice.index.Slice.index
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                          bytes { start := offset, «end» := stop } =
                            encodedResult at success
                      cases encodedResult with
                      | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at success
                      | div => simp [Bind.bind, Aeneas.Std.bind] at success
                      | ok encoded =>
                          simp only [bind_tc_ok] at success
                          generalize decodedEquation :
                            V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes
                              encoded = decodedResult at success
                          cases decodedResult with
                          | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at success
                          | div => simp [Bind.bind, Aeneas.Std.bind] at success
                          | ok decoded =>
                              cases decoded with
                              | none =>
                                  simp [Bind.bind, Aeneas.Std.bind] at success
                              | some value =>
                                  simp only [bind_tc_ok] at success
                                  generalize updateEquation :
                                    Array.update values column value =
                                      updateResult at success
                                  cases updateResult with
                                  | fail error =>
                                      simp [Bind.bind, Aeneas.Std.bind] at success
                                  | div =>
                                      simp [Bind.bind, Aeneas.Std.bind] at success
                                  | ok updated =>
                                      simp only [bind_tc_ok] at success
                                      generalize nextEquation :
                                        column + 1#usize = nextResult at success
                                      cases nextResult with
                                      | fail error =>
                                          simp [Bind.bind, Aeneas.Std.bind]
                                            at success
                                      | div =>
                                          simp [Bind.bind, Aeneas.Std.bind]
                                            at success
                                      | ok next =>
                                          simp only [bind_tc_ok] at success
                                          have valueCanonical :
                                              EntryCanonicalQM31 value :=
                                            decoder_success_entry_canonical
                                              encoded value decodedEquation
                                          have updatedCanonical :
                                              EntryCanonicalArray updated :=
                                            array_update_preserves_entryCanonical
                                              values updated column value
                                              columnBound valuesCanonical
                                              valueCanonical updateEquation
                                          have addFacts :=
                                            @UScalar.add_equiv UScalarTy.Usize
                                              column 1#usize
                                          rw [nextEquation] at addFacts
                                          have nextValue :
                                              next.val = column.val + 1 := by
                                            calc
                                              next.val =
                                                  column.val +
                                                    (1#usize : Std.Usize).val :=
                                                addFacts.2.1
                                              _ = column.val + 1 := by rfl
                                          apply inductionHypothesis point next bytes
                                            updated output
                                          · omega
                                          · exact updatedCanonical
                                          · exact success

theorem entry_qm31_zero_success_canonical
    (value : EntryQM31)
    (success : V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO =
      .ok value) :
    EntryCanonicalQM31 value := by
  unfold V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO at success
  rw [V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO] at success
  simp only [V5AcceptedEntryGenerated.aspis_core.field.fromLinkedQM31,
    V5AcceptedEntryGenerated.aspis_core.field.fromLinkedCM31,
    Result.ok.injEq] at success
  subst value
  norm_num [EntryCanonicalQM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

theorem entryCanonicalArray_repeat
    (count : Std.Usize) (value : EntryQM31)
    (canonical : EntryCanonicalQM31 value) :
    EntryCanonicalArray (Array.repeat count value) := by
  intro index
  simpa [Array.repeat, index.isLt] using canonical

theorem preparePointClaimsAux_success_canonical
    (remaining : Nat) :
    ∀ (point : Std.Usize) (bytes : Slice Std.U8)
      (powers : Array EntryQM31 19#usize)
      (claims output : Array EntryQM31 4#usize),
      point.val + remaining ≤ 4 →
      EntryCanonicalArray powers →
      EntryCanonicalArray claims →
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux
          remaining point bytes powers claims = .ok (.Ok output) →
      EntryCanonicalArray output := by
  induction remaining with
  | zero =>
      intro point bytes powers claims output _ _ claimsCanonical success
      simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux]
        at success
      subst output
      exact claimsCanonical
  | succ remaining inductionHypothesis =>
      intro point bytes powers claims output spanBound powersCanonical
        claimsCanonical success
      have pointBound : point.val < 4 := by omega
      unfold
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux
        at success
      generalize zeroEquation :
        V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO = zeroResult
        at success
      cases zeroResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
      | div => simp [Bind.bind, Aeneas.Std.bind] at success
      | ok zero =>
          simp only [bind_tc_ok] at success
          let initialValues : Array EntryQM31 19#usize :=
            Array.repeat 19#usize zero
          have zeroCanonical : EntryCanonicalQM31 zero :=
            entry_qm31_zero_success_canonical zero zeroEquation
          have initialValuesCanonical : EntryCanonicalArray initialValues :=
            entryCanonicalArray_repeat 19#usize zero zeroCanonical
          generalize decodeEquation :
            V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux
              19 point 0#usize bytes initialValues = decodeResult at success
          cases decodeResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
          | div => simp [Bind.bind, Aeneas.Std.bind] at success
          | ok decoded =>
              cases decoded with
              | Err error =>
                  simp [Bind.bind, Aeneas.Std.bind] at success
              | Ok values =>
                  simp only [bind_tc_ok] at success
                  have valuesCanonical : EntryCanonicalArray values :=
                    decodeClaimValuesAux_success_canonical 19 point 0#usize
                      bytes initialValues values (by norm_num)
                      initialValuesCanonical decodeEquation
                  generalize claimEquation :
                    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks
                      powers values = claimResult at success
                  cases claimResult with
                  | fail error =>
                      simp [Bind.bind, Aeneas.Std.bind] at success
                  | div => simp [Bind.bind, Aeneas.Std.bind] at success
                  | ok claim =>
                      simp only [bind_tc_ok] at success
                      have claimCanonical : EntryCanonicalQM31 claim :=
                        sumPreparedClaimBlocks_success_canonical powers values
                          claim powersCanonical valuesCanonical claimEquation
                      generalize updateEquation :
                        Array.update claims point claim = updateResult at success
                      cases updateResult with
                      | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at success
                      | div =>
                          simp [Bind.bind, Aeneas.Std.bind] at success
                      | ok updatedClaims =>
                          simp only [bind_tc_ok] at success
                          have updatedClaimsCanonical :
                              EntryCanonicalArray updatedClaims :=
                            array_update_preserves_entryCanonical claims
                              updatedClaims point claim pointBound claimsCanonical
                              claimCanonical updateEquation
                          generalize nextEquation :
                            point + 1#usize = nextResult at success
                          cases nextResult with
                          | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at success
                          | div =>
                              simp [Bind.bind, Aeneas.Std.bind] at success
                          | ok next =>
                              simp only [bind_tc_ok] at success
                              have addFacts :=
                                @UScalar.add_equiv UScalarTy.Usize point 1#usize
                              rw [nextEquation] at addFacts
                              have nextValue : next.val = point.val + 1 := by
                                calc
                                  next.val = point.val +
                                      (1#usize : Std.Usize).val := addFacts.2.1
                                  _ = point.val + 1 := by rfl
                              apply inductionHypothesis next bytes powers
                                updatedClaims output
                              · omega
                              · exact powersCanonical
                              · exact updatedClaimsCanonical
                              · exact success

def PreparedClaimsCanonical
    (prepared :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    Prop :=
  prepared.inner.claims.val.length = 4 ∧
    ∀ index : Fin 4,
      EntryCanonicalQM31 prepared.inner.claims.val[index.val]!

theorem prepare_v5_pcs_claims_success_canonical
    (gamma : EntryQM31) (bytes : Slice Std.U8)
    (prepared :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (gammaCanonical : EntryCanonicalQM31 gamma)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepare_v5_pcs_claims
          gamma bytes = .ok (.Ok prepared)) :
    PreparedClaimsCanonical prepared := by
  unfold
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepare_v5_pcs_claims
    at success
  dsimp only at success
  split at success
  · simp at success
  · generalize powersEquation :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers
        gamma = powersResult at success
    cases powersResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
    | div => simp [Bind.bind, Aeneas.Std.bind] at success
    | ok powers =>
        simp only [bind_tc_ok] at success
        have powersCanonical : EntryCanonicalArray powers :=
          preparedKernelGammaPowers_success_canonical gamma powers
            gammaCanonical powersEquation
        let emptyLimbs := Array.repeat 4#usize 0#u32
        generalize c1Equation :
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepareC1WeightsAux
            16 0#usize powers (Array.repeat 16#usize emptyLimbs) = c1Result
          at success
        cases c1Result with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
        | div => simp [Bind.bind, Aeneas.Std.bind] at success
        | ok c1WeightLimbs =>
            simp only [bind_tc_ok] at success
            generalize zeroEquation :
              V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO = zeroResult
              at success
            cases zeroResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
            | div => simp [Bind.bind, Aeneas.Std.bind] at success
            | ok zero =>
                simp only [bind_tc_ok] at success
                have zeroCanonical : EntryCanonicalQM31 zero :=
                  entry_qm31_zero_success_canonical zero zeroEquation
                generalize multiplierEquation :
                  V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier.new
                    zero = multiplierResult at success
                cases multiplierResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
                | div => simp [Bind.bind, Aeneas.Std.bind] at success
                | ok emptyMultiplier =>
                    simp only [bind_tc_ok] at success
                    generalize c2Equation :
                      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepareC2MultipliersAux
                        3 0#usize powers
                          (Array.repeat 3#usize emptyMultiplier) = c2Result
                      at success
                    cases c2Result with
                    | fail error =>
                        simp [Bind.bind, Aeneas.Std.bind] at success
                    | div => simp [Bind.bind, Aeneas.Std.bind] at success
                    | ok c2Multipliers =>
                        simp only [bind_tc_ok] at success
                        let initialClaims : Array EntryQM31 4#usize :=
                          Array.repeat 4#usize zero
                        have initialClaimsCanonical :
                            EntryCanonicalArray initialClaims :=
                          entryCanonicalArray_repeat 4#usize zero zeroCanonical
                        generalize claimsEquation :
                          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux
                            4 0#usize bytes powers initialClaims = claimsResult
                          at success
                        cases claimsResult with
                        | fail error =>
                            simp [Bind.bind, Aeneas.Std.bind] at success
                        | div =>
                            simp [Bind.bind, Aeneas.Std.bind] at success
                        | ok claimsResult =>
                            cases claimsResult with
                            | Err error =>
                                simp [Bind.bind, Aeneas.Std.bind] at success
                            | Ok claims =>
                                have claimsCanonical :
                                    EntryCanonicalArray claims :=
                                  preparePointClaimsAux_success_canonical 4
                                    0#usize bytes powers initialClaims claims
                                    (by norm_num) powersCanonical
                                    initialClaimsCanonical claimsEquation
                                have preparedEquality :
                                    prepared = {
                                      inner := {
                                        claims := ⟨claims.val, by scalar_tac⟩
                                        powers := ⟨powers.val, by scalar_tac⟩ }
                                      c1_weight_limbs := c1WeightLimbs
                                      c2_multipliers := c2Multipliers } := by
                                  exact (core.result.Result.Ok.inj
                                    (Result.ok.inj success)).symm
                                subst prepared
                                constructor
                                · simpa using claims.property
                                · intro index
                                  exact claimsCanonical index

#print axioms prepare_v5_pcs_claims_success_canonical

end AspisV5AcceptedPreparedClaimsCanonical
