import AspisFormal.V5ComponentCRejectionSampler

/-!
# v5 Component C: exact variable-consumption stopping-time sampler

The deployed sampler does not reserve sixteen words for every M31 limb.  It
reads from one sequential word source and moves to the next limb immediately
after the first accepted word.  This leaf models that literal control flow on
a finite iid `u32` prefix of the maximum possible length.

The theorem below conditions once on all 4092 calls succeeding and proves that
their joint output is exactly uniform.  It does not inspect Rust object code or
identify the ideal iid prefix with the production 256-bit expander; those are
separate exact control-flow and computational-PRG interfaces below.
-/

namespace AspisV5ComponentCStoppingTimeSampler

open scoped ENNReal
open AspisV5ComponentCRejectionSampler

/-! ## Literal sequential parser -/

/-- The exact low-31-bit rejection result of one Rust `u32` word. -/
def rawWordResult (word : RawWord) : Option M31Value :=
  candidateResult (low31Candidate word)

/-- Consume between one and `fuel` sequential words, returning immediately at
the first accepted word.  On success the second component is the untouched
suffix from which the next logical M31 call starts. -/
def consumeFirstSuccess : Nat → List RawWord → Option (M31Value × List RawWord)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, word :: rest =>
      match rawWordResult word with
      | some value => some (value, rest)
      | none => consumeFirstSuccess fuel rest

/-- Run `callCount` bounded M31 calls consecutively on one shared stream.
Unused words remain in the returned suffix. -/
def runSequentialCalls : (callCount : Nat) → List RawWord →
    Option ((Fin callCount → M31Value) × List RawWord)
  | 0, words => some (Fin.elim0, words)
  | callCount + 1, words =>
      match consumeFirstSuccess retryLimit words with
      | none => none
      | some (head, rest) =>
          match runSequentialCalls callCount rest with
          | none => none
          | some (tail, unused) => some (Fin.cases head tail, unused)

/-! ## Accepted-value permutations preserve the stopping path -/

/-- One `u32` is exactly an `Option M31` result paired with its discarded high
bit. -/
def rawWordResultHighBitEquiv : RawWord ≃ Option M31Value × RawHighBit :=
  rawCandidateHighBitEquiv.symm.trans
    (Equiv.prodCongr candidateResultEquiv (Equiv.refl RawHighBit))

@[simp] theorem rawWordResultHighBitEquiv_fst (word : RawWord) :
    (rawWordResultHighBitEquiv word).1 = rawWordResult word := by
  change candidateResult ((rawCandidateHighBitEquiv.symm word).1) =
    rawWordResult word
  rw [rawCandidateHighBitEquiv_symm_fst]
  rfl

/-- Permute accepted values while preserving rejection and the discarded high
bit.  This is a literal permutation of all 32-bit words. -/
def permuteAcceptedWord (e : M31Value ≃ M31Value) : RawWord ≃ RawWord :=
  rawWordResultHighBitEquiv.trans
    ((Equiv.prodCongr e.optionCongr (Equiv.refl RawHighBit)).trans
      rawWordResultHighBitEquiv.symm)

@[simp] theorem rawWordResult_permuteAcceptedWord
    (e : M31Value ≃ M31Value) (word : RawWord) :
    rawWordResult (permuteAcceptedWord e word) =
      e.optionCongr (rawWordResult word) := by
  have h := rawWordResultHighBitEquiv_fst (permuteAcceptedWord e word)
  rw [permuteAcceptedWord, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply] at h
  exact h.symm

/-- Transform the words consumed by one bounded call and then invoke `next` on
the untouched suffix after success. -/
def mapBoundedThen (e : M31Value ≃ M31Value)
    (next : List RawWord → List RawWord) : Nat → List RawWord → List RawWord
  | 0, words => words
  | _ + 1, [] => []
  | fuel + 1, word :: rest =>
      permuteAcceptedWord e word ::
        match rawWordResult word with
        | some _ => next rest
        | none => mapBoundedThen e next fuel rest

/-- Apply a separate accepted-value permutation to each consecutive logical
call.  Because the permutation preserves accept/reject status, the transformed
run consumes exactly the same number of words at every call. -/
def mapSequentialCalls : (callCount : Nat) →
    (Fin callCount → M31Value ≃ M31Value) → List RawWord → List RawWord
  | 0, _, words => words
  | callCount + 1, permutations, words =>
      mapBoundedThen (permutations 0)
        (mapSequentialCalls callCount (fun i => permutations i.succ))
        retryLimit words

def mapSequentialValues {callCount : Nat}
    (permutations : Fin callCount → M31Value ≃ M31Value)
    (values : Fin callCount → M31Value) : Fin callCount → M31Value :=
  fun i => permutations i (values i)

theorem consumeFirstSuccess_mapBoundedThen
    (e : M31Value ≃ M31Value) (next : List RawWord → List RawWord)
    (fuel : Nat) (words : List RawWord) :
    consumeFirstSuccess fuel (mapBoundedThen e next fuel words) =
      (consumeFirstSuccess fuel words).map
        (fun result => (e result.1, next result.2)) := by
  induction fuel generalizing words with
  | zero => simp [consumeFirstSuccess]
  | succ fuel ih =>
      cases words with
      | nil => simp [consumeFirstSuccess, mapBoundedThen]
      | cons word rest =>
          cases hresult : rawWordResult word with
          | none =>
              simp [consumeFirstSuccess, mapBoundedThen, hresult, ih]
          | some value =>
              simp [consumeFirstSuccess, mapBoundedThen, hresult]

theorem runSequentialCalls_mapSequentialCalls
    (callCount : Nat)
    (permutations : Fin callCount → M31Value ≃ M31Value)
    (words : List RawWord) :
    runSequentialCalls callCount
        (mapSequentialCalls callCount permutations words) =
      (runSequentialCalls callCount words).map
        (fun result => (mapSequentialValues permutations result.1, result.2)) := by
  induction callCount generalizing words with
  | zero =>
      simp only [runSequentialCalls, mapSequentialCalls, Option.map_some]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ callCount ih =>
      simp only [mapSequentialCalls, runSequentialCalls]
      rw [
        consumeFirstSuccess_mapBoundedThen]
      cases hhead : consumeFirstSuccess retryLimit words with
      | none => rfl
      | some first =>
          rcases first with ⟨head, rest⟩
          simp only [Option.map_some]
          rw [ih]
          cases htail : runSequentialCalls callCount rest with
          | none => rfl
          | some tailResult =>
              rcases tailResult with ⟨tail, unused⟩
              simp only [Option.map_some]
              congr 2
              funext i
              refine Fin.cases ?_ (fun j => ?_) i
              · rfl
              · rfl

theorem mapBoundedThen_length
    (e : M31Value ≃ M31Value) (next : List RawWord → List RawWord)
    (hnext : ∀ words, (next words).length = words.length)
    (fuel : Nat) (words : List RawWord) :
    (mapBoundedThen e next fuel words).length = words.length := by
  induction fuel generalizing words with
  | zero => rfl
  | succ fuel ih =>
      cases words with
      | nil => rfl
      | cons word rest =>
          cases hresult : rawWordResult word with
          | none => simp [mapBoundedThen, hresult, ih]
          | some value => simp [mapBoundedThen, hresult, hnext]

theorem mapSequentialCalls_length
    (callCount : Nat)
    (permutations : Fin callCount → M31Value ≃ M31Value)
    (words : List RawWord) :
    (mapSequentialCalls callCount permutations words).length = words.length := by
  induction callCount generalizing words with
  | zero => rfl
  | succ callCount ih =>
      exact mapBoundedThen_length _ _
        (fun rest => ih (fun i => permutations i.succ) rest) _ _

@[simp] theorem permuteAcceptedWord_symm_apply_apply
    (e : M31Value ≃ M31Value) (word : RawWord) :
    permuteAcceptedWord e.symm (permuteAcceptedWord e word) = word := by
  apply rawWordResultHighBitEquiv.injective
  rcases hword : rawWordResultHighBitEquiv word with ⟨result, highBit⟩
  cases result with
  | none => simp [permuteAcceptedWord, Equiv.trans_apply, hword]
  | some value =>
      simp only [permuteAcceptedWord, Equiv.trans_apply, hword,
        Equiv.prodCongr_apply, Equiv.apply_symm_apply]
      rw [Equiv.optionCongr_symm]
      change
        (e.optionCongr.symm (e.optionCongr (some value)), highBit) =
          (some value, highBit)
      rw [e.optionCongr.symm_apply_apply]

theorem mapBoundedThen_symm
    (e : M31Value ≃ M31Value)
    (next undo : List RawWord → List RawWord)
    (hundo : ∀ words, undo (next words) = words)
    (fuel : Nat) (words : List RawWord) :
    mapBoundedThen e.symm undo fuel
        (mapBoundedThen e next fuel words) = words := by
  induction fuel generalizing words with
  | zero => rfl
  | succ fuel ih =>
      cases words with
      | nil => rfl
      | cons word rest =>
          cases hresult : rawWordResult word with
          | none =>
              simp [mapBoundedThen, hresult,
                rawWordResult_permuteAcceptedWord, ih]
          | some value =>
              simp [mapBoundedThen, hresult,
                rawWordResult_permuteAcceptedWord, hundo]

theorem mapSequentialCalls_symm
    (callCount : Nat)
    (permutations : Fin callCount → M31Value ≃ M31Value)
    (words : List RawWord) :
    mapSequentialCalls callCount (fun i => (permutations i).symm)
        (mapSequentialCalls callCount permutations words) = words := by
  induction callCount generalizing words with
  | zero => rfl
  | succ callCount ih =>
      exact mapBoundedThen_symm _ _ _
        (fun rest => ih (fun i => permutations i.succ) rest) _ _

/-! ## Fixed maximum-length iid stream experiment -/

/-- Opaque-at-use name for the deployed 1023×4 call count.  Keeping the
symbolic name prevents elaboration from trying to unfold a 4092-step parser
inside unrelated type-casts. -/
def componentCSequentialCallCount : Nat := componentCCallCount

theorem componentCSequentialCallCount_eq :
    componentCSequentialCallCount = 4092 := by
  norm_num [componentCSequentialCallCount, componentCCallCount,
    componentCFreeCoordinateCount, qm31LimbCount]

/-- Maximum words read by 4092 calls with sixteen attempts each. -/
def componentCSequentialWordCount : Nat := componentCSequentialCallCount * retryLimit

/-- A fixed iid prefix long enough for every possible stopping path. -/
abbrev ComponentCSequentialRawStream :=
  List.Vector RawWord componentCSequentialWordCount

instance : Fintype ComponentCSequentialRawStream :=
  Fintype.ofEquiv (Fin componentCSequentialWordCount → RawWord)
    (Equiv.vectorEquivFin RawWord componentCSequentialWordCount).symm

def mapSequentialVector
    (permutations : Fin componentCSequentialCallCount → M31Value ≃ M31Value)
    (words : ComponentCSequentialRawStream) : ComponentCSequentialRawStream :=
  ⟨mapSequentialCalls componentCSequentialCallCount permutations words.1,
    (mapSequentialCalls_length _ _ _).trans words.2⟩

/-- The dynamic accepted-value relabelling is a permutation of the entire
fixed maximum-length word prefix. -/
def sequentialRawStreamPerm
    (permutations : Fin componentCSequentialCallCount → M31Value ≃ M31Value) :
    ComponentCSequentialRawStream ≃ ComponentCSequentialRawStream where
  toFun := mapSequentialVector permutations
  invFun := mapSequentialVector (fun i => (permutations i).symm)
  left_inv := by
    intro words
    apply Subtype.ext
    exact mapSequentialCalls_symm _ _ words.1
  right_inv := by
    intro words
    apply Subtype.ext
    exact mapSequentialCalls_symm _ (fun i => (permutations i).symm) words.1

def sequentialStreamWords (raw : ComponentCSequentialRawStream) : List RawWord :=
  raw.1

theorem sequentialStreamWords_perm
    (permutations : Fin componentCSequentialCallCount → M31Value ≃ M31Value)
    (raw : ComponentCSequentialRawStream) :
    sequentialStreamWords (sequentialRawStreamPerm permutations raw) =
      mapSequentialCalls componentCSequentialCallCount permutations
        (sequentialStreamWords raw) := by
  rfl

/-- Literal variable-consumption run on the fixed iid prefix. -/
def componentCSequentialRun (raw : ComponentCSequentialRawStream) :
    Option ((Fin componentCSequentialCallCount → M31Value) × List RawWord) :=
  runSequentialCalls componentCSequentialCallCount (sequentialStreamWords raw)

theorem componentCSequentialRun_perm
    (permutations : Fin componentCSequentialCallCount → M31Value ≃ M31Value)
    (raw : ComponentCSequentialRawStream) :
    componentCSequentialRun (sequentialRawStreamPerm permutations raw) =
      (componentCSequentialRun raw).map
        (fun result => (mapSequentialValues permutations result.1, result.2)) := by
  rw [componentCSequentialRun, sequentialStreamWords_perm,
    runSequentialCalls_mapSequentialCalls]
  rfl

/-- Success of every one of the consecutive 4092 bounded calls. -/
def ComponentCSequentialSucceeds (raw : ComponentCSequentialRawStream) : Prop :=
  (componentCSequentialRun raw).isSome

instance (raw : ComponentCSequentialRawStream) :
    Decidable (ComponentCSequentialSucceeds raw) := by
  unfold ComponentCSequentialSucceeds
  infer_instance

abbrev SuccessfulComponentCSequentialStream :=
  {raw : ComponentCSequentialRawStream // ComponentCSequentialSucceeds raw}

theorem ComponentCSequentialSucceeds_perm
    (permutations : Fin componentCSequentialCallCount → M31Value ≃ M31Value)
    (raw : ComponentCSequentialRawStream) :
    ComponentCSequentialSucceeds raw ↔
      ComponentCSequentialSucceeds (sequentialRawStreamPerm permutations raw) := by
  unfold ComponentCSequentialSucceeds
  rw [componentCSequentialRun_perm, Option.isSome_map]

def successfulSequentialStreamPerm
    (permutations : Fin componentCSequentialCallCount → M31Value ≃ M31Value) :
    SuccessfulComponentCSequentialStream ≃ SuccessfulComponentCSequentialStream :=
  (sequentialRawStreamPerm permutations).subtypeEquiv fun raw =>
    ComponentCSequentialSucceeds_perm permutations raw

/-- Extract all 4092 values from a proved-successful variable-consumption
run. -/
def componentCSequentialValuesOrFirst (raw : ComponentCSequentialRawStream) :
    Fin componentCSequentialCallCount → M31Value :=
  match componentCSequentialRun raw with
  | some result => result.1
  | none => fun _ => firstM31Value

def successfulSequentialValues (raw : SuccessfulComponentCSequentialStream) :
    Fin componentCSequentialCallCount → M31Value :=
  componentCSequentialValuesOrFirst raw.1

theorem successfulSequentialValues_perm
    (permutations : Fin componentCSequentialCallCount → M31Value ≃ M31Value)
    (raw : SuccessfulComponentCSequentialStream) :
    successfulSequentialValues (successfulSequentialStreamPerm permutations raw) =
      mapSequentialValues permutations (successfulSequentialValues raw) := by
  have hrun := componentCSequentialRun_perm permutations raw.1
  cases hresult : componentCSequentialRun raw.1 with
  | none =>
      have hsuccess := raw.2
      change (componentCSequentialRun raw.1).isSome at hsuccess
      rw [hresult] at hsuccess
      contradiction
  | some result =>
      rw [hresult] at hrun
      have hval :
          (successfulSequentialStreamPerm permutations raw).1 =
            sequentialRawStreamPerm permutations raw.1 := rfl
      rw [successfulSequentialValues, hval,
        componentCSequentialValuesOrFirst, hrun]
      simp [successfulSequentialValues, componentCSequentialValuesOrFirst,
        hresult]

/-! ## Non-vacuity and exact conditioned law -/

/-- A concrete `u32` whose low bits are the canonical zero residue. -/
def acceptedFirstRawWord : RawWord :=
  rawWordResultHighBitEquiv.symm (some firstM31Value, 0)

@[simp] theorem rawWordResult_acceptedFirstRawWord :
    rawWordResult acceptedFirstRawWord = some firstM31Value := by
  have h := rawWordResultHighBitEquiv_fst acceptedFirstRawWord
  simpa [acceptedFirstRawWord] using h.symm

theorem runSequentialCalls_replicate_accepted
    (callCount : Nat) (unused : List RawWord) :
    runSequentialCalls callCount
        (List.replicate callCount acceptedFirstRawWord ++ unused) =
      some (fun _ => firstM31Value, unused) := by
  induction callCount with
  | zero =>
      simp only [List.replicate_zero, List.nil_append,
        runSequentialCalls.eq_1]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ callCount ih =>
      rw [List.replicate_succ, List.cons_append, runSequentialCalls.eq_2]
      simp only [consumeFirstSuccess, rawWordResult_acceptedFirstRawWord]
      rw [ih]
      simp only
      congr 2
      funext i
      refine Fin.cases rfl (fun _ => rfl) i

theorem componentCSequentialCallCount_le_wordCount :
    componentCSequentialCallCount ≤ componentCSequentialWordCount := by
  simp only [componentCSequentialWordCount, retryLimit]
  omega

/-- A maximum-length stream on which every call accepts its first word. -/
def acceptedComponentCSequentialStream : ComponentCSequentialRawStream :=
  ⟨List.replicate componentCSequentialWordCount acceptedFirstRawWord,
    List.length_replicate⟩

theorem acceptedComponentCSequentialStream_succeeds :
    ComponentCSequentialSucceeds acceptedComponentCSequentialStream := by
  unfold ComponentCSequentialSucceeds componentCSequentialRun
  have hsplit :
      List.replicate componentCSequentialWordCount acceptedFirstRawWord =
        List.replicate componentCSequentialCallCount acceptedFirstRawWord ++
          List.replicate
            (componentCSequentialWordCount - componentCSequentialCallCount)
            acceptedFirstRawWord := by
    rw [← List.replicate_add]
    congr
  change
    (runSequentialCalls componentCSequentialCallCount
      (List.replicate componentCSequentialWordCount acceptedFirstRawWord)).isSome
  rw [hsplit, runSequentialCalls_replicate_accepted]
  rfl

def successfulComponentCSequentialStreamExample :
    SuccessfulComponentCSequentialStream :=
  ⟨acceptedComponentCSequentialStream,
    acceptedComponentCSequentialStream_succeeds⟩

instance : Nonempty SuccessfulComponentCSequentialStream :=
  ⟨successfulComponentCSequentialStreamExample⟩

instance : Nonempty ComponentCSequentialRawStream :=
  ⟨acceptedComponentCSequentialStream⟩

/-- Per-coordinate transpositions give an explicit equivalence between every
two output fibres of the successful variable-consumption experiment. -/
def successfulSequentialValuesFibreEquiv
    (values base : Fin componentCSequentialCallCount → M31Value) :
    {raw : SuccessfulComponentCSequentialStream //
        successfulSequentialValues raw = values} ≃
      {raw : SuccessfulComponentCSequentialStream //
        successfulSequentialValues raw = base} :=
  (successfulSequentialStreamPerm
    (fun i => Equiv.swap (values i) (base i))).subtypeEquiv fun raw => by
      rw [successfulSequentialValues_perm]
      constructor
      · intro hvalues
        funext i
        rw [mapSequentialValues, hvalues]
        exact Equiv.swap_apply_left (values i) (base i)
      · intro hmapped
        funext i
        apply (Equiv.swap (values i) (base i)).injective
        rw [Equiv.swap_apply_left]
        exact congrFun hmapped i

/-- Conditional on all 4092 bounded calls succeeding, the outputs of the
literal shared-stream stopping-time parser are exactly joint-uniform. -/
theorem successfulSequentialValues_joint_uniform :
    (PMF.uniformOfFintype SuccessfulComponentCSequentialStream).map
        successfulSequentialValues =
      PMF.uniformOfFintype
        (Fin componentCSequentialCallCount → M31Value) := by
  let base : Fin componentCSequentialCallCount → M31Value :=
    fun _ => firstM31Value
  exact uniform_map_of_equiv_fibres successfulSequentialValues base
    (fun values => successfulSequentialValuesFibreEquiv values base)

theorem successfulComponentCSequentialConditioningWitness :
    ∃ raw ∈ {raw : ComponentCSequentialRawStream |
        ComponentCSequentialSucceeds raw},
      raw ∈ (PMF.uniformOfFintype ComponentCSequentialRawStream).support :=
  ⟨acceptedComponentCSequentialStream,
    acceptedComponentCSequentialStream_succeeds,
    PMF.mem_support_uniformOfFintype _⟩

/-- Literal one-shot conditional law of the shared-stream control-flow model. -/
noncomputable def successfulComponentCSequentialLaw :
    PMF (Fin componentCSequentialCallCount → M31Value) :=
  ((PMF.uniformOfFintype ComponentCSequentialRawStream).filter
    {raw : ComponentCSequentialRawStream | ComponentCSequentialSucceeds raw}
      successfulComponentCSequentialConditioningWitness).map
        componentCSequentialValuesOrFirst

/-- **Exact stopping-time capstone.**  Start with one joint-uniform
maximum-length `u32` prefix, consume words sequentially with the same loop
shape as the deployed sampler, and condition once on no bounded call aborting.
All 4092 released M31 limbs remain jointly uniform.  Equality of the executable
Rust state transformer with this model is the named interface below. -/
theorem successfulComponentCSequentialLaw_eq_joint_uniform :
    successfulComponentCSequentialLaw =
      PMF.uniformOfFintype
        (Fin componentCSequentialCallCount → M31Value) := by
  rw [successfulComponentCSequentialLaw,
    uniform_filter_eq_uniform_subtype ComponentCSequentialSucceeds
      successfulComponentCSequentialConditioningWitness,
    PMF.map_comp]
  have hfun : componentCSequentialValuesOrFirst ∘
      (Subtype.val : SuccessfulComponentCSequentialStream →
        ComponentCSequentialRawStream) = successfulSequentialValues := rfl
  rw [hfun]
  exact successfulSequentialValues_joint_uniform

/-! ## Deployed 1023×4 shape and sampler-kernel bridge -/

/-- The sequential call order is exactly coordinate-major, then the four QM31
limbs, matching Rust's nested `for value in free` / `sample_qm31` order. -/
def sequentialCallIndexEquiv :
    Fin componentCSequentialCallCount ≃ ComponentCCallIndex :=
  (finCongr (by rfl)).trans finProdFinEquiv.symm

def sequentialLimbReindex :
    (Fin componentCSequentialCallCount → M31Value) ≃
      (ComponentCCallIndex → M31Value) :=
  Equiv.arrowCongr sequentialCallIndexEquiv (Equiv.refl M31Value)

/-- Literal shared-stream successful law in flat `(coordinate, limb)` order. -/
noncomputable def successfulComponentCSequentialFlatLaw :
    PMF (ComponentCCallIndex → M31Value) :=
  successfulComponentCSequentialLaw.map sequentialLimbReindex

theorem successfulComponentCSequentialFlatLaw_eq_joint_uniform :
    successfulComponentCSequentialFlatLaw =
      PMF.uniformOfFintype (ComponentCCallIndex → M31Value) := by
  rw [successfulComponentCSequentialFlatLaw,
    successfulComponentCSequentialLaw_eq_joint_uniform]
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv sequentialLimbReindex

/-- Literal shared-stream successful law in 1023 four-limb coordinates. -/
noncomputable def successfulComponentCSequentialCoordinatesLaw :
    PMF (Fin componentCFreeCoordinateCount → QM31Limbs) :=
  successfulComponentCSequentialFlatLaw.map componentCFlatToCoordinates

theorem successfulComponentCSequentialCoordinatesLaw_eq_joint_uniform :
    successfulComponentCSequentialCoordinatesLaw =
      PMF.uniformOfFintype
        (Fin componentCFreeCoordinateCount → QM31Limbs) := by
  rw [successfulComponentCSequentialCoordinatesLaw,
    successfulComponentCSequentialFlatLaw_eq_joint_uniform]
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv componentCFlatToCoordinates

/-- The old stopping-time seam is now discharged for the exact ideal iid-u32
experiment: variable consumption and preallocated blocks have identical
successful output laws, because both equal the same joint uniform law. -/
theorem idealIidSequentialStream_matches_preallocatedBlockExperiment :
    RustIidStreamStoppingTimeMatchesBlockExperiment
      successfulComponentCSequentialCoordinatesLaw := by
  rw [RustIidStreamStoppingTimeMatchesBlockExperiment]
  exact successfulComponentCSequentialCoordinatesLaw_eq_joint_uniform.trans
    successfulComponentCBlockCoordinates_eq_joint_uniform.symm

/-- Reinterpret the four canonical limbs through the exact caller-supplied
QM31 representation equivalence. -/
noncomputable def successfulComponentCStoppingTimeFreeCoordinateLaw
    {K : Type*} [Fintype K] [Nonempty K] (e : QM31Limbs ≃ K) :
    PMF (AspisV5ComponentCSamplerKernel.FreeCoordinates K) :=
  successfulComponentCSequentialCoordinatesLaw.map
    (componentCCoordinateRepresentationEquiv e)

theorem successfulComponentCStoppingTimeFreeCoordinateLaw_isIndependentUniform
    {K : Type*} [Field K] [Fintype K] (e : QM31Limbs ≃ K) :
    AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform
      (successfulComponentCStoppingTimeFreeCoordinateLaw e) := by
  classical
  rw [AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform,
    successfulComponentCStoppingTimeFreeCoordinateLaw,
    AspisV5ComponentCSamplerKernel.idealFreeCoordinateLaw,
    successfulComponentCSequentialCoordinatesLaw_eq_joint_uniform]
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv
    (componentCCoordinateRepresentationEquiv e)

/-- Exact law-level closure of the former stopping-time seam: the literal
shared-stream experiment and the preallocated-block experiment induce the
same successful free-coordinate law. -/
theorem successfulComponentCStoppingTimeFreeCoordinateLaw_eq_blockLaw
    {K : Type*} [Field K] [Fintype K] (e : QM31Limbs ≃ K) :
    successfulComponentCStoppingTimeFreeCoordinateLaw e =
      successfulComponentCFreeCoordinateLaw e := by
  have hsequential :=
    successfulComponentCStoppingTimeFreeCoordinateLaw_isIndependentUniform e
  have hblock := successfulComponentCFreeCoordinateLaw_isIndependentUniform e
  rw [AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform]
    at hsequential hblock
  exact hsequential.trans hblock.symm

/-- After the exact four-limb representation and the proved pivot encoder,
the literal stopping-time law is uniform on the Component-C kernel. -/
theorem successfulComponentCStoppingTimeKernelLaw_eq_uniform
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (e : QM31Limbs ≃ K) (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1) :
    (successfulComponentCStoppingTimeFreeCoordinateLaw e).map
        (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot) =
      PMF.uniformOfFintype (LinearMap.ker ell) := by
  rw [successfulComponentCStoppingTimeFreeCoordinateLaw_isIndependentUniform e,
    AspisV5ComponentCSamplerKernel.idealFreeCoordinateLaw]
  exact AspisV5RankOneOpeningHiding.uniform_map_linearEquiv
    (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot)

/-! ## Remaining deployment seams -/

/-- Exact code/model edge for the variable-consumption state transformer.
The Rust side must expose the composition of its 4092 consecutive bounded
M31 calls as a pure function from a word list to the values plus untouched
suffix.  Equality here binds first-success, the 16-word cap, immediate whole-run
abort, coordinate-major/four-limb order, and source advancement all at once.

The separate imported `RustLow31MaskMatches` and
`DeployedQM31LimbOrderAndCodecMatch` interfaces bind the bit-mask and the
four-limb field representation; this definition does not silently absorb
either of those code/model obligations. -/
def RustComponentCStoppingTimeControlFlowMatches
    (rustRun : List RawWord →
      Option ((Fin componentCSequentialCallCount → M31Value) × List RawWord)) :
    Prop :=
  rustRun = runSequentialCalls componentCSequentialCallCount

/-- Production derives a variable stream from finite seed material.  Replacing
it by the genuinely joint-uniform prefix used above remains exactly the
external computational PRG/CSPRNG hybrid, not an information-theoretic fact. -/
def ProductionSequentialU32StreamPseudorandomness
    (Indist : PMF ComponentCSequentialRawStream →
      PMF ComponentCSequentialRawStream → Prop)
    (productionLaw : PMF ComponentCSequentialRawStream) : Prop :=
  Indist productionLaw (PMF.uniformOfFintype ComponentCSequentialRawStream)

/-! ## Axiom audit -/

#print axioms runSequentialCalls_mapSequentialCalls
#print axioms successfulSequentialValues_joint_uniform
#print axioms successfulComponentCSequentialLaw_eq_joint_uniform
#print axioms successfulComponentCSequentialCoordinatesLaw_eq_joint_uniform
#print axioms idealIidSequentialStream_matches_preallocatedBlockExperiment
#print axioms successfulComponentCStoppingTimeFreeCoordinateLaw_isIndependentUniform
#print axioms successfulComponentCStoppingTimeFreeCoordinateLaw_eq_blockLaw
#print axioms successfulComponentCStoppingTimeKernelLaw_eq_uniform
#print axioms RustComponentCStoppingTimeControlFlowMatches
#print axioms ProductionSequentialU32StreamPseudorandomness



end AspisV5ComponentCStoppingTimeSampler
