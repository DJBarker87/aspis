import AspisFormal.V5ComponentCStoppingTimeSampler
import AspisFormal.V5ComponentCQM31TowerExact
import AspisFormal.K1.V7Tag73DeployedDecoderFiberCap

/-!
# Exact law of the Tag-73 eight-retry four-limb sampler

Tag-73 gives each M31 limb eight attempts and consumes the four limbs from
one shared stream.  This file proves, without a random-oracle assumption,
that conditioning the fixed maximum-length raw-word experiment on success
makes the four returned limbs exactly joint-uniform.

The proof is by a measure-preserving permutation of the complete raw stream.
It preserves every accept/reject decision and therefore the literal stopping
path, while independently relabelling each accepted limb value.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73EightRetrySamplerLaw

open scoped ENNReal
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

def tag73LimbRetryLimit : Nat := 8
def tag73LimbCount : Nat := 4
def tag73MaximumRawWordCount : Nat :=
  tag73LimbCount * tag73LimbRetryLimit

/-- Run consecutive bounded M31 calls with an explicit per-call fuel. -/
def runSequentialCallsWithFuel (fuel : Nat) :
    (callCount : Nat) → List RawWord →
      Option ((Fin callCount → M31Value) × List RawWord)
  | 0, words => some (Fin.elim0, words)
  | callCount + 1, words =>
      match consumeFirstSuccess fuel words with
      | none => none
      | some (head, rest) =>
          match runSequentialCallsWithFuel fuel callCount rest with
          | none => none
          | some (tail, unused) => some (Fin.cases head tail, unused)

/-- Relabel the accepted result of every bounded call, preserving its exact
stopping path and unused suffix. -/
def mapSequentialCallsWithFuel (fuel : Nat) : (callCount : Nat) →
    (Fin callCount → M31Value ≃ M31Value) → List RawWord → List RawWord
  | 0, _, words => words
  | callCount + 1, permutations, words =>
      mapBoundedThen (permutations 0)
        (mapSequentialCallsWithFuel fuel callCount
          (fun i => permutations i.succ)) fuel words

theorem runSequentialCallsWithFuel_map
    (fuel callCount : Nat)
    (permutations : Fin callCount → M31Value ≃ M31Value)
    (words : List RawWord) :
    runSequentialCallsWithFuel fuel callCount
        (mapSequentialCallsWithFuel fuel callCount permutations words) =
      (runSequentialCallsWithFuel fuel callCount words).map
        (fun result => (mapSequentialValues permutations result.1, result.2)) := by
  induction callCount generalizing words with
  | zero =>
      simp only [runSequentialCallsWithFuel, mapSequentialCallsWithFuel,
        Option.map_some]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ callCount ih =>
      simp only [mapSequentialCallsWithFuel, runSequentialCallsWithFuel]
      rw [consumeFirstSuccess_mapBoundedThen]
      cases hhead : consumeFirstSuccess fuel words with
      | none => rfl
      | some first =>
          rcases first with ⟨head, rest⟩
          simp only [Option.map_some]
          rw [ih]
          cases htail : runSequentialCallsWithFuel fuel callCount rest with
          | none => rfl
          | some tailResult =>
              rcases tailResult with ⟨tail, unused⟩
              simp only [Option.map_some]
              congr 2
              funext i
              refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem mapSequentialCallsWithFuel_length
    (fuel callCount : Nat)
    (permutations : Fin callCount → M31Value ≃ M31Value)
    (words : List RawWord) :
    (mapSequentialCallsWithFuel fuel callCount permutations words).length =
      words.length := by
  induction callCount generalizing words with
  | zero => rfl
  | succ callCount ih =>
      exact mapBoundedThen_length _ _
        (fun rest => ih (fun i => permutations i.succ) rest) _ _

theorem mapSequentialCallsWithFuel_symm
    (fuel callCount : Nat)
    (permutations : Fin callCount → M31Value ≃ M31Value)
    (words : List RawWord) :
    mapSequentialCallsWithFuel fuel callCount
        (fun i => (permutations i).symm)
        (mapSequentialCallsWithFuel fuel callCount permutations words) = words := by
  induction callCount generalizing words with
  | zero => rfl
  | succ callCount ih =>
      exact mapBoundedThen_symm _ _ _
        (fun rest => ih (fun i => permutations i.succ) rest) _ _

abbrev Tag73RawStream :=
  List.Vector RawWord tag73MaximumRawWordCount

instance : Fintype Tag73RawStream :=
  Fintype.ofEquiv (Fin tag73MaximumRawWordCount → RawWord)
    (Equiv.vectorEquivFin RawWord tag73MaximumRawWordCount).symm

def mapTag73RawStream
    (permutations : Fin tag73LimbCount → M31Value ≃ M31Value)
    (words : Tag73RawStream) : Tag73RawStream :=
  ⟨mapSequentialCallsWithFuel tag73LimbRetryLimit tag73LimbCount
      permutations words.1,
    (mapSequentialCallsWithFuel_length _ _ _ _).trans words.2⟩

def tag73RawStreamPerm
    (permutations : Fin tag73LimbCount → M31Value ≃ M31Value) :
    Tag73RawStream ≃ Tag73RawStream where
  toFun := mapTag73RawStream permutations
  invFun := mapTag73RawStream (fun i => (permutations i).symm)
  left_inv := by
    intro words
    apply Subtype.ext
    exact mapSequentialCallsWithFuel_symm _ _ _ words.1
  right_inv := by
    intro words
    apply Subtype.ext
    exact mapSequentialCallsWithFuel_symm _ _
      (fun i => (permutations i).symm) words.1

def tag73RawRun (raw : Tag73RawStream) :
    Option ((Fin tag73LimbCount → M31Value) × List RawWord) :=
  runSequentialCallsWithFuel tag73LimbRetryLimit tag73LimbCount raw.1

theorem tag73RawRun_perm
    (permutations : Fin tag73LimbCount → M31Value ≃ M31Value)
    (raw : Tag73RawStream) :
    tag73RawRun (tag73RawStreamPerm permutations raw) =
      (tag73RawRun raw).map
        (fun result => (mapSequentialValues permutations result.1, result.2)) := by
  exact runSequentialCallsWithFuel_map _ _ _ raw.1

def Tag73RawSucceeds (raw : Tag73RawStream) : Prop :=
  (tag73RawRun raw).isSome

instance (raw : Tag73RawStream) : Decidable (Tag73RawSucceeds raw) := by
  unfold Tag73RawSucceeds
  infer_instance

abbrev SuccessfulTag73RawStream :=
  {raw : Tag73RawStream // Tag73RawSucceeds raw}

theorem tag73RawSucceeds_perm
    (permutations : Fin tag73LimbCount → M31Value ≃ M31Value)
    (raw : Tag73RawStream) :
    Tag73RawSucceeds raw ↔
      Tag73RawSucceeds (tag73RawStreamPerm permutations raw) := by
  unfold Tag73RawSucceeds
  rw [tag73RawRun_perm, Option.isSome_map]

def successfulTag73RawStreamPerm
    (permutations : Fin tag73LimbCount → M31Value ≃ M31Value) :
    SuccessfulTag73RawStream ≃ SuccessfulTag73RawStream :=
  (tag73RawStreamPerm permutations).subtypeEquiv fun raw =>
    tag73RawSucceeds_perm permutations raw

def tag73ValuesOrFirst (raw : Tag73RawStream) :
    Fin tag73LimbCount → M31Value :=
  match tag73RawRun raw with
  | some result => result.1
  | none => fun _ => firstM31Value

def successfulTag73Values (raw : SuccessfulTag73RawStream) :
    Fin tag73LimbCount → M31Value :=
  tag73ValuesOrFirst raw.1

theorem successfulTag73Values_perm
    (permutations : Fin tag73LimbCount → M31Value ≃ M31Value)
    (raw : SuccessfulTag73RawStream) :
    successfulTag73Values (successfulTag73RawStreamPerm permutations raw) =
      mapSequentialValues permutations (successfulTag73Values raw) := by
  have hrun := tag73RawRun_perm permutations raw.1
  cases hresult : tag73RawRun raw.1 with
  | none =>
      have hsuccess := raw.2
      change (tag73RawRun raw.1).isSome at hsuccess
      rw [hresult] at hsuccess
      contradiction
  | some result =>
      have hval :
          (successfulTag73RawStreamPerm permutations raw).1 =
            tag73RawStreamPerm permutations raw.1 := rfl
      rw [successfulTag73Values, hval, tag73ValuesOrFirst, hrun]
      simp [successfulTag73Values, tag73ValuesOrFirst, hresult]

def acceptedTag73RawWord : RawWord :=
  rawWordResultHighBitEquiv.symm (some firstM31Value, 0)

@[simp] theorem rawWordResult_acceptedTag73RawWord :
    rawWordResult acceptedTag73RawWord = some firstM31Value := by
  have h := rawWordResultHighBitEquiv_fst acceptedTag73RawWord
  simpa [acceptedTag73RawWord] using h.symm

theorem runSequentialCallsWithFuel_replicate_accepted
    (fuel callCount : Nat) (unused : List RawWord) (fuelPositive : 0 < fuel) :
    runSequentialCallsWithFuel fuel callCount
        (List.replicate callCount acceptedTag73RawWord ++ unused) =
      some (fun _ => firstM31Value, unused) := by
  induction callCount with
  | zero =>
      simp only [List.replicate_zero, List.nil_append,
        runSequentialCallsWithFuel]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ callCount ih =>
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt fuelPositive)
      rw [List.replicate_succ, List.cons_append,
        runSequentialCallsWithFuel]
      simp only [consumeFirstSuccess, rawWordResult_acceptedTag73RawWord]
      rw [ih]
      simp only
      congr 2
      funext i
      refine Fin.cases rfl (fun _ => rfl) i

def acceptedTag73RawStream : Tag73RawStream :=
  ⟨List.replicate tag73MaximumRawWordCount acceptedTag73RawWord,
    List.length_replicate⟩

theorem tag73LimbCount_le_maximumRawWordCount :
    tag73LimbCount ≤ tag73MaximumRawWordCount := by
  norm_num [tag73LimbCount, tag73MaximumRawWordCount, tag73LimbRetryLimit]

theorem acceptedTag73RawStream_succeeds :
    Tag73RawSucceeds acceptedTag73RawStream := by
  unfold Tag73RawSucceeds tag73RawRun
  have hsplit :
      List.replicate tag73MaximumRawWordCount acceptedTag73RawWord =
        List.replicate tag73LimbCount acceptedTag73RawWord ++
          List.replicate (tag73MaximumRawWordCount - tag73LimbCount)
            acceptedTag73RawWord := by
    rw [← List.replicate_add]
    congr
  change
    (runSequentialCallsWithFuel tag73LimbRetryLimit tag73LimbCount
      (List.replicate tag73MaximumRawWordCount acceptedTag73RawWord)).isSome
  rw [hsplit, runSequentialCallsWithFuel_replicate_accepted]
  · rfl
  · norm_num [tag73LimbRetryLimit]

def successfulTag73RawStreamExample : SuccessfulTag73RawStream :=
  ⟨acceptedTag73RawStream, acceptedTag73RawStream_succeeds⟩

instance : Nonempty SuccessfulTag73RawStream :=
  ⟨successfulTag73RawStreamExample⟩

instance : Nonempty Tag73RawStream :=
  ⟨acceptedTag73RawStream⟩

def successfulTag73ValuesFibreEquiv
    (values base : Fin tag73LimbCount → M31Value) :
    {raw : SuccessfulTag73RawStream // successfulTag73Values raw = values} ≃
      {raw : SuccessfulTag73RawStream // successfulTag73Values raw = base} :=
  (successfulTag73RawStreamPerm
    (fun i => Equiv.swap (values i) (base i))).subtypeEquiv fun raw => by
      rw [successfulTag73Values_perm]
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

/-- Conditional on successful completion, the literal Tag-73 shared-stream
four-limb sampler is exactly joint-uniform. -/
theorem successfulTag73Values_joint_uniform :
    (PMF.uniformOfFintype SuccessfulTag73RawStream).map
        successfulTag73Values =
      PMF.uniformOfFintype (Fin tag73LimbCount → M31Value) := by
  let base : Fin tag73LimbCount → M31Value := fun _ => firstM31Value
  exact uniform_map_of_equiv_fibres successfulTag73Values base
    (fun values => successfulTag73ValuesFibreEquiv values base)

theorem successfulTag73ConditioningWitness :
    ∃ raw ∈ {raw : Tag73RawStream | Tag73RawSucceeds raw},
      raw ∈ (PMF.uniformOfFintype Tag73RawStream).support :=
  ⟨acceptedTag73RawStream, acceptedTag73RawStream_succeeds,
    PMF.mem_support_uniformOfFintype _⟩

/-- The literal conditional distribution obtained from a uniform 32-word
prefix and the deployed eight-attempt stopping rule. -/
def successfulTag73FourLimbLaw :
    PMF (Fin tag73LimbCount → M31Value) :=
  ((PMF.uniformOfFintype Tag73RawStream).filter
    {raw : Tag73RawStream | Tag73RawSucceeds raw}
      successfulTag73ConditioningWitness).map tag73ValuesOrFirst

/-- Exact PMF form of the four-limb law. -/
theorem successfulTag73FourLimbLaw_eq_joint_uniform :
    successfulTag73FourLimbLaw =
      PMF.uniformOfFintype (Fin tag73LimbCount → M31Value) := by
  rw [successfulTag73FourLimbLaw,
    uniform_filter_eq_uniform_subtype Tag73RawSucceeds
      successfulTag73ConditioningWitness,
    PMF.map_comp]
  have hfun : tag73ValuesOrFirst ∘
      (Subtype.val : SuccessfulTag73RawStream → Tag73RawStream) =
        successfulTag73Values := rfl
  rw [hfun]
  exact successfulTag73Values_joint_uniform

def tag73LimbVectorEquiv :
    (Fin tag73LimbCount → M31Value) ≃ QM31Limbs :=
  Equiv.arrowCongr
    (finCongr (by norm_num [tag73LimbCount, qm31LimbCount]))
    (Equiv.refl M31Value)

def tag73FourLimbsToExact :
    (Fin tag73LimbCount → M31Value) ≃ QM31Exact :=
  tag73LimbVectorEquiv.trans qm31ExactLimbEquiv

def successfulTag73OrdinaryExactLaw : PMF QM31Exact :=
  successfulTag73FourLimbLaw.map tag73FourLimbsToExact

/-- Conditional on no eight-attempt limb abort, one ordinary deployed
Tag-73 challenge is exactly uniform over the complete QM31 tower. -/
theorem successfulTag73OrdinaryExactLaw_eq_uniform :
    successfulTag73OrdinaryExactLaw = PMF.uniformOfFintype QM31Exact := by
  rw [successfulTag73OrdinaryExactLaw,
    successfulTag73FourLimbLaw_eq_joint_uniform]
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv tag73FourLimbsToExact

/-! ## Three-attempt nonzero wrapper -/

abbrev NonzeroQM31Exact := {value : QM31Exact // value ≠ 0}
abbrev Tag73NonzeroAttemptValues := Fin 3 → QM31Exact

instance : Nonempty NonzeroQM31Exact :=
  ⟨⟨1, one_ne_zero⟩⟩

/-- First nonzero result among the bounded outer attempts. -/
def firstNonzeroExact : (attempts : Nat) →
    (Fin attempts → QM31Exact) → Option NonzeroQM31Exact
  | 0, _ => none
  | attempts + 1, values =>
      if nonzero : values 0 ≠ 0 then
        some ⟨values 0, nonzero⟩
      else
        firstNonzeroExact attempts (fun i => values i.succ)

def mapNonzeroExact (e : QM31Exact ≃ QM31Exact)
    (fixZero : e 0 = 0) (value : NonzeroQM31Exact) : NonzeroQM31Exact :=
  ⟨e value.1, by
    intro equalZero
    apply value.2
    apply e.injective
    simpa [fixZero] using equalZero⟩

theorem firstNonzeroExact_map
    (e : QM31Exact ≃ QM31Exact) (fixZero : e 0 = 0)
    (attempts : Nat) (values : Fin attempts → QM31Exact) :
    firstNonzeroExact attempts (fun i => e (values i)) =
      (firstNonzeroExact attempts values).map (mapNonzeroExact e fixZero) := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      simp only [firstNonzeroExact]
      by_cases nonzero : values 0 ≠ 0
      · have mappedNonzero : e (values 0) ≠ 0 := by
          intro equalZero
          apply nonzero
          apply e.injective
          simpa [fixZero] using equalZero
        rw [dif_pos nonzero, dif_pos mappedNonzero]
        rfl
      · have zero : values 0 = 0 := not_ne_iff.mp nonzero
        have mappedZero : e (values 0) = 0 := by simpa [zero]
        rw [dif_neg nonzero, dif_neg (not_ne_iff.mpr mappedZero), ih]

def tag73NonzeroAttemptPerm
    (e : QM31Exact ≃ QM31Exact) :
    Tag73NonzeroAttemptValues ≃ Tag73NonzeroAttemptValues :=
  Equiv.piCongrRight fun _ => e

def Tag73NonzeroSucceeds (values : Tag73NonzeroAttemptValues) : Prop :=
  (firstNonzeroExact 3 values).isSome

instance (values : Tag73NonzeroAttemptValues) :
    Decidable (Tag73NonzeroSucceeds values) := by
  unfold Tag73NonzeroSucceeds
  infer_instance

abbrev SuccessfulTag73NonzeroAttempts :=
  {values : Tag73NonzeroAttemptValues // Tag73NonzeroSucceeds values}

theorem tag73NonzeroSucceeds_perm
    (e : QM31Exact ≃ QM31Exact) (fixZero : e 0 = 0)
    (values : Tag73NonzeroAttemptValues) :
    Tag73NonzeroSucceeds values ↔
      Tag73NonzeroSucceeds (tag73NonzeroAttemptPerm e values) := by
  unfold Tag73NonzeroSucceeds
  have hmap := firstNonzeroExact_map e fixZero 3 values
  have permApply :
      tag73NonzeroAttemptPerm e values = fun i => e (values i) := by
    funext i
    rfl
  have hmap' :
      firstNonzeroExact 3 (tag73NonzeroAttemptPerm e values) =
        (firstNonzeroExact 3 values).map (mapNonzeroExact e fixZero) := by
    rw [permApply]
    exact hmap
  rw [hmap', Option.isSome_map]

def successfulTag73NonzeroAttemptPerm
    (e : QM31Exact ≃ QM31Exact) (fixZero : e 0 = 0) :
    SuccessfulTag73NonzeroAttempts ≃ SuccessfulTag73NonzeroAttempts :=
  (tag73NonzeroAttemptPerm e).subtypeEquiv fun values =>
    tag73NonzeroSucceeds_perm e fixZero values

def tag73NonzeroValueOrOne (values : Tag73NonzeroAttemptValues) :
    NonzeroQM31Exact :=
  (firstNonzeroExact 3 values).getD ⟨1, one_ne_zero⟩

def successfulTag73NonzeroValue
    (values : SuccessfulTag73NonzeroAttempts) : NonzeroQM31Exact :=
  tag73NonzeroValueOrOne values.1

theorem successfulTag73NonzeroValue_perm
    (e : QM31Exact ≃ QM31Exact) (fixZero : e 0 = 0)
    (values : SuccessfulTag73NonzeroAttempts) :
    successfulTag73NonzeroValue
        (successfulTag73NonzeroAttemptPerm e fixZero values) =
      mapNonzeroExact e fixZero (successfulTag73NonzeroValue values) := by
  have hrun := firstNonzeroExact_map e fixZero 3 values.1
  have permApply :
      tag73NonzeroAttemptPerm e values.1 = fun i => e (values.1 i) := by
    funext i
    rfl
  have hrun' :
      firstNonzeroExact 3 (tag73NonzeroAttemptPerm e values.1) =
        (firstNonzeroExact 3 values.1).map (mapNonzeroExact e fixZero) := by
    rw [permApply]
    exact hrun
  cases hresult : firstNonzeroExact 3 values.1 with
  | none =>
      have hsuccess := values.2
      change (firstNonzeroExact 3 values.1).isSome at hsuccess
      rw [hresult] at hsuccess
      contradiction
  | some result =>
      change
        (firstNonzeroExact 3
          (tag73NonzeroAttemptPerm e values.1)).getD ⟨1, one_ne_zero⟩ = _
      rw [hrun', hresult]
      simp [successfulTag73NonzeroValue, tag73NonzeroValueOrOne, hresult]

def successfulTag73NonzeroAttemptsExample : SuccessfulTag73NonzeroAttempts :=
  ⟨fun _ => 1, by
    unfold Tag73NonzeroSucceeds
    simp [firstNonzeroExact]⟩

instance : Nonempty SuccessfulTag73NonzeroAttempts :=
  ⟨successfulTag73NonzeroAttemptsExample⟩

def successfulTag73NonzeroValueFibreEquiv
    (value base : NonzeroQM31Exact) :
    {attempts : SuccessfulTag73NonzeroAttempts //
        successfulTag73NonzeroValue attempts = value} ≃
      {attempts : SuccessfulTag73NonzeroAttempts //
        successfulTag73NonzeroValue attempts = base} := by
  let e : QM31Exact ≃ QM31Exact := Equiv.swap value.1 base.1
  have fixZero : e 0 = 0 := by
    exact Equiv.swap_apply_of_ne_of_ne value.2.symm base.2.symm
  exact (successfulTag73NonzeroAttemptPerm e fixZero).subtypeEquiv
    (fun attempts => by
      rw [successfulTag73NonzeroValue_perm]
      constructor
      · intro hvalue
        apply Subtype.ext
        change e (successfulTag73NonzeroValue attempts).1 = base.1
        rw [hvalue]
        exact Equiv.swap_apply_left _ _
      · intro hmapped
        apply Subtype.ext
        apply e.injective
        change e (successfulTag73NonzeroValue attempts).1 = e value.1
        rw [Equiv.swap_apply_left]
        exact congrArg Subtype.val hmapped)

/-- Conditional on at least one nonzero result, three iid uniform QM31
attempts return an exactly uniform nonzero QM31 element. -/
theorem successfulTag73NonzeroValue_uniform :
    (PMF.uniformOfFintype SuccessfulTag73NonzeroAttempts).map
        successfulTag73NonzeroValue =
      PMF.uniformOfFintype NonzeroQM31Exact := by
  let base : NonzeroQM31Exact := ⟨1, one_ne_zero⟩
  exact uniform_map_of_equiv_fibres successfulTag73NonzeroValue base
    (fun value => successfulTag73NonzeroValueFibreEquiv value base)

def nonzeroTargetEvent (target : Finset QM31Exact) :
    Set NonzeroQM31Exact :=
  {value | value.1 ∈ target}

def nonzeroTargetEventSubtypeEquiv (target : Finset QM31Exact) :
    (nonzeroTargetEvent target) ≃
      {value : NonzeroQM31Exact // value.1 ∈ target} where
  toFun value := ⟨value.1, value.2⟩
  invFun value := ⟨value.1, value.2⟩
  left_inv value := by cases value; rfl
  right_inv value := by cases value; rfl

/-- Exact finite-uniform probability of a target set after the three-attempt
nonzero wrapper. -/
theorem uniform_nonzero_target_probability_exact
    (target : Finset QM31Exact) :
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (nonzeroTargetEvent target) =
      (Fintype.card {value : NonzeroQM31Exact // value.1 ∈ target} : ENNReal) /
        (Fintype.card NonzeroQM31Exact : ENNReal) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr (nonzeroTargetEventSubtypeEquiv target)]

def nonzeroTargetEmbedding (target : Finset QM31Exact) :
    {value : NonzeroQM31Exact // value.1 ∈ target} ↪
      {value : QM31Exact // value ∈ target} where
  toFun value := ⟨value.1.1, value.2⟩
  inj' := by
    intro left right equal
    have valueEqual : left.1.1 = right.1.1 :=
      congrArg
        (fun value : {value : QM31Exact // value ∈ target} => value.1)
        equal
    apply Subtype.ext
    apply Subtype.ext
    exact valueEqual

theorem nonzero_target_card_le (target : Finset QM31Exact) :
    Fintype.card {value : NonzeroQM31Exact // value.1 ∈ target} ≤ target.card := by
  classical
  calc
    Fintype.card {value : NonzeroQM31Exact // value.1 ∈ target} ≤
        Fintype.card {value : QM31Exact // value ∈ target} :=
      Fintype.card_le_of_injective (nonzeroTargetEmbedding target)
        (nonzeroTargetEmbedding target).injective
    _ = target.card := Fintype.card_coe _

theorem nonzero_qm31_exact_card :
    Fintype.card NonzeroQM31Exact = P ^ 4 - 1 := by
  change Fintype.card {value : QM31Exact // value ≠ 0} = P ^ 4 - 1
  simp [qm31Exact_card]

/-- A target fixed before the nonzero challenge is sampled is hit with at
most its cardinality divided by the exact nonzero QM31 field size. -/
theorem uniform_nonzero_target_probability_le
    (target : Finset QM31Exact) :
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (nonzeroTargetEvent target) ≤
      (target.card : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  rw [uniform_nonzero_target_probability_exact, nonzero_qm31_exact_card]
  gcongr
  exact_mod_cast nonzero_target_card_le target

end

#print axioms successfulTag73FourLimbLaw_eq_joint_uniform
#print axioms successfulTag73OrdinaryExactLaw_eq_uniform
#print axioms successfulTag73NonzeroValue_uniform
#print axioms uniform_nonzero_target_probability_le

end AspisK1.V7Tag73EightRetrySamplerLaw
