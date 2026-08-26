import AspisFormal.K1.V7Tag73EightRetrySamplerLaw

/-!
# Exact raw-stream law for the Tag-73 nonzero QM31 wrapper

One deployed nonzero challenge makes at most three ordinary `challenge_qm31`
calls.  Each ordinary call starts at a fresh 256-bit block boundary and may
consume at most four blocks (32 little-endian words).  This file composes the
already proved eight-retry ordinary-call law across those three fresh calls.

The sample space retains the complete successful raw stream for every outer
attempt, including the independent continuations after the first nonzero
value.  Those unused continuations are ghost randomness only: the returned
value is the literal first nonzero decoded value.  Equicardinal fibres prove
that conditioning on outer success gives the exact uniform law on
`QM31Exact \ {0}`.  No proof-of-work normalization is used.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73RawNonzeroSamplerLaw

open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

abbrev Tag73SuccessfulOrdinaryRawAttempts :=
  Fin 3 → SuccessfulTag73RawStream

/-- The exact tower-field value decoded by each independently block-aligned
ordinary attempt. -/
def successfulRawAttemptExactValues
    (raw : Tag73SuccessfulOrdinaryRawAttempts) :
    Tag73NonzeroAttemptValues :=
  fun attempt => tag73FourLimbsToExact (successfulTag73Values (raw attempt))

/-- Outer success is exactly the production condition that at least one of
the three successfully decoded ordinary values is nonzero. -/
def Tag73SuccessfulRawNonzero (raw : Tag73SuccessfulOrdinaryRawAttempts) : Prop :=
  Tag73NonzeroSucceeds (successfulRawAttemptExactValues raw)

instance (raw : Tag73SuccessfulOrdinaryRawAttempts) :
    Decidable (Tag73SuccessfulRawNonzero raw) := by
  unfold Tag73SuccessfulRawNonzero
  infer_instance

abbrev SuccessfulTag73RawNonzeroAttempts :=
  {raw : Tag73SuccessfulOrdinaryRawAttempts // Tag73SuccessfulRawNonzero raw}

/-- The value-level outer-attempt vector retained by one successful raw
execution. -/
def successfulRawToValueAttempts
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    SuccessfulTag73NonzeroAttempts :=
  ⟨successfulRawAttemptExactValues raw.1, raw.2⟩

/-- Literal returned nonzero value of one successful raw execution. -/
def successfulRawNonzeroValue
    (raw : SuccessfulTag73RawNonzeroAttempts) : NonzeroQM31Exact :=
  successfulTag73NonzeroValue (successfulRawToValueAttempts raw)

private def exactValueLimbVector (value : QM31Exact) :
    Fin tag73LimbCount → M31Value :=
  tag73FourLimbsToExact.symm value

/-- Relabel one ordinary raw stream from one exact tower value to another,
without changing any of its four limb stopping positions. -/
def successfulRawExactValueFibreEquiv (value base : QM31Exact) :
    {raw : SuccessfulTag73RawStream //
        tag73FourLimbsToExact (successfulTag73Values raw) = value} ≃
      {raw : SuccessfulTag73RawStream //
        tag73FourLimbsToExact (successfulTag73Values raw) = base} :=
  (successfulTag73RawStreamPerm
    (fun limb => Equiv.swap
      (exactValueLimbVector value limb)
      (exactValueLimbVector base limb))).subtypeEquiv fun raw => by
    rw [successfulTag73Values_perm]
    constructor
    · intro hvalue
      rw [← tag73FourLimbsToExact.apply_symm_apply base]
      apply congrArg tag73FourLimbsToExact
      funext limb
      rw [mapSequentialValues]
      have limbs : successfulTag73Values raw = exactValueLimbVector value := by
        apply tag73FourLimbsToExact.injective
        simpa [exactValueLimbVector] using hvalue
      rw [limbs]
      exact Equiv.swap_apply_left _ _
    · intro hmapped
      rw [← tag73FourLimbsToExact.apply_symm_apply value]
      apply congrArg tag73FourLimbsToExact
      funext limb
      change successfulTag73Values raw limb = exactValueLimbVector value limb
      have mappedLimbs :
          mapSequentialValues
              (fun limb => Equiv.swap
                (exactValueLimbVector value limb)
                (exactValueLimbVector base limb))
              (successfulTag73Values raw) =
            exactValueLimbVector base := by
        apply tag73FourLimbsToExact.injective
        simpa [exactValueLimbVector] using hmapped
      apply (Equiv.swap
        (exactValueLimbVector value limb)
        (exactValueLimbVector base limb)).injective
      have mappedAt := congrFun mappedLimbs limb
      change (Equiv.swap
          (exactValueLimbVector value limb)
          (exactValueLimbVector base limb))
          (successfulTag73Values raw limb) =
        exactValueLimbVector base limb at mappedAt
      simpa only [Equiv.swap_apply_left] using mappedAt

/-- Relabel the three block-aligned ordinary attempts independently. -/
def successfulRawAttemptVectorFibreEquiv
    (values base : Tag73NonzeroAttemptValues) :
    {raw : Tag73SuccessfulOrdinaryRawAttempts //
        successfulRawAttemptExactValues raw = values} ≃
      {raw : Tag73SuccessfulOrdinaryRawAttempts //
        successfulRawAttemptExactValues raw = base} := by
  let permutation : Tag73SuccessfulOrdinaryRawAttempts ≃
      Tag73SuccessfulOrdinaryRawAttempts :=
    Equiv.piCongrRight fun attempt =>
      successfulTag73RawStreamPerm
        (fun limb => Equiv.swap
          (exactValueLimbVector (values attempt) limb)
          (exactValueLimbVector (base attempt) limb))
  exact permutation.subtypeEquiv fun raw => by
    constructor
    · intro hvalues
      funext attempt
      change tag73FourLimbsToExact
          (successfulTag73Values (permutation raw attempt)) = base attempt
      change tag73FourLimbsToExact
          (successfulTag73Values
            (successfulTag73RawStreamPerm _ (raw attempt))) = base attempt
      rw [successfulTag73Values_perm]
      rw [← tag73FourLimbsToExact.apply_symm_apply (base attempt)]
      apply congrArg tag73FourLimbsToExact
      funext limb
      rw [mapSequentialValues]
      have valueAt := congrFun hvalues attempt
      have limbsAt : successfulTag73Values (raw attempt) =
          exactValueLimbVector (values attempt) := by
        apply tag73FourLimbsToExact.injective
        simpa [successfulRawAttemptExactValues, exactValueLimbVector]
          using valueAt
      rw [limbsAt]
      exact Equiv.swap_apply_left _ _
    · intro hmapped
      funext attempt
      unfold successfulRawAttemptExactValues
      rw [← tag73FourLimbsToExact.apply_symm_apply (values attempt)]
      apply congrArg tag73FourLimbsToExact
      funext limb
      change successfulTag73Values (raw attempt) limb =
        exactValueLimbVector (values attempt) limb
      have mappedAttempt := congrFun hmapped attempt
      dsimp [permutation, successfulRawAttemptExactValues] at mappedAttempt
      change tag73FourLimbsToExact
          (successfulTag73Values
            (successfulTag73RawStreamPerm
              (fun limb => Equiv.swap
                (exactValueLimbVector (values attempt) limb)
                (exactValueLimbVector (base attempt) limb))
              (raw attempt))) = base attempt at mappedAttempt
      rw [successfulTag73Values_perm] at mappedAttempt
      change tag73FourLimbsToExact
          (mapSequentialValues
            (fun limb => Equiv.swap
              (exactValueLimbVector (values attempt) limb)
              (exactValueLimbVector (base attempt) limb))
            (successfulTag73Values (raw attempt))) = base attempt
        at mappedAttempt
      have mappedLimbs :
          mapSequentialValues
              (fun limb => Equiv.swap
                (exactValueLimbVector (values attempt) limb)
                (exactValueLimbVector (base attempt) limb))
              (successfulTag73Values (raw attempt)) =
            exactValueLimbVector (base attempt) := by
        apply tag73FourLimbsToExact.injective
        simpa [exactValueLimbVector] using mappedAttempt
      apply (Equiv.swap
        (exactValueLimbVector (values attempt) limb)
        (exactValueLimbVector (base attempt) limb)).injective
      have mappedAt := congrFun mappedLimbs limb
      change (Equiv.swap
          (exactValueLimbVector (values attempt) limb)
          (exactValueLimbVector (base attempt) limb))
          (successfulTag73Values (raw attempt) limb) =
        exactValueLimbVector (base attempt) limb at mappedAt
      simpa only [Equiv.swap_apply_left] using mappedAt

/-- Three independently block-aligned successful ordinary raw samplers decode
to a joint-uniform vector of three exact QM31 values. -/
theorem successfulRawAttemptExactValues_joint_uniform :
    (PMF.uniformOfFintype Tag73SuccessfulOrdinaryRawAttempts).map
        successfulRawAttemptExactValues =
      PMF.uniformOfFintype Tag73NonzeroAttemptValues := by
  let base : Tag73NonzeroAttemptValues := fun _ => 0
  exact uniform_map_of_equiv_fibres successfulRawAttemptExactValues base
    (fun values => successfulRawAttemptVectorFibreEquiv values base)

def successfulZeroRawStream :
    {raw : SuccessfulTag73RawStream //
      tag73FourLimbsToExact (successfulTag73Values raw) = 0} := by
  refine ⟨successfulTag73RawStreamExample, ?_⟩
  change tag73FourLimbsToExact (fun _ => firstM31Value) = 0
  rw [← tag73FourLimbsToExact.apply_symm_apply (0 : QM31Exact)]
  apply congrArg tag73FourLimbsToExact
  funext limb
  fin_cases limb <;>
    simp [firstM31Value, tag73FourLimbsToExact, tag73LimbVectorEquiv,
      qm31ExactLimbEquiv, qm31ExactToLimbs, m31ResidueEquiv]

def successfulOneRawStream :
    {raw : SuccessfulTag73RawStream //
      tag73FourLimbsToExact (successfulTag73Values raw) = 1} :=
  (successfulRawExactValueFibreEquiv 1 0).symm successfulZeroRawStream

def successfulTag73RawNonzeroAttemptsExample :
    SuccessfulTag73RawNonzeroAttempts := by
  let raw : Tag73SuccessfulOrdinaryRawAttempts :=
    fun _ => successfulOneRawStream.1
  refine ⟨raw, ?_⟩
  unfold Tag73SuccessfulRawNonzero Tag73NonzeroSucceeds
    successfulRawAttemptExactValues
  have oneAt : ∀ attempt,
      tag73FourLimbsToExact (successfulTag73Values (raw attempt)) = 1 := by
    intro attempt
    exact successfulOneRawStream.2
  simp only [firstNonzeroExact]
  simp [oneAt]

instance : Nonempty SuccessfulTag73RawNonzeroAttempts :=
  ⟨successfulTag73RawNonzeroAttemptsExample⟩

/-- Fibres of the successful raw-to-value projection are equicardinal. -/
def successfulRawValueFibreForget
    (values : SuccessfulTag73NonzeroAttempts) :
    {raw : SuccessfulTag73RawNonzeroAttempts //
        successfulRawToValueAttempts raw = values} ≃
      {raw : Tag73SuccessfulOrdinaryRawAttempts //
        successfulRawAttemptExactValues raw = values.1} where
  toFun raw := ⟨raw.1.1, by
    exact congrArg Subtype.val raw.2⟩
  invFun raw := by
    have succeeds : Tag73SuccessfulRawNonzero raw.1 := by
      unfold Tag73SuccessfulRawNonzero
      rw [raw.2]
      exact values.2
    refine ⟨⟨raw.1, succeeds⟩, ?_⟩
    apply Subtype.ext
    exact raw.2
  left_inv raw := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv raw := by
    apply Subtype.ext
    rfl

/-- Fibres of the successful raw-to-value projection are equicardinal. -/
def successfulRawToValueAttemptsFibreEquiv
    (values base : SuccessfulTag73NonzeroAttempts) :
    {raw : SuccessfulTag73RawNonzeroAttempts //
        successfulRawToValueAttempts raw = values} ≃
      {raw : SuccessfulTag73RawNonzeroAttempts //
        successfulRawToValueAttempts raw = base} :=
  (successfulRawValueFibreForget values).trans
    ((successfulRawAttemptVectorFibreEquiv values.1 base.1).trans
      (successfulRawValueFibreForget base).symm)

/-- Conditioning the exact block-aligned raw experiment on outer success and
then forgetting the raw words gives the uniform successful value experiment. -/
theorem successfulRawToValueAttempts_uniform :
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).map
        successfulRawToValueAttempts =
      PMF.uniformOfFintype SuccessfulTag73NonzeroAttempts := by
  let base : SuccessfulTag73NonzeroAttempts :=
    successfulTag73NonzeroAttemptsExample
  exact uniform_map_of_equiv_fibres successfulRawToValueAttempts base
    (fun values => successfulRawToValueAttemptsFibreEquiv values base)

/-- Exact deployed outer-wrapper conclusion: conditional on no inner sampler
abort and on finding a nonzero value within three attempts, the literal
returned value is uniform on `QM31Exact \ {0}`. -/
theorem successfulRawNonzeroValue_uniform :
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).map
        successfulRawNonzeroValue =
      PMF.uniformOfFintype NonzeroQM31Exact := by
  rw [show successfulRawNonzeroValue =
      successfulTag73NonzeroValue ∘ successfulRawToValueAttempts by rfl,
    ← PMF.map_comp, successfulRawToValueAttempts_uniform]
  exact successfulTag73NonzeroValue_uniform

end


#print axioms successfulRawAttemptExactValues_joint_uniform
#print axioms successfulRawToValueAttempts_uniform
#print axioms successfulRawNonzeroValue_uniform

end AspisK1.V7Tag73RawNonzeroSamplerLaw
