import AspisFormal.K1.V7Tag73RawNonzeroSamplerLaw

/-!
# Nuisance/value factorization of the Tag-73 nonzero sampler

The response produced after restoring `gamma` may depend on rejection
positions, unused words, high bits, and the independent duplex-advance
answers.  A sound causal argument therefore cannot merely prove that gamma is
uniform after averaging those values away.

This file starts the stronger factorization.  A successful ordinary sampler
stream is equivalent to:

* a canonical skeleton whose four accepted values have been relabelled to
  zero while all stopping positions and unused words are retained; and
* the four exact accepted values.

Applying that equivalence independently to the three outer attempts gives a
product of a complete raw skeleton and three exact QM31 values.  Restricting
to outer success affects only the value component, so the successful nonzero
experiment factors into independent skeleton data and the existing
successful value experiment.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73RawNonzeroSamplerFactorization

open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

def zeroTag73LimbValues : Fin tag73LimbCount → M31Value :=
  fun _ => firstM31Value

abbrev Tag73OrdinarySamplerSkeleton :=
  {raw : SuccessfulTag73RawStream //
    successfulTag73Values raw = zeroTag73LimbValues}

instance : Nonempty Tag73OrdinarySamplerSkeleton :=
  ⟨(successfulTag73ValuesFibreEquiv
      (successfulTag73Values successfulTag73RawStreamExample)
      zeroTag73LimbValues)
    ⟨successfulTag73RawStreamExample, rfl⟩⟩

/-- Exact product decomposition of one successful ordinary sampler.  Building
this as a composition through the sigma type of exact fibres lets Lean carry
the dependent equality witnesses without any proof-irrelevant casts. -/
def successfulOrdinaryRawFactorization :
    SuccessfulTag73RawStream ≃
      Tag73OrdinarySamplerSkeleton ×
        (Fin tag73LimbCount → M31Value) :=
  (Equiv.sigmaFiberEquiv successfulTag73Values).symm |>.trans
    (Equiv.sigmaCongrRight fun values =>
      successfulTag73ValuesFibreEquiv values zeroTag73LimbValues) |>.trans
    (Equiv.sigmaEquivProd
      (Fin tag73LimbCount → M31Value) Tag73OrdinarySamplerSkeleton) |>.trans
    (Equiv.prodComm _ _)

def splitSuccessfulOrdinaryRaw
    (raw : SuccessfulTag73RawStream) :
    Tag73OrdinarySamplerSkeleton × (Fin tag73LimbCount → M31Value) :=
  successfulOrdinaryRawFactorization raw

def combineSuccessfulOrdinaryRaw
    (pair : Tag73OrdinarySamplerSkeleton ×
      (Fin tag73LimbCount → M31Value)) : SuccessfulTag73RawStream :=
  successfulOrdinaryRawFactorization.symm pair

theorem combine_split_successful_ordinary_raw
    (raw : SuccessfulTag73RawStream) :
    combineSuccessfulOrdinaryRaw (splitSuccessfulOrdinaryRaw raw) = raw := by
  exact successfulOrdinaryRawFactorization.symm_apply_apply raw

theorem split_combine_successful_ordinary_raw
    (pair : Tag73OrdinarySamplerSkeleton ×
      (Fin tag73LimbCount → M31Value)) :
    splitSuccessfulOrdinaryRaw (combineSuccessfulOrdinaryRaw pair) = pair := by
  exact successfulOrdinaryRawFactorization.apply_symm_apply pair

@[simp] theorem successfulOrdinaryRawFactorization_values
    (raw : SuccessfulTag73RawStream) :
    (successfulOrdinaryRawFactorization raw).2 = successfulTag73Values raw := by
  rfl

abbrev Tag73OuterSamplerSkeleton := Fin 3 → Tag73OrdinarySamplerSkeleton

instance : Nonempty Tag73OuterSamplerSkeleton := inferInstance

def splitSuccessfulOuterRaw
    (raw : Tag73SuccessfulOrdinaryRawAttempts) :
    Tag73OuterSamplerSkeleton × Tag73NonzeroAttemptValues :=
  (fun attempt => (successfulOrdinaryRawFactorization (raw attempt)).1,
   fun attempt => tag73FourLimbsToExact
     (successfulOrdinaryRawFactorization (raw attempt)).2)

def combineSuccessfulOuterRaw
    (pair : Tag73OuterSamplerSkeleton × Tag73NonzeroAttemptValues) :
    Tag73SuccessfulOrdinaryRawAttempts :=
  fun attempt => successfulOrdinaryRawFactorization.symm
    (pair.1 attempt, tag73FourLimbsToExact.symm (pair.2 attempt))

theorem combine_split_successful_outer_raw
    (raw : Tag73SuccessfulOrdinaryRawAttempts) :
    combineSuccessfulOuterRaw (splitSuccessfulOuterRaw raw) = raw := by
  funext attempt
  unfold combineSuccessfulOuterRaw splitSuccessfulOuterRaw
  change successfulOrdinaryRawFactorization.symm
      ((successfulOrdinaryRawFactorization (raw attempt)).1,
        tag73FourLimbsToExact.symm
          (tag73FourLimbsToExact
            (successfulOrdinaryRawFactorization (raw attempt)).2)) =
      raw attempt
  rw [tag73FourLimbsToExact.symm_apply_apply]
  exact successfulOrdinaryRawFactorization.symm_apply_apply (raw attempt)

theorem split_combine_successful_outer_raw
    (pair : Tag73OuterSamplerSkeleton × Tag73NonzeroAttemptValues) :
    splitSuccessfulOuterRaw (combineSuccessfulOuterRaw pair) = pair := by
  apply Prod.ext
  · funext attempt
    unfold splitSuccessfulOuterRaw combineSuccessfulOuterRaw
    simp
  · funext attempt
    unfold splitSuccessfulOuterRaw combineSuccessfulOuterRaw
    simp

/-- Exact product decomposition before imposing the outer nonzero-success
condition. -/
def successfulOuterRawFactorization :
    Tag73SuccessfulOrdinaryRawAttempts ≃
      Tag73OuterSamplerSkeleton × Tag73NonzeroAttemptValues where
  toFun := splitSuccessfulOuterRaw
  invFun := combineSuccessfulOuterRaw
  left_inv := combine_split_successful_outer_raw
  right_inv := split_combine_successful_outer_raw

@[simp] theorem splitSuccessfulOuterRaw_values
    (raw : Tag73SuccessfulOrdinaryRawAttempts) :
    (splitSuccessfulOuterRaw raw).2 = successfulRawAttemptExactValues raw := by
  rfl

def splitSuccessfulRawNonzero
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    Tag73OuterSamplerSkeleton × SuccessfulTag73NonzeroAttempts :=
  ((splitSuccessfulOuterRaw raw.1).1,
    ⟨(splitSuccessfulOuterRaw raw.1).2, by
      rw [splitSuccessfulOuterRaw_values]
      exact raw.2⟩)

def combineSuccessfulRawNonzero
    (pair : Tag73OuterSamplerSkeleton ×
      SuccessfulTag73NonzeroAttempts) : SuccessfulTag73RawNonzeroAttempts := by
  let raw := combineSuccessfulOuterRaw (pair.1, pair.2.1)
  refine ⟨raw, ?_⟩
  unfold Tag73SuccessfulRawNonzero
  have valuesExact : successfulRawAttemptExactValues raw = pair.2.1 := by
    change (splitSuccessfulOuterRaw raw).2 = pair.2.1
    rw [show raw = combineSuccessfulOuterRaw (pair.1, pair.2.1) by rfl,
      split_combine_successful_outer_raw]
  rw [valuesExact]
  exact pair.2.2

theorem combine_split_successful_raw_nonzero
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    combineSuccessfulRawNonzero (splitSuccessfulRawNonzero raw) = raw := by
  apply Subtype.ext
  unfold combineSuccessfulRawNonzero splitSuccessfulRawNonzero
  exact combine_split_successful_outer_raw raw.1

theorem split_combine_successful_raw_nonzero
    (pair : Tag73OuterSamplerSkeleton × SuccessfulTag73NonzeroAttempts) :
    splitSuccessfulRawNonzero (combineSuccessfulRawNonzero pair) = pair := by
  apply Prod.ext
  · change (splitSuccessfulOuterRaw
      (combineSuccessfulOuterRaw (pair.1, pair.2.1))).1 = pair.1
    rw [split_combine_successful_outer_raw]
  · apply Subtype.ext
    change (splitSuccessfulOuterRaw
      (combineSuccessfulOuterRaw (pair.1, pair.2.1))).2 = pair.2.1
    rw [split_combine_successful_outer_raw]

/-- Strong deployed-sampler factorization: all path/nuisance data is an
independent product component, while the second component is precisely the
three-attempt successful value experiment already proved uniform. -/
def successfulRawNonzeroFactorization :
    SuccessfulTag73RawNonzeroAttempts ≃
      Tag73OuterSamplerSkeleton × SuccessfulTag73NonzeroAttempts where
  toFun := splitSuccessfulRawNonzero
  invFun := combineSuccessfulRawNonzero
  left_inv := combine_split_successful_raw_nonzero
  right_inv := split_combine_successful_raw_nonzero

@[simp] theorem successfulRawNonzeroFactorization_value
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    successfulTag73NonzeroValue
        (successfulRawNonzeroFactorization raw).2 =
      successfulRawNonzeroValue raw := by
  rfl

end


#print axioms successfulOrdinaryRawFactorization
#print axioms successfulOuterRawFactorization
#print axioms successfulRawNonzeroFactorization
#print axioms successfulRawNonzeroFactorization_value

end AspisK1.V7Tag73RawNonzeroSamplerFactorization
