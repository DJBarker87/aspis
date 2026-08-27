import AspisFormal.K1.V7Tag73RawNonzeroSamplerLaw
import AspisFormal.K1.V7Tag73TranscriptSchedule

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
open AspisK1.V7Tag73TranscriptSchedule

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

abbrev Tag73OrdinaryAttemptSkeletons := Fin 3 → Tag73OrdinarySamplerSkeleton

instance : Nonempty Tag73OrdinaryAttemptSkeletons := inferInstance

def splitSuccessfulOuterRaw
    (raw : Tag73SuccessfulOrdinaryRawAttempts) :
    Tag73OrdinaryAttemptSkeletons × Tag73NonzeroAttemptValues :=
  (fun attempt => (successfulOrdinaryRawFactorization (raw attempt)).1,
   fun attempt => tag73FourLimbsToExact
     (successfulOrdinaryRawFactorization (raw attempt)).2)

def combineSuccessfulOuterRaw
    (pair : Tag73OrdinaryAttemptSkeletons × Tag73NonzeroAttemptValues) :
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
    (pair : Tag73OrdinaryAttemptSkeletons × Tag73NonzeroAttemptValues) :
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
      Tag73OrdinaryAttemptSkeletons × Tag73NonzeroAttemptValues where
  toFun := splitSuccessfulOuterRaw
  invFun := combineSuccessfulOuterRaw
  left_inv := combine_split_successful_outer_raw
  right_inv := split_combine_successful_outer_raw

@[simp] theorem splitSuccessfulOuterRaw_values
    (raw : Tag73SuccessfulOrdinaryRawAttempts) :
    (splitSuccessfulOuterRaw raw).2 = successfulRawAttemptExactValues raw := by
  rfl

/-- Canonical fibre retaining the complete outer-attempt value pattern while
relabeling only the returned nonzero value to one.  Thus the outer stopping
position, preceding zeros, and unused later values remain nuisance data. -/
abbrev Tag73NonzeroValueSkeleton :=
  {attempts : SuccessfulTag73NonzeroAttempts //
    successfulTag73NonzeroValue attempts = ⟨1, one_ne_zero⟩}

instance : Nonempty Tag73NonzeroValueSkeleton := by
  let sampleAttempts := successfulTag73NonzeroAttemptsExample
  exact ⟨(successfulTag73NonzeroValueFibreEquiv
    (successfulTag73NonzeroValue sampleAttempts) ⟨1, one_ne_zero⟩)
      ⟨sampleAttempts, rfl⟩⟩

/-- Exact decomposition of the complete successful outer value vector into
all non-returned nuisance values and the returned uniform nonzero value. -/
def successfulNonzeroValueFactorization :
    SuccessfulTag73NonzeroAttempts ≃
      Tag73NonzeroValueSkeleton × NonzeroQM31Exact :=
  (Equiv.sigmaFiberEquiv successfulTag73NonzeroValue).symm |>.trans
    (Equiv.sigmaCongrRight fun value =>
      successfulTag73NonzeroValueFibreEquiv value ⟨1, one_ne_zero⟩) |>.trans
    (Equiv.sigmaEquivProd NonzeroQM31Exact Tag73NonzeroValueSkeleton) |>.trans
    (Equiv.prodComm _ _)

/-- Complete nuisance for the squeeze-output-word marginal: raw limb stopping
paths plus the outer nonzero-attempt pattern and every non-returned value.
This type deliberately does not include the independent duplex-advance
answers; actual future-response causality uses
`Tag73CompleteSamplerSkeleton` below. -/
abbrev Tag73OuterSamplerSkeleton :=
  Tag73OrdinaryAttemptSkeletons × Tag73NonzeroValueSkeleton

instance : Nonempty Tag73OuterSamplerSkeleton := inferInstance

private def splitRawToOrdinaryAndValues
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    Tag73OrdinaryAttemptSkeletons × SuccessfulTag73NonzeroAttempts :=
  ((splitSuccessfulOuterRaw raw.1).1,
    ⟨(splitSuccessfulOuterRaw raw.1).2, by
      rw [splitSuccessfulOuterRaw_values]
      exact raw.2⟩)

private def combineRawFromOrdinaryAndValues
    (pair : Tag73OrdinaryAttemptSkeletons ×
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

private theorem combine_split_raw_to_ordinary_and_values
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    combineRawFromOrdinaryAndValues (splitRawToOrdinaryAndValues raw) = raw := by
  apply Subtype.ext
  unfold combineRawFromOrdinaryAndValues splitRawToOrdinaryAndValues
  exact combine_split_successful_outer_raw raw.1

private theorem split_combine_raw_from_ordinary_and_values
    (pair : Tag73OrdinaryAttemptSkeletons ×
      SuccessfulTag73NonzeroAttempts) :
    splitRawToOrdinaryAndValues (combineRawFromOrdinaryAndValues pair) = pair := by
  apply Prod.ext
  · change (splitSuccessfulOuterRaw
      (combineSuccessfulOuterRaw (pair.1, pair.2.1))).1 = pair.1
    rw [split_combine_successful_outer_raw]
  · apply Subtype.ext
    change (splitSuccessfulOuterRaw
      (combineSuccessfulOuterRaw (pair.1, pair.2.1))).2 = pair.2.1
    rw [split_combine_successful_outer_raw]

private def rawOrdinaryAndValuesFactorization :
    SuccessfulTag73RawNonzeroAttempts ≃
      Tag73OrdinaryAttemptSkeletons × SuccessfulTag73NonzeroAttempts where
  toFun := splitRawToOrdinaryAndValues
  invFun := combineRawFromOrdinaryAndValues
  left_inv := combine_split_raw_to_ordinary_and_values
  right_inv := split_combine_raw_from_ordinary_and_values

/-- Strong deployed-sampler factorization: every executed-path and unused
coordinate is in the first component; the second component is only the
returned nonzero QM31 value. -/
def successfulRawNonzeroFactorization :
    SuccessfulTag73RawNonzeroAttempts ≃
      Tag73OuterSamplerSkeleton × NonzeroQM31Exact :=
  rawOrdinaryAndValuesFactorization |>.trans
    (Equiv.prodCongr (Equiv.refl Tag73OrdinaryAttemptSkeletons)
      successfulNonzeroValueFactorization) |>.trans
    { toFun := fun pair => ((pair.1, pair.2.1), pair.2.2)
      invFun := fun pair => (pair.1.1, pair.1.2, pair.2)
      left_inv := by intro pair; rfl
      right_inv := by intro pair; rfl }

@[simp] theorem successfulRawNonzeroFactorization_value
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    (successfulRawNonzeroFactorization raw).2 = successfulRawNonzeroValue raw := by
  rfl

/-! ## Complete duplex nuisance

Each 256-bit squeeze output has a second, domain-separated SHA-256 answer
which advances the transcript state.  The word stream above contains the
complete squeeze outputs, but not those independent advance answers.  A
future prover can depend on the resulting transcript state, so the causal
sample space must retain all four possible advance answers for each of the
three possible outer calls.  Unexecuted suffix coordinates are independent
ghost randomness used only to obtain a fixed finite product space.
-/

abbrev Tag73AdvanceDigestGhosts := Fin 3 → Fin 4 → Digest256

instance : Nonempty Tag73AdvanceDigestGhosts := inferInstance

/-- Successful fixed-size sampler data including both squeeze-output words
and every corresponding independent duplex-advance answer. -/
abbrev SuccessfulTag73DuplexNonzeroAttempts :=
  SuccessfulTag73RawNonzeroAttempts × Tag73AdvanceDigestGhosts

/-- The complete pre-value nuisance component used by a causal restored
prover. -/
abbrev Tag73CompleteSamplerSkeleton :=
  Tag73OuterSamplerSkeleton × Tag73AdvanceDigestGhosts

instance : Nonempty Tag73CompleteSamplerSkeleton := inferInstance

def successfulDuplexNonzeroValue
    (sample : SuccessfulTag73DuplexNonzeroAttempts) : NonzeroQM31Exact :=
  successfulRawNonzeroValue sample.1

/-- Exact factorization retaining independent duplex-advance answers in the
nuisance component while isolating only the returned nonzero gamma. -/
def successfulDuplexNonzeroFactorization :
    SuccessfulTag73DuplexNonzeroAttempts ≃
      Tag73CompleteSamplerSkeleton × NonzeroQM31Exact :=
  (Equiv.prodCongr successfulRawNonzeroFactorization
      (Equiv.refl Tag73AdvanceDigestGhosts)).trans
    { toFun := fun pair => ((pair.1.1, pair.2), pair.1.2)
      invFun := fun pair => ((pair.1.1, pair.2), pair.1.2)
      left_inv := by intro pair; rfl
      right_inv := by intro pair; rfl }

@[simp] theorem successfulDuplexNonzeroFactorization_value
    (sample : SuccessfulTag73DuplexNonzeroAttempts) :
    (successfulDuplexNonzeroFactorization sample).2 =
      successfulDuplexNonzeroValue sample := by
  rfl

end


#print axioms successfulOrdinaryRawFactorization
#print axioms successfulOuterRawFactorization
#print axioms successfulNonzeroValueFactorization
#print axioms successfulRawNonzeroFactorization
#print axioms successfulRawNonzeroFactorization_value
#print axioms successfulDuplexNonzeroFactorization
#print axioms successfulDuplexNonzeroFactorization_value

end AspisK1.V7Tag73RawNonzeroSamplerFactorization
