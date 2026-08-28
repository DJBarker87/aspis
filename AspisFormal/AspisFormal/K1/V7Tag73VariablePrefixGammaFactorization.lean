import AspisFormal.K1.V7Tag73VariablePrefixGammaSampler
import AspisFormal.K1.V7Tag73EightRetryDecoderBridge

/-!
# Exact finite coordinates for the variable-prefix Tag-73 gamma sampler

This file connects four concrete SHA-256 output blocks to the existing
thirty-two-word ordinary-sampler experiment.  The connection is literal:
the block and word coordinates are reindexed by an equivalence and the
deployed decoder is proved to commute with the raw stopping machine.

The outer nonzero sampler cannot be split into three fixed four-block
windows.  Production begins the next ordinary attempt after the preceding
attempt's actual `blocksUsed`.  The block-level results below are the local
ingredient required by the adaptive reindexing of the twelve-block tape.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73VariablePrefixGammaFactorization

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73EightRetryDecoderBridge
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

abbrev FourGammaBlocks := Fin 4 → Digest256

def fourBlockWordIndexEquiv :
    Fin 4 × Fin 8 ≃ Fin tag73MaximumRawWordCount :=
  finProdFinEquiv.trans (finCongr (by
    norm_num [tag73MaximumRawWordCount, tag73LimbCount,
      tag73LimbRetryLimit]))

/-- Four chronological digest blocks are exactly the thirty-two mathematical
`u32` words used by one maximum-size ordinary Tag-73 attempt. -/
def fourGammaBlocksRawEquiv : FourGammaBlocks ≃ Tag73RawStream :=
  { toFun := fun blocks =>
      (Equiv.vectorEquivFin RawWord tag73MaximumRawWordCount).symm
        fun draw =>
          let coordinate := fourBlockWordIndexEquiv.symm draw
          digestWordsEquiv (blocks coordinate.1) coordinate.2
    invFun := fun raw block =>
      digestWordsEquiv.symm fun word =>
        (Equiv.vectorEquivFin RawWord tag73MaximumRawWordCount raw)
          (fourBlockWordIndexEquiv (block, word))
    left_inv := by
      intro blocks
      funext block
      apply digestWordsEquiv.injective
      funext word
      simp [fourBlockWordIndexEquiv]
    right_inv := by
      intro raw
      apply (Equiv.vectorEquivFin RawWord tag73MaximumRawWordCount).injective
      funext draw
      simp [fourBlockWordIndexEquiv] }

@[simp] theorem fourGammaBlocksRawEquiv_word
    (blocks : FourGammaBlocks) (block : Fin 4) (word : Fin 8) :
    (Equiv.vectorEquivFin RawWord tag73MaximumRawWordCount
        (fourGammaBlocksRawEquiv blocks))
          (fourBlockWordIndexEquiv (block, word)) =
      digestWordsEquiv (blocks block) word := by
  simp [fourGammaBlocksRawEquiv, fourBlockWordIndexEquiv]

@[simp] theorem fourGammaBlocksRawEquiv_word_value
    (blocks : FourGammaBlocks) (block : Fin 4) (word : Fin 8) :
    (((Equiv.vectorEquivFin RawWord tag73MaximumRawWordCount
        (fourGammaBlocksRawEquiv blocks))
          (fourBlockWordIndexEquiv (block, word)) : RawWord) : Nat) =
      littleEndianWord (blocks block) word := by
  rw [fourGammaBlocksRawEquiv_word]
  exact digestWordsEquiv_apply_val (blocks block) word

/-! ## Routed successful branches

The adaptive flat-tape reindex has two logically separate parts.  This
section proves the value-factorization part completely.  Only attempts which
the stopping execution reaches are required to succeed.  Every later
four-block window is an arbitrary raw stream and is retained verbatim as
nuisance data.

The still-separate flat/routed equivalence must concatenate the actually
consumed heads of the reached windows and move their padding, together with
all unreached windows, into the unread suffix.  Nothing below assumes that
that suffix decodes. -/

def successfulOrdinaryExactValue
    (raw : SuccessfulTag73RawStream) : QM31Exact :=
  tag73FourLimbsToExact (successfulTag73Values raw)

/-- One successful ordinary call split into its complete stopping-path
skeleton and its exact four-limb value. -/
def successfulOrdinaryExactFactorization :
    SuccessfulTag73RawStream ≃
      Tag73OrdinarySamplerSkeleton × QM31Exact :=
  successfulOrdinaryRawFactorization.trans
    (Equiv.prodCongr (Equiv.refl Tag73OrdinarySamplerSkeleton)
      tag73FourLimbsToExact)

@[simp] theorem successfulOrdinaryExactFactorization_value
    (raw : SuccessfulTag73RawStream) :
    (successfulOrdinaryExactFactorization raw).2 =
      successfulOrdinaryExactValue raw := by
  rfl

abbrev SuccessfulZeroGammaOrdinaryRaw :=
  {raw : SuccessfulTag73RawStream // successfulOrdinaryExactValue raw = 0}

abbrev SuccessfulNonzeroGammaOrdinaryRaw :=
  {raw : SuccessfulTag73RawStream // successfulOrdinaryExactValue raw ≠ 0}

instance : Nonempty SuccessfulZeroGammaOrdinaryRaw :=
  ⟨successfulZeroRawStream⟩

instance : Nonempty SuccessfulNonzeroGammaOrdinaryRaw :=
  ⟨⟨successfulOneRawStream.1, by
    rw [successfulOrdinaryExactValue, successfulOneRawStream.2]
    exact one_ne_zero⟩⟩

/-- A reached zero-valued ordinary attempt has no exposed value coordinate;
its entire remaining information is its ordinary stopping-path skeleton. -/
def successfulZeroGammaOrdinaryFactorization :
    SuccessfulZeroGammaOrdinaryRaw ≃ Tag73OrdinarySamplerSkeleton where
  toFun raw := (successfulOrdinaryExactFactorization raw.1).1
  invFun skeleton :=
    ⟨successfulOrdinaryExactFactorization.symm (skeleton, 0), by
      rw [← successfulOrdinaryExactFactorization_value]
      simp⟩
  left_inv raw := by
    apply Subtype.ext
    have secondExact :
        (successfulOrdinaryExactFactorization raw.1).2 = 0 := by
      rw [successfulOrdinaryExactFactorization_value]
      exact raw.2
    have pairExact :
        ((successfulOrdinaryExactFactorization raw.1).1, (0 : QM31Exact)) =
          successfulOrdinaryExactFactorization raw.1 := by
      apply Prod.ext
      · rfl
      · exact secondExact.symm
    change successfulOrdinaryExactFactorization.symm
        ((successfulOrdinaryExactFactorization raw.1).1, 0) = raw.1
    rw [pairExact]
    exact successfulOrdinaryExactFactorization.symm_apply_apply raw.1
  right_inv skeleton := by
    have exactPair := successfulOrdinaryExactFactorization.apply_symm_apply
      (skeleton, (0 : QM31Exact))
    exact congrArg Prod.fst exactPair

/-- A reached nonzero ordinary attempt factors into its full nuisance
skeleton and exactly the returned nonzero QM31 value. -/
def successfulNonzeroGammaOrdinaryFactorization :
    SuccessfulNonzeroGammaOrdinaryRaw ≃
      Tag73OrdinarySamplerSkeleton × NonzeroQM31Exact where
  toFun raw :=
    ((successfulOrdinaryExactFactorization raw.1).1,
      ⟨(successfulOrdinaryExactFactorization raw.1).2, by
        rw [successfulOrdinaryExactFactorization_value]
        exact raw.2⟩)
  invFun pair :=
    ⟨successfulOrdinaryExactFactorization.symm (pair.1, pair.2.1), by
      rw [← successfulOrdinaryExactFactorization_value]
      simpa using pair.2.2⟩
  left_inv raw := by
    apply Subtype.ext
    exact successfulOrdinaryExactFactorization.symm_apply_apply raw.1
  right_inv pair := by
    apply Prod.ext
    · change (successfulOrdinaryExactFactorization
          (successfulOrdinaryExactFactorization.symm
            (pair.1, pair.2.1))).1 = pair.1
      have exactPair := successfulOrdinaryExactFactorization.apply_symm_apply
        (pair.1, pair.2.1)
      exact congrArg Prod.fst exactPair
    · apply Subtype.ext
      change (successfulOrdinaryExactFactorization
          (successfulOrdinaryExactFactorization.symm
            (pair.1, pair.2.1))).2 = pair.2.1
      have exactPair := successfulOrdinaryExactFactorization.apply_symm_apply
        (pair.1, pair.2.1)
      exact congrArg Prod.snd exactPair

noncomputable instance : Fintype SuccessfulZeroGammaOrdinaryRaw :=
  Fintype.ofEquiv Tag73OrdinarySamplerSkeleton
    successfulZeroGammaOrdinaryFactorization.symm

noncomputable instance : Fintype SuccessfulNonzeroGammaOrdinaryRaw :=
  Fintype.ofEquiv
    (Tag73OrdinarySamplerSkeleton × NonzeroQM31Exact)
    successfulNonzeroGammaOrdinaryFactorization.symm

/-- Correct routed successful sampler.  The constructors record the literal
outer stopping branch.  Calls after that branch are arbitrary raw streams,
not successful-call subtypes. -/
inductive RoutedSuccessfulGammaTape where
  | stop0
      (current : SuccessfulNonzeroGammaOrdinaryRaw)
      (later : Fin 2 → Tag73RawStream)
      (advance : Tag73AdvanceDigestGhosts)
  | stop1
      (before : SuccessfulZeroGammaOrdinaryRaw)
      (current : SuccessfulNonzeroGammaOrdinaryRaw)
      (later : Tag73RawStream)
      (advance : Tag73AdvanceDigestGhosts)
  | stop2
      (first second : SuccessfulZeroGammaOrdinaryRaw)
      (current : SuccessfulNonzeroGammaOrdinaryRaw)
      (advance : Tag73AdvanceDigestGhosts)

instance : Nonempty RoutedSuccessfulGammaTape :=
  ⟨RoutedSuccessfulGammaTape.stop0
    (Classical.choice
      (inferInstance : Nonempty SuccessfulNonzeroGammaOrdinaryRaw))
    (fun _ => acceptedTag73RawStream)
      (fun _ _ => zeroBytes 32)⟩

/-- Complete nuisance for the routed variable-prefix experiment.  Reached
attempts retain ordinary stopping skeletons; unreached attempts retain their
arbitrary raw words; every possible advance answer remains fixed. -/
inductive VariableGammaCompleteSkeleton where
  | stop0
      (current : Tag73OrdinarySamplerSkeleton)
      (later : Fin 2 → Tag73RawStream)
      (advance : Tag73AdvanceDigestGhosts)
  | stop1
      (before current : Tag73OrdinarySamplerSkeleton)
      (later : Tag73RawStream)
      (advance : Tag73AdvanceDigestGhosts)
  | stop2
      (first second current : Tag73OrdinarySamplerSkeleton)
      (advance : Tag73AdvanceDigestGhosts)

instance : Nonempty VariableGammaCompleteSkeleton :=
  ⟨VariableGammaCompleteSkeleton.stop0
    (Classical.choice
      (inferInstance : Nonempty Tag73OrdinarySamplerSkeleton))
    (fun _ => acceptedTag73RawStream)
      (fun _ _ => zeroBytes 32)⟩

abbrev RoutedSuccessfulGammaData :=
  (SuccessfulNonzeroGammaOrdinaryRaw ×
      (Fin 2 → Tag73RawStream) × Tag73AdvanceDigestGhosts) ⊕
    ((SuccessfulZeroGammaOrdinaryRaw ×
        SuccessfulNonzeroGammaOrdinaryRaw × Tag73RawStream ×
        Tag73AdvanceDigestGhosts) ⊕
      (SuccessfulZeroGammaOrdinaryRaw ×
        SuccessfulZeroGammaOrdinaryRaw ×
        SuccessfulNonzeroGammaOrdinaryRaw × Tag73AdvanceDigestGhosts))

/-- Finite tagged-product presentation of the three routed stopping
branches. -/
def routedSuccessfulGammaDataEquiv :
    RoutedSuccessfulGammaTape ≃ RoutedSuccessfulGammaData where
  toFun sample := match sample with
    | .stop0 current later advance => .inl (current, later, advance)
    | .stop1 before current later advance =>
        .inr (.inl (before, current, later, advance))
    | .stop2 first second current advance =>
        .inr (.inr (first, second, current, advance))
  invFun data := match data with
    | .inl data => .stop0 data.1 data.2.1 data.2.2
    | .inr (.inl data) =>
        .stop1 data.1 data.2.1 data.2.2.1 data.2.2.2
    | .inr (.inr data) =>
        .stop2 data.1 data.2.1 data.2.2.1 data.2.2.2
  left_inv sample := by cases sample <;> rfl
  right_inv data := by rcases data with data | data <;>
    rcases data with data | data <;> rfl

noncomputable instance : Fintype RoutedSuccessfulGammaData :=
  Fintype.ofFinite _

noncomputable instance : Fintype RoutedSuccessfulGammaTape :=
  Fintype.ofEquiv RoutedSuccessfulGammaData
    routedSuccessfulGammaDataEquiv.symm

abbrev VariableGammaCompleteSkeletonData :=
  (Tag73OrdinarySamplerSkeleton ×
      (Fin 2 → Tag73RawStream) × Tag73AdvanceDigestGhosts) ⊕
    ((Tag73OrdinarySamplerSkeleton × Tag73OrdinarySamplerSkeleton ×
        Tag73RawStream × Tag73AdvanceDigestGhosts) ⊕
      (Tag73OrdinarySamplerSkeleton × Tag73OrdinarySamplerSkeleton ×
        Tag73OrdinarySamplerSkeleton × Tag73AdvanceDigestGhosts))

def variableGammaCompleteSkeletonDataEquiv :
    VariableGammaCompleteSkeleton ≃ VariableGammaCompleteSkeletonData where
  toFun skeleton := match skeleton with
    | .stop0 current later advance => .inl (current, later, advance)
    | .stop1 before current later advance =>
        .inr (.inl (before, current, later, advance))
    | .stop2 first second current advance =>
        .inr (.inr (first, second, current, advance))
  invFun data := match data with
    | .inl data => .stop0 data.1 data.2.1 data.2.2
    | .inr (.inl data) =>
        .stop1 data.1 data.2.1 data.2.2.1 data.2.2.2
    | .inr (.inr data) =>
        .stop2 data.1 data.2.1 data.2.2.1 data.2.2.2
  left_inv skeleton := by cases skeleton <;> rfl
  right_inv data := by rcases data with data | data <;>
    rcases data with data | data <;> rfl

def routedSuccessfulGammaValue
    (sample : RoutedSuccessfulGammaTape) : NonzeroQM31Exact :=
  match sample with
  | .stop0 current _ _ =>
      (successfulNonzeroGammaOrdinaryFactorization current).2
  | .stop1 _ current _ _ =>
      (successfulNonzeroGammaOrdinaryFactorization current).2
  | .stop2 _ _ current _ =>
      (successfulNonzeroGammaOrdinaryFactorization current).2

/-- Exact factorization of all three genuine stopping branches.  In
particular, the value coordinate is independent of the branch, every reached
zero path, every unread raw word, and all duplex-advance answers. -/
def routedSuccessfulGammaFactorization :
    RoutedSuccessfulGammaTape ≃
      VariableGammaCompleteSkeleton × NonzeroQM31Exact where
  toFun sample := match sample with
    | .stop0 current later advance =>
        (.stop0
          (successfulNonzeroGammaOrdinaryFactorization current).1
          later advance,
          (successfulNonzeroGammaOrdinaryFactorization current).2)
    | .stop1 before current later advance =>
        (.stop1
          (successfulZeroGammaOrdinaryFactorization before)
          (successfulNonzeroGammaOrdinaryFactorization current).1
          later advance,
          (successfulNonzeroGammaOrdinaryFactorization current).2)
    | .stop2 first second current advance =>
        (.stop2
          (successfulZeroGammaOrdinaryFactorization first)
          (successfulZeroGammaOrdinaryFactorization second)
          (successfulNonzeroGammaOrdinaryFactorization current).1
          advance,
          (successfulNonzeroGammaOrdinaryFactorization current).2)
  invFun pair := match pair.1 with
    | .stop0 current later advance =>
        .stop0
          (successfulNonzeroGammaOrdinaryFactorization.symm
            (current, pair.2)) later advance
    | .stop1 before current later advance =>
        .stop1
          (successfulZeroGammaOrdinaryFactorization.symm before)
          (successfulNonzeroGammaOrdinaryFactorization.symm
            (current, pair.2)) later advance
    | .stop2 first second current advance =>
        .stop2
          (successfulZeroGammaOrdinaryFactorization.symm first)
          (successfulZeroGammaOrdinaryFactorization.symm second)
          (successfulNonzeroGammaOrdinaryFactorization.symm
            (current, pair.2)) advance
  left_inv sample := by
    cases sample with
    | stop0 current later advance =>
        change RoutedSuccessfulGammaTape.stop0
          (successfulNonzeroGammaOrdinaryFactorization.symm
            (successfulNonzeroGammaOrdinaryFactorization current))
          later advance = RoutedSuccessfulGammaTape.stop0 current later advance
        rw [Equiv.symm_apply_apply]
    | stop1 before current later advance =>
        change RoutedSuccessfulGammaTape.stop1
          (successfulZeroGammaOrdinaryFactorization.symm
            (successfulZeroGammaOrdinaryFactorization before))
          (successfulNonzeroGammaOrdinaryFactorization.symm
            (successfulNonzeroGammaOrdinaryFactorization current))
          later advance =
            RoutedSuccessfulGammaTape.stop1 before current later advance
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    | stop2 first second current advance =>
        change RoutedSuccessfulGammaTape.stop2
          (successfulZeroGammaOrdinaryFactorization.symm
            (successfulZeroGammaOrdinaryFactorization first))
          (successfulZeroGammaOrdinaryFactorization.symm
            (successfulZeroGammaOrdinaryFactorization second))
          (successfulNonzeroGammaOrdinaryFactorization.symm
            (successfulNonzeroGammaOrdinaryFactorization current))
          advance =
            RoutedSuccessfulGammaTape.stop2 first second current advance
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
  right_inv pair := by
    rcases pair with ⟨skeleton, value⟩
    cases skeleton with
    | stop0 current later advance =>
        change
          (VariableGammaCompleteSkeleton.stop0
              (successfulNonzeroGammaOrdinaryFactorization
                (successfulNonzeroGammaOrdinaryFactorization.symm
                  (current, value))).1 later advance,
            (successfulNonzeroGammaOrdinaryFactorization
              (successfulNonzeroGammaOrdinaryFactorization.symm
                (current, value))).2) =
            (VariableGammaCompleteSkeleton.stop0 current later advance, value)
        rw [Equiv.apply_symm_apply]
    | stop1 before current later advance =>
        change
          (VariableGammaCompleteSkeleton.stop1
              (successfulZeroGammaOrdinaryFactorization
                (successfulZeroGammaOrdinaryFactorization.symm before))
              (successfulNonzeroGammaOrdinaryFactorization
                (successfulNonzeroGammaOrdinaryFactorization.symm
                  (current, value))).1 later advance,
            (successfulNonzeroGammaOrdinaryFactorization
              (successfulNonzeroGammaOrdinaryFactorization.symm
                (current, value))).2) =
            (VariableGammaCompleteSkeleton.stop1 before current later advance,
              value)
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    | stop2 first second current advance =>
        change
          (VariableGammaCompleteSkeleton.stop2
              (successfulZeroGammaOrdinaryFactorization
                (successfulZeroGammaOrdinaryFactorization.symm first))
              (successfulZeroGammaOrdinaryFactorization
                (successfulZeroGammaOrdinaryFactorization.symm second))
              (successfulNonzeroGammaOrdinaryFactorization
                (successfulNonzeroGammaOrdinaryFactorization.symm
                  (current, value))).1 advance,
            (successfulNonzeroGammaOrdinaryFactorization
              (successfulNonzeroGammaOrdinaryFactorization.symm
                (current, value))).2) =
            (VariableGammaCompleteSkeleton.stop2 first second current advance,
              value)
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]

noncomputable instance : Fintype VariableGammaCompleteSkeleton := by
  let value : NonzeroQM31Exact := ⟨1, one_ne_zero⟩
  let encode : VariableGammaCompleteSkeleton → RoutedSuccessfulGammaTape :=
    fun skeleton => routedSuccessfulGammaFactorization.symm (skeleton, value)
  have injective : Function.Injective encode := by
    intro left right equal
    have mapped := congrArg routedSuccessfulGammaFactorization equal
    simpa [encode] using congrArg Prod.fst mapped
  letI : Finite VariableGammaCompleteSkeleton :=
    Finite.of_injective encode injective
  exact Fintype.ofFinite _

@[simp] theorem routedSuccessfulGammaFactorization_value
    (sample : RoutedSuccessfulGammaTape) :
    (routedSuccessfulGammaFactorization sample).2 =
      routedSuccessfulGammaValue sample := by
  cases sample <;> rfl

#print axioms fourGammaBlocksRawEquiv_word
#print axioms fourGammaBlocksRawEquiv_word_value
#print axioms successfulOrdinaryExactFactorization_value
#print axioms successfulZeroGammaOrdinaryFactorization
#print axioms successfulNonzeroGammaOrdinaryFactorization
#print axioms routedSuccessfulGammaDataEquiv
#print axioms variableGammaCompleteSkeletonDataEquiv
#print axioms routedSuccessfulGammaFactorization
#print axioms routedSuccessfulGammaFactorization_value

end


end AspisK1.V7Tag73VariablePrefixGammaFactorization
