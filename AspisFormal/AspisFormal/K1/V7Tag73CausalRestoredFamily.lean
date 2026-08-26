import AspisFormal.K1.V7Tag73CausalGammaProbability
import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier
import AspisFormal.K1.V7Tag73ParsedK13K14Classifier
import AspisFormal.K1.V7Tag73RestoredPointCompatibleK14

/-!
# Causal construction of the restoration-wide selected-chain family

The correlated width-29 theorem needs one response family fixed before the
batching challenge.  This module constructs that family from a dependent
provider of actual accepted K1.4 branches.  A provider may depend on the
pre-gamma hidden state and on the complete sampler skeleton, but its branch
function is fixed before its `gamma` argument is evaluated.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalRestoredFamily

open MeasureTheory
open AspisK1.V7Tag73CausalGammaProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- The exact pre-K1.4 information carried by one restored continuation.
This is deliberately weaker than `RestoredK14Branch`: a width-29
decomposition failure still has a canonical selected K1.3 chain and must
therefore remain present in the response family used to bound K1.4. -/
structure RestoredSelectedBranch
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) where
  disclosedFinal : FinalMessage QM31Exact
  schedule : ExactSchedule
  selected : ExactCandidatePair
  selectedExact :
    selectCandidateChain
        (decoder.decodeBoth
          (extractedIdealTranscript words gamma disclosedFinal).initial
          (foldedReceived schedule
            (extractedIdealTranscript words gamma disclosedFinal)))
      schedule disclosedFinal = some selected

/-- K1.3 acceptance always supplies the canonical selected chain, including
on the branch where K1.4 subsequently reports width-29 decomposition
failure. -/
theorem exactK13_has_selected_chain
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k13 : ExactK13Certificate decoder input k12) :
    ∃ selected,
      selectCandidateChain
          (decoder.decodeBoth
            (exactK13Transcript input k12).initial
            (foldedReceived (exactK13ParsedProof input).schedule
              (exactK13Transcript input k12)))
        (exactK13ParsedProof input).schedule
        (exactK13ParsedProof input).disclosedFinal = some selected := by
  obtain ⟨selected, selectedExact, _initial, _final, _fold, _terminal⟩ :=
    accepted_selects_one_consistent_chain
      (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
      (exactK13Transcript input k12) (exactK13ParsedProof input).queries
      decoder rfl rfl k13.accepts k13.noQueryFailure k13.noFoldFailure
      k13.noListCapFailure
  exact ⟨selected, selectedExact⟩

/-- Forget the later K1.4 result while retaining the selected K1.3 response
from the literal fixed execution. -/
noncomputable def restoredSelectedBranchOfExactK13
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k13 : ExactK13Certificate decoder input k12) :
    RestoredSelectedBranch decoder k12.words (exactK13ParsedProof input).gamma :=
  { disclosedFinal := (exactK13ParsedProof input).disclosedFinal
    schedule := (exactK13ParsedProof input).schedule
    selected := Classical.choose (exactK13_has_selected_chain k13)
    selectedExact := Classical.choose_spec (exactK13_has_selected_chain k13) }

theorem parsedK13_has_selected_chain
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {proof : Tag73K12ParsedProof}
    (k13 : ParsedK13Certificate decoder words proof) :
    ∃ selected,
      selectCandidateChain
          (decoder.decodeBoth
            (parsedK13Transcript words proof).initial
            (foldedReceived proof.schedule
              (parsedK13Transcript words proof)))
        proof.schedule proof.disclosedFinal = some selected := by
  obtain ⟨selected, selectedExact, _initial, _final, _fold, _terminal⟩ :=
    accepted_selects_one_consistent_chain proof.schedule
      (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
      proof.queries decoder rfl rfl k13.accepts k13.noQueryFailure
      k13.noFoldFailure k13.noListCapFailure
  exact ⟨selected, selectedExact⟩

/-- A parser-data K1.3 certificate, such as one obtained from a restored
accumulator node, supplies the same causal response-family branch. -/
noncomputable def restoredSelectedBranchOfParsedK13
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {proof : Tag73K12ParsedProof}
    (k13 : ParsedK13Certificate decoder words proof) :
    RestoredSelectedBranch decoder words proof.gamma :=
  { disclosedFinal := proof.disclosedFinal
    schedule := proof.schedule
    selected := Classical.choose (parsedK13_has_selected_chain k13)
    selectedExact := Classical.choose_spec (parsedK13_has_selected_chain k13) }

/-- A pre-gamma restoration client supplies at most one canonical selected
K1.3 branch per challenge.  Unavailable challenges are totalized by a real
fallback branch but have empty support in the resulting family. -/
structure RestoredSelectedBranchProvider
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  /-- Fixed pre-gamma values used only on unavailable branches, whose
  accepted strategy has empty support.  They intentionally carry no
  post-gamma certificate. -/
  defaultResponse : InitialMessage QM31Exact
  defaultDisclosedFinal : FinalMessage QM31Exact
  defaultSchedule : ExactSchedule
  defaultSelected : ExactCandidatePair
  branch : (gamma : QM31Exact) →
    Option (RestoredSelectedBranch decoder words gamma)

def selectedProviderAvailable
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredSelectedBranchProvider decoder words)
    (gamma : QM31Exact) : Prop :=
  (provider.branch gamma).isSome

/-- The exact accepted-family object required by the correlated width-29
theorem, now constructed already at K1.3 rather than assuming K1.4 success. -/
def restoredSelectedChainFamilyOfK13Provider
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredSelectedBranchProvider decoder words) :
    RestoredSelectedChainFamily decoder words where
  available := selectedProviderAvailable provider
  response := fun gamma =>
    match provider.branch gamma with
    | some branch => branch.selected.1
    | none => provider.defaultResponse
  disclosedFinal := fun gamma =>
    match provider.branch gamma with
    | some branch => branch.disclosedFinal
    | none => provider.defaultDisclosedFinal
  schedule := fun gamma =>
    match provider.branch gamma with
    | some branch => branch.schedule
    | none => provider.defaultSchedule
  selected := fun gamma =>
    match provider.branch gamma with
    | some branch => branch.selected
    | none => provider.defaultSelected
  responseAt := by
    intro gamma available
    cases branchEq : provider.branch gamma with
    | none => simp [selectedProviderAvailable, branchEq] at available
    | some branch => simp [branchEq]
  selectedExact := by
    intro gamma available
    cases branchEq : provider.branch gamma with
    | none => simp [selectedProviderAvailable, branchEq] at available
    | some branch => simpa [branchEq] using branch.selectedExact

theorem k13_family_selected_of_branch
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredSelectedBranchProvider decoder words)
    (gamma : QM31Exact)
    (branch : RestoredSelectedBranch decoder words gamma)
    (branchExact : provider.branch gamma = some branch) :
    (restoredSelectedChainFamilyOfK13Provider provider).available gamma ∧
      (restoredSelectedChainFamilyOfK13Provider provider).selected gamma =
        branch.selected := by
  constructor <;> simp [restoredSelectedChainFamilyOfK13Provider,
    selectedProviderAvailable, branchExact]

/-! ## Finite accumulator family -/

/-- Existentially packed parser-data branch used by the finite terminal
accumulator.  The challenge is stored together with the dependently typed
selected-chain certificate. -/
structure PackedRestoredSelectedBranch
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  gamma : QM31Exact
  branch : RestoredSelectedBranch decoder words gamma

noncomputable def firstRestoredSelectedBranch?
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords} :
    List (PackedRestoredSelectedBranch decoder words) →
      (gamma : QM31Exact) → Option (RestoredSelectedBranch decoder words gamma)
  | [], _gamma => none
  | packed :: rest, gamma =>
      if exact : packed.gamma = gamma then
        some (exact ▸ packed.branch)
      else
        firstRestoredSelectedBranch? rest gamma

/-- A nonempty finite list of certified restored K1.3 branches constructs a
totalized provider.  The distinguished root is inserted first, so its exact
selected chain wins even if another restored node happens to repeat gamma. -/
noncomputable def finiteK13Provider
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (root : PackedRestoredSelectedBranch decoder words)
    (restored : List (PackedRestoredSelectedBranch decoder words)) :
    RestoredSelectedBranchProvider decoder words where
  defaultResponse := defaultResponse
  defaultDisclosedFinal := defaultDisclosedFinal
  defaultSchedule := defaultSchedule
  defaultSelected := defaultSelected
  branch := firstRestoredSelectedBranch? (root :: restored)

@[simp] theorem finiteK13Provider_root_branch
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (root : PackedRestoredSelectedBranch decoder words)
    (restored : List (PackedRestoredSelectedBranch decoder words)) :
    (finiteK13Provider defaultResponse defaultDisclosedFinal defaultSchedule
      defaultSelected root restored).branch root.gamma = some root.branch := by
  simp [finiteK13Provider, firstRestoredSelectedBranch?]

theorem finite_k13_family_contains_exact_root
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (root : PackedRestoredSelectedBranch decoder words)
    (restored : List (PackedRestoredSelectedBranch decoder words)) :
    (restoredSelectedChainFamilyOfK13Provider
        (finiteK13Provider defaultResponse defaultDisclosedFinal defaultSchedule
          defaultSelected root restored)).available root.gamma ∧
      (restoredSelectedChainFamilyOfK13Provider
        (finiteK13Provider defaultResponse defaultDisclosedFinal defaultSchedule
          defaultSelected root restored)).selected root.gamma =
          root.branch.selected :=
  k13_family_selected_of_branch
    (finiteK13Provider defaultResponse defaultDisclosedFinal defaultSchedule
      defaultSelected root restored) root.gamma root.branch
    (finiteK13Provider_root_branch defaultResponse defaultDisclosedFinal
      defaultSchedule defaultSelected root restored)

noncomputable def causalK13ProviderGammaTarget
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (provider : Tag73OuterSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words)
    (skeleton : Tag73OuterSamplerSkeleton) : Finset QM31Exact :=
  acceptedRestoredPointConstrainedGammaSet decoder words point claims
    (restoredSelectedChainFamilyOfK13Provider (provider skeleton))

def causalK13ProviderRawGammaEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (provider : Tag73OuterSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words) :
    Set SuccessfulTag73RawNonzeroAttempts :=
  rawSkeletonDependentGammaEvent
    (causalK13ProviderGammaTarget point claims provider)

/-- The width-29 K1.4 bound uses the pre-K1.4 selected-chain family.  Thus a
branch where K1.3 succeeded but matching decomposition failed is included in
the challenged family rather than silently disappearing. -/
theorem no_k14_causal_k13_provider_raw_gamma_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (provider : Tag73OuterSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words)
    (noK14 : ∀ skeleton,
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder words point claims
        (restoredSelectedChainFamilyOfK13Provider (provider skeleton))) :
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).toOuterMeasure
        (causalK13ProviderRawGammaEvent point claims provider) ≤
      (AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply raw_skeleton_dependent_gamma_probability_le
  intro skeleton
  exact no_accepted_restored_point_compatible_k14_card_le decoder published
    words point claims
      (restoredSelectedChainFamilyOfK13Provider (provider skeleton))
      (noK14 skeleton)

/-- The exact information supplied by one restored branch after it has passed
K1.2--K1.4.  Its selected pair is not caller supplied: it is the pair carried
by the coherent extraction and certified by `combinedSelected`. -/
structure RestoredK14Branch
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) where
  disclosedFinal : FinalMessage QM31Exact
  schedule : ExactSchedule
  extraction : CoherentTraceExtraction decoder binding words gamma
    disclosedFinal schedule

/-- A restoration client fixes this provider before gamma.  `branch gamma`
is `some` exactly when the corresponding restored continuation passed through
K1.4.  The fallback is used only to totalize rejecting/unavailable branches;
it never makes such a branch available. -/
structure RestoredK14BranchProvider
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  fallbackGamma : QM31Exact
  fallback : RestoredK14Branch decoder binding words fallbackGamma
  branch : (gamma : QM31Exact) →
    Option (RestoredK14Branch decoder binding words gamma)

def providerAvailable
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (gamma : QM31Exact) : Prop :=
  (provider.branch gamma).isSome

def providerResponse
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (gamma : QM31Exact) : InitialMessage QM31Exact :=
  match provider.branch gamma with
  | some branch => branch.extraction.combined.1
  | none => provider.fallback.extraction.combined.1

def providerDisclosedFinal
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (gamma : QM31Exact) : FinalMessage QM31Exact :=
  match provider.branch gamma with
  | some branch => branch.disclosedFinal
  | none => provider.fallback.disclosedFinal

def providerSchedule
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (gamma : QM31Exact) : ExactSchedule :=
  match provider.branch gamma with
  | some branch => branch.schedule
  | none => provider.fallback.schedule

def providerSelected
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (gamma : QM31Exact) : ExactCandidatePair :=
  match provider.branch gamma with
  | some branch => branch.extraction.combined
  | none => provider.fallback.extraction.combined

/-- Kernel-checked construction of the restoration-wide family. -/
def restoredSelectedChainFamilyOfProvider
    {decoder : ExactDecoderInstantiation QM31Exact}
    (binding : InitialProjectionBinding decoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words) :
    RestoredSelectedChainFamily decoder words where
  available := providerAvailable provider
  response := providerResponse provider
  disclosedFinal := providerDisclosedFinal provider
  schedule := providerSchedule provider
  selected := providerSelected provider
  responseAt := by
    intro gamma available
    cases branchEq : provider.branch gamma with
    | none => simp [providerAvailable, branchEq] at available
    | some branch =>
        simp [providerResponse, providerSelected, branchEq]
  selectedExact := by
    intro gamma available
    cases branchEq : provider.branch gamma with
    | none => simp [providerAvailable, branchEq] at available
    | some branch =>
        simpa [providerDisclosedFinal, providerSchedule, providerSelected,
          branchEq] using branch.extraction.combinedSelected

@[simp] theorem family_of_provider_available_iff
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (gamma : QM31Exact) :
    (restoredSelectedChainFamilyOfProvider binding provider).available gamma ↔
      (provider.branch gamma).isSome := by
  rfl

theorem family_of_provider_selected_of_branch
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (gamma : QM31Exact)
    (branch : RestoredK14Branch decoder binding words gamma)
    (branchExact : provider.branch gamma = some branch) :
    (restoredSelectedChainFamilyOfProvider binding provider).available gamma ∧
      (restoredSelectedChainFamilyOfProvider binding provider).selected gamma =
        branch.extraction.combined := by
  constructor
  · simp [restoredSelectedChainFamilyOfProvider, providerAvailable, branchExact]
  · simp [restoredSelectedChainFamilyOfProvider, providerSelected, branchExact]

/-- Every literal fixed-run K1.4 certificate is one branch of the causal
provider type. -/
def restoredK14BranchOfExactCertificate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k14 : ExactK14Certificate decoder binding input k12) :
    RestoredK14Branch decoder binding k12.words
      (exactK13ParsedProof input).gamma where
  disclosedFinal := (exactK13ParsedProof input).disclosedFinal
  schedule := (exactK13ParsedProof input).schedule
  extraction := k14.extraction

def restoredK14BranchOfParsedCertificate
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {proof : Tag73K12ParsedProof}
    (k14 : ParsedK14Certificate decoder binding words proof) :
    RestoredK14Branch decoder binding words proof.gamma where
  disclosedFinal := proof.disclosedFinal
  schedule := proof.schedule
  extraction := k14.extraction

noncomputable def causalProviderGammaTarget
    {decoder : ExactDecoderInstantiation QM31Exact}
    (binding : InitialProjectionBinding decoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (provider : Tag73OuterSamplerSkeleton →
      RestoredK14BranchProvider decoder binding words)
    (skeleton : Tag73OuterSamplerSkeleton) : Finset QM31Exact :=
  acceptedRestoredPointConstrainedGammaSet decoder words point claims
    (restoredSelectedChainFamilyOfProvider binding (provider skeleton))

def causalProviderRawGammaEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    (binding : InitialProjectionBinding decoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (provider : Tag73OuterSamplerSkeleton →
      RestoredK14BranchProvider decoder binding words) :
    Set SuccessfulTag73RawNonzeroAttempts :=
  rawSkeletonDependentGammaEvent
    (causalProviderGammaTarget binding point claims provider)

/-- Exact causal K1.4 probability theorem.  The complete restored branch
provider may vary with every sampler nuisance coordinate, but is fixed as a
function of gamma before the sampled value is supplied. -/
theorem no_k14_causal_provider_raw_gamma_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (binding : InitialProjectionBinding decoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (provider : Tag73OuterSamplerSkeleton →
      RestoredK14BranchProvider decoder binding words)
    (noK14 : ∀ skeleton,
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder words point claims
        (restoredSelectedChainFamilyOfProvider binding (provider skeleton))) :
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).toOuterMeasure
        (causalProviderRawGammaEvent binding point claims provider) ≤
      (AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply raw_skeleton_dependent_gamma_probability_le
  intro skeleton
  exact no_accepted_restored_point_compatible_k14_card_le decoder published
    words point claims
      (restoredSelectedChainFamilyOfProvider binding (provider skeleton))
      (noK14 skeleton)

end


#print axioms restoredSelectedChainFamilyOfProvider
#print axioms exactK13_has_selected_chain
#print axioms restoredSelectedBranchOfExactK13
#print axioms restoredSelectedBranchOfParsedK13
#print axioms finiteK13Provider_root_branch
#print axioms finite_k13_family_contains_exact_root
#print axioms restoredSelectedChainFamilyOfK13Provider
#print axioms k13_family_selected_of_branch
#print axioms no_k14_causal_k13_provider_raw_gamma_probability_le
#print axioms family_of_provider_selected_of_branch
#print axioms restoredK14BranchOfExactCertificate
#print axioms restoredK14BranchOfParsedCertificate
#print axioms no_k14_causal_provider_raw_gamma_probability_le

end AspisK1.V7Tag73CausalRestoredFamily
