import AspisFormal.K1.V7Tag73CausalGammaProbability
import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier
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
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

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
#print axioms family_of_provider_selected_of_branch
#print axioms restoredK14BranchOfExactCertificate
#print axioms no_k14_causal_provider_raw_gamma_probability_le

end AspisK1.V7Tag73CausalRestoredFamily
