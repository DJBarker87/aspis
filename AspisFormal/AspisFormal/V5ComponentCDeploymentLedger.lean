import AspisFormal.V5ComponentCBlockSamplerDirectHiding
import AspisFormal.V5ComponentCQM31Representation
import AspisFormal.V5ComponentCStoppingTimeSampler

/-!
# v5 Component C: honest deployment ledger for the direct construction

This leaf does not prove that Rust implements the Component-C model.  It
connects the strongest finite direct-hiding theorem to a decoded runtime-view
statement while making every executable or cryptographic edge an explicit,
load-bearing input.

The exact finite core is already proved in the imported leaves.  Here a
runtime successful law is connected to that core through, in order:

* literal low-31-bit semantics and a stopping-time-law equality;
* four-limb QM31 assembly;
* the `1023 -> 1024` pivot encoder;
* the physical `58 -> 36` relation-tail reorder and the schedule-sized
  downstream evaluator;
* the one combined inactive scalar and eighteen `E` rows for each witness;
* independence of the outer A/H/B source from Component C; and
* terminal PCS, serialization, hash/RO/Fiat--Shamir code correspondence, the
  production-entropy hybrid, and compiler transport.

None of those deployment edges is asserted here.  The fixed-schedule theorem
is an exact PMF equality conditional on the code/model equalities.  The final
theorem invokes a supplied compiler/simulator function; it therefore does not
misstate a per-schedule equality as a Fiat--Shamir theorem.
-/

namespace AspisV5ComponentCDeploymentLedger

open AspisV5ComponentCBlockSamplerDirectHiding
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDirectHiding
open AspisV5ComponentCPreCProjection
open AspisV5ComponentCPreCProjectionMixed
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCSamplerKernel
open AspisV5ComponentCStoppingTimeSampler
open AspisV5MixedFieldComposition

/-! ## Literal successful-law bridge -/

/-- Assemble the 1023 four-limb values produced by the runtime parser into
the field used by the direct Component-C theorem. -/
def assembleFreeCoordinates {K : Type*} (assemble : QM31Limbs -> K)
    (limbs : Fin componentCFreeCoordinateCount -> QM31Limbs) :
    FreeCoordinates K :=
  fun i => assemble (limbs i)

/-- Runtime successful free-coordinate law after four-limb assembly. -/
noncomputable def runtimeSuccessfulFreeLaw {K : Type*}
    (successfulLimbLaw : PMF
      (Fin componentCFreeCoordinateCount -> QM31Limbs))
    (assemble : QM31Limbs -> K) : PMF (FreeCoordinates K) :=
  successfulLimbLaw.map (assembleFreeCoordinates assemble)

/-- Exact executable representation bundle used by the deployment ledger.
Cardinality and a codec round trip are not enough: the sampler constructor,
the pinned `(c0.a,c0.b,c1.a,c1.b)` byte codec, and every Rust tower operation
used downstream must all commute with the same field equivalence. -/
def DeployedQM31RepresentationMatches {K : Type*}
    [Field K] [DecidableEq K]
    (e : QM31Limbs ≃ K) (rustAssemble : QM31Limbs → K)
    (rustLimbEncode : QM31Limbs → QM31Bytes)
    (rustLimbDecode : QM31Bytes → Option QM31Limbs)
    (rustZero rustOne : QM31Limbs)
    (rustAdd rustMul : QM31Limbs → QM31Limbs → QM31Limbs)
    (rustNeg : QM31Limbs → QM31Limbs)
    (rustTryInv : QM31Limbs → Option QM31Limbs) : Prop :=
  RustQM31SamplerAssemblyMatches e rustAssemble ∧
  RustQM31CodecMatchesPinnedLimbOrder rustLimbEncode rustLimbDecode ∧
  RustQM31TowerArithmeticMatches e rustZero rustOne rustAdd rustMul rustNeg
    rustTryInv

/-- All finite sampler seams are consumed in this equality.

`stoppingLaw` is deliberately a function of the executable low31 operation.
The first equality binds the runtime parser to that function; the second binds
the executable bit operation to the kernel-checked `word & 0x7fff_ffff`
model; and the third is the still-external code/model equality between that
parser law and the literal shared-stream experiment.  The equality from the
shared-stream experiment to the preallocated block experiment is proved in
`V5ComponentCStoppingTimeSampler` and is discharged internally here. -/
theorem runtimeSuccessfulFreeLaw_eq_literal_u32_law
    {K : Type*} [Field K] [Fintype K]
    (e : QM31Limbs ≃ K)
    (rustLow31 : RawWord -> RawCandidate)
    (stoppingLaw : (RawWord -> RawCandidate) ->
      PMF (Fin componentCFreeCoordinateCount -> QM31Limbs))
    (runtimeLimbLaw : PMF
      (Fin componentCFreeCoordinateCount -> QM31Limbs))
    (rustAssemble : QM31Limbs -> K)
    (hparser : runtimeLimbLaw = stoppingLaw rustLow31)
    (hlow31 : rustLow31 = rustLow31BitAnd)
    (hstopping : stoppingLaw low31Candidate =
      successfulComponentCSequentialCoordinatesLaw)
    (hassemble : rustAssemble = e) :
    runtimeSuccessfulFreeLaw runtimeLimbLaw rustAssemble =
      successfulComponentCFreeCoordinateLaw e := by
  subst runtimeLimbLaw
  subst rustLow31
  rw [rustLow31BitAnd_eq_low31Candidate, hstopping]
  subst rustAssemble
  exact successfulComponentCStoppingTimeFreeCoordinateLaw_eq_blockLaw e

/-! ## Runtime fixed-schedule decoding boundary -/

/-- A supplied executable-correspondence theorem turns the independently
audited seams into equality with one exact fixed-schedule mathematical law.
The function shape forces every edge to be supplied to obtain the equality;
this file does not manufacture any of them.

Logically, this is the irreducible code/model theorem and it dominates the
individual audit edges: a dishonest caller could postulate the curried
function.  The point of the type is audit accounting, not magic reduction of
Rust semantics to Lean.  Closing it requires executable correspondence/KATs
or a verified Rust refinement, outside this leaf. -/
def RuntimeDecodeTransport {MathView : Type*}
    (runtimeLaw idealLaw : PMF MathView)
    (Low31Edge StoppingTimeEdge RepresentationEdge EncoderEdge
      PhysicalReorderEdge DownstreamEdge SourceIndependenceEdge : Prop) : Prop :=
  Low31Edge -> StoppingTimeEdge -> RepresentationEdge -> EncoderEdge ->
    PhysicalReorderEdge -> DownstreamEdge -> SourceIndependenceEdge ->
    runtimeLaw = idealLaw

/-- Exact product-law statement used for the A/H/B versus C source seam. -/
def JointSourceIndependent {Outer Free : Type*}
    (joint : PMF (Outer × Free)) (outer : PMF Outer) (free : PMF Free) : Prop :=
  joint = outer.bind fun x => free.map fun y => (x, y)

/-- Computational hybrid replacing the production, domain-separated joint
source by the ideal product of the outer A/H/B source and Component C.  The
finite fixed-schedule theorem below assumes the product law exactly and is
therefore explicitly post-hybrid. -/
def ProductionJointSourcePseudorandomness {Outer Free : Type*}
    (Indist : PMF (Outer × Free) → PMF (Outer × Free) → Prop)
    (productionJoint : PMF (Outer × Free))
    (idealOuter : PMF Outer) (idealFree : PMF Free) : Prop :=
  Indist productionJoint
    (idealOuter.bind fun x => idealFree.map fun y => (x, y))

section FixedScheduleLedger

variable {F K FA MA MH SB PB VA VH VB TB U : Type*}
variable [Field F] [Field K] [Algebra F K] [Field FA]
variable [DecidableEq K]
variable [AddCommGroup MA] [Module FA MA]
variable [AddCommGroup VA] [Module FA VA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup U] [Module K U]
variable [Fintype K]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- The exact successful, fixed-schedule mathematical view used by the
deployment ledger. -/
noncomputable def idealFixedScheduleLaw
    (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (LA : MA →ₗ[FA] VA) (wA : VA)
    (LH : MH →ₗ[K] VH) (wH : VH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (wBS : SB) (wBV : VB)
    (semantic : MixedOuterSample MA MH SB PB → SemanticLane → CWord K)
    (hcopy componentB : MixedOuterSample MA MH SB PB → CWord K)
    (ell : CWord K →ₗ[K] K) (E : CWord K →ₗ[K] U) (gamma : K)
    (e : QM31Limbs ≃ K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1) :
    PMF (MixedOuterVisible VA VH SB TB VB × U ×
      (Fin (fRows schedule.fri) → K)) :=
  (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind fun sample =>
    successfulSamplerJointKernel ell
      (successfulComponentCFreeCoordinateLaw e)
      (componentCEncoderEquiv ell pivot hpivot) E
      (concreteDownstream schedule enc) gamma
      (mixedOuterVisible LA wA LH wH terminalB RB AB wBS wBV sample)
      (preCWord gamma (semantic sample) (hcopy sample) (componentB sample))

/-- **Strongest exact post-entropy-hybrid Component-C statement before the
Fiat--Shamir compiler.**  The conclusion concerns two decoded idealized runtime
laws, not two restatements of the Lean model.  Replacing the finite-seed
production expander by the iid stream, and the domain-separated A/H/B/C source
by an independent product source, are computational steps consumed only by the
adaptive compiler interface below; neither can be promoted to equality here.

Every implementation edge is consumed through `RuntimeDecodeTransport`.
In particular the physical reorder and schedule-sized evaluator remain
separate inputs, and source independence is an equality of joint PMFs. -/
theorem post_entropy_hybrid_fixed_schedule_laws_equal
    (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : MixedOuterSample MA MH SB PB →
      SemanticLane → CWord K)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ :
      MixedOuterSample MA MH SB PB → CWord K)
    (ell : CWord K →ₗ[K] K) (E : CWord K →ₗ[K] U)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows : MixedOuterVisible VA VH SB TB VB →
      PreCConditionedRows U)
    (hrows₁ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₁ hcopy₁ componentB₁)
    (hrows₂ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₂ hcopy₂ componentB₂)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1)
    (e : QM31Limbs ≃ K)
    (rustLow31 : RawWord → RawCandidate)
    (stoppingLaw : (RawWord → RawCandidate) →
      PMF (Fin componentCFreeCoordinateCount → QM31Limbs))
    (runtimeLimbLaw : PMF
      (Fin componentCFreeCoordinateCount → QM31Limbs))
    (rustAssemble : QM31Limbs → K)
    (hparser : runtimeLimbLaw = stoppingLaw rustLow31)
    (hlow31 : rustLow31 = rustLow31BitAnd)
    (hstopping : stoppingLaw low31Candidate =
      successfulComponentCSequentialCoordinatesLaw)
    (rustLimbEncode : QM31Limbs → QM31Bytes)
    (rustLimbDecode : QM31Bytes → Option QM31Limbs)
    (rustZero rustOne : QM31Limbs)
    (rustAdd rustMul : QM31Limbs → QM31Limbs → QM31Limbs)
    (rustNeg : QM31Limbs → QM31Limbs)
    (rustTryInv : QM31Limbs → Option QM31Limbs)
    (hrepresentation : DeployedQM31RepresentationMatches e rustAssemble
      rustLimbEncode rustLimbDecode rustZero rustOne rustAdd rustMul rustNeg
      rustTryInv)
    {RelationBytes : Type*}
    (rustEncode : FreeCoordinates K → LinearMap.ker ell)
    (hencode : RustEncoderMatchesKernelEquiv ell pivot hpivot rustEncode)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (rustMaskDownstream : FreeCoordinateVector K →
      Fin (fRows schedule.fri) → K)
    (rustTailBytes : CWord K → RelationBytes)
    (decodeTail : RelationBytes → Fin physicalRelationTailFieldCount → K)
    (hphysical : UnmetDeployment.PhysicalRustRelationTailCorresponds
      schedule rustTailBytes decodeTail)
    (hdownstream : UnmetDeployment.RustConcreteDownstreamCorresponds
      schedule encodeFree enc rustMaskDownstream)
    (runtimeJoint₁ runtimeJoint₂ :
      PMF (MixedOuterSample MA MH SB PB × FreeCoordinates K))
    (hsource₁ : JointSourceIndependent runtimeJoint₁
      (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB))
      (runtimeSuccessfulFreeLaw runtimeLimbLaw rustAssemble))
    (hsource₂ : JointSourceIndependent runtimeJoint₂
      (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB))
      (runtimeSuccessfulFreeLaw runtimeLimbLaw rustAssemble))
    (runtimeLaw₁ runtimeLaw₂ :
      PMF (MixedOuterVisible VA VH SB TB VB × U ×
        (Fin (fRows schedule.fri) → K)))
    (decodeTransport₁ : RuntimeDecodeTransport runtimeLaw₁
      (idealFixedScheduleLaw schedule enc LA wA₁ LH wH₁ terminalB RB AB
        wBS₁ wBV₁ semantic₁ hcopy₁ componentB₁ ell E gamma e pivot hpivot)
      (rustLow31 = rustLow31BitAnd)
      (runtimeSuccessfulFreeLaw runtimeLimbLaw rustAssemble =
        successfulComponentCFreeCoordinateLaw e)
      (DeployedQM31RepresentationMatches e rustAssemble
        rustLimbEncode rustLimbDecode rustZero rustOne rustAdd rustMul rustNeg
        rustTryInv)
      (RustEncoderMatchesKernelEquiv ell pivot hpivot rustEncode)
      (UnmetDeployment.PhysicalRustRelationTailCorresponds
        schedule rustTailBytes decodeTail)
      (UnmetDeployment.RustConcreteDownstreamCorresponds
        schedule encodeFree enc rustMaskDownstream)
      (JointSourceIndependent runtimeJoint₁
        (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB))
        (runtimeSuccessfulFreeLaw runtimeLimbLaw rustAssemble)))
    (decodeTransport₂ : RuntimeDecodeTransport runtimeLaw₂
      (idealFixedScheduleLaw schedule enc LA wA₂ LH wH₂ terminalB RB AB
        wBS₂ wBV₂ semantic₂ hcopy₂ componentB₂ ell E gamma e pivot hpivot)
      (rustLow31 = rustLow31BitAnd)
      (runtimeSuccessfulFreeLaw runtimeLimbLaw rustAssemble =
        successfulComponentCFreeCoordinateLaw e)
      (DeployedQM31RepresentationMatches e rustAssemble
        rustLimbEncode rustLimbDecode rustZero rustOne rustAdd rustMul rustNeg
        rustTryInv)
      (RustEncoderMatchesKernelEquiv ell pivot hpivot rustEncode)
      (UnmetDeployment.PhysicalRustRelationTailCorresponds
        schedule rustTailBytes decodeTail)
      (UnmetDeployment.RustConcreteDownstreamCorresponds
        schedule encodeFree enc rustMaskDownstream)
      (JointSourceIndependent runtimeJoint₂
        (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB))
        (runtimeSuccessfulFreeLaw runtimeLimbLaw rustAssemble))) :
    runtimeLaw₁ = runtimeLaw₂ := by
  have hassemble : rustAssemble = e := hrepresentation.1
  have hsampler := runtimeSuccessfulFreeLaw_eq_literal_u32_law e rustLow31
    stoppingLaw runtimeLimbLaw rustAssemble hparser hlow31 hstopping hassemble
  have hdecode₁ := decodeTransport₁ hlow31 hsampler hrepresentation hencode
    hphysical hdownstream hsource₁
  have hdecode₂ := decodeTransport₂ hlow31 hsampler hrepresentation hencode
    hphysical hdownstream hsource₂
  have hfinite :=
    concrete_downstream_complete_joint_hiding_conditioned_u32_sampler
      schedule enc LA hLA LH hLH terminalB RB AB hAB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
      semantic₁ semantic₂ hcopy₁ hcopy₂ componentB₁ componentB₂
      ell E gamma hgamma publishedInactive decodeConditionedRows hrows₁ hrows₂
      pivot hpivot e
  exact hdecode₁.trans (hfinite.trans hdecode₂.symm)

end FixedScheduleLedger

/-! ## Post-fixed-schedule compiler boundary -/

/-- Exact terminal PCS/code-model compatibility.  This is an equality of
functions, not a decorative proposition about a commitment scheme. -/
def TerminalPCSCompatibility {MathView PCSView : Type*}
    (rustPCS modelPCS : MathView -> PCSView) : Prop :=
  rustPCS = modelPCS

/-- Exact, injective serialization boundary. -/
def SerializationExactAndInjective {PCSView Bytes : Type*}
    (rustSerialize modelSerialize : PCSView -> Bytes) : Prop :=
  rustSerialize = modelSerialize ∧ Function.Injective modelSerialize

/-- A supplied literature/compiler interface lifts a fixed-schedule decoded
law equality to the desired *adaptive deployed transcript* relation.

`deployedLeft` and `deployedRight` are not defined as deterministic maps of
the fixed-schedule laws.  The supplied method owns adaptive schedule
selection, random-oracle programming, and the cryptographic hash/RO security
argument; the `rustHash = modelHash` and `rustROProgram = modelROProgram`
arguments below are only code equalities.  Its arguments include actual
schedule-selector and RO-program functions and exact Rust/model equalities,
along with terminal PCS, injective serialization, the production-entropy
hybrid, FS and compiler correspondences.  Thus this leaf cannot silently infer
adaptive FS security from one fixed-schedule PMF equality. -/
def AdaptiveFSROCompilerTransport
    {MathView PCSView Bytes Digest Prefix Schedule Query Challenge Transcript
      Outer Free : Type*}
    (Indist : PMF Transcript -> PMF Transcript -> Prop)
    (StreamIndist : PMF ComponentCSequentialRawStream →
      PMF ComponentCSequentialRawStream → Prop)
    (productionStreamLaw : PMF ComponentCSequentialRawStream)
    (SourceIndist : PMF (Outer × Free) → PMF (Outer × Free) → Prop)
    (productionJointLaw : PMF (Outer × Free))
    (idealOuterLaw : PMF Outer) (idealFreeLaw : PMF Free)
    (deployedLeft deployedRight : PMF Transcript)
    (rustPCS modelPCS : MathView -> PCSView)
    (rustSerialize modelSerialize : PCSView -> Bytes)
    (rustHash modelHash : Bytes -> Digest)
    (rustScheduleSelect modelScheduleSelect : Prefix -> Schedule)
    (rustROProgram modelROProgram : Query -> Digest)
    (rustFS modelFS : Digest -> Challenge)
    (rustCompiler modelCompiler :
      (Prefix -> Schedule) -> (Query -> Digest) -> Challenge -> Transcript) :
    Prop :=
  ProductionSequentialU32StreamPseudorandomness StreamIndist
      productionStreamLaw →
    ProductionJointSourcePseudorandomness SourceIndist productionJointLaw
      idealOuterLaw idealFreeLaw →
    ∀ (left right : PMF MathView), left = right ->
    rustPCS = modelPCS ->
    rustSerialize = modelSerialize -> Function.Injective modelSerialize ->
    rustHash = modelHash ->
    rustScheduleSelect = modelScheduleSelect ->
    rustROProgram = modelROProgram -> rustFS = modelFS ->
    rustCompiler = modelCompiler ->
    Indist deployedLeft deployedRight

/-- Post-compiler capstone.  The only route from the fixed-schedule equality
to the adaptive transcript conclusion is the supplied compiler/simulator
method, which explicitly consumes terminal PCS, exact and injective
serialization, the production-entropy hybrid, hash/RO code equality, adaptive
schedule selection, RO programming, Fiat--Shamir and compiler
correspondences.  Hash/RO cryptographic security lives in that supplied
method, not in the equality hypotheses. -/
theorem deployed_transcripts_indist_of_adaptive_compiler
    {MathView PCSView Bytes Digest Prefix Schedule Query Challenge Transcript
      Outer Free : Type*}
    (Indist : PMF Transcript → PMF Transcript → Prop)
    (StreamIndist : PMF ComponentCSequentialRawStream →
      PMF ComponentCSequentialRawStream → Prop)
    (productionStreamLaw : PMF ComponentCSequentialRawStream)
    (SourceIndist : PMF (Outer × Free) → PMF (Outer × Free) → Prop)
    (productionJointLaw : PMF (Outer × Free))
    (idealOuterLaw : PMF Outer) (idealFreeLaw : PMF Free)
    (fixedLeft fixedRight : PMF MathView)
    (deployedLeft deployedRight : PMF Transcript)
    (rustPCS modelPCS : MathView → PCSView)
    (rustSerialize modelSerialize : PCSView → Bytes)
    (rustHash modelHash : Bytes → Digest)
    (rustScheduleSelect modelScheduleSelect : Prefix → Schedule)
    (rustROProgram modelROProgram : Query → Digest)
    (rustFS modelFS : Digest → Challenge)
    (rustCompiler modelCompiler :
      (Prefix → Schedule) → (Query → Digest) → Challenge → Transcript)
    (hfixed : fixedLeft = fixedRight)
    (hprg : ProductionSequentialU32StreamPseudorandomness StreamIndist
      productionStreamLaw)
    (hsourceHybrid : ProductionJointSourcePseudorandomness SourceIndist
      productionJointLaw idealOuterLaw idealFreeLaw)
    (hpcs : TerminalPCSCompatibility rustPCS modelPCS)
    (hserialization : SerializationExactAndInjective
      rustSerialize modelSerialize)
    (hhash : rustHash = modelHash)
    (hschedule : rustScheduleSelect = modelScheduleSelect)
    (hro : rustROProgram = modelROProgram)
    (hfs : rustFS = modelFS)
    (hcompiler : rustCompiler = modelCompiler)
    (htransport : AdaptiveFSROCompilerTransport Indist
      StreamIndist productionStreamLaw SourceIndist productionJointLaw
      idealOuterLaw idealFreeLaw deployedLeft deployedRight rustPCS modelPCS
      rustSerialize modelSerialize rustHash modelHash
      rustScheduleSelect modelScheduleSelect rustROProgram modelROProgram
      rustFS modelFS rustCompiler modelCompiler) :
    Indist deployedLeft deployedRight := by
  exact htransport hprg hsourceHybrid fixedLeft fixedRight hfixed hpcs
    hserialization.1 hserialization.2 hhash hschedule hro hfs hcompiler

/-! ## Non-vacuity and negative teeth -/

/-- The irreducible runtime boundary is satisfiable when executable and model
laws are literally the same. -/
theorem runtimeDecodeTransport_nonvacuous (law : PMF PUnit) :
    RuntimeDecodeTransport law law True True True True True True True := by
  intro _ _ _ _ _ _ _
  rfl

/-- The runtime correspondence cannot be dropped: with all seven audit flags
trivial, it still cannot transport two different decoded laws. -/
theorem runtimeDecodeTransport_is_loadBearing :
    ¬ RuntimeDecodeTransport (PMF.pure false) (PMF.pure true)
      True True True True True True True := by
  intro h
  have heq := h trivial trivial trivial trivial trivial trivial trivial
  have hmass := congrArg (fun law : PMF Bool => law false) heq
  simp at hmass

/-- Both production-entropy hybrid interfaces have concrete identity models;
their antecedents are not made true only by inconsistency. -/
theorem productionSequentialU32Pseudorandomness_nonvacuous :
    ProductionSequentialU32StreamPseudorandomness
      (fun left right => left = right)
      (PMF.uniformOfFintype ComponentCSequentialRawStream) := by
  rfl

theorem productionJointSourcePseudorandomness_nonvacuous :
    ProductionJointSourcePseudorandomness
      (fun left right : PMF (PUnit × PUnit) => left = right)
      (PMF.pure (PUnit.unit, PUnit.unit))
      (PMF.pure PUnit.unit) (PMF.pure PUnit.unit) := by
  rw [ProductionJointSourcePseudorandomness, PMF.pure_bind, PMF.pure_map]

/-- The adaptive compiler interface itself has a concrete identity model. -/
theorem adaptiveCompilerTransport_nonvacuous :
    AdaptiveFSROCompilerTransport
      (fun left right : PMF PUnit => left = right)
      (fun left right : PMF ComponentCSequentialRawStream => left = right)
      (PMF.uniformOfFintype ComponentCSequentialRawStream)
      (fun left right : PMF (PUnit × PUnit) => left = right)
      (PMF.pure (PUnit.unit, PUnit.unit))
      (PMF.pure PUnit.unit) (PMF.pure PUnit.unit)
      (PMF.pure PUnit.unit) (PMF.pure PUnit.unit)
      (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit)
      (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit)
      (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit)
      (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit)
      (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit)
      (fun _ : PUnit => PUnit.unit) (fun _ : PUnit => PUnit.unit)
      (fun _ _ _ => PUnit.unit) (fun _ _ _ => PUnit.unit) := by
  intro _ _ left right hleft _ _ _ _ _ _ _ _
  rfl

/-! ## Axiom audit -/

#print axioms runtimeSuccessfulFreeLaw_eq_literal_u32_law
#print axioms post_entropy_hybrid_fixed_schedule_laws_equal
#print axioms deployed_transcripts_indist_of_adaptive_compiler
#print axioms runtimeDecodeTransport_nonvacuous
#print axioms runtimeDecodeTransport_is_loadBearing
#print axioms productionSequentialU32Pseudorandomness_nonvacuous
#print axioms productionJointSourcePseudorandomness_nonvacuous
#print axioms adaptiveCompilerTransport_nonvacuous

end AspisV5ComponentCDeploymentLedger
