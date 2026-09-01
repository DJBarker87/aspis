import AspisFormal.K1.V7Tag73ExactFixedClientExtraction

/-!
# Proof-relevant K1.2--K1.5 boundary for the exact Tag-73 experiment

The existing fixed-instance arithmetic accepts one aggregate probability
inequality on the clean compiler event.  That is useful only after the
interactive K1.2--K1.5 theorem has been instantiated; it does not say what
operational object that theorem consumes or which upstream stage failed.

This module exposes the smaller upstream-only interface.  Its input event is
not a caller-selected `Set`: it is inhabitedness of a type indexed by the
literal sample.  A later module will instantiate that type with the actual
`ExactFixedSchedulerK12ToK15Input` constructed from the scheduler run.

The four stages remain dependent and separately classified:

* K1.2 authenticates the two typed, shared-topology 208-bit Merkle trees;
* K1.3 decodes the deployed circle words and bounded candidate list;
* K1.4 selects one coherent candidate chain;
* K1.5 recovers the spend witness by applying the actual fixed-instance
  restoration client's returned extractor to its literal accumulator.

Success at the last stage is not an abstract witness proposition.  It is a
proof-relevant certificate containing the literal completed scheduler root,
client run, returned extractor, accumulator evaluation, and witness.  The
certificate is equivalent to
membership in the already defined fixed client-extraction event.

There is deliberately no Fiat--Shamir acceptance field, clean-event field,
compiler inclusion, restoration function, or aggregate upstream inequality
in this interface.  Concrete K1.2--K1.5 developments must instantiate the
four certificate/error families and classifiers.  The theorems below only
derive their deterministic cover and ordinary four-event union arithmetic.

The maintained upstream library already exposes the relevant endpoint
objects--`AcceptedV5Forest`/`V5DriverOutput` for authenticated openings,
`FriReadScheduleDecoderAgreement` and `IdealTranscript` for decoded FRI data,
`CoherentChain` for one four-fold candidate, and `ExtractedV5Trace` plus
`StatementHasSpendWitness` for the terminal relation.  What is not yet proved
is the adapter from the exact Tag-73 scheduler input to those objects.  The
dependent families below are precisely the slots that adapter must
instantiate; this module does not pretend that the endpoint types are already
connected.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ProofRelevantUpstreamInterface

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedClientExtraction

noncomputable section

/-! ## The actual fixed-instance extraction certificate -/

/-- Proof-relevant form of the existing fixed client-extraction event.

Every datum is read from the literal result-carrying scheduler.  In
particular, `clientReturned` is about the actual restoration-client terminal
and `extractorReturned` evaluates it on that run's actual accumulator; there
is no caller-selected per-sample witness source. -/
structure ExactFixedClientExtractionCertificate
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (sample : ExactCompilerSample HiddenTape parameters) where
  root : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
    Payload
  clientRun : ConcreteRestorationClientRun Statement Proof Payload
    (ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
  extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness
  witness : Witness
  completed :
    exactPlainRomCompleted? transitionFuel configuration sample =
      some (root, clientRun)
  fixedInstanceExact :
    root.adversaryValue.1.publicProof.publicInstance = fixedInstance
  clientReturned : clientRun.halt = .returned extractor
  extractorReturned : extractor clientRun.accumulator = some witness
  relationValid : relation fixedInstance witness

/-- Forgetting the proof-relevant packaging gives membership in the literal
fixed-instance extraction event by constructor reduction alone. -/
theorem ExactFixedClientExtractionCertificate.toEventMembership
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {sample : ExactCompilerSample HiddenTape parameters}
    (certificate : ExactFixedClientExtractionCertificate transitionFuel
      configuration fixedInstance relation sample) :
    sample ∈ exactFixedPlainRomValidClientExtractionEvent transitionFuel
      configuration fixedInstance relation := by
  exact ⟨certificate.root, certificate.clientRun, certificate.extractor,
    certificate.witness,
    certificate.completed, certificate.fixedInstanceExact,
    certificate.clientReturned, certificate.extractorReturned,
    certificate.relationValid⟩

/-- The event and the proof-relevant certificate contain exactly the same
root, client-run, witness, and fixed-instance equalities. -/
theorem mem_exact_fixed_client_extraction_event_iff_certificate
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ exactFixedPlainRomValidClientExtractionEvent transitionFuel
        configuration fixedInstance relation ↔
      Nonempty (ExactFixedClientExtractionCertificate transitionFuel
        configuration fixedInstance relation sample) := by
  constructor
  · rintro ⟨root, clientRun, extractor, witness, completed, fixedExact,
      returned, extracted, valid⟩
    exact ⟨
      { root := root
        clientRun := clientRun
        extractor := extractor
        witness := witness
        completed := completed
        fixedInstanceExact := fixedExact
        clientReturned := returned
        extractorReturned := extracted
        relationValid := valid }⟩
  · rintro ⟨certificate⟩
    exact certificate.toEventMembership

/-! ## A sample-indexed operational input, not a supplied event -/

/-- The canonical event generated by a proof-relevant operational input
family.  Later specialization fixes `OperationalInput sample` to the exact
scheduler/client certificate for that same sample. -/
def proofRelevantOperationalInputEvent
    {Sample : Type} (OperationalInput : Sample → Type) : Set Sample :=
  {sample | Nonempty (OperationalInput sample)}

@[simp] theorem mem_proof_relevant_operational_input_event_iff
    {Sample : Type} (OperationalInput : Sample → Type) (sample : Sample) :
    sample ∈ proofRelevantOperationalInputEvent OperationalInput ↔
      Nonempty (OperationalInput sample) := by
  rfl

/-! ## Four dependent upstream classifiers -/

/-- The explicit upstream interface.  Each success certificate is indexed by
the exact output of the preceding stage.  Each classifier returns either
that next proof object or a witness for the correspondingly named stage
failure.  No numerical bound is a structure field. -/
structure ProofRelevantK12ToK15Stages
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (OperationalInput : ExactCompilerSample HiddenTape parameters → Type) where
  k12TwoTreeMerkle208Certificate :
    (sample : ExactCompilerSample HiddenTape parameters) →
      OperationalInput sample → Type
  k12TwoTreeMerkle208Error :
    (sample : ExactCompilerSample HiddenTape parameters) →
      OperationalInput sample → Type
  classifyK12TwoTreeMerkle208 :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : OperationalInput sample),
      k12TwoTreeMerkle208Certificate sample input ⊕
        k12TwoTreeMerkle208Error sample input

  k13CircleListDecodeCertificate :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : OperationalInput sample) →
      k12TwoTreeMerkle208Certificate sample input → Type
  k13CircleListDecodeError :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : OperationalInput sample) →
      k12TwoTreeMerkle208Certificate sample input → Type
  classifyK13CircleListDecode :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : OperationalInput sample)
      (k12 : k12TwoTreeMerkle208Certificate sample input),
      k13CircleListDecodeCertificate sample input k12 ⊕
        k13CircleListDecodeError sample input k12

  k14CoherentChainCertificate :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : OperationalInput sample) →
      (k12 : k12TwoTreeMerkle208Certificate sample input) →
      k13CircleListDecodeCertificate sample input k12 → Type
  k14CoherentChainError :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : OperationalInput sample) →
      (k12 : k12TwoTreeMerkle208Certificate sample input) →
      k13CircleListDecodeCertificate sample input k12 → Type
  classifyK14CoherentChain :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : OperationalInput sample)
      (k12 : k12TwoTreeMerkle208Certificate sample input)
      (k13 : k13CircleListDecodeCertificate sample input k12),
      k14CoherentChainCertificate sample input k12 k13 ⊕
        k14CoherentChainError sample input k12 k13

  k15SpendWitnessError :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : OperationalInput sample) →
      (k12 : k12TwoTreeMerkle208Certificate sample input) →
      (k13 : k13CircleListDecodeCertificate sample input k12) →
      k14CoherentChainCertificate sample input k12 k13 → Type
  classifyK15SpendWitness :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : OperationalInput sample)
      (k12 : k12TwoTreeMerkle208Certificate sample input)
      (k13 : k13CircleListDecodeCertificate sample input k12)
      (k14 : k14CoherentChainCertificate sample input k12 k13),
      ExactFixedClientExtractionCertificate transitionFuel configuration
          fixedInstance relation sample ⊕
        k15SpendWitnessError sample input k12 k13 k14

/-! ## The four actual error events -/

def k12TwoTreeMerkle208ErrorEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ input : OperationalInput sample,
    Nonempty (stages.k12TwoTreeMerkle208Error sample input)}

def k13CircleListDecodeErrorEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ (input : OperationalInput sample)
      (k12 : stages.k12TwoTreeMerkle208Certificate sample input),
    Nonempty (stages.k13CircleListDecodeError sample input k12)}

def k14CoherentChainErrorEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ (input : OperationalInput sample)
      (k12 : stages.k12TwoTreeMerkle208Certificate sample input)
      (k13 : stages.k13CircleListDecodeCertificate sample input k12),
    Nonempty (stages.k14CoherentChainError sample input k12 k13)}

def k15SpendWitnessErrorEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ (input : OperationalInput sample)
      (k12 : stages.k12TwoTreeMerkle208Certificate sample input)
      (k13 : stages.k13CircleListDecodeCertificate sample input k12)
      (k14 : stages.k14CoherentChainCertificate sample input k12 k13),
    Nonempty (stages.k15SpendWitnessError sample input k12 k13 k14)}

/-- Literal union of the four upstream errors. -/
def proofRelevantUpstreamErrorUnion
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  k12TwoTreeMerkle208ErrorEvent stages ∪
    (k13CircleListDecodeErrorEvent stages ∪
      (k14CoherentChainErrorEvent stages ∪
        k15SpendWitnessErrorEvent stages))

/-! ## Deterministic stage cover -/

/-- Every inhabited operational input either reaches the actual fixed client
extraction terminal or produces a witness for one of the four named upstream
failures.  This is classification only; it says nothing about source or
Fiat--Shamir acceptance. -/
theorem proof_relevant_operational_input_subset_extraction_union_errors
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (OperationalInput : ExactCompilerSample HiddenTape parameters → Type)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    proofRelevantOperationalInputEvent OperationalInput ⊆
      exactFixedPlainRomValidClientExtractionEvent transitionFuel configuration
          fixedInstance relation ∪
        proofRelevantUpstreamErrorUnion stages := by
  intro sample member
  rcases member with ⟨input⟩
  cases k12Result : stages.classifyK12TwoTreeMerkle208 sample input with
  | inr k12Error =>
      exact Or.inr (Or.inl ⟨input, ⟨k12Error⟩⟩)
  | inl k12 =>
      cases k13Result : stages.classifyK13CircleListDecode sample input k12 with
      | inr k13Error =>
          exact Or.inr (Or.inr (Or.inl ⟨input, k12, ⟨k13Error⟩⟩))
      | inl k13 =>
          cases k14Result : stages.classifyK14CoherentChain sample input k12 k13 with
          | inr k14Error =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inl
                  ⟨input, k12, k13, ⟨k14Error⟩⟩)))
          | inl k14 =>
              cases k15Result : stages.classifyK15SpendWitness sample input k12
                  k13 k14 with
              | inr k15Error =>
                  exact Or.inr
                    (Or.inr (Or.inr (Or.inr
                      ⟨input, k12, k13, k14, ⟨k15Error⟩⟩)))
              | inl extracted =>
                  exact Or.inl extracted.toEventMembership

/-- Equivalent failure-only form: after removing actual fixed client
extraction, the operational input event is covered by exactly the four
upstream error classes. -/
theorem proof_relevant_operational_input_without_extraction_subset_errors
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (OperationalInput : ExactCompilerSample HiddenTape parameters → Type)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    proofRelevantOperationalInputEvent OperationalInput \
        exactFixedPlainRomValidClientExtractionEvent transitionFuel
          configuration fixedInstance relation ⊆
      proofRelevantUpstreamErrorUnion stages := by
  intro sample member
  rcases member with ⟨operational, notExtracted⟩
  rcases proof_relevant_operational_input_subset_extraction_union_errors
      transitionFuel configuration fixedInstance relation OperationalInput
        stages operational with extracted | failed
  · exact (notExtracted extracted).elim
  · exact failed

/-! ## Restriction to the compiler-clean event

The top-level compiler theorem already partitions accepted executions into a
literal target-clean event and the separately bounded causal target event.
Consequently K1.2--K1.5 are required only on that clean event.  The following
definitions and theorems retain this restriction explicitly instead of asking
for stronger global bounds on executions which K1.6 has already charged to the
target event.
-/

/-- The four stage errors, each intersected with one fixed clean event. -/
def proofRelevantRestrictedUpstreamErrorUnion
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  (clean ∩ k12TwoTreeMerkle208ErrorEvent stages) ∪
    ((clean ∩ k13CircleListDecodeErrorEvent stages) ∪
      ((clean ∩ k14CoherentChainErrorEvent stages) ∪
        (clean ∩ k15SpendWitnessErrorEvent stages)))

/-- Classification restricted to the event which K1.6 actually consumes.
No stage result is changed: the clean-membership proof is simply retained on
the error branch. -/
theorem clean_subset_extraction_union_restricted_upstream_errors
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (OperationalInput : ExactCompilerSample HiddenTape parameters → Type)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (cleanOperational : clean ⊆
      proofRelevantOperationalInputEvent OperationalInput) :
    clean ⊆
      exactFixedPlainRomValidClientExtractionEvent transitionFuel configuration
          fixedInstance relation ∪
        proofRelevantRestrictedUpstreamErrorUnion clean stages := by
  intro sample cleanMember
  rcases proof_relevant_operational_input_subset_extraction_union_errors
      transitionFuel configuration fixedInstance relation OperationalInput
        stages (cleanOperational cleanMember) with extracted | failed
  · exact Or.inl extracted
  · refine Or.inr ?_
    rcases failed with k12Failure | laterFailures
    · exact Or.inl ⟨cleanMember, k12Failure⟩
    · rcases laterFailures with k13Failure | laterFailures
      · exact Or.inr (Or.inl ⟨cleanMember, k13Failure⟩)
      · rcases laterFailures with k14Failure | k15Failure
        · exact Or.inr (Or.inr (Or.inl ⟨cleanMember, k14Failure⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨cleanMember, k15Failure⟩))

/-- Sum of the four stage-error measures after restriction to `clean`. -/
def proofRelevantRestrictedUpstreamRawError
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) : ENNReal :=
  let law := exactCompilerJointLaw hiddenLaw parameters
  law.toOuterMeasure (clean ∩ k12TwoTreeMerkle208ErrorEvent stages) +
    law.toOuterMeasure (clean ∩ k13CircleListDecodeErrorEvent stages) +
    law.toOuterMeasure (clean ∩ k14CoherentChainErrorEvent stages) +
    law.toOuterMeasure (clean ∩ k15SpendWitnessErrorEvent stages)

/-- Ordinary union arithmetic for the four clean-restricted errors. -/
theorem restricted_upstream_error_union_probability_le_raw_error
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (proofRelevantRestrictedUpstreamErrorUnion clean stages) ≤
      proofRelevantRestrictedUpstreamRawError hiddenLaw clean stages := by
  let law : OuterMeasure (ExactCompilerSample HiddenTape parameters) :=
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
  calc
    law (proofRelevantRestrictedUpstreamErrorUnion clean stages) ≤
        law (clean ∩ k12TwoTreeMerkle208ErrorEvent stages) +
          law ((clean ∩ k13CircleListDecodeErrorEvent stages) ∪
            ((clean ∩ k14CoherentChainErrorEvent stages) ∪
              (clean ∩ k15SpendWitnessErrorEvent stages))) :=
      measure_union_le (μ := law) _ _
    _ ≤ law (clean ∩ k12TwoTreeMerkle208ErrorEvent stages) +
          (law (clean ∩ k13CircleListDecodeErrorEvent stages) +
            law ((clean ∩ k14CoherentChainErrorEvent stages) ∪
              (clean ∩ k15SpendWitnessErrorEvent stages))) := by
      exact add_le_add (le_refl _) (measure_union_le (μ := law) _ _)
    _ ≤ law (clean ∩ k12TwoTreeMerkle208ErrorEvent stages) +
          (law (clean ∩ k13CircleListDecodeErrorEvent stages) +
            (law (clean ∩ k14CoherentChainErrorEvent stages) +
              law (clean ∩ k15SpendWitnessErrorEvent stages))) := by
      exact add_le_add (le_refl _)
        (add_le_add (le_refl _) (measure_union_le (μ := law) _ _))
    _ = proofRelevantRestrictedUpstreamRawError hiddenLaw clean stages := by
      unfold proofRelevantRestrictedUpstreamRawError
      ac_rfl

/-- The clean event is bounded by actual extraction plus only the portions of
the four stage errors lying in that same event. -/
theorem clean_probability_le_extraction_plus_restricted_upstream_raw_error
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (OperationalInput : ExactCompilerSample HiddenTape parameters → Type)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (cleanOperational : clean ⊆
      proofRelevantOperationalInputEvent OperationalInput) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure clean ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        proofRelevantRestrictedUpstreamRawError hiddenLaw clean stages := by
  let law : OuterMeasure (ExactCompilerSample HiddenTape parameters) :=
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
  calc
    law clean ≤ law
        (exactFixedPlainRomValidClientExtractionEvent transitionFuel
            configuration fixedInstance relation ∪
          proofRelevantRestrictedUpstreamErrorUnion clean stages) :=
      measure_mono
        (clean_subset_extraction_union_restricted_upstream_errors
          transitionFuel configuration fixedInstance relation OperationalInput
          stages clean cleanOperational)
    _ ≤ law (exactFixedPlainRomValidClientExtractionEvent transitionFuel
            configuration fixedInstance relation) +
          law (proofRelevantRestrictedUpstreamErrorUnion clean stages) :=
      measure_union_le (μ := law) _ _
    _ ≤ exactFixedPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration fixedInstance relation +
          proofRelevantRestrictedUpstreamRawError hiddenLaw clean stages := by
      exact add_le_add (le_refl _)
        (restricted_upstream_error_union_probability_le_raw_error hiddenLaw
          clean stages)

/-! ## Separate measured errors and union arithmetic -/

def proofRelevantUpstreamRawError
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) : ENNReal :=
  let law := exactCompilerJointLaw hiddenLaw parameters
  law.toOuterMeasure (k12TwoTreeMerkle208ErrorEvent stages) +
    law.toOuterMeasure (k13CircleListDecodeErrorEvent stages) +
    law.toOuterMeasure (k14CoherentChainErrorEvent stages) +
    law.toOuterMeasure (k15SpendWitnessErrorEvent stages)

theorem proof_relevant_upstream_raw_error_four_term_expansion
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    proofRelevantUpstreamRawError hiddenLaw stages =
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (k12TwoTreeMerkle208ErrorEvent stages) +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (k13CircleListDecodeErrorEvent stages) +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (k14CoherentChainErrorEvent stages) +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (k15SpendWitnessErrorEvent stages) := by
  rfl

theorem proof_relevant_upstream_error_union_probability_le_raw_error
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (proofRelevantUpstreamErrorUnion stages) ≤
      proofRelevantUpstreamRawError hiddenLaw stages := by
  let law : OuterMeasure (ExactCompilerSample HiddenTape parameters) :=
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
  calc
    law (proofRelevantUpstreamErrorUnion stages) ≤
        law (k12TwoTreeMerkle208ErrorEvent stages) +
          law (k13CircleListDecodeErrorEvent stages ∪
            (k14CoherentChainErrorEvent stages ∪
              k15SpendWitnessErrorEvent stages)) :=
      measure_union_le (μ := law) _ _
    _ ≤ law (k12TwoTreeMerkle208ErrorEvent stages) +
          (law (k13CircleListDecodeErrorEvent stages) +
            law (k14CoherentChainErrorEvent stages ∪
              k15SpendWitnessErrorEvent stages)) := by
      exact add_le_add (le_refl _)
        (measure_union_le (μ := law) _ _)
    _ ≤ law (k12TwoTreeMerkle208ErrorEvent stages) +
          (law (k13CircleListDecodeErrorEvent stages) +
            (law (k14CoherentChainErrorEvent stages) +
              law (k15SpendWitnessErrorEvent stages))) := by
      exact add_le_add (le_refl _)
        (add_le_add (le_refl _) (measure_union_le (μ := law) _ _))
    _ = proofRelevantUpstreamRawError hiddenLaw stages := by
      unfold proofRelevantUpstreamRawError
      ac_rfl

theorem proof_relevant_operational_input_probability_le_extraction_plus_raw_error
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (OperationalInput : ExactCompilerSample HiddenTape parameters → Type)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (proofRelevantOperationalInputEvent OperationalInput) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        proofRelevantUpstreamRawError hiddenLaw stages := by
  let law : OuterMeasure (ExactCompilerSample HiddenTape parameters) :=
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
  calc
    law (proofRelevantOperationalInputEvent OperationalInput) ≤
        law (exactFixedPlainRomValidClientExtractionEvent transitionFuel
          configuration fixedInstance relation ∪
            proofRelevantUpstreamErrorUnion stages) :=
      measure_mono
        (proof_relevant_operational_input_subset_extraction_union_errors
          transitionFuel configuration fixedInstance relation OperationalInput
          stages)
    _ ≤ law (exactFixedPlainRomValidClientExtractionEvent transitionFuel
            configuration fixedInstance relation) +
          law (proofRelevantUpstreamErrorUnion stages) :=
      measure_union_le (μ := law) _ _
    _ ≤ exactFixedPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration fixedInstance relation +
          proofRelevantUpstreamRawError hiddenLaw stages := by
      exact add_le_add (le_refl _)
        (proof_relevant_upstream_error_union_probability_le_raw_error
          hiddenLaw stages)

/-! ## Four separately supplied numerical bounds -/

def K12TwoTreeMerkle208ErrorMeasureBound
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (bound : ENNReal) : Prop :=
  (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (k12TwoTreeMerkle208ErrorEvent stages) ≤ bound

def K13CircleListDecodeErrorMeasureBound
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (bound : ENNReal) : Prop :=
  (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (k13CircleListDecodeErrorEvent stages) ≤ bound

def K14CoherentChainErrorMeasureBound
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (bound : ENNReal) : Prop :=
  (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (k14CoherentChainErrorEvent stages) ≤ bound

def K15SpendWitnessErrorMeasureBound
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (bound : ENNReal) : Prop :=
  (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (k15SpendWitnessErrorEvent stages) ≤ bound

/-- Numerical corollary from four independently supplied stage bounds.  It is
not stored as an interface field and does not mention a compiler event. -/
theorem proof_relevant_operational_input_probability_le_four_upstream_terms
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (OperationalInput : ExactCompilerSample HiddenTape parameters → Type)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw stages
      terms.k12TwoTreeMerkle208)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      terms.k13CircleListDecoding)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw stages
      terms.k14CoherentChainSelection)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw stages
      terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (proofRelevantOperationalInputEvent OperationalInput) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms := by
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (proofRelevantOperationalInputEvent OperationalInput) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        proofRelevantUpstreamRawError hiddenLaw stages :=
      proof_relevant_operational_input_probability_le_extraction_plus_raw_error
        hiddenLaw transitionFuel configuration fixedInstance relation
          OperationalInput stages
    _ ≤ exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms := by
      apply add_le_add (le_refl _)
      unfold proofRelevantUpstreamRawError concreteUpstreamRawError
      exact add_le_add
        (add_le_add (add_le_add k12Bound k13Bound) k14Bound) k15Bound

#print axioms ExactFixedClientExtractionCertificate.toEventMembership
#print axioms mem_exact_fixed_client_extraction_event_iff_certificate
#print axioms proof_relevant_operational_input_subset_extraction_union_errors
#print axioms proof_relevant_operational_input_without_extraction_subset_errors
#print axioms clean_subset_extraction_union_restricted_upstream_errors
#print axioms restricted_upstream_error_union_probability_le_raw_error
#print axioms
  clean_probability_le_extraction_plus_restricted_upstream_raw_error
#print axioms proof_relevant_upstream_raw_error_four_term_expansion
#print axioms proof_relevant_upstream_error_union_probability_le_raw_error
#print axioms proof_relevant_operational_input_probability_le_extraction_plus_raw_error
#print axioms proof_relevant_operational_input_probability_le_four_upstream_terms

end

end AspisK1.V7Tag73ProofRelevantUpstreamInterface
