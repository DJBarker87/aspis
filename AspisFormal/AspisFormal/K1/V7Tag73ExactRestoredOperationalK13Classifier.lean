import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.K1.V7Tag73RestoredDerivedK13View

/-!
# Exact restoration-wide operational K1.3 classifier

The original fixed-run K1.3 classifier consumes the parser-owned root proof.
That is not the correct endpoint for the state-restoring K1.6 extractor: the
completed client contains the root and every successful same-tape restored
execution, and a future q16 coordinate may first have been queried by the
adversary.

This leaf makes the corrected endpoint proof relevant.  A source provider
supplies only the canonically decoded fixed fields and verifier-recorded
challenge data for every stored accepting node.  Its q16 schedule is already
part of `RestoredOperationalK13Data`, hence is the selected record of the
retained verifier ledger rather than the opaque parsed query vector.

The total classifier returns either one actual stored-node K1.3 certificate or
an exact typed K1.3 error for every stored accepting node.  It contains no
probability bound, witness, acceptance oracle, or caller-selected query
schedule.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK13Classifier

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Source-facing material for the corrected restoration-wide classifier.

`data` is indexed by literal node membership and terminal control.  In
particular, it cannot select a different accumulator, a different node, or a
parser-owned q16 schedule.  `hasDone` prevents an empty accumulator from
turning the universal failure branch into a vacuous result. -/
structure ExactRestoredOperationalK13DataProvider
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  hasDone : Nonempty
    { node : RestoredK13Node Statement Payload //
      node ∈ (exactRestorationAccumulator input).nodes ∧
        node.verifierFinalState.current.control = .done }
  data : (node : RestoredK13Node Statement Payload) →
    node ∈ (exactRestorationAccumulator input).nodes →
    node.verifierFinalState.current.control = .done →
      RestoredOperationalK13Data configuration.machine.environment node

/-- Successful restoration-wide K1.3 classification chooses one literal
accepting node from the returned accumulator and retains its exact corrected
operational data and certificate. -/
structure ExactRestoredOperationalK13Certificate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  node : RestoredK13Node Statement Payload
  member : node ∈ (exactRestorationAccumulator input).nodes
  done : node.verifierFinalState.current.control = .done
  data : RestoredOperationalK13Data configuration.machine.environment node
  classified : RestoredOperationalK13Certificate decoder node data

/-- Failure means that every accepting node retained by the actual client has
its exact total-classifier error.  The provider's `hasDone` field makes this
statement nonvacuous. -/
structure ExactRestoredOperationalK13Error
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (provider : ExactRestoredOperationalK13DataProvider input) : Type where
  everyDoneFailed : ∀ (node : RestoredK13Node Statement Payload)
      (member : node ∈ (exactRestorationAccumulator input).nodes)
      (done : node.verifierFinalState.current.control = .done),
    RestoredOperationalK13Error decoder node (provider.data node member done)

/-- Total restoration-wide classifier.  The choice is over the finite literal
node store and the already fixed provider data; no transcript value or query
schedule is synthesized by the classifier. -/
noncomputable def classifyExactRestoredOperationalK13
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (provider : ExactRestoredOperationalK13DataProvider input) :
    ExactRestoredOperationalK13Certificate decoder input ⊕
      ExactRestoredOperationalK13Error decoder input provider := by
  classical
  by_cases succeeds : Nonempty
      (ExactRestoredOperationalK13Certificate decoder input)
  · exact Sum.inl (Classical.choice succeeds)
  · apply Sum.inr
    refine { everyDoneFailed := ?_ }
    intro node member done
    cases classified : classifyRestoredOperationalK13 decoder node
        (provider.data node member done) with
    | inl certificate =>
        exact (succeeds ⟨
          { node := node
            member := member
            done := done
            data := provider.data node member done
            classified := certificate }⟩).elim
    | inr error => exact error

/-- The failure branch exposes an actual accepting stored node and its typed
corrected K1.3 error.  This is the nonvacuous event witness consumed by the
subsequent probability decomposition. -/
theorem exact_restored_operational_k13_error_exposes_done_failure
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
    {provider : ExactRestoredOperationalK13DataProvider input}
    (failure : ExactRestoredOperationalK13Error decoder input provider) :
    ∃ (node : RestoredK13Node Statement Payload)
        (member : node ∈ (exactRestorationAccumulator input).nodes)
        (done : node.verifierFinalState.current.control = .done),
      Nonempty (RestoredOperationalK13Error decoder node
        (provider.data node member done)) := by
  rcases provider.hasDone with ⟨⟨node, member, done⟩⟩
  exact ⟨node, member, done, ⟨failure.everyDoneFailed node member done⟩⟩

/-- Conversely, a success is tied definitionally to one node in the literal
returned accumulator and never to the opaque root-only parser view. -/
theorem exact_restored_operational_k13_certificate_has_literal_node
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
    (certificate : ExactRestoredOperationalK13Certificate decoder input) :
    certificate.node ∈ (exactRestorationAccumulator input).nodes ∧
      certificate.node.verifierFinalState.current.control = .done := by
  exact ⟨certificate.member, certificate.done⟩

#print axioms classifyExactRestoredOperationalK13
#print axioms exact_restored_operational_k13_error_exposes_done_failure
#print axioms exact_restored_operational_k13_certificate_has_literal_node

end

end AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
